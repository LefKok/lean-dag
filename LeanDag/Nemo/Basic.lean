import LeanDag.Block
import LeanDag.BlockRecord

/-!
# Nemo-Nemo: the crash-fault DAG foundation

"Finding Nemo-Nemo: CFT DAG-based Consensus in the WAN."

Nemo-Nemo is crash-fault-tolerant: `n ≥ 2f+1` validators, all honest — they may
halt, but never equivocate. Its quorum is a bare **majority** `n/2+1`, which is
mathematically outside the core Byzantine model (`Faults` forces `n − f`, a
`~2n/3` supermajority). So this arc builds a self-contained crash foundation
consuming only the fault-agnostic parts of the core (`Block`, `creatorsOf`).

The crash setting is *leaner* than the Byzantine one: there is no `byzantine`
set, every validator is correct, so non-equivocation is universal and the single
quorum fact is that **two majorities intersect** — no correct-member filtering.

This file provides the majority quorum, its intersection lemma, crash block
validity, the crash universe, and the block-level lemmas the commit rule needs.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}

/-- The majority quorum: strictly more than half the validators, `n/2 + 1`. -/
def majority (Validator : Type*) [Fintype Validator] : ℕ :=
  Fintype.card Validator / 2 + 1

/-- **The one quorum fact.** Two majorities always intersect —
`(n/2+1) + (n/2+1) > n` — and, all validators being honest, the shared member is
consistent. This is the crash analogue of the core's `exists_correct_mem_inter`,
with the correctness filtering gone. -/
theorem exists_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : majority Validator ≤ Q₁.card) (h₂ : majority Validator ≤ Q₂.card) :
    (Q₁ ∩ Q₂).Nonempty := by
  rw [← Finset.card_pos]
  have hunion : (Q₁ ∪ Q₂).card ≤ Fintype.card Validator := by
    rw [← Finset.card_univ]; exact Finset.card_le_univ _
  have hadd := Finset.card_union_add_card_inter Q₁ Q₂
  unfold majority at h₁ h₂
  omega

/-- Crash block validity: like the core `ValidWrt`, but the parents quorum is the
majority `n/2+1` rather than `n − f`, and the core's `self_parent` and
`distinct_creators` fields are gone. The implementation's block verifier imposes
neither: there is no self-parent check, and duplicate-author includes are
deduplicated by the stake aggregator, not rejected. Under crash the second is
also derivable — universal non-equivocation makes duplicate creators among refs
impossible (`Universe.eq_of_mem_refs_of_creator_eq`). -/
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- Non-genesis blocks reference a **majority** of distinct validators. -/
  quorum : 0 < b.round → majority Validator ≤ (creators blk b).card

instance [DecidableEq BlockId] (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Decidable (ValidWrt blk b) :=
  decidable_of_iff
    ((∀ i ∈ b.refs, (blk i).round + 1 = b.round) ∧
      (0 < b.round → majority Validator ≤ (creators blk b).card))
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.predecessor, h.quorum⟩⟩

namespace ValidWrt

variable {blk : BlockId → Block Validator BlockId Payload}
  {b : Block Validator BlockId Payload}

/-- A non-genesis block has at least one reference (the majority quorum is
positive). -/
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty := by
  have hq : majority Validator ≤ (creatorsOf blk b.refs).card := h.quorum h0
  have hpos : 0 < (creatorsOf blk b.refs).card := by unfold majority at hq; omega
  exact nonempty_of_creatorsOf_card_pos hpos

end ValidWrt

/-- **Nemo's validity is mechanised.** -/
instance ValidWrt.mechanised :
    Validity.Mechanised (ValidWrt (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  pred := fun _ _ h => h.predecessor
  reads := by
    intro blk blk' ids b _ hb hagree h
    refine ⟨?_, ?_⟩
    · intro j hj; rw [hagree j (hb j hj)]; exact h.predecessor j hj
    · intro hr
      refine le_trans (h.quorum hr) (Finset.card_le_card ?_)
      intro c hc
      unfold creators creatorsOf at hc ⊢
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨j, hj, by rw [hagree j (hb j hj)]; exact hjc⟩
  base := by
    intro blk b h0 hr
    refine ⟨?_, ?_⟩
    · intro j hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro h; omega
  chops := by
    intro blk G b h hG
    refine ⟨?_, ?_⟩
    · intro j hj
      have := h.predecessor j hj
      change (chopBlk blk G j).round + 1 = b.round - G
      rw [chopBlk_round]; omega
    · intro hr
      change majority Validator ≤ (creatorsOf (chopBlk blk G) b.refs).card
      rw [creatorsOf_chopBlk]
      exact h.quorum (by change 0 < b.round - G at hr; omega)

/-- **And does not read the author**, so the copy fill is valid. -/
instance ValidWrt.copyStable :
    Validity.CopyStable (ValidWrt (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  copy := fun _ _ _ h => ⟨h.predecessor, h.quorum⟩

/-- **Nemo's universe**: the block record at Nemo's validity, with
non-equivocation asked of everyone — the crash model has no Byzantine
validators. -/
abbrev Universe (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] :=
  BlockRecord Validator BlockId Payload ValidWrt (Finset.univ : Finset Validator)

/-- A view: one validator's local, reference-closed sub-DAG. -/
abbrev View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] (U : Universe Validator BlockId Payload) :=
  BlockRecord.View U

namespace Universe

variable {U : Universe Validator BlockId Payload}

/-- Two ids with the same author and round are the same id — universal, no
correctness hypothesis (the crash simplification of the core's T1). -/
theorem eq_of_creator_eq {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ U.ids)
    (hc : (U.block i).creator = (U.block j).creator)
    (hround : (U.block i).round = (U.block j).round) : i = j :=
  U.no_equivocation i hi j hj (Finset.mem_univ _) hc hround

/-- Completeness, as a subset statement. -/
theorem refs_subset {i : BlockId} (hi : i ∈ U.ids) : (U.block i).refs ⊆ U.ids :=
  fun _ hj => U.complete i hi _ hj

/-- A reference sits in the round immediately below its referrer. -/
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round :=
  (U.valid i hi).predecessor j hj

/-- References of a non-genesis block carry a majority of distinct authors. -/
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    majority Validator ≤ (creatorsOf U.block (U.block i).refs).card :=
  (U.valid i hi).quorum hround

/-- A non-genesis block references at least one block. -/
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (U.block i).refs.Nonempty :=
  (U.valid i hi).refs_nonempty hround

/-- Distinct creators among references are automatic under crash: two refs of
the same block sharing a creator sit at the same round (`predecessor`), so
universal `no_equivocation` identifies them. This is why the crash `ValidWrt`
has no `distinct_creators` field. -/
theorem eq_of_mem_refs_of_creator_eq {i j k : BlockId} (hi : i ∈ U.ids)
    (hj : j ∈ (U.block i).refs) (hk : k ∈ (U.block i).refs)
    (hc : (U.block j).creator = (U.block k).creator) : j = k := by
  have h1 := U.round_of_mem_refs hi hj
  have h2 := U.round_of_mem_refs hi hk
  exact U.eq_of_creator_eq (U.refs_subset hi hj) (U.refs_subset hi hk) hc (by omega)

/-- **Two majority-backed sets of round-`n` blocks share a block.** The crash
analogue of the core's `exists_common_mem_of_quorums`: majority intersection
(all honest) plus universal non-equivocation. -/
theorem exists_common_mem_of_quorums {s t : Finset BlockId} {n : ℕ}
    (hs : ∀ q ∈ s, q ∈ U.ids ∧ (U.block q).round = n)
    (ht : ∀ q ∈ t, q ∈ U.ids ∧ (U.block q).round = n)
    (hsq : majority Validator ≤ (creatorsOf U.block s).card)
    (htq : majority Validator ≤ (creatorsOf U.block t).card) :
    ∃ q, q ∈ s ∧ q ∈ t := by
  obtain ⟨v, hv⟩ := exists_mem_inter hsq htq
  rw [Finset.mem_inter, mem_creatorsOf, mem_creatorsOf] at hv
  obtain ⟨⟨q₁, hq₁, hq₁c⟩, q₂, hq₂, hq₂c⟩ := hv
  obtain ⟨hq₁i, hq₁r⟩ := hs q₁ hq₁
  obtain ⟨hq₂i, hq₂r⟩ := ht q₂ hq₂
  have : q₁ = q₂ :=
    U.eq_of_creator_eq hq₁i hq₂i (hq₁c.trans hq₂c.symm) (by omega)
  exact ⟨q₁, hq₁, this ▸ hq₂⟩

end Universe

end Nemo

end LeanDag
