import LeanDag.Common.Block
import LeanDag.Common.BlockRecord
import LeanDag.Common.Density
/-!
# The block universe

`spec.md` §3.3 and the non-equivocation lemma T1.

A `BlockUniverse` is every block that exists — authored by anyone, correct
or Byzantine. Non-equivocation is stated **here**, at the universe level,
rather than on any individual DAG. Per-DAG would be too weak: two DAGs could
each satisfy "at most one block per correct validator per round" while
holding *different* such blocks, which is exactly a correct validator
equivocating, with both DAGs looking well-formed. T5 would silently break.

Note the `valid` field reads `ValidWrt block (block i)`, mentioning only its
sibling field `block`. That is the whole reason `ValidWrt` (§3.2) takes a
lookup function rather than a universe: a structure field cannot mention the
structure being defined.
-/

namespace LeanDag

/-- **The core's fault model, as a counting parameter.** `Correct` is
`byzantineᶜ`, so the slack is exactly `|byzantine| ≤ f`, and `n = 3f + 1`
makes it a minority. -/
def coreReliability (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] : Reliability Validator where
  correct := (Correct : Finset Validator)
  slack := F.f
  covers := by
    have : (Correct : Finset Validator)ᶜ = F.byzantine := by
      simp [Correct]
    rw [this]; exact F.card_byzantine
  minority := by have := F.card_validators; omega

@[simp] theorem coreReliability_correct (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] :
    (coreReliability Validator).correct = (Correct : Finset Validator) := rfl

@[simp] theorem coreReliability_slack (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] [F : Faults Validator] :
    (coreReliability Validator).slack = F.f := rfl

/-- **The block universe**: every block that exists, authored by anyone,
correct or Byzantine. The block record (`BlockRecord.lean`) at the
core's validity predicate, with non-equivocation asked of the correct
validators only. `block` is total, with junk outside `ids`; every clause
quantifies over `i ∈ ids`, so the junk is never observed. -/
abbrev BlockUniverse (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] [Faults Validator] :=
  BlockRecord Validator BlockId Payload ValidWrt (Correct : Finset Validator)

/-- **A view**: one validator's local sub-DAG, a subset of the universe
itself closed under references. Views share `U.block`, so they disagree
about *which* blocks they hold, never about what an id denotes, and they
inherit validity and non-equivocation from `U` unchanged. Different
correct validators may hold different views — that asymmetry is the
entire point of the cross-view results. -/
abbrev View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator]
    (U : BlockUniverse Validator BlockId Payload) :=
  BlockRecord.View U

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable (U : BlockUniverse Validator BlockId Payload)

namespace BlockUniverse

variable {U}

/-- **T1.** A correct validator authors at most one block per round, so two
ids in the universe with the same correct author and the same round are the
*same id*.

Phrased around the author `v` rather than around `(U.block i).creator`,
because that is how every use site arrives: a quorum intersection yields a
correct validator, and T1 turns two blocks known to be authored by it into a
single concrete id. -/
theorem eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ (Correct : Finset Validator))
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) :
    i = j :=
  U.no_equivocation i hi j hj (hic ▸ hv) (hic.trans hjc.symm) hround

/-- Completeness, as a subset statement. -/
theorem refs_subset {i : BlockId} (hi : i ∈ U.ids) : (U.block i).refs ⊆ U.ids :=
  fun _ hj => U.complete i hi _ hj

/-- A reference sits in the round immediately below its referrer. -/
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round :=
  (U.valid i hi).predecessor j hj

/-- References of a non-genesis block carry a quorum of distinct authors.
This is the hypothesis T0' consumes. -/
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    quorumCard Validator ≤ (creatorsOf U.block (U.block i).refs).card :=
  (U.valid i hi).quorum hround

/-- **The core's universes are quorate**: validity's counting clause,
read off. -/
theorem quorateOn (U : BlockUniverse Validator BlockId Payload) :
    QuorateOn U.block U.ids (coreReliability Validator) :=
  fun b hb hr => U.creators_quorum hb hr

/-- A non-genesis block references at least one block. -/
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (U.block i).refs.Nonempty :=
  (U.valid i hi).refs_nonempty hround

/-- **Two quorum-backed sets of round-`n` blocks must share a block.**

T0' gives a correct author common to both creator sets, and T1 makes that
author's round-`n` block unique — so the two blocks it contributes coincide.

This is the recurring "peel off one certification layer" step: it is exactly
what M5′ does to two certificates' vote sets, and what M5 would otherwise do a second time to two certificate sets. -/
theorem exists_common_mem_of_quorums {s t : Finset BlockId} {n : ℕ}
    (hs : ∀ q ∈ s, q ∈ U.ids ∧ (U.block q).round = n)
    (ht : ∀ q ∈ t, q ∈ U.ids ∧ (U.block q).round = n)
    (hsq : quorumCard Validator ≤ (creatorsOf U.block s).card)
    (htq : quorumCard Validator ≤ (creatorsOf U.block t).card) :
    ∃ q, q ∈ s ∧ q ∈ t := by
  obtain ⟨v, hv_inter, hv_correct⟩ := exists_correct_mem_creators_inter hsq htq
  rw [Finset.mem_inter] at hv_inter
  obtain ⟨hv_s, hv_t⟩ := hv_inter
  rw [mem_creatorsOf] at hv_s hv_t
  obtain ⟨q₁, hq₁, hq₁_creator⟩ := hv_s
  obtain ⟨q₂, hq₂, hq₂_creator⟩ := hv_t
  obtain ⟨hq₁_ids, hq₁_round⟩ := hs q₁ hq₁
  obtain ⟨hq₂_ids, hq₂_round⟩ := ht q₂ hq₂
  have hqq : q₁ = q₂ :=
    U.eq_of_creator_eq hq₁_ids hq₂_ids hv_correct hq₁_creator hq₂_creator (by omega)
  exact ⟨q₁, hq₁, hqq ▸ hq₂⟩

end BlockUniverse


/-! ## What the core's validity owes the mechanisms -/

section Mechanised

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}

/-- **The core's validity is the family** at the core's quorum, with
distinct creators and the self-parent clause. -/
theorem ValidWrt.iff_validAt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) :
    ValidWrt blk b ↔ ValidAt (quorumCard Validator) (Clause.distinct.and Clause.selfParent) blk b :=
  ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators, h.self_parent⟩,
   fun h => ⟨h.predecessor, h.clause.1, h.quorum, h.clause.2⟩⟩

/-- **The core's validity is mechanised**, along the family. -/
instance ValidWrt.mechanised :
    Validity.Mechanised
      (ValidWrt (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Validity.Mechanised.of_iff ValidWrt.iff_validAt

end Mechanised

end LeanDag
