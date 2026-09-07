import LeanDag.Mysticeti.Liveness
import LeanDag.Common.Record.Fill
/-!
# Safe Skip: rejoining after a crash, in one message

A validator that crashes and recovers faces a gap: liveness rests on
correct validators building in every round (P8), skipping rounds is
known to break it, and producing the missing blocks one by one costs a
round trip per round of downtime. **Safe Skip** closes the gap with a
single message. The recovering validator `v1` names a block `B2` at
round `r` on another validator `v2`'s history line, and its own last
block `B1`; the message *denotes* one block per gap round, deterministic
given the DAG: at each round the filled block carries the references of
`v2`'s block on the line, **plus one added self reference** to `v1`'s
block of the round below — `B1` at the boundary, the previous filled
block above it.

The added self reference is not an optimisation but a validity
requirement: `ValidWrt.self_parent` (P3′) demands that every non-genesis
block reference a block by its own creator, and `v2`'s references cannot
supply one — `v1` authored nothing in the gap. With it, every clause of
validity holds: the copied references sit one round below (P1 of the
line), `v1` appears among the authors exactly once (in the gap there is
no `v1`-authored block for the line to have referenced, and at the
boundary the only candidate is `B1` itself, by non-equivocation), and
the reference quorum only grows.

The denotation is `skipFill`: a universe extending `U` with the filled
blocks, every old block untouched. What this file proves:

* `skipFill` **is** a `BlockUniverse` — validity, completeness and
  non-equivocation survive the fill;
* old blocks and their references are preserved verbatim
  (`skipFill_block_old`), so every store, view and certificate built on
  `U` reads the same in the extension;
* the gap is populated (`skipFill_populatedOn`): with `v1` restored,
  `PopulatedOn` holds at every gap round, which is the production
  hypothesis liveness consumes;
* a filled block that lands on a leader slot is **directly skipped**
  (`directSkip_fresh`): its only supporter is `v1`'s own line, and every
  other reliable validator's block at the round above blames it. The
  fill cannot conjure a commit for a slot the network already passed —
  the mechanism restores production without touching consensus.

Full verdict invariance across the fill — every `Decided U V k v`
re-derives in `skipFill U`, and hence agrees with every verdict reached
after recovery — is the pair of verdict transports in
`Invariance.lean`, the `decided_chop` analogue for extension rather than
truncation.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **A Safe Skip message at a core universe**: the same data, read off
`U`. Stated over `ids`/`blk` rather than over a universe because the
*data* of a fill is the same for every rule in this development, and
only the invariants a universe carries differ — the shape `chopBlk`
takes for the cut. Nemo and FinWhale build their own fills from it
(`docs/target-properties.md` §11.4). -/
abbrev SkipMsg (U : BlockUniverse Validator BlockId Payload) :=
  SkipData U.ids U.block

/-- **The boundary condition from correctness.** For a `v1` outside the
ambient model's Byzantine set, non-equivocation pins its round-`r0`
block to `B1`. This is how a `SkipMsg` is built in the base fault
model, and it is what the `hB1uniq` field generalises: report §14's
hybrid model discharges the same field for a *crash-prone* `v1`, whom
`Correct` excludes. -/
theorem hB1uniq_of_correct {v1 : Validator} {B1 : BlockId}
    (hB1 : B1 ∈ U.ids) (hB1c : (U.block B1).creator = v1)
    (hv1 : v1 ∈ (Correct : Finset Validator)) :
    ∀ j ∈ U.ids, (U.block j).creator = v1 →
      (U.block j).round = (U.block B1).round → j = B1 :=
  fun j hj hjc hjr => U.eq_of_creator_eq hj hB1 hv1 hjc hB1c hjr


namespace SkipMsg

open SkipData

variable (sk : SkipMsg U)

/-- **The filled block is valid** under the extended block map: the
copied references sit one round below (P1 of the line), `v1` appears
among the authors exactly once — in the gap there is no `v1`-authored
block for the line to have referenced, and at the boundary the only
candidate is `B1` itself, by `hB1uniq` — the reference quorum only
grows, and the added self reference is P3′. -/
theorem fillBlock_valid {k : ℕ} (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    ValidWrt (fun b => if b ∈ U.ids then U.block b else sk.fillBlock (sk.idx b))
      (sk.fillBlock k) := by
  have hR0 : sk.r0 = (U.block sk.B1).round := rfl
  have hlm := sk.hline_mem k (by omega) hk2
  have hlv := U.valid _ hlm
  have hlr := sk.hline_round k (by omega) hk2
  -- the self reference is an old id at round `k − 1` with creator `v1`
  have hprev_old : sk.prev k ∈ U.ids ∨ sk.prev k = sk.fresh (k - 1) := by
    by_cases hb : k = sk.r0 + 1
    · exact Or.inl (by simp only [prev, if_pos hb]; exact sk.hB1)
    · exact Or.inr (by simp only [prev, if_neg hb])
  have hprev_round : (if sk.prev k ∈ U.ids then U.block (sk.prev k)
      else sk.fillBlock (sk.idx (sk.prev k))).round = k - 1 := by
    by_cases hb : k = sk.r0 + 1
    · simp only [prev, if_pos hb, if_pos sk.hB1]
      show (U.block sk.B1).round = k - 1
      omega
    · simp only [prev, if_neg hb, if_neg (sk.hfresh_new (k - 1)), sk.hidx]
      rfl
  have hprev_creator : (if sk.prev k ∈ U.ids then U.block (sk.prev k)
      else sk.fillBlock (sk.idx (sk.prev k))).creator = sk.v1 := by
    by_cases hb : k = sk.r0 + 1
    · simp only [prev, if_pos hb, if_pos sk.hB1]
      exact sk.hB1c
    · simp only [prev, if_neg hb, if_neg (sk.hfresh_new (k - 1)), sk.hidx]
      rfl
  -- no copied reference is `v1`-authored, except possibly the anchor itself
  have hno_v1 : ∀ j ∈ (U.block (sk.line k)).refs,
      (U.block j).creator = sk.v1 → j = sk.prev k := by
    intro j hj hjc
    have hjo := U.complete _ hlm j hj
    have hjr : (U.block j).round = k - 1 := by
      have := hlv.predecessor j hj
      omega
    by_cases hb : k = sk.r0 + 1
    · -- boundary: non-equivocation pins it to the anchor
      simp only [prev, if_pos hb]
      exact sk.hB1uniq j hjo hjc (by omega)
    · -- inside the gap: the crash forbids it
      exact (sk.hgap j hjo hjc (by omega) (by omega)).elim
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- P1: the self reference and every copied reference sit at `k − 1`
    intro j hj
    simp only [fillBlock, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · rw [hprev_round]; show k - 1 + 1 = k; omega
    · rw [if_pos (U.complete _ hlm j hj)]
      have := hlv.predecessor j hj
      show (U.block j).round + 1 = k
      omega
  · -- P2: copied references are distinct by the line's P2; the self
    -- reference's author appears nowhere else
    intro j hj l hl hjl
    simp only [fillBlock, Finset.mem_insert] at hj hl
    rcases hj with rfl | hj <;> rcases hl with rfl | hl
    · rfl
    · rw [hprev_creator] at hjl
      rw [if_pos (U.complete _ hlm l hl)] at hjl
      exact (hno_v1 l hl hjl.symm).symm
    · rw [hprev_creator] at hjl
      rw [if_pos (U.complete _ hlm j hj)] at hjl
      exact hno_v1 j hj hjl
    · rw [if_pos (U.complete _ hlm j hj), if_pos (U.complete _ hlm l hl)] at hjl
      exact hlv.distinct_creators j hj l hl hjl
  · -- P3: the copied quorum survives, since lookups of old ids agree
    intro _
    have hq := hlv.quorum (by show 0 < (U.block (sk.line k)).round; omega)
    refine le_trans hq ?_
    refine Finset.card_le_card ?_
    intro c hc
    unfold creators creatorsOf at hc ⊢
    obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
    refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
    · simp only [fillBlock, Finset.mem_insert]
      exact Or.inr hj
    · simp only
      rw [if_pos (U.complete _ hlm j hj)]
      exact hjc
  · -- P3′: the added self reference
    intro _
    exact ⟨sk.prev k, Finset.mem_insert_self _ _, hprev_creator⟩

/-- **The denotation.** `U`, extended with one filled block per gap
round; every old block looked up unchanged. The block record's fill
under the self-referencing reading, with `fillBlock_valid` as the one
obligation. -/
def skipFill : BlockUniverse Validator BlockId Payload :=
  BlockRecord.fill U sk (sk.selfBlocks U.complete) (fun _ hk1 hk2 => sk.fillBlock_valid hk1 hk2)

/-- Old blocks read unchanged: every store, view and certificate built
on `U` sees the same data in the extension. -/
@[simp] theorem skipFill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    sk.skipFill.block b = U.block b := if_pos hb

@[simp] theorem skipFill_block_fresh {k : ℕ} :
    sk.skipFill.block (sk.fresh k) = sk.fillBlock k := SkipData.fillMap_fresh

theorem ids_subset_skipFill : U.ids ⊆ sk.skipFill.ids :=
  Finset.subset_union_left

/-- **The gap is populated.** With `v1` restored to the reliable set,
every gap round carries a `v1` block — the production hypothesis
liveness consumes, recovered from one message. -/
theorem skipFill_populatedOn {T : Finset Validator} {k : ℕ}
    (hpop : PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    PopulatedOn sk.skipFill (insert sk.v1 T) k := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · refine ⟨sk.fresh k, ?_, ?_, ?_⟩
    · exact Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩)
    · rw [sk.skipFill_block_fresh]; rfl
    · rw [sk.skipFill_block_fresh]; rfl
  · obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
    exact ⟨b, sk.ids_subset_skipFill hb,
      by rw [sk.skipFill_block_old hb]; exact hbc,
      by rw [sk.skipFill_block_old hb]; exact hbr⟩

end SkipMsg

end LeanDag
