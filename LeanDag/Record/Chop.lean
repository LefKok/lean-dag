import LeanDag.BlockRecord

/-!
# The cut, at the block record

`chop U G` keeps the blocks at or above the horizon, rebases rounds by
`−G`, and strips the references of the new base layer. Built once, for
any validity predicate that is `Mechanised`; every rule's cut is this at
its own record.
-/

namespace LeanDag

namespace BlockRecord

variable {Validator : Type*} {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [P.Mechanised]

/-- **The cut.** -/
def chop (U : BlockRecord Validator BlockId Payload P honest) (G : ℕ) :
    BlockRecord Validator BlockId Payload P honest where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlk U.block G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hj
      have hjr := Validity.Mechanised.pred U.block (U.block i) (U.valid i hi.1) j hj
      exact Finset.mem_filter.mpr ⟨U.complete i hi.1 j hj, by omega⟩
    · rw [chopBlk_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlk_of_lt h]
      exact Validity.Mechanised.chops U.block G (U.block i) (U.valid i hi.1) h
    · apply Validity.Mechanised.base
      · rw [chopBlk_round]; omega
      · exact chopBlk_refs_of_le h
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rw [Finset.mem_filter] at hi hj
    simp only [chopBlk_creator, chopBlk_round] at hic hcc hrr
    exact U.no_equivocation i hi.1 j hj.1 hic hcc (by omega)

variable {U : BlockRecord Validator BlockId Payload P honest} {G : ℕ} {i : BlockId}

@[simp] theorem mem_chop_ids :
    i ∈ (U.chop G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  Finset.mem_filter

theorem chop_ids : (U.chop G).ids = U.ids.filter fun i => G ≤ (U.block i).round := rfl

@[simp] theorem chop_block : (U.chop G).block = chopBlk U.block G := rfl

/-- **A view, truncated at the horizon**: keep what clears the cut. -/
def View.chop (V : U.View) (G : ℕ) : (U.chop G).View where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := Finset.filter_subset_filter _ V.subset_ids
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    change j ∈ (chopBlk U.block G i).refs at hj
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hj
      have hjr := Validity.Mechanised.pred U.block (U.block i)
        (U.valid i (V.subset_ids hi.1)) j hj
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj, by omega⟩
    · rw [chopBlk_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)

theorem View.chop_ids (V : U.View) :
    (V.chop G).ids = V.ids.filter fun i => G ≤ (U.block i).round := rfl

end BlockRecord

end LeanDag
