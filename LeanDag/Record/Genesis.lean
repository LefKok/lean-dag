import LeanDag.BlockRecord

/-!
# Re-genesis, at the block record

`addGenesis U v g p hg hsev` extends a record with one reference-free
block at round zero for a validator that has none. Built once: the new
block is valid by the predicate's `base`, the old blocks by its `reads`,
and non-equivocation holds because the author had no block.
-/

namespace LeanDag

namespace BlockRecord

variable {Validator : Type*} {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [P.Mechanised]

/-- **Re-genesis.** -/
def addGenesis (U : BlockRecord Validator BlockId Payload P honest) (v : Validator)
    (g : BlockId) (p : Payload) (hg : g ∉ U.ids)
    (hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v) :
    BlockRecord Validator BlockId Payload P honest where
  ids := insert g U.ids
  block b := if b ∈ U.ids then U.block b else ⟨0, v, ∅, p⟩
  complete := by
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with rfl | ho
    · rw [if_neg hg] at hj
      exact absurd hj (Finset.notMem_empty j)
    · rw [if_pos ho] at hj
      exact Finset.mem_insert_of_mem (U.complete i ho j hj)
  valid := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | ho
    · rw [if_neg hg]
      exact Validity.Mechanised.base _ _ rfl rfl
    · rw [if_pos ho]
      exact Validity.Mechanised.reads U.block _ U.ids (U.block i) U.complete
        (U.complete i ho) (fun j hj => if_pos hj) (U.valid i ho)
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rcases Finset.mem_insert.mp hi with rfl | ho <;>
      rcases Finset.mem_insert.mp hj with rfl | ho'
    · rfl
    · rw [if_neg hg, if_pos ho'] at hcc
      exact absurd hcc.symm (hsev j ho')
    · rw [if_pos ho, if_neg hg] at hcc
      exact absurd hcc (hsev i ho)
    · rw [if_pos ho] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact U.no_equivocation i ho j ho' hic hcc hrr

variable {U : BlockRecord Validator BlockId Payload P honest} {v : Validator}
variable {g : BlockId} {p : Payload}
variable {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}

@[simp] theorem addGenesis_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (addGenesis U v g p hg hsev).block b = U.block b := if_pos hb

@[simp] theorem addGenesis_block_new :
    (addGenesis U v g p hg hsev).block g = ⟨0, v, ∅, p⟩ := if_neg hg

theorem addGenesis_ids : (addGenesis U v g p hg hsev).ids = insert g U.ids := rfl

theorem mem_addGenesis : g ∈ (addGenesis U v g p hg hsev).ids := Finset.mem_insert_self _ _

end BlockRecord

end LeanDag
