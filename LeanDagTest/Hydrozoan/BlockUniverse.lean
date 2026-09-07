import LeanDag.Hydrozoan.Helpers.Block
import LeanDagTest.Hydrozoan.Model
/-!
# Witness: a block universe with faults

A concrete two-round `BlockUniverse` over the seven-replica fault model
of `HydrozoanTest.Model`: Byzantine replica 0 equivocates at round 1
(two blocks, ids 7 and 8), and crashed replica 1 creators its genesis
block but nothing afterwards — halting made visible. All universe
conditions are checked by `decide`.

The negative examples keep the definitions biting: the *unguarded*
non-equivocation is false in this universe (so the `NonByzantine` guard
does real work), and each `ValidWrt` field individually rejects a
malformed block.
-/

namespace LeanDagTest

namespace Hydrozoan

open LeanDag LeanDag.Hydrozoan

/-- Fourteen blocks over the seven replicas: ids 0–6 genesis (creator =
id), ids 7 and 8 round-1 blocks both by Byzantine replica 0
(equivocation, with different parent quorums), ids 9–13 round-1 blocks
by replicas 2–6. Crashed replica 1 creators only its genesis block. -/
def lk : Fin 14 → Block (Fin 7) (Fin 14) := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 7 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4}, payload := () }
  else if (i : ℕ) = 8 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 5}, payload := () }
  else
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩, refs := {0, 1, 2, 3, 4}, payload := () }

/-- The witness universe: all fourteen blocks satisfy completeness,
validity, and (`NonByzantine`-guarded) non-equivocation. -/
def U : BlockUniverse (Fin 7) (Fin 14) where
  ids := Finset.univ
  block := lk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The guard does real work: WITHOUT the `NonByzantine` restriction,
-- non-equivocation is FALSE in `U` — ids 7 and 8 are a genuine Byzantine
-- equivocations.
example :
    ¬ (∀ i ∈ U.ids, ∀ j ∈ U.ids,
      (U.block i).creator = (U.block j).creator →
      (U.block i).round = (U.block j).round → i = j) := by
  decide

-- Crashed replica 1 halts after genesis: no round-1 block by it exists.
example : ∀ i : Fin 14, (lk i).round = 1 → (lk i).creator ≠ 1 := by decide

-- `predecessor` bites: a round-2 block referencing genesis blocks.
example :
    ¬ ValidWrt lk { round := 2, creator := 2, refs := {0, 1, 2, 3, 4}, payload := () } := by
  decide

-- `distinct_creators` bites: refs include both of creator 0's
-- equivocating round-1 blocks (five distinct creators, so `quorum` alone
-- would pass).
example :
    ¬ ValidWrt lk { round := 2, creator := 2, refs := {7, 8, 9, 10, 11, 12}, payload := () } := by
  decide

-- `quorum` bites: only four distinct creators, one short of q = 5.
example :
    ¬ ValidWrt lk { round := 1, creator := 2, refs := {0, 1, 2, 3}, payload := () } := by
  decide

end Hydrozoan

end LeanDagTest
