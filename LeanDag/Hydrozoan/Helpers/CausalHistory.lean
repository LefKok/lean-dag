import LeanDag.Hydrozoan.Model.View
import LeanDag.CausalHistory

/-!
# Causal-reachability lemmas

Generated infrastructure. Reachability is the shared `Reaches` at the
block record; what remains here is the one fact stated in Hydrozoan's
own vocabulary. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [F : LeanDag.Hydrozoan.Faults Replica] {U : BlockUniverse Replica BlockId}

/-- Refs of a universe member sit exactly one round below it. -/
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids)
    (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round :=
  (U.valid i hi).predecessor j hj

end Hydrozoan

end LeanDag
