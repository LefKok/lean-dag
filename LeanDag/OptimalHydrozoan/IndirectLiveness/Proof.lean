import LeanDag.OptimalHydrozoan.IndirectLiveness.Statement
import LeanDag.OptimalHydrozoan.Helpers.Decided
import LeanDag.Anchored.Bounded

/-!
# Optimal-Hydrozoan: indirect liveness — proof

Generated. Totality and the descent are the relation's
`exists_decided_of_anchor` and `decided_below_of_committed_run` at the
rule's rung choices, the latter at the run's last slot `n := b + c - 1`.
-/

namespace LeanDag

namespace OptimalHydrozoan
namespace IndirectLiveness

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ U
  constructor
  · intro V k j A helig hj hmid
    exact AnchoredRule.exists_decided_of_anchor exists_least helig hj hmid
  · intro V b c hc hspan hrun i hi
    exact AnchoredRule.decided_below_of_committed_run exists_least (by omega)
      (fun i' hi' => hspan b i' hi') hrun i hi

end IndirectLiveness
end OptimalHydrozoan

end LeanDag
