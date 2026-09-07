import LeanDag.Barnacle.OptimalHydrozoan.Statement
import LeanDag.OptimalHydrozoan.Carrier
/-!
# Barnacle over Optimal-Hydrozoan — proof

Unaudited. Two laws are read off the `View` structure and the other
three are the properties Optimal-Hydrozoan's own carrier shows: `agree`
is `Agree`, `candidates` is `CommitsCandidate`, and
`decided_of_directCommitIn` is `CommitsDirect` — which is what that
optional property is for. Nothing here inspects `DecidedOpt`.

The two carriers agree on the decision relation by construction:
`Barnacle.slotsOf` and `Hydrozoan.ofCoreSlots` build the same schedule
from the same fields, and both rules read `optUniverseOf` at it.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoan

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _
  exact
    { full_ids := fun _ => rfl
      historyView_ids := fun _ _ _ => rfl
      agree := fun S {_} V₁ V₂ k v₁ v₂ h₁ h₂ =>
        LeanDag.OptimalHydrozoanProperties.agree S V₁ V₂ k v₁ v₂ h₁ h₂
      decided_of_directCommitIn := fun S {_} V k L hL hdc =>
        LeanDag.OptimalHydrozoanProperties.commitsDirect S _ V k L hL hdc
      candidates := fun S {_} V k L h =>
        LeanDag.OptimalHydrozoanProperties.commitsCandidate S _ V k L h }

end OptimalHydrozoan

end Barnacle

end LeanDag
