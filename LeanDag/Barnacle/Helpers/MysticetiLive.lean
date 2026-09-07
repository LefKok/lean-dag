import LeanDag.Barnacle.MysticetiLive.Statement
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Mysticeti.Properties
/-!
# Mysticeti liveness helpers

Not part of the audit surface. The descent laws for Mysticeti, and they
are no longer proved here.

`goodLeaders` was L4 applied and `indirect` was a case split on a
certified candidate. Both come from the properties now — L4 from
`coreSupport`'s `OfCoverage` and `Commits`, the case split from
`Indirect` — and `descent_of_support` assembles them. What is left in
this file is the one-line fact that Mysticeti's good DAG — a
synchronised, populated quorum — is `GoodOf` at the core's fault model.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}


/-- **A good DAG is good in the properties' terms**: the same quorum,
the same coverage, the same production. -/
theorem mysticetiLive_goodOf [F : Faults Validator] :
    ∀ U Rnd N, (mysticetiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).Good U Rnd N →
      GoodOf (mysticetiLive (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)).toBaseRule.toDagRule (coreReliability Validator) U Rnd N :=
  fun _ _ _ ⟨T, hT, hcard, hs, hpop⟩ => ⟨T, ⟨hT, hcard⟩, hs, hpop⟩

/-- **Mysticeti has the descent laws at slack `f`** — from its support,
with no `LeaderCommits` and no precondition of its own in this file. -/
theorem mysticetiLive_descent [F : Faults Validator] :
    (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f :=
  descent_of_support (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    MysticetiProperties.coreSupport MysticetiProperties.coreSupport_ofCoverage
    MysticetiProperties.coreSupport_commits MysticetiProperties.indirect (by change 2 ≤ 3; omega)
    mysticetiLive_goodOf

#print axioms mysticetiLive_descent

end Barnacle

end LeanDag
