import LeanDag.Barnacle.Odontoceti.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.OdontocetiProperties

/-!
# Odontoceti instance helpers

Not part of the audit surface. The laws are O5 (`decided_unique`), the
direct constructor and `isLeaderBlock_of_decided`; the descent laws are
O7 (`decided_of_leader_mem`) and the two indirect constructors, the
commit one at the least candidate with a thick link.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The laws, for Odontoceti. -/
theorem odontoceti_laws [Faults5 Validator] :
    BaseRule.Laws (odontoceti (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun S {_} V₁ V₂ k v₁ v₂ h₁ h₂ =>
    OdontocetiProperties.agree S V₁ V₂ k v₁ v₂ h₁ h₂
  decided_of_directCommitIn := fun S {_} V k L hL hdc =>
    OdontocetiProperties.commitsDirect S _ V k L hL hdc
  candidates := fun S {_} V k L h => OdontocetiProperties.commitsCandidate S _ V k L h


/-- **A good DAG is good in the properties' terms.** -/
theorem odontocetiLive_goodOf [F : Faults5 Validator] :
    ∀ U Rnd N, (odontocetiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).Good U Rnd N →
      GoodOf (odontocetiLive (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)).toBaseRule.toDagRule (coreReliability Validator) U Rnd N :=
  fun _ _ _ ⟨T, hT, hcard, hs, hpop⟩ => ⟨T, ⟨hT, hcard⟩, hs, hpop⟩

/-- **The descent laws, for Odontoceti at slack `f`** — from its
support. -/
theorem odontocetiLive_descent [F : Faults5 Validator] :
    (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f :=
  descent_of_support (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (Properties.voteSupport _) (Properties.voteSupport_ofCoverage _)
    OdontocetiProperties.voteSupport_commits OdontocetiProperties.indirect (by change 1 ≤ 2; omega)
    odontocetiLive_goodOf

end Barnacle

end LeanDag
