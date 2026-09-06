import LeanDag.Barnacle.FinWhale.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent

/-!
# Barnacle over FinWhale — proof

Not part of the audit surface. Every law is a property: `Agree`,
`CommitsDirect` and `CommitsCandidate` for the base laws; the support's
`OfCoverage` and `Commits` with `Indirect` for the descent, assembled by
`descent_of_support`. FinWhale's support is its slow path, at wave two
under the rule's wave of three. Round-robin liveness is at slack `f`
with `3f + 1 ≤ n` from the committee bound.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The laws, for FinWhale. -/
theorem finWhale_laws :
    BaseRule.Laws (finWhale (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun S {_} V₁ V₂ k v₁ v₂ h₁ h₂ =>
    FinWhaleProperties.agree S V₁ V₂ k v₁ v₂ h₁ h₂
  decided_of_directCommitIn := fun S {_} V k L hL hdc =>
    FinWhaleProperties.commitsDirect S _ V k L hL hdc
  candidates := fun S {_} V k L h => FinWhaleProperties.commitsCandidate S _ V k L h

/-- **A good DAG is good in the properties' terms.** -/
theorem finWhaleLive_goodOf :
    ∀ U Rnd N, (finWhaleLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).Good U Rnd N →
      GoodOf (finWhaleLive (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)).toBaseRule.toDagRule (coreReliability Validator) U Rnd N :=
  fun _ _ _ ⟨T, hT, hcard, hs, hpop⟩ => ⟨T, ⟨hT, hcard⟩, hs, hpop⟩

/-- **The descent laws, for FinWhale at slack `f`** — from its support. -/
theorem finWhaleLive_descent :
    (finWhaleLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f :=
  descent_of_support (finWhaleLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))
    FinWhaleProperties.fwSupport FinWhaleProperties.fwSupport_ofCoverage
    FinWhaleProperties.fwSupport_commits FinWhaleProperties.indirect (by change 2 ≤ 3; omega)
    finWhaleLive_goodOf

namespace FinWhale

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ _
    exact finWhale_laws
  · intro Validator BlockId Payload _ _ F _ _
    exact finWhaleLive_descent
  · intro n hn F P BlockId Payload _ W hk m hm hmax
    have hbound : (finWhaleLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      change 3 * F.f + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ finWhaleLive_descent (by change 0 < 3; omega) hbound hk m hm hmax

end FinWhale

end Barnacle

end LeanDag
