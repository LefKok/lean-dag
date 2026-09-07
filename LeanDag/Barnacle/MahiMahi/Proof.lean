import LeanDag.Barnacle.MahiMahi.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.MahiMahi.Properties
/-!
# Barnacle over Mahi-Mahi — proof

Not part of the audit surface. Every law is a property: `Agree`,
`CommitsDirect` and `CommitsCandidate` for the base laws; the support's
`OfCoverage` and `Commits` with `Indirect` for the descent, assembled by
`descent_of_support`. What is left is the one-line fact that Mahi-Mahi's
good DAG is `GoodOf` at the core's fault model, and the round-robin
bound, taken as a hypothesis.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The laws, for Mahi-Mahi. -/
theorem mahiMahi_laws [Faults Validator] {w : ℕ} (hw : 2 ≤ w) :
    BaseRule.Laws (mahiMahi (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun S {_} V₁ V₂ k v₁ v₂ h₁ h₂ =>
    MahiMahiProperties.agree hw S V₁ V₂ k v₁ v₂ h₁ h₂
  decided_of_directCommitIn := fun S {_} V k L hL hdc =>
    MahiMahiProperties.commitsDirect w S _ V k L hL hdc
  candidates := fun S {_} V k L h => MahiMahiProperties.commitsCandidate w S _ V k L h

/-- **A good DAG is good in the properties' terms.** -/
theorem mahiMahiLive_goodOf [Faults Validator] {w : ℕ} :
    ∀ U Rnd N, (mahiMahiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w).Good U Rnd N →
      GoodOf (mahiMahiLive (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) w).toBaseRule.toDagRule (coreReliability Validator) U Rnd N :=
  fun _ _ _ ⟨T, hT, hcard, hs, hpop⟩ => ⟨T, ⟨hT, hcard⟩, hs, hpop⟩

/-- **The descent laws, for Mahi-Mahi at slack `f`** — from its support. -/
theorem mahiMahiLive_descent [F : Faults Validator] {w : ℕ} (hw : 4 ≤ w) :
    (mahiMahiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w).Descent
      F.f :=
  descent_of_support (mahiMahiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
    (MahiMahiProperties.mmSupport w) (MahiMahiProperties.mmSupport_ofCoverage hw)
    (MahiMahiProperties.mmSupport_commits (by omega)) (MahiMahiProperties.indirect (by omega))
    (by change w - 1 ≤ w; omega) mahiMahiLive_goodOf

namespace MahiMahi

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ w hw
    exact mahiMahi_laws hw
  · intro Validator BlockId Payload _ _ F _ w hw
    exact mahiMahiLive_descent hw
  · intro n hn F BlockId Payload _ w hw hbound W hk m hm hmax
    have hbound' : (mahiMahiLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload) w).waveLength * F.f + 1 ≤ n := hbound
    exact liveOn_roundRobin hn _ (mahiMahiLive_descent hw) (by change 0 < w; omega) hbound'
      hk m hm hmax

end MahiMahi

end Barnacle

end LeanDag
