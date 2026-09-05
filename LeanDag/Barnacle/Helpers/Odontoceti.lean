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
  agree := fun _ {_} _ _ _ _ _ h₁ h₂ => Odontoceti.decided_unique h₁ _ _ h₂
  decided_of_directCommitIn := fun _ {_} _ _ _ hL hdc => Odontoceti.Decided.directCommit hL hdc
  candidates := fun _ {_} _ _ _ h => Odontoceti.isLeaderBlock_of_decided h

/-- **A good DAG meets Odontoceti's precondition.** `Good` and
`OdontocetiProperties.odontocetiLive` name the same three facts about
the same quorum, at Odontoceti's own wavelength — the horizon sits one
round above the slot, where the core's sits two. -/
theorem odontocetiLive_goodGives [F : Faults5 Validator] :
    (odontocetiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).GoodGives F.f
      (fun S {U} V T lo K => OdontocetiProperties.odontocetiLive S (U := U) V T lo K) := by
  intro U Rnd N hgood
  obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
  refine ⟨T, by omega, ?_⟩
  intro S V κ hcov hRnd hN hlead
  change S.slotRound κ + 2 ≤ N at hN
  refine ⟨hcard, Rnd, N, hsync, hRnd, hpop, hcov, ?_⟩
  intro k hk
  have := S.mono (Nat.lt_succ_iff.mp hk)
  omega

/-- **The descent laws, for Odontoceti at slack `f`** — from the
properties, with no argument about `Decided` here. -/
theorem odontocetiLive_descent [F : Faults5 Validator] :
    (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f :=
  descent_of_properties _ OdontocetiProperties.leaderCommits OdontocetiProperties.indirect
    odontocetiLive_goodGives


end Barnacle

end LeanDag
