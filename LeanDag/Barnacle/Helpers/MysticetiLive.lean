import LeanDag.Barnacle.MysticetiLive.Statement
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.MysticetiProperties

/-!
# Mysticeti liveness helpers

Not part of the audit surface. The descent laws for Mysticeti, and they
are no longer proved here.

`goodLeaders` was L4 applied and `indirect` was a case split on a
certified candidate. Both are properties now — `LeaderCommits` and
`Indirect` — and `descent_of_properties` assembles them. What is left in
this file is the bridge: Mysticeti's notion of a good DAG is a
synchronised, populated quorum, and that is `coreLive`'s precondition
with the horizon read off the same numbers. It mentions no verdict.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A good DAG meets the timed core's precondition.** `Good` and
`coreLive` name the same three facts about the same quorum; the window
is the single slot, and its rounds fit because the wave does. -/
theorem mysticetiLive_goodGives [F : Faults Validator] :
    (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).GoodGives
      F.f (fun S {U} V T lo K => MysticetiProperties.coreLive S (U := U) V T lo K) := by
  intro U Rnd N hgood
  obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
  refine ⟨T, by omega, ?_⟩
  intro S V κ hcov hRnd hN hlead
  change S.slotRound κ + 3 ≤ N at hN
  refine ⟨hcard, Rnd, N, hsync, hRnd, hpop, hcov, ?_⟩
  intro k hk
  have := S.mono (Nat.lt_succ_iff.mp hk)
  omega

/-- **Mysticeti has the descent laws at slack `f`** — from the
properties, with no argument about `Decided` in this file. -/
theorem mysticetiLive_descent [F : Faults Validator] :
    (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f :=
  descent_of_properties _ MysticetiProperties.leaderCommits MysticetiProperties.indirect
    mysticetiLive_goodGives

#print axioms mysticetiLive_descent

end Barnacle

end LeanDag
