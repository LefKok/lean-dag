import LeanDag.Barnacle.OptimalHydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.OptimalHydrozoan.Carrier

/-!
# Barnacle over Optimal-Hydrozoan — the live rule, proof

Unaudited, and the mirror of `Barnacle/HydrozoanLive/Proof.lean`.
`goodLeaders` was OH5 and `indirect` was OH6, each applied without
adaptation; both come from the properties now — OH5 from the support's
`OfCoverage` and `Commits`, OH6 from `Indirect` — and
`descent_of_support` assembles them, so what is left is the one-line
fact that Optimal's good DAG is `GoodOf` at its own quorum. Round-robin liveness is `liveOn_roundRobin` at
slack `f + c` and wave length three.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoanLive


/-- **A good DAG is good in the properties' terms.** -/
theorem goodOf (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica] :
    ∀ U Rnd N, (optimalHydrozoanLive (Replica := Replica) (BlockId := BlockId)).Good U Rnd N →
      GoodOf (optimalHydrozoanLive (Replica := Replica) (BlockId := BlockId)).toBaseRule.toDagRule
        (LeanDag.Hydrozoan.hzReliability Replica) U Rnd N := by
  rintro U Rnd N ⟨T, hT, hcard, hs, hpop⟩
  refine ⟨T, ⟨hT, ?_⟩, hs, ?_⟩
  · change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card
    unfold LeanDag.Hydrozoan.q at hcard; omega
  · intro r h1 h2 v hv
    obtain ⟨b, hb, hba, hbr⟩ := hpop r h1 h2 v hv
    exact ⟨b, hb, hba, hbr⟩

theorem descent : Descent := by
  intro Replica BlockId _ _ _ _
  exact descent_of_support (optimalHydrozoanLive (Replica := Replica) (BlockId := BlockId))
    LeanDag.OptimalHydrozoanProperties.optSupport
    LeanDag.OptimalHydrozoanProperties.optSupport_ofCoverage
    LeanDag.OptimalHydrozoanProperties.optSupport_commits
    LeanDag.OptimalHydrozoanProperties.indirect (by change 2 ≤ 3; omega) (goodOf Replica BlockId)

theorem roundRobinLive : RoundRobinLive := by
  intro n hn BlockId _ _ hb w hk m hm hmax
  have hbound : (optimalHydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength
      * (LeanDag.Hydrozoan.Faults.f (Fin n) + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n := by
    change 3 * (LeanDag.Hydrozoan.Faults.f (Fin n)
      + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n
    exact hb
  have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId) (Nat.succ_pos 2) hbound hk m hm hmax
  have hw3 : (optimalHydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength = 3 := rfl
  rw [hw3] at h
  simpa using h

theorem holds : Statement := ⟨descent, roundRobinLive⟩

end OptimalHydrozoanLive

end Barnacle

end LeanDag
