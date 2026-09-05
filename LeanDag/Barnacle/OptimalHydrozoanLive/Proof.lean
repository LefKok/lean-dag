import LeanDag.Barnacle.OptimalHydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.OptimalHydrozoan.Carrier

/-!
# Barnacle over Optimal-Hydrozoan — the live rule, proof

Unaudited, and the mirror of `Barnacle/HydrozoanLive/Proof.lean`.
`goodLeaders` was OH5 and `indirect` was OH6, each applied without
adaptation; both are properties now — `LeaderCommits` and `Indirect` —
and `descent_of_properties` assembles them, so what is left is the
bridge from Optimal's good DAG to its own liveness precondition, which
mentions no verdict. Round-robin liveness is `liveOn_roundRobin` at
slack `f + c` and wave length three.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoanLive

/-- **A good DAG meets Optimal-Hydrozoan's precondition.** `Good` and
`optLive` name the same facts about the same quorum; the window is the
single slot, and its rounds fit because the wave does. -/
theorem goodGives (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica] :
    (optimalHydrozoanLive (Replica := Replica) (BlockId := BlockId)).GoodGives
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica)
      (fun S {U} V T lo K =>
        LeanDag.OptimalHydrozoanProperties.optLive S (U := U) V T lo K) := by
  intro U Rnd N hGood
  obtain ⟨T, hTC, hTq, hsync, hpop⟩ := hGood
  refine ⟨T, ?_, ?_⟩
  · have hcard := LeanDag.Hydrozoan.Faults.card_replicas (Replica := Replica)
    simp only [LeanDag.Hydrozoan.q] at hTq
    omega
  · intro S V κ hcov hRnd hwave hlead
    have hw3 : (optimalHydrozoanLive (Replica := Replica)
        (BlockId := BlockId)).waveLength = 3 := rfl
    rw [hw3] at hwave
    refine ⟨hTC, hTq, Rnd, N, hsync, hRnd, hpop, hcov, ?_⟩
    intro k hk
    have := S.mono (Nat.lt_succ_iff.mp hk)
    omega

theorem descent : Descent := by
  intro Replica BlockId _ _ _ _
  exact descent_of_properties _ LeanDag.OptimalHydrozoanProperties.leaderCommits
    LeanDag.OptimalHydrozoanProperties.indirect (goodGives Replica BlockId)

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
