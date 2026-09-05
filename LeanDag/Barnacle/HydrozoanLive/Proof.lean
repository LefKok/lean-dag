import LeanDag.Barnacle.HydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Hydrozoan.Helpers.Commit

/-!
# Barnacle over Hydrozoan — the live rule, proof

Unaudited. `goodLeaders` was HZ5 and `indirect` was HZ6, each applied
without adaptation. Both are properties now — `LeaderCommits` and
`Indirect` — and `descent_of_properties` assembles them, so what is
left is the bridge from Hydrozoan's good DAG to its own liveness
precondition, which mentions no verdict. Round-robin liveness is
`liveOn_roundRobin` at
slack `f + c` and wave length three, whose bound `3·(f + c) + 1 ≤ n`
is the committee bound, taken as a hypothesis rather than derived
from the slack.
-/

namespace LeanDag

namespace Barnacle

namespace HydrozoanLive

/-- **A good DAG meets Hydrozoan's precondition.** `Good` and `hzLive`
name the same facts about the same quorum; the window is the single
slot, and its rounds fit because the wave does. -/
theorem goodGives (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica] :
    (hydrozoanLive (Replica := Replica) (BlockId := BlockId)).GoodGives (F.f + F.c)
      (fun S {U} V T lo K => LeanDag.Hydrozoan.hzLive S (U := U) V T lo K) := by
  intro U Rnd N hGood
  obtain ⟨T, hTC, hTq, hsync, hpop⟩ := hGood
  refine ⟨T, ?_, ?_⟩
  · have hcard := F.card_replicas
    simp only [LeanDag.Hydrozoan.q] at hTq
    omega
  · intro S V κ hcov hRnd hwave hlead
    have hw3 : (hydrozoanLive (Replica := Replica)
        (BlockId := BlockId)).waveLength = 3 := rfl
    rw [hw3] at hwave
    refine ⟨hTC, hTq, Rnd, N, hsync, hRnd, hpop, hcov, ?_⟩
    intro k hk
    have := S.mono (Nat.lt_succ_iff.mp hk)
    omega

theorem descent : Descent := by
  intro Replica BlockId _ _ _ F
  exact descent_of_properties _ LeanDag.Hydrozoan.leaderCommits LeanDag.Hydrozoan.indirect
    (goodGives Replica BlockId)

theorem roundRobinLive : RoundRobinLive := by
  intro n hn BlockId _ F hck w hk m hm hmax
  have hbound : (hydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength * (F.f + F.c) + 1 ≤ n := by
    change 3 * (F.f + F.c) + 1 ≤ n
    exact hck
  have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId) (Nat.succ_pos 2) hbound hk m hm hmax
  -- the gap is `n + waveLength - 1`, and the wave length is three
  have hw3 : (hydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength = 3 := rfl
  rw [hw3] at h
  simpa using h

theorem holds : Statement := ⟨descent, roundRobinLive⟩

end HydrozoanLive

end Barnacle

end LeanDag
