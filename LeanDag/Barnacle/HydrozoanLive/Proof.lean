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


/-- **A good DAG is good in the properties' terms.** -/
theorem goodOf (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica] :
    ∀ U Rnd N, (hydrozoanLive (Replica := Replica) (BlockId := BlockId)).Good U Rnd N →
      GoodOf (hydrozoanLive (Replica := Replica) (BlockId := BlockId)).toBaseRule.toDagRule
        (LeanDag.Hydrozoan.hzReliability Replica) U Rnd N := by
  rintro U Rnd N ⟨T, hT, hcard, hs, hpop⟩
  refine ⟨T, ⟨hT, ?_⟩, hs, ?_⟩
  · change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card
    unfold LeanDag.Hydrozoan.q at hcard; omega
  · intro r h1 h2 v hv
    obtain ⟨b, hb, hbr, hba⟩ := hpop r h1 h2 v hv
    exact ⟨b, hb, hba, hbr⟩

theorem descent : Descent := by
  intro Replica BlockId _ _ _ F
  exact descent_of_support (hydrozoanLive (Replica := Replica) (BlockId := BlockId))
    LeanDag.Hydrozoan.hzSupport LeanDag.Hydrozoan.hzSupport_ofCoverage
    LeanDag.Hydrozoan.hzSupport_commits LeanDag.Hydrozoan.indirect (by change 2 ≤ 3; omega)
    (goodOf Replica BlockId)

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
