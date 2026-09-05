import LeanDag.OptimalHydrozoan.SlotAgreement.Proof
import LeanDag.Barnacle.Helpers.OptimalHydrozoan
import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct

/-!
# Optimal-Hydrozoan as a carrier, and the three properties its rules give

`docs/porting-plan.md` step 3. The carrier and the properties whose
proof is a single Optimal theorem apiece.

**The universe looked as though it could not be a carrier, and the way
out is a fact about the rule rather than about the interface.**
`OptUniverse` is *indexed by the schedule*: its `leader_excluded` field
reads `S.leader k` and `decisionRound k`, so `OptUniverse` at `S` and at
`S'` are different types. `DagRule.Universe` is one type, and
`Properties.Banded` compares verdicts across schedules — so a carrier
over `OptUniverse` could not state the band at all, and the cut's own
`optChopHZ` lands in a *different* universe type from the one it starts
in.

`LeaderExcludedAll` is the escape, and it was already in the
development: the same exclusion quantified over rounds and validators
rather than over slots, hence schedule-free, with `optUniverseOf`
rebuilding the indexed universe at whatever schedule is wanted. The
carrier's universe is the subtype it cuts out, exactly as Hybrid's is
the subtype `HonestNoEquiv` cuts out, and the schedule re-enters where
`DagRule` puts it — in `Decided`.
-/

namespace LeanDag

namespace OptimalHydrozoanProperties

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan as a carrier.** -/
def optimalRule : DagRule Replica BlockId Unit where
  Universe := {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId //
    Barnacle.OptimalHydrozoan.LeaderExcludedAll U}
  View := fun U => LeanDag.Hydrozoan.View U.val
  block := fun U i => LeanDag.Hydrozoan.adaptBlock (U.val.block i)
  ids := fun U => U.val.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  Decided := fun S U V k v =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.DecidedOpt
      (Barnacle.OptimalHydrozoan.optUniverseOf U.val U.property) V k v

/-- Optimal's universes are block DAGs — Hydrozoan's argument, the
underlying universe being Hydrozoan's. -/
theorem causal : Causal (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  fun U =>
    { complete := fun i hi j hj => U.val.complete i hi j hj
      refs_round := fun i hi j hj => (U.val.valid i hi).predecessor j hj }

/-- **Two views decide alike.** OH5 under the property's name, and
unconditional because the exclusion invariant is a field of the
universe. -/
theorem agree : Agree (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  fun S U V₁ V₂ _ _ _ h₁ h₂ =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.SlotAgreement.decided_unique h₁ V₂ _ h₂

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate :
    CommitsCandidate (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  fun S _ _ _ _ hd =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.isLeaderBlock_of_decidedOpt hd

set_option maxHeartbeats 1000000 in
/-- **And a direct commit is a verdict**, at Optimal's own direct
predicate — a *disjunction*, the fast path or the slow one. -/
theorem commitsDirect :
    CommitsDirect (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun {U} V L r => LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L r ∨
        LeanDag.Hydrozoan.SlowCommitInView U.val V L r) := by
  intro S U V k L hL hc
  letI := LeanDag.Hydrozoan.ofCoreSlots S
  rcases hc with h | h
  · exact LeanDag.OptimalHydrozoan.DecidedOpt.directFast hL h
  · exact LeanDag.OptimalHydrozoan.DecidedOpt.directSlow hL h

end OptimalHydrozoanProperties

end LeanDag
