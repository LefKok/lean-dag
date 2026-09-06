import LeanDag.Hydrozoan.Model.BlockUniverse
import LeanDag.Slots

/-!
# Slots and the leader schedule

Trusted core: the abstract slot schedule of the paper's "Waves and
pipelining" paragraph (`sections/algorithms.tex`). A **slot** is one
leader-decision instance: slot `k` is proposed at `slotRound k` by
`leader k`, voted on one round later, and (slow-)decided two rounds
later. There is no `leadersPerRound` constant: multiple leaders per
round are simply slots sharing a round, and the paper's ranked iteration
over `(round, leaderOffset)` pairs becomes enumeration by slot index.

Pipelining is an *instantiation*, not a proof obligation: safety
quantifies over all schedules, and the pipelined schedule (every round a
propose round) appears only as a witness instance.
-/

namespace LeanDag

namespace Hydrozoan

section SlotArithmetic

variable (Replica : Type*) [S : Slots Replica]

/-- The round at which slot `k` is voted on (the paper's
`VotingRound`): votes for the slot's candidate live here. -/
def votingRound (k : ℕ) : ℕ := S.slotRound k + 1

/-- The round at which slot `k`'s slow path is settled (the paper's
`DecisionRound`): its certificates live here. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2

end SlotArithmetic

section LeaderBlocks

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [F : LeanDag.Hydrozoan.Faults Replica] [S : Slots Replica]

/-- `L` is a candidate block for slot `k`: the right round, the right
creator (the paper's `GetLeaderBlocks`, as a membership predicate).
Because replicas may equivocate, several blocks can satisfy this for one
slot — the rules count creators, and the graded rule's tie-break picks
among copies. Reducible so decidability is inferable inside filters. -/
@[reducible]
def IsLeaderBlock (U : BlockUniverse Replica BlockId) (k : ℕ) (L : BlockId) :
    Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k

end LeaderBlocks

end Hydrozoan

end LeanDag
