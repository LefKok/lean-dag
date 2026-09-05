import LeanDag.FinWhale.Model.Decision

/-!
# FinWhale — the anchor, and the indirect commit rule

The indirect rule commits a slot from a committed **anchor** above it:
either the anchor reaches an SP-certificate for a block of the slot, or
it reaches a quorum of FP-evidence blocks for one. `IndirectCommit` is
that condition, and no view occurs in it — its input is the anchor's
causal history and nothing else, which is what makes the paper's
deterministic tie-break safe here (`Anchor.lean`).

`IndirectCommitOn` is the same condition over `historyFrom`, the causal
history as a computed `Finset`, so a concrete model can settle the rule
by `decide` rather than exhibit a path through a transitive closure.
`indirectCommitOn_iff` is the equivalence, for an anchor of the DAG.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Sched Validator}

/-- **The indirect commit condition**, as a predicate of the anchor `A`,
the slot's round `r`, and the candidate block `b`. No view occurs in it:
the anchor's causal history is a function of the anchor. -/
def IndirectCommit (S : Sched Validator) (D : Dag Validator BlockId Payload) (A : BlockId)
    (k : ℕ) (b : BlockId) : Prop :=
  b ∈ slotBlocks S D k ∧
    ((∃ c ∈ blocksAt D (S.round k + 2), ReachesFrom D.block A c ∧ SPCertificate D c b) ∨
      (∃ ev : Finset Validator, spQuorum Validator ≤ ev.card ∧
        ∀ v ∈ ev, ∃ c ∈ blocksAt D (S.round k + 2), ReachesFrom D.block A c ∧
          (D.block c).creator = v ∧ FPEvidence D c b))

/-- **The same condition, decidably.** `ReachesFrom` is a reflexive
transitive closure and settles nothing by computation;
`historyFrom` is the same relation as a `Finset`, computed from the
references with the round as its fuel. On a block of the DAG the two
agree (`mem_history_iff`), so this is the rule a concrete model can
check. -/
def IndirectCommitOn (S : Sched Validator) (D : Dag Validator BlockId Payload) (A : BlockId)
    (k : ℕ) (b : BlockId) : Prop :=
  b ∈ slotBlocks S D k ∧
    ((∃ c ∈ blocksAt D (S.round k + 2), c ∈ historyFrom D.block A ∧ SPCertificate D c b) ∨
      (∃ ev : Finset Validator, spQuorum Validator ≤ ev.card ∧
        ∀ v ∈ ev, ∃ c ∈ blocksAt D (S.round k + 2), c ∈ historyFrom D.block A ∧
          (D.block c).creator = v ∧ FPEvidence D c b))

instance (S : Sched Validator) (D : Dag Validator BlockId Payload) (A : BlockId) (k : ℕ)
    (b : BlockId) : Decidable (IndirectCommitOn S D A k b) := by
  unfold IndirectCommitOn; infer_instance

end FinWhale

end LeanDag
