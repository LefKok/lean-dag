import LeanDag.Properties.Candidate

/-!
# What a rule owes about its own direct rule

`docs/target-properties.md` §11.4b. `Properties/Optional/` holds what a
protocol **may** show and need not, and this is the second such
property. A rule with no direct-commit predicate — or one no mechanism
counts — owes nothing here.

**Who asks for it.** `Barnacle`'s leader count adapts on a window count:
how many slots of the recent past were directly committed, measured on
the anchor's causal history. That count filters on the rule's own direct
predicate, and until this property existed nothing related that
predicate to the decision relation. A rule whose direct predicate held
of everything would reach its expected count every window and raise the
leader count forever, with every theorem about the count still true.

**Where it came from.** `Barnacle.BaseRule.Laws.decided_of_directCommitIn`,
promoted. It sat unused for exactly as long as its own docstring claimed
it was what made the window count a count of verdicts: six protocols
proved it and nothing read it.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A direct commit is a verdict.** The converse of
`CommitsCandidate`, parameterised by the rule's own direct-commit
predicate — what counts as *direct* is the rule's business and not the
carrier's, which is why `Direct` is an argument rather than a field. -/
def CommitsDirect (R : DagRule Validator BlockId Payload)
    (Direct : ∀ {U : R.Universe}, R.View U → BlockId → ℕ → Prop) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (k : ℕ) (L : BlockId),
    R.IsCandidate S U k L → Direct V L (S.slotRound k) → R.Decided S V k (some L)

end Properties

end LeanDag
