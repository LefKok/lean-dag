import LeanDag.Properties.Bounded

/-!
# What a protocol provides for a schedule mechanism's liveness

`docs/target-properties.md` §4, the liveness side. `Sustains` is what a
DAG-transforming mechanism owes a protocol; a *schedule* mechanism
transforms no DAG, and its liveness theorem is the one that needs
feeding. Two properties, both proved by the protocol.

* `LeaderCommits` — under the protocol's own liveness precondition
  `Live`, a slot led by a member of the reliable set `T` is committed
  with a bound one above the slot. `Live` is a parameter, not a field:
  the same rule under two execution models — the timed core and the
  reactive discipline — has two preconditions and one relation, and the
  property is stated once for each.

  `Live S V T lo K` is indexed by the schedule, because a reactive
  execution's clauses read the schedule's leaders, and by a slot window
  `[lo, K)`: an adaptive schedule is only determined so far, and what a
  protocol can promise about an execution is confined to the slots
  whose leaders that execution followed.

* `Descends` — a run of `c` consecutive committed slots decides every
  slot below it, inside the run's bound. The indirect rule's descent,
  stated over the bounded family; `c` is the protocol's, as is the
  hypothesis on the round structure under which it holds, so the
  property is indexed by the schedule too.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A reliable leader's slot commits**, within a bound one above it,
wherever the protocol's precondition `Live` holds over a slot window
containing the slot. -/
def LeaderCommits (R : BoundedRule Validator BlockId Payload)
    (Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop) :
    Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (T : Finset Validator) (lo K : ℕ),
    Live S V T lo K → ∀ k, lo ≤ k → k < K → S.leader k ∈ T →
      ∃ L, R.DecidedWithin S (k + 1) V k (some L)

/-- **A committed run decides everything below it.** `c` consecutive
slots from `b`, each committed within `b + c`, decide every slot below
`b` within `b + c`. -/
def Descends (R : BoundedRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) : Prop :=
  ∀ {U : R.Universe} (V : R.View U) (b : ℕ),
    (∀ j, b ≤ j → j < b + c → ∃ L, R.DecidedWithin S (b + c) V j (some L)) →
    ∀ i, i < b → ∃ v, R.DecidedWithin S (b + c) V i v

end Properties

end LeanDag
