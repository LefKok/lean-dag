import LeanDag.Properties.Agree

/-!
# Verdicts decided below a slot bound

`docs/target-properties.md` §4. What an adaptive leader schedule
consumes from a protocol, on the safety side.

An adaptive schedule computes the leaders of high slots from the
verdicts of low ones, and a verdict may be anchored arbitrarily far
above the slot it decides. For the fixpoint to be stratified, a verdict
has to come with a **bound**: it must be unchanged when the leaders at
or above that bound are reassigned.

**This used to be a second decision relation, supplied by the protocol
as a field of the carrier.** `BoundedRule` carried `DecidedWithin`
alongside `Decided`, and three laws related them, on the reasoning that
a `Decided` derivation is a proof of a `Prop` whose anchors cannot be
recovered after the fact. That reasoning is sound about *derivations*
and beside the point about *verdicts*: what the fixpoint needs is not
which slots a derivation named but which leaders the verdict depends on,
and that is a statement about `Decided` alone.

`DecidedBelow` is that statement. It is a **definition**, so a protocol
proves nothing to have it, and its laws are theorems rather than
obligations — which is why they sit in `Derived/Bounded.lean` and this
file holds the definition alone. The carrier is `DagRule` again, with
no second relation in it.

A protocol still needs a way to *produce* a verdict at a tight bound,
and that is what `LeaderCommits` and `Descends` are for
(`Commit.lean`); `Witness.lean` derives the untight version from the
band, for a rule that would rather not name a bound at all.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A verdict decided below `B`**: the slot sits below the bound, the
verdict holds, and it is unchanged by any reassignment of the leaders at
or above the bound. The round structure is held fixed, which is what
reassignment means. -/
def DecidedBelow (R : DagRule Validator BlockId Payload) (S : Slots Validator) (B : ℕ)
    {U : R.Universe} (V : R.View U) (k : ℕ) (v : Option BlockId) : Prop :=
  k < B ∧ R.Decided S V k v ∧
    ∀ S' : Slots Validator, S'.slotRound = S.slotRound →
      (∀ m, m < B → S'.leader m = S.leader m) → R.Decided S' V k v

end Properties

end LeanDag
