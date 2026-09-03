import LeanDag.Properties.Carrier

/-!
# Truncation: pruning below a horizon, and renumbering from it

`docs/target-properties.md` §3.4, restated after a failed attempt that
is worth recording.

**The attempt.** Locality (`Local.lean`) says two DAGs agreeing above a
round decide alike; the plan was to pair it with a *re-indexing*
property saying a consistent renumbering carries verdicts, and compose
the two through the universe that has been restricted and not yet
renumbered.

**Why that cannot work.** Two reasons, and the second is the fatal one.

The intermediate does not exist. Agreement forces its rounds to equal
the original's, so its bottom layer sits at round `G`; the renumbering
forces its references to equal the truncation's, which are empty there.
A block with no references above round zero fails the quorum clause of
validity.

And the renumbering half was **vacuous on its own**. A pure shift keeps
every block, so the bottom layer lands at round zero carrying the
references it had at round `G` — which validity forbids, since a
round-zero block has none. Descending by the predecessor condition, any
non-empty valid universe has a round-zero block, so a shift by a
positive horizon admits no non-empty target at all.
`Hydrozoan/Helpers/Truncation.lean` carries the witness.

**So restriction and renumbering are not separately realisable**, and
only their combination has models. `Truncates` below is that
combination, and `truncates_chopHZ` exhibits the development's own
truncation as a witness — checked before anything was proved about it,
which is the discipline the failed attempt lacked.

`Local` survives unchanged. It is not vacuous, it is proved for
Hydrozoan, and it states what a verdict reads. It is simply not what a
renumbering mechanism consumes.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **`U'` is `U` pruned below `G` and renumbered from slot `d`.**

The two clauses that distinguish this from a pure shift are `mem` and
`refs`. Membership keeps only what lies at or above the horizon, so what
lies below is legitimately gone; and references are compared only
**strictly** above the horizon, so the retained bottom layer may
legitimately lose the references that pointed below it. A relation
demanding either of those in full has no models. -/
structure Truncates (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (S S' : Slots Validator) (G d : ℕ) : Prop where
  /-- What survives the cut: the blocks at or above the horizon. -/
  mem : ∀ b, b ∈ R.ids U' ↔ (b ∈ R.ids U ∧ G ≤ (R.block U b).round)
  /-- Rounds fall by the horizon. Stated additively, so truncated
  subtraction never appears. -/
  round : ∀ b, b ∈ R.ids U' → (R.block U' b).round + G = (R.block U b).round
  /-- Authors are untouched. -/
  creator : ∀ b, b ∈ R.ids U' → (R.block U' b).creator = (R.block U b).creator
  /-- References survive **strictly** above the horizon. Nothing is
  claimed at the horizon itself, which is where a truncation empties
  them and where the renumbering puts them at round zero. -/
  refs : ∀ b, b ∈ R.ids U' → G < (R.block U b).round →
    (R.block U' b).refs = (R.block U b).refs
  /-- The schedule moves with the universe. -/
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  /-- And leads the same replica. -/
  leader : ∀ k, S'.leader k = S.leader (d + k)
  /-- The horizon does not reach past the base slot. -/
  base : G ≤ S.slotRound d

/-- **Two views correspond across a truncation.** -/
def ViewTruncates (R : DagRule Validator BlockId Payload) {U U' : R.Universe}
    (V : R.View U) (V' : R.View U') (G : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → G ≤ (R.block U b).round →
    (b ∈ R.viewIds V ↔ b ∈ R.viewIds V')

/-- **Truncation invariance.** A replica that has pruned below the
horizon reaches exactly the verdicts it would have reached with its
whole history, at its own numbering.

An `↔`, because both directions are consumed: a joiner needs verdicts
to survive the cut, and cross-cut agreement needs them to come back. -/
def LocalTruncate (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator) (U U' : R.Universe) (G d : ℕ),
    Truncates R U U' S S' G d →
    ∀ (V : R.View U) (V' : R.View U'), ViewTruncates R V V' G →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V (d + k) v ↔ R.Decided S' V' k v

namespace Truncates

variable {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}

/-- A retained block is a block of the original. -/
theorem mem_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U') :
    b ∈ R.ids U := ((h.mem b).mp hb).1

/-- And sits at or above the horizon there. -/
theorem le_round (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U') :
    G ≤ (R.block U b).round := ((h.mem b).mp hb).2

end Truncates

end Properties

end LeanDag
