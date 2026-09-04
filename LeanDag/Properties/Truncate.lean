import LeanDag.Properties.Agreement

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

/-- **The schedule moves with the DAG.** Slot `k` of the truncated
schedule is slot `d + k` of the original, at a round `G` lower, leading
the same replica. Stated additively, so truncated subtraction never
appears.

Separate from the block relation because the two axes are independent:
`RebasedAbove` says what became of the DAG, `Rebases` says what became
of the schedule, and a mechanism that touches only one states only
one. -/
structure Rebases (S S' : Slots Validator) (G d : ℕ) : Prop where
  /-- Rounds fall by the horizon. -/
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  /-- And each slot leads the same replica. -/
  leader : ∀ k, S'.leader k = S.leader (d + k)
  /-- The horizon does not reach past the base slot. -/
  base : G ≤ S.slotRound d

/-- **`U'` is `U` pruned below `G` and renumbered from slot `d`.**

The two clauses that distinguish this from a pure shift are `mem` and
`refs`. Membership keeps only what lies at or above the horizon, so what
lies below is legitimately gone; and references are compared only
**strictly** above the horizon, so the retained bottom layer may
legitimately lose the references that pointed below it. A relation
demanding either of those in full has no models.

Both clauses are `RebasedAbove`'s, read at `R₀ = G`. That was not how
this started: `Truncates` was written with its own four block clauses,
and they were found to be the same four a mechanism already owed under
`Sustains`. What is left here is the schedule half. -/
structure Truncates (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (S S' : Slots Validator) (G d : ℕ) : Prop
    extends RebasedAbove R U U' G G, Rebases S S' G d

namespace Truncates

variable {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}

/-- **What survives the cut**, in the shape the cut is usually read in:
the blocks at or above the horizon, and no others. The inherited `mem`
pairs the round condition on both sides, which at `R₀ = G` is vacuous on
the right. -/
theorem mem_iff (h : Truncates R U U' S S' G d) (b : BlockId) :
    b ∈ R.ids U' ↔ (b ∈ R.ids U ∧ G ≤ (R.block U b).round) := by
  constructor
  · intro hb; exact (h.mem b).mpr ⟨hb, by omega⟩
  · rintro ⟨hb, hr⟩; exact ((h.mem b).mp ⟨hb, hr⟩).1

/-- Rounds fall by the horizon, read from the truncation. -/
theorem round_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U') :
    (R.block U' b).round + G = (R.block U b).round :=
  have hm := (h.mem_iff b).mp hb
  h.round b hm.1 hm.2

/-- Authors are untouched, read from the truncation. -/
theorem creator_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U') :
    (R.block U' b).creator = (R.block U b).creator :=
  have hm := (h.mem_iff b).mp hb
  h.creator b hm.1 hm.2

/-- And references survive strictly above the horizon. -/
theorem refs_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U')
    (hgt : G < (R.block U b).round) :
    (R.block U' b).refs = (R.block U b).refs :=
  h.refs b ((h.mem_iff b).mp hb).1 hgt

end Truncates

end Properties

end LeanDag
