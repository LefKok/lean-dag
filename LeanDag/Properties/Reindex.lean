import LeanDag.Properties.Carrier

/-!
# Re-indexing: renumbering rounds and slots together

`docs/target-properties.md` §3.4, and the part of the plan that was
recorded as least certain.

A truncation does two things: it drops what lies below a horizon, and it
renumbers what remains so the retained layer sits at round zero. The
first is locality. The second is here, and it is a different kind of
statement — nothing is removed, every block keeps its author and its
references, and only the *numbering* moves, in the universe and in the
schedule together.

**The property.** Shift every round down by `G` and every slot down by
`d`, consistently, and the verdicts move with them: what was decided at
slot `d + k` is decided at slot `k`. Nothing about the rule appears, so
this is the closest thing in the arc to a statement that ought to be
free — and it is not, because each protocol's predicates name rounds
and a protocol must check that each of them commutes with the shift.

**Why it is stated separately from locality.** The two do not compose
directly: `AgreeAbove` asks for equal rounds, and a truncation's rounds
are not equal. They compose through the universe that has been
restricted and not yet renumbered — see `Arcs/GC.lean`, which takes it
as a parameter. That intermediate is not something this file can
construct, since `DagRule.Universe` is abstract, and no arc in the
development currently defines one: `GC.chop` restricts and renumbers in
a single step.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **`U'` is `U` renumbered**, its rounds lower by `G`, together with
the schedule whose slots are lower by `d`. The same blocks, the same
authors, the same references: only the numbering moves. -/
structure Shifted (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (S S' : Slots Validator) (G d : ℕ) : Prop where
  /-- The same blocks are present. -/
  mem : ∀ b, b ∈ R.ids U ↔ b ∈ R.ids U'
  /-- Rounds move down by the horizon. Stated additively, so the
  natural-number subtraction never appears. -/
  round : ∀ b, b ∈ R.ids U → (R.block U' b).round + G = (R.block U b).round
  /-- Authors are untouched. -/
  creator : ∀ b, b ∈ R.ids U → (R.block U' b).creator = (R.block U b).creator
  /-- And references. -/
  refs : ∀ b, b ∈ R.ids U → (R.block U' b).refs = (R.block U b).refs
  /-- The schedule moves with the universe: slot `k` of the new schedule
  is slot `d + k` of the old, at the round lowered by `G`. -/
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  /-- And leads the same replica. -/
  leader : ∀ k, S'.leader k = S.leader (d + k)

/-- **Re-indexing.** A renumbering carries verdicts, slot for slot. -/
def Reindex (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator) (U U' : R.Universe) (G d : ℕ),
    Shifted R U U' S S' G d →
    ∀ (V : R.View U) (V' : R.View U'), R.viewIds V = R.viewIds V' →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V (d + k) v → R.Decided S' V' k v

namespace Shifted

variable {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}

/-- A shifted block sits at or above nothing in particular, but its
round determines the original's, which is what an arithmetic step
needs. -/
theorem round_eq (h : Shifted R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U) :
    (R.block U' b).round = (R.block U b).round - G := by
  have := h.round b hb; omega

/-- The identity shift, at no horizon and no base slot. -/
theorem refl {U : R.Universe} {S : Slots Validator} : Shifted R U U S S 0 0 where
  mem := fun _ => Iff.rfl
  round := fun _ _ => rfl
  creator := fun _ _ => rfl
  refs := fun _ _ => rfl
  slotRound := fun k => by simp
  leader := fun k => by simp

end Shifted

end Properties

end LeanDag
