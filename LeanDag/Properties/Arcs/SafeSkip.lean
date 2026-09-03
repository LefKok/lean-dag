import LeanDag.Properties.Persist
import LeanDag.SafeSkip.Basic

/-!
# Crash recovery, for any protocol with `Persist`

`docs/target-properties.md` G2, the crash-recovery half. Safe Skip
restores a crashed validator by one message, denoting the repaired DAG
as `SkipMsg.skipFill`. This file says what that construction is, in the
vocabulary of `Properties`, and draws the conclusion for any protocol
that has proved `Persist`.

**The file is short, and that is the point.** All the depth moves into
the per-protocol `Persist` proof — one induction over that protocol's
own relation, paid once and serving every extension-shaped mechanism,
where today each pair of mechanism and protocol is a separate
development. What is left here is the observation that the fill is an
extension, which is two of its own simp lemmas.

**No mechanism is named but this one.** The rule the arc keeps is that
mechanisms depend on properties and never on each other, so nothing
below mentions the adaptive leader count, garbage collection or any
protocol. A rule reaches the fill through the four equations of
`extends_of_skipFill`, which are `rfl` for any protocol whose universes
are core block universes.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [Faults Validator]

/-- **The fill is an extension.** It holds every block the original
held — `ids` is a union — and denotes each of them unchanged, which is
`skipFill_block_old`. Stated through four equations rather than a type
equality, so that a rule whose universes *are* core block universes can
apply it with `rfl` and this file need name no protocol. -/
theorem extends_of_skipFill (R : DagRule Validator BlockId Payload)
    {U U' : R.Universe} {D : BlockUniverse Validator BlockId Payload}
    (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block) :
    Extends R U U' where
  subset := fun b h => by
    rw [hi'] ; rw [hi] at h
    exact Finset.mem_union_left _ h
  block := fun b h => by
    rw [hi] at h
    rw [hb', hb, sk.skipFill_block_old h]

/-- **Verdicts survive the recovery**, for any protocol that has proved
persistence and whose condition the fill meets. The replica that
recovered reaches every verdict it reached before, so what it had
already output stands. -/
theorem decided_skipFill {R : DagRule Validator BlockId Payload}
    {Ok : Slots Validator → R.Universe → R.Universe → Prop} (hp : Persist R Ok)
    {S : Slots Validator} {U U' : R.Universe}
    {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block)
    (hok : Ok S U U')
    {V : R.View U} {V' : R.View U'} (hV : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {v : Option BlockId} (h : R.Decided S V k v) :
    R.Decided S V' k v :=
  hp S U U' (extends_of_skipFill R sk hi hb hi' hb') hok V V' hV k v h

/-- And for an evidence-backed rule the condition is nothing at all. -/
theorem decided_skipFill_unconditional {R : DagRule Validator BlockId Payload}
    (hp : Persist.Unconditional R)
    {S : Slots Validator} {U U' : R.Universe}
    {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block)
    {V : R.View U} {V' : R.View U'} (hV : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {v : Option BlockId} (h : R.Decided S V k v) :
    R.Decided S V' k v :=
  decided_skipFill hp sk hi hb hi' hb' trivial hV h

end Arcs

end Properties

end LeanDag
