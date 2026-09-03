import LeanDag.Properties.Persist
import LeanDag.SafeSkip.Basic
import LeanDag.SafeSkip.Invariance
import LeanDag.MysticetiProperties

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
    {Ok : Slots Validator → ∀ (U U' : R.Universe), R.View U → Prop} (hp : Persist R Ok)
    {S : Slots Validator} {U U' : R.Universe}
    {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block)
    {V : R.View U} {V' : R.View U'} (hok : Ok S U U' V) (hV : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {v : Option BlockId} (h : R.Decided S V k v) :
    R.Decided S V' k v :=
  hp S U U' (extends_of_skipFill R sk hi hb hi' hb') V V' hok hV k v h

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

/-! ## For the core: the grade the fill meets, and the bespoke theorem re-derived

The consumer test for `MysticetiProperties.persist`. `SafeSkip.decided_fill`
proves the fill transports the core's verdicts by a four-constructor
induction under `QuorateOverGap`. Here `QuorateOverGap` is shown to imply
the core's grade `Quorate` — a fresh candidate sits at a gap round, and
the gap is where the quorum is asked for — and `decided_fill` follows from
`persist` with no induction of its own. -/

section Core

variable {U : BlockUniverse Validator BlockId Payload}

/-- **Quorate over the gap is the core's grade**, for the fill. A candidate
the fill introduces is a fresh block, a fresh block sits at a gap round,
and at every gap round the view holds a quorum one round above. -/
theorem quorate_of_quorateOverGap [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} (hq : sk.QuorateOverGap V) :
    MysticetiProperties.Quorate S U sk.skipFill V := by
  intro k L hL hLo
  obtain ⟨hLm, hLr, -⟩ := hL
  have hfresh : L ∈ sk.freshIds := by
    rcases Finset.mem_union.mp hLm with h | h
    · exact absurd h hLo
    · exact h
  obtain ⟨m, hm1, hm2, rfl⟩ := sk.mem_freshIds.mp hfresh
  have hround : S.slotRound k = m := by
    rw [sk.skipFill_block_fresh] at hLr
    exact hLr.symm
  rw [hround]
  exact hq m hm1 hm2

/-- **`SafeSkip.decided_fill`, from `Persist`.** The same statement, with
no induction: persistence is proved once for the protocol, and the fill
is one extension among others — one that meets the core's grade. -/
theorem decided_fill_of_persist [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (hq : sk.QuorateOverGap V) (h : Decided U V k v) :
    Decided sk.skipFill (sk.liftView V) k v :=
  decided_skipFill (R := MysticetiProperties.mysticetiRule) MysticetiProperties.persist sk
    rfl rfl rfl rfl (quorate_of_quorateOverGap sk hq) (fun _ hb => hb) h

end Core

end Arcs

end Properties

end LeanDag
