import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Skip
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

/-! ### The filled slot is decided, and SS3 falls out

`SafeSkip.directSkip_fresh` (SS3) says the fill cannot conjure a
commit: a filled block on a leader slot is blamed by every reliable
block above it. Here the same conclusion is reached from the properties
— the fill is an extension, so its candidates are unsupported by the
old view (`unsupported_of_novel`), and the core skips an unsupported
slot from a correct quorum (`skipsUnsupported`) — and it lands as a
*verdict*, `Decided … k none`, rather than SS3's universe-level
`DirectSkip`.

SS3's hypothesis `v1 ∉ T` is not needed. Presence is asked of the
pre-crash view, whose blocks are old, and `hgap` says the recovering
replica authored nothing in the gap — so a `T` present at a gap round
cannot contain it. -/

/-- Presence in the pre-crash view is presence in the lifted one: the
ids are the same and old blocks are unchanged. -/
theorem presentAt_liftView [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {T : Finset Validator} {r : ℕ}
    (h : PresentAt MysticetiProperties.mysticetiRule V T r) :
    PresentAt MysticetiProperties.mysticetiRule (sk.liftView V) T r := by
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := h v hv
  have hcU : c ∈ U.ids := V.subset_ids hcV
  refine ⟨c, hcV, ?_, ?_⟩
  · show (sk.skipFill.block c).creator = v
    rw [sk.skipFill_block_old hcU]; exact hcc
  · show (sk.skipFill.block c).round = r
    rw [sk.skipFill_block_old hcU]; exact hcr

/-- **Every candidate of a slot the recovering replica leads, at a gap
round, is a filled block** — the replica authored nothing old there. -/
theorem candidates_fresh [S : Slots Validator] (sk : SkipMsg U) {k : ℕ}
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    {L : BlockId} (hL : IsLeaderBlock sk.skipFill k L) : L ∉ U.ids := by
  intro hLU
  obtain ⟨-, hLr, hLc⟩ := hL
  rw [sk.skipFill_block_old hLU] at hLr hLc
  exact sk.hgap L hLU (by rw [hLc, hlead]) (by change sk.r0 < _; omega) (by omega)

/-- **SS3, as a verdict, from the properties.** The slot the recovering
replica leads at a gap round is decided `none` on the lifted view, given
a quorum of the pre-crash view present one round above it. No induction;
the fill is an extension, and the core skips what nothing supports. -/
theorem decided_none_fresh [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt MysticetiProperties.mysticetiRule V T (S.slotRound k + 1)) :
    Decided sk.skipFill (sk.liftView V) k none :=
  MysticetiProperties.skipsUnsupported S sk.skipFill (sk.liftView V) T k hcard
    (presentAt_liftView sk hpres)
    (unsupported_of_novel MysticetiProperties.causal
      (extends_of_skipFill MysticetiProperties.mysticetiRule sk rfl rfl rfl rfl)
      (fun L hL => ⟨hL.1, candidates_fresh sk hlead hk1 hk2 hL⟩)
      (fun c hcV _ _ => V.subset_ids hcV))

end Core
