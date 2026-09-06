import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Optional.Skip
import LeanDag.SafeSkip.Basic
import LeanDag.SafeSkip.Invariance
import LeanDag.MysticetiProperties
import LeanDag.OdontocetiProperties
import LeanDag.MahiMahiProperties

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
/-! ## Promptness: the fill cannot conjure a commit

For any rule that skips unsupported slots (`SkipsUnsupported`, optional)
and any extension whose candidates at a slot are all novel: the slot is
decided `none` at once, on any view whose reliable blocks one round up
are old. No old block references a novel id (`Extends.old_refs_old`),
so the slot is unsupported, and the rule skips it. This is SS3 for
every rule that shows the property, at every fill. -/

/-- **A slot whose candidates are all novel is skipped**, promptly. -/
theorem decided_none_of_novel {R : DagRule Validator BlockId Payload}
    {Ok : Finset Validator → Prop} (hsk : SkipsUnsupported R Ok)
    {U U' : R.Universe} (he : Extends R U U') (S : Slots Validator)
    {V' : R.View U'} {T : Finset Validator} {k : ℕ} (hok : Ok T)
    (hpres : PresentAt R V' T (S.slotRound k + 1))
    (hnov : ∀ L, R.IsCandidate S U' k L → L ∉ R.ids U)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U) :
    R.Decided S V' k none :=
  hsk S U' V' T k hok hpres (unsupported_of_novel he (fun L hL => ⟨hL.1, hnov L hL⟩) hold)

section Faults

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
persistence. The replica that recovered reaches every verdict it reached
before, so what it had already output stands. -/
theorem decided_skipFill {R : DagRule Validator BlockId Payload} (hp : Persist R)
    {S : Slots Validator} {U U' : R.Universe}
    {D : BlockUniverse Validator BlockId Payload} (sk : SkipMsg D)
    (hi : R.ids U = D.ids) (hb : R.block U = D.block)
    (hi' : R.ids U' = sk.skipFill.ids) (hb' : R.block U' = sk.skipFill.block)
    {V : R.View U} {V' : R.View U'} (hV : R.viewIds V ⊆ R.viewIds V')
    {k : ℕ} {v : Option BlockId} (h : R.Decided S V k v) :
    R.Decided S V' k v :=
  hp S U U' (extends_of_skipFill R sk hi hb hi' hb') V V' hV k v h

omit [Faults Validator] in
/-- **Agreement across the recovery.** A validator that recovered agrees
with one that did not, from any view of the extension — the same shape
as cross-cut agreement (`Arcs/GC.lean`), with `Persist` going up where
`LocalTruncate` goes down. Stated for any extension, so re-genesis and
the fill both take it. -/
theorem decided_agree_extends {R : DagRule Validator BlockId Payload}
    (ha : Agree R) (hp : Persist R) {S : Slots Validator} {U U' : R.Universe}
    (he : Extends R U U') {V : R.View U} {V' W : R.View U'}
    (hsub : R.viewIds V ⊆ R.viewIds V') {k : ℕ} {v w : Option BlockId}
    (hV : R.Decided S V k v) (hW : R.Decided S W k w) : v = w :=
  ha S V' W k v w (hp S U U' he V V' hsub k v hV) hW

omit [Faults Validator] in
/-- **The prompt skip conflicts with no verdict.** On any view of the
extension, and on any view of any further extension a caught-up view
reaches, a verdict at the skipped slot is `none`: `Agree` at the
extension, `Persist` past it. -/
theorem decided_none_of_novel_agree {R : DagRule Validator BlockId Payload}
    (ha : Agree R) (hb : Banded R) {Ok : Finset Validator → Prop} (hsk : SkipsUnsupported R Ok)
    {U U' : R.Universe} (he : Extends R U U') (S : Slots Validator)
    {V' : R.View U'} {T : Finset Validator} {k : ℕ} (hok : Ok T)
    (hpres : PresentAt R V' T (S.slotRound k + 1))
    (hnov : ∀ L, R.IsCandidate S U' k L → L ∉ R.ids U)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U)
    {U'' : R.Universe} (he' : Extends R U' U'') {V'' W : R.View U''}
    (hsub : R.viewIds V' ⊆ R.viewIds V'') {v : Option BlockId} (hW : R.Decided S W k v) :
    v = none :=
  (decided_agree_extends ha (Persist.of_banded hb) he' hsub
    (decided_none_of_novel hsk he S hok hpres hnov hold) hW).symm

/-! ## For the core: the grade the fill meets, and the bespoke theorem re-derived

The consumer test for `MysticetiProperties.persist`. The bespoke
transport in `SafeSkip/Invariance.lean` proved the fill carries the
core's verdicts by a four-constructor induction under
`QuorateOverGap`, and the theorem below followed from
`persist` with no induction of its own.

`QuorateOverGap` used to be needed here, to meet a grade the core's
persistence carried. Both went when the core's skip rule was repaired,
so the transport now asks nothing of the view. -/

section Core

variable {U : BlockUniverse Validator BlockId Payload}

/-- **Verdicts survive the core's fill, from `Persist`.** The bespoke
theorem's statement, with no induction: persistence is proved once for
the protocol, and the fill is one extension among others. That theorem
carried `QuorateOverGap`; this does not, the hypothesis having gone with
the grade it was there to meet. It has since been deleted, leaving this
the only route. -/
theorem decided_fill_of_persist [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (h : Decided U V k v) :
    Decided sk.skipFill (sk.liftView V) k v :=
  decided_skipFill (R := MysticetiProperties.mysticetiRule) MysticetiProperties.persist sk
    (U := U) (U' := sk.skipFill) rfl rfl rfl rfl (fun _ hb => hb) h

/-- **Agreement across the core's recovery, from `Persist` and
`Agree`.** A verdict reached before the recovery agrees with any reached
after it.
The bespoke version composed its induction with `decided_agree` by hand;
this is `decided_agree_extends`, which every rule with the two
properties has. -/
theorem decided_fill_agree_of_properties [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U}
    {W : View Validator BlockId Payload sk.skipFill} {k : ℕ} {v w : Option BlockId}
    (hv : Decided U V k v) (hw : Decided sk.skipFill W k w) : v = w :=
  MysticetiProperties.agree S (sk.liftView V) W k v w (decided_fill_of_persist sk hv) hw

/-! ### What the fill sustains

The witness §11.2's table recorded as missing. The cut had one
(`Arcs/GC.lean`) and Hydrozoan's fill had one
(`Integration/Hydrozoan/ViaProperties.lean`); the core's fill did not,
so the two core mechanisms could not be composed through the properties
even though each had a transport of its own. -/

/-- **A fill sustains from the top of its gap.** Above `sk.r` the fill
added nothing, so every block there is old and unchanged. Below it the
claim would be false, and deliberately: the blocks a fill adds stand in
for blocks that voted, and need not vote as they did. -/
theorem sustains_skipFill (sk : SkipMsg U) :
    Sustains (MysticetiProperties.mysticetiRule (Payload := Payload))
      U sk.skipFill 0 (sk.r + 1) where
  mem := fun b => by
    show (b ∈ U.ids ∧ sk.r + 1 ≤ (U.block b).round) ↔
      (b ∈ sk.skipFill.ids ∧ sk.r + 1 ≤ (sk.skipFill.block b).round + 0)
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨sk.ids_subset_skipFill hb, by rw [sk.skipFill_block_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      have hbU : b ∈ U.ids := by
        rcases Finset.mem_union.mp hb with ho | hf
        · exact ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
          rw [sk.skipFill_block_fresh] at hr
          simp only [SkipData.fillBlock] at hr
          omega
      exact ⟨hbU, by rw [sk.skipFill_block_old hbU] at hr; omega⟩
  round := fun b hb _ => by
    show (sk.skipFill.block b).round + 0 = (U.block b).round
    rw [sk.skipFill_block_old hb]; omega
  creator := fun b hb _ => by
    show (sk.skipFill.block b).creator = (U.block b).creator
    rw [sk.skipFill_block_old hb]
  refs := fun b hb _ => by
    show (sk.skipFill.block b).refs = (U.block b).refs
    rw [sk.skipFill_block_old hb]

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
  decided_none_of_novel MysticetiProperties.skipsUnsupported
    (extends_of_skipFill MysticetiProperties.mysticetiRule sk rfl rfl rfl rfl) S hcard
    (presentAt_liftView sk hpres) (fun L hL => candidates_fresh sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And the skip conflicts with no verdict**: any view of the fill, or
of any extension of it a caught-up view reaches, decides the slot
`none` if at all. -/
theorem decided_none_fresh_agree [S : Slots Validator] (sk : SkipMsg U)
    {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt MysticetiProperties.mysticetiRule V T (S.slotRound k + 1))
    {U'' : BlockUniverse Validator BlockId Payload}
    (he' : Extends MysticetiProperties.mysticetiRule sk.skipFill U'')
    {V'' W : View Validator BlockId Payload U''} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option BlockId} (hW : Decided U'' W k v) : v = none :=
  (decided_agree_extends MysticetiProperties.agree (Persist.of_banded MysticetiProperties.banded)
    he' (V := sk.liftView V) (V' := V'') hsub (decided_none_fresh sk hcard hlead hk1 hk2 hpres) hW).symm

end Core

end Faults

/-! ### And for Odontoceti, whose universes are the core's

`scripts/audit-mechanisms.py` asked for this cell. The four equations
`extends_of_skipFill` is stated through are what makes it free: the two
carriers project identically, so the rule's `ids` and `block` *are* the
core universe's and every equation is `rfl`. A rule with its own
universe record would have to build its own fill instead, which is the
limit `docs/target-properties.md` §11.4 records. -/

section Odontoceti

variable [Faults5 Validator] {B : Type} [LinearOrder B]
variable {W : BlockUniverse Validator B Payload}

/-- **Verdicts survive the fill, for Odontoceti.** -/
theorem decided_fill_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {k : ℕ} {v : Option B}
    (h : Odontoceti.Decided W V k v) :
    Odontoceti.Decided (U := sk.skipFill) (sk.liftView V) k v :=
  decided_skipFill (R := OdontocetiProperties.odontocetiRule (Payload := Payload))
    (Persist.of_banded OdontocetiProperties.banded) sk
    (U := W) (U' := sk.skipFill) rfl rfl rfl rfl (fun _ hb => hb) h

/-- **And agreement across it.** -/
theorem decided_fill_agree_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {Y : View Validator B Payload sk.skipFill}
    {k : ℕ} {v w : Option B}
    (hv : Odontoceti.Decided W V k v)
    (hw : Odontoceti.Decided (U := sk.skipFill) Y k w) : v = w :=
  decided_agree_extends OdontocetiProperties.agree
    (Persist.of_banded OdontocetiProperties.banded)
    (extends_of_skipFill (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk
      (U := W) (U' := sk.skipFill) rfl rfl rfl rfl)
    (V' := sk.liftView V) (fun _ hb => hb) hv hw

/-- **SS3 for Odontoceti**: the slot the recovering replica leads at a
gap round is skipped at once, from its `SkipsUnsupported`. -/
theorem decided_none_fresh_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (OdontocetiProperties.odontocetiRule (Payload := Payload)) V T
      (S.slotRound k + 1)) :
    Odontoceti.Decided (U := sk.skipFill) (sk.liftView V) k none :=
  decided_none_of_novel OdontocetiProperties.skipsUnsupported
    (extends_of_skipFill (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk
      (U := W) (U' := sk.skipFill) rfl rfl rfl rfl) S hcard
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ W.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (sk.skipFill.block c).creator = v
        rw [sk.skipFill_block_old hcU]; exact hcc
      · show (sk.skipFill.block c).round = S.slotRound k + 1
        rw [sk.skipFill_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict.** -/
theorem decided_none_fresh_agree_odontoceti [S : Slots Validator] (sk : SkipMsg W)
    {V : View Validator B Payload W} {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (OdontocetiProperties.odontocetiRule (Payload := Payload)) V T
      (S.slotRound k + 1))
    {U'' : BlockUniverse Validator B Payload}
    (he' : Extends (OdontocetiProperties.odontocetiRule (Payload := Payload)) sk.skipFill U'')
    {V'' Y : View Validator B Payload U''} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option B} (hY : Odontoceti.Decided U'' Y k v) : v = none :=
  (decided_agree_extends OdontocetiProperties.agree
    (Persist.of_banded OdontocetiProperties.banded) he' (V := sk.liftView V) (V' := V'') hsub
    (decided_none_fresh_odontoceti sk hcard hlead hk1 hk2 hpres) hY).symm

end Odontoceti

/-! ### And for Mahi-Mahi, at each wave width

The same four `rfl`s: its universes are the core's at the core's fault
model, so the fill is the core's and the two theorems are the generic
ones at Mahi-Mahi's band and agreement. -/

section MahiMahi

variable [Faults Validator] {B : Type} [LinearOrder B]
variable {W : BlockUniverse Validator B Payload} {w : ℕ}

/-- **Verdicts survive the fill, for Mahi-Mahi.** -/
theorem decided_fill_mahimahi [S : Slots Validator] (hw : 2 ≤ w) (sk : SkipMsg W)
    {V : View Validator B Payload W} {k : ℕ} {v : Option B}
    (h : MahiMahi.Decided w W V k v) :
    MahiMahi.Decided (U := sk.skipFill) w (sk.liftView V) k v :=
  decided_skipFill (R := MahiMahiProperties.mahiMahiRule (Payload := Payload) w)
    (Persist.of_banded (MahiMahiProperties.banded hw)) sk
    (U := W) (U' := sk.skipFill) rfl rfl rfl rfl (fun _ hb => hb) h

/-- **And agreement across it.** -/
theorem decided_fill_agree_mahimahi [S : Slots Validator] (hw : 2 ≤ w) (sk : SkipMsg W)
    {V : View Validator B Payload W} {Y : View Validator B Payload sk.skipFill}
    {k : ℕ} {v v' : Option B}
    (hv : MahiMahi.Decided w W V k v)
    (hw' : MahiMahi.Decided (U := sk.skipFill) w Y k v') : v = v' :=
  decided_agree_extends (MahiMahiProperties.agree hw)
    (Persist.of_banded (MahiMahiProperties.banded hw))
    (extends_of_skipFill (MahiMahiProperties.mahiMahiRule (Payload := Payload) w) sk
      (U := W) (U' := sk.skipFill) rfl rfl rfl rfl)
    (V' := sk.liftView V) (fun _ hb => hb) hv hw'

end MahiMahi
