import LeanDag.Properties.Sustain
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Optional.Skip
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.Bounded
import LeanDag.Properties.Band
import LeanDag.Properties.Deliver
import LeanDag.Properties.Derived.FromBand
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import LeanDag.Liveness

/-!
# The core rule as a carrier, and what it makes of a sustaining mechanism

The core protocol is a single file, `Mysticeti.lean`, rather than a
directory, so its properties-arc material lives here rather than in a
`Mysticeti/Properties/` pair. Two things:

* `mysticetiRule`, the core rule as a `Properties.DagRule` — stated here
  rather than taken from `Barnacle.mysticeti.toDagRule` so that the core's
  conformance depends on no mechanism.

* **What a sustaining mechanism gives the core's liveness.** `Sustains`
  promises that above a settling round old blocks keep their authors,
  references and (shifted) rounds; `certifiesAt_of_sustains` turns that
  into transport of the core's own certificate layer, and
  `directCommit_of_sustains` feeds the result to
  `directCommit_of_certifiesAt` — the lemma the reactive commit runs
  through. So any mechanism that sustains preserves the reactive
  discipline's commit on the transformed DAG, **with no pacing structure
  transported**: what the reactive exit produces is a certificate like
  any other, and certificates are made of references.

This is the consumer test `Sustains` owed. The first statement of that
obligation transported votes by name and could not be fed to this lemma;
the restatement over blocks can.
-/

namespace LeanDag

section ScheduleCongruence

/-! ## Reading the schedule at one slot

Three lemmas the band's induction and the bounded relation both use:
the direct rules consult the schedule's leaders only at the slot being
decided, so two schedules naming the same round and leader there agree
on the direct verdicts. Stated here, before either consumer, and
universe-polymorphic so both can use them. -/

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- Only the leader clause of `IsLeaderBlock` consults the schedule's
leaders, at the slot itself. -/
theorem isLeaderBlock_congr {S₁ S₂ : Slots Validator} {k : ℕ} {L : BlockId}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : IsLeaderBlock (S := S₁) U k L) : IsLeaderBlock (S := S₂) U k L := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [← hround]; exact h2, by rw [← hk]; exact h3⟩

/-- **The slot-level skip reads the schedule only at its own slot**, so
two schedules naming the same round and the same leader there agree on
whether the slot is skipped. -/
theorem slotBlamers_congr {S₁ S₂ : Slots Validator} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k) :
    slotBlamers (S := S₁) U k = slotBlamers (S := S₂) U k := by
  ext q
  simp only [slotBlamers, Finset.mem_filter, mem_blocksAt, hround]
  constructor
  · rintro ⟨hqb, hqn⟩
    exact ⟨hqb, fun j hj hjL => hqn j hj (isLeaderBlock_congr hround.symm hk.symm hjL)⟩
  · rintro ⟨hqb, hqn⟩
    exact ⟨hqb, fun j hj hjL => hqn j hj (isLeaderBlock_congr hround hk hjL)⟩

/-- The count that reads it is therefore the same count. -/
theorem directSkipSlotIn_congr {S₁ S₂ : Slots Validator}
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : DirectSkipSlotIn (S := S₁) U V k) : DirectSkipSlotIn (S := S₂) U V k := by
  unfold DirectSkipSlotIn at h ⊢
  rwa [slotBlamers_congr hround hk] at h

end ScheduleCongruence

namespace MysticetiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [Faults Validator]

/-- **The core rule as a carrier.** -/
def mysticetiRule : DagRule Validator BlockId Payload where
  Universe := BlockUniverse Validator BlockId Payload
  View := fun U => View Validator BlockId Payload U
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  Decided := fun S _ V k v => Decided (S := S) _ V k v

variable {U U' : BlockUniverse Validator BlockId Payload} {G R₀ : ℕ}

/-- The carrier's production predicate and the core's are the same
statement with the conjuncts in the other order — the one per-protocol
agreement `Sustains` asks for, here a reordering rather than `rfl`. -/
theorem populatedOn_ofCore {T : Finset Validator} {r : ℕ}
    (h : LeanDag.PopulatedOn U T r) : Properties.PopulatedOn mysticetiRule U T r :=
  fun v hv => let ⟨b, hb, hc, hr⟩ := h v hv; ⟨b, hb, hr, hc⟩

theorem populatedOn_toCore {T : Finset Validator} {r : ℕ}
    (h : Properties.PopulatedOn mysticetiRule U T r) : LeanDag.PopulatedOn U T r :=
  fun v hv => let ⟨b, hb, hr, hc⟩ := h v hv; ⟨b, hb, hc, hr⟩

/-- The carrier's synchrony predicate is the core's, on the nose. -/
theorem synchronisedOn_eq {T : Finset Validator} {r : ℕ} :
    Properties.SynchronisedOn mysticetiRule U T r ↔ LeanDag.SynchronisedOn U T r :=
  Iff.rfl

/-- The votes an old decision-round block counts are the votes it
counted: its references are unchanged, and so are theirs. -/
theorem votesIn_of_sustains (h : Sustains mysticetiRule U U' G R₀) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : R₀ + 1 < (U.block C).round) :
    votesIn U' C L = votesIn U C L := by
  unfold votesIn
  have hrefs : (U'.block C).refs = (U.block C).refs :=
    h.refs C hC (by change R₀ < (U.block C).round; omega)
  rw [hrefs]
  refine Finset.filter_congr fun q hq => ?_
  have hqU : q ∈ U.ids := U.complete C hC q hq
  have hqr := U.round_of_mem_refs hC hq
  have : (U'.block q).refs = (U.block q).refs :=
    h.refs q hqU (by change R₀ < (U.block q).round; omega)
  rw [this]

/-- **The core's certificate predicate transports.** -/
theorem certifies_of_sustains (h : Sustains mysticetiRule U U' G R₀) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : R₀ + 1 < (U.block C).round) :
    Certifies U' C L ↔ Certifies U C L := by
  unfold Certifies
  rw [votesIn_of_sustains h hC hCr]
  have : creatorsOf U'.block (votesIn U C L) = creatorsOf U.block (votesIn U C L) := by
    refine Finset.image_congr fun q hq => ?_
    have hqref := (Finset.mem_filter.mp hq).1
    have hqU : q ∈ U.ids := U.complete C hC q hqref
    have hqr := U.round_of_mem_refs hC hqref
    exact h.creator q hqU (by change R₀ ≤ (U.block q).round; omega)
  rw [this]

/-- **Certification at a slot survives a sustaining mechanism**, above
its settling round. -/
theorem certifiesAt_of_sustains (h : Sustains mysticetiRule U U' G R₀)
    {T : Finset Validator} {r : ℕ} {L : BlockId} (hr : R₀ ≤ r) (hG : G ≤ r)
    (hc : CertifiesAt U T r L) : CertifiesAt U' T (r - G) L := by
  intro v hv c hc' hcc hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc' (by change R₀ ≤ (U'.block c).round + G; omega)
  have hround' : (U'.block c).round + G = (U.block c).round := hround
  have hUr : (U.block c).round = r + 2 := by omega
  have hcreator : (U'.block c).creator = (U.block c).creator :=
    h.creator c hcU (by change R₀ ≤ (U.block c).round; omega)
  have hcc' : (U.block c).creator = v := by rw [← hcreator]; exact hcc
  exact (certifies_of_sustains h hcU (by omega)).mpr (hc v hv c hcU hcc' hUr)

/-- **The reactive commit survives any sustaining mechanism.** The
hypotheses are exactly what `Reactive/Mysticeti.directCommit` establishes
on the original DAG — certification by `cert_or_wait`, and production —
and the conclusion is the commit on the transformed one. -/
theorem directCommit_of_sustains (h : Sustains mysticetiRule U U' G R₀)
    {T : Finset Validator} {r : ℕ} {L : BlockId} (hr : R₀ ≤ r) (hG : G ≤ r)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommit U' L (r - G) :=
  directCommit_of_certifiesAt hcard
    (by
      have := h.populatedOn_of (T := T) (r := r + 2) (by omega) (by omega)
        (populatedOn_ofCore hpop)
      have e : r + 2 - G = r - G + 2 := by omega
      rw [e] at this
      exact populatedOn_toCore this)
    (certifiesAt_of_sustains h hr hG hc)

/-! ## Persistence

The second protocol to prove it, and the one that found the defect. The
core's skip once quantified over the candidates a universe holds, so a
slot with none was skipped *vacuously* and an extension supplying one
broke the derivation. Persistence was therefore stated at a grade,
`Quorate`, asking the view to hold a blaming quorum at the voting round
of every slot the extension gave a candidate to.

That grade named the repair rather than a property of the protocol. A
skip resting on the absence of a candidate is not final, which is the
one thing a skip rule exists to be, and `Decided.directSkip` now takes
`DirectSkipSlotIn` — a count of blockers at the slot, as Hydrozoan's
does. Both protocols persist unconditionally, the grade is gone from
`Persist`, and `Quorate` with it.
-/


/-- The core's universes are block DAGs. -/
theorem causal : Causal (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  fun U =>
    { complete := fun i hi j hj => U.complete i hi j hj
      refs_round := fun i hi j hj => U.round_of_mem_refs hi hj }

/-- Two quorums share a correct validator, so a quorum is not empty. -/
theorem quorumCard_pos : 0 < quorumCard Validator := by
  have := (inferInstance : Faults Validator).card_validators; omega

section PersistProof

variable {U U' : BlockUniverse Validator BlockId Payload}

theorem ext_block (he : Extends mysticetiRule U U') {b : BlockId} (hb : b ∈ U.ids) :
    U'.block b = U.block b := he.block b hb

theorem ext_mem (he : Extends mysticetiRule U U') {b : BlockId} (hb : b ∈ U.ids) :
    b ∈ U'.ids := he.subset b hb

/-- An old block votes for nothing the extension added. -/
theorem not_mem_refs_novel (he : Extends mysticetiRule U U') {b L : BlockId}
    (hb : b ∈ U.ids) (hL : L ∉ U.ids) : L ∉ (U'.block b).refs := by
  rw [ext_block he hb]; exact fun hin => hL (U.complete b hb L hin)

theorem blocksAt_subset (he : Extends mysticetiRule U U') (r : ℕ) :
    blocksAt U r ⊆ blocksAt U' r := by
  intro b hb
  rw [mem_blocksAt] at hb ⊢
  exact ⟨ext_mem he hb.1, by rw [ext_block he hb.1]; exact hb.2⟩

theorem creatorsOf_old (he : Extends mysticetiRule U U') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids) : creatorsOf U'.block s = creatorsOf U.block s :=
  Finset.image_congr fun i hi => by rw [ext_block he (hs i hi)]

theorem isLeaderBlock_mono [S : Slots Validator] (he : Extends mysticetiRule U U') {k : ℕ} {L : BlockId}
    (h : IsLeaderBlock U k L) : IsLeaderBlock U' k L := by
  obtain ⟨hm, hr, hc⟩ := h
  exact ⟨ext_mem he hm, by rw [ext_block he hm]; exact hr, by rw [ext_block he hm]; exact hc⟩

theorem isLeaderBlock_old [S : Slots Validator] (he : Extends mysticetiRule U U') {k : ℕ} {L : BlockId}
    (hL : L ∈ U.ids) (h : IsLeaderBlock U' k L) : IsLeaderBlock U k L := by
  obtain ⟨_, hr, hc⟩ := h
  rw [ext_block he hL] at hr hc
  exact ⟨hL, hr, hc⟩

/-- The votes an old certificate counts are the votes it counted. -/
theorem votesIn_old (he : Extends mysticetiRule U U') {C L : BlockId} (hC : C ∈ U.ids) :
    votesIn U' C L = votesIn U C L := by
  unfold votesIn
  rw [ext_block he hC]
  refine Finset.filter_congr fun q hq => ?_
  rw [ext_block he (U.complete C hC q hq)]

theorem certifies_old (he : Extends mysticetiRule U U') {C L : BlockId} (hC : C ∈ U.ids) :
    Certifies U' C L ↔ Certifies U C L := by
  unfold Certifies
  rw [votesIn_old he hC, creatorsOf_old he]
  intro q hq
  exact U.complete C hC q (Finset.mem_filter.mp hq).1

theorem mem_certificates_old (he : Extends mysticetiRule U U') {C L : BlockId} {r : ℕ}
    (hC : C ∈ U.ids) : C ∈ certificates U' L r ↔ C ∈ certificates U L r := by
  simp only [certificates, Finset.mem_filter, mem_blocksAt]
  rw [ext_block he hC, certifies_old he hC]
  exact ⟨fun h => ⟨⟨hC, h.1.2⟩, h.2⟩, fun h => ⟨⟨ext_mem he hC, h.1.2⟩, h.2⟩⟩

/-! ### The direct rules -/

theorem directCommitIn_mono (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ}
    (h : DirectCommitIn U V L r) : DirectCommitIn U' V' L r := by
  unfold DirectCommitIn at h ⊢
  refine le_trans h (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hvC⟩ := Finset.mem_image.mp hv
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCU : C ∈ U.ids := (mem_blocksAt.mp (Finset.mem_filter.mp hCc).1).1
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨(mem_certificates_old he hCU).mpr hCc, hV hCV⟩, ?_⟩
  rw [ext_block he hCU]; exact hvC

/-- **An old candidate blamed before is blamed still.** -/
theorem directSkipIn_mono (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ}
    (h : DirectSkipIn U V L r) : DirectSkipIn U' V' L r := by
  unfold DirectSkipIn at h ⊢
  refine le_trans h (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hv
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqn⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨blocksAt_subset he _ hqA, ?_⟩, hV hqV⟩, ?_⟩
  · rw [ext_block he hqU]; exact hqn
  · rw [ext_block he hqU]; exact hvq

/-- **A new candidate is blamed by every old block in view** — and the
grade supplies a quorum of them. This is the one place the condition is
consumed. -/
theorem directSkipIn_novel (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ} (hL : L ∉ U.ids)
    (hq : quorumCard Validator ≤ (creatorsOf U.block ((blocksAt U (r + 1)) ∩ V.ids)).card) :
    DirectSkipIn U' V' L r := by
  unfold DirectSkipIn
  refine le_trans hq (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq', hvq⟩ := Finset.mem_image.mp hv
  obtain ⟨hqA, hqV⟩ := Finset.mem_inter.mp hq'
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨blocksAt_subset he _ hqA, not_mem_refs_novel he hqU hL⟩, hV hqV⟩, ?_⟩
  rw [ext_block he hqU]; exact hvq

/-! ### The rung test -/

theorem certifiedIn_old (he : Extends mysticetiRule U U') {A L : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) : CertifiedIn U' A L r ↔ CertifiedIn U A L r := by
  unfold CertifiedIn
  constructor
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hreU, hCU⟩ := Extends.reaches_old causal he hA hre
    exact ⟨C, (mem_certificates_old he hCU).mp hC, hreU⟩
  · rintro ⟨C, hC, hre⟩
    have hCU : C ∈ U.ids := (mem_blocksAt.mp (Finset.mem_filter.mp hC).1).1
    exact ⟨C, (mem_certificates_old he hCU).mpr hC,
      (Extends.reaches_iff causal he hA).mpr hre⟩

/-- **A new candidate is certified by nothing an old anchor can see.** -/
theorem not_certifiedIn_novel (he : Extends mysticetiRule U U') {A L : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) (hL : L ∉ U.ids) : ¬ CertifiedIn U' A L r := by
  rintro ⟨C, hC, hre⟩
  obtain ⟨-, hCU⟩ := Extends.reaches_old causal he hA hre
  have hcert : Certifies U' C L := (Finset.mem_filter.mp hC).2
  unfold Certifies at hcert
  have hempty : votesIn U' C L = ∅ := by
    rw [votesIn_old he hCU, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqref, hqv⟩ := Finset.mem_filter.mp hq
    exact hL (U.complete q (U.complete C hCU q hqref) L hqv)
  rw [hempty] at hcert
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty, Nat.le_zero] at hcert
  exact absurd hcert (Nat.pos_iff_ne_zero.mp quorumCard_pos)

/-! ### The band, and the helpers it needs

The same lemmas as above, with the extension replaced by agreement on a
range of rounds. One-directional: `U'` may hold blocks `U` does not,
inside the band or out of it. -/

section Band

variable {lo hi g g' : ℕ}

theorem band_mem (h : AgreeBand mysticetiRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    b ∈ U'.ids := h.mem b hb h1 h2

theorem band_block (h : AgreeBand mysticetiRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).creator = (U.block b).creator :=
  h.block b hb (Or.inl ⟨h1, h2⟩)

theorem band_block' (h : AgreeBand mysticetiRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (hb' : b ∈ U'.ids)
    (h1 : lo ≤ (U'.block b).round + g') (h2 : (U'.block b).round + g' ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).creator = (U.block b).creator :=
  h.block b hb (Or.inr ⟨hb', h1, h2⟩)

theorem band_refs (h : AgreeBand mysticetiRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (h1 : lo < (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).refs = (U.block b).refs := h.refs b hb h1 h2

/-- A round layer of `U` lands on the layer of `U'` the shift names. -/
theorem blocksAt_band (h : AgreeBand mysticetiRule U U' lo hi g g') {r r' : ℕ}
    (hrr : r + g = r' + g') (h1 : lo ≤ r + g) (h2 : r + g ≤ hi) :
    blocksAt U r ⊆ blocksAt U' r' := by
  intro b hb
  rw [mem_blocksAt] at hb ⊢
  have hbb := band_block h hb.1 (by omega) (by omega)
  exact ⟨band_mem h hb.1 (by omega) (by omega), by omega⟩

theorem creatorsOf_band (h : AgreeBand mysticetiRule U U' lo hi g g') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round + g ∧ (U.block b).round + g ≤ hi) :
    creatorsOf U'.block s = creatorsOf U.block s :=
  Finset.image_congr fun i hi' => (band_block h (hs i hi').1 (hs i hi').2.1 (hs i hi').2.2).2

variable {S S' : Slots Validator}

/-- A candidate of slot `k` is a candidate of the slot `k'` that answers
to it: the shift carries its round, and the schedules name the same
leader there. -/
theorem isLeaderBlock_band (h : AgreeBand mysticetiRule U U' lo hi g g') {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi) {L : BlockId}
    (hL : IsLeaderBlock (S := S) U k L) : IsLeaderBlock (S := S') U' k' L := by
  obtain ⟨hm, hr, hc⟩ := hL
  have hb := band_block h hm (by omega) (by omega)
  exact ⟨band_mem h hm (by omega) (by omega), by omega, by rw [hb.2, hc, hlead]⟩

/-- And back, for a candidate the band already had. -/
theorem isLeaderBlock_band_old (h : AgreeBand mysticetiRule U U' lo hi g g') {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi) {L : BlockId}
    (hLU : L ∈ U.ids) (hL : IsLeaderBlock (S := S') U' k' L) :
    IsLeaderBlock (S := S) U k L := by
  obtain ⟨hm, hr, hc⟩ := hL
  have hb := band_block' h hLU hm (by omega) (by omega)
  exact ⟨hLU, by omega, by rw [← hb.2, hc, ← hlead]⟩

/-- The votes an in-band certificate counts are the votes it counted. -/
theorem votesIn_band (h : AgreeBand mysticetiRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) : votesIn U' C L = votesIn U C L := by
  unfold votesIn
  rw [band_refs h hC (by omega) h2]
  refine Finset.filter_congr fun q hq => ?_
  have hqU : q ∈ U.ids := U.complete C hC q hq
  have hqr := U.round_of_mem_refs hC hq
  rw [band_refs h hqU (by omega) (by omega)]

theorem certifies_band (h : AgreeBand mysticetiRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    Certifies U' C L ↔ Certifies U C L := by
  unfold Certifies
  rw [votesIn_band h hC h1 h2, creatorsOf_band h]
  intro q hq
  have hqU : q ∈ U.ids := U.complete C hC q (Finset.mem_filter.mp hq).1
  have hqr := U.round_of_mem_refs hC (Finset.mem_filter.mp hq).1
  exact ⟨hqU, by omega, by omega⟩

theorem mem_certificates_band (h : AgreeBand mysticetiRule U U' lo hi g g') {C L : BlockId}
    {r r' : ℕ} (hC : C ∈ U.ids) (hr : (U.block C).round = r + 2) (hrr : r + g = r' + g')
    (h1 : lo ≤ r + g) (h2 : r + 2 + g ≤ hi) :
    C ∈ certificates U' L r' ↔ C ∈ certificates U L r := by
  simp only [certificates, Finset.mem_filter, mem_blocksAt]
  have hb := band_block h hC (by omega) (by omega)
  rw [certifies_band h hC (by omega) (by omega)]
  exact ⟨fun hx => ⟨⟨hC, hr⟩, hx.2⟩,
    fun hx => ⟨⟨band_mem h hC (by omega) (by omega), by omega⟩, hx.2⟩⟩

/-! ### The direct rules and the anchor test, across a shifted band -/

theorem directCommitIn_band (h : AgreeBand mysticetiRule U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 2 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hc : DirectCommitIn U V L r) : DirectCommitIn U' V' L r' := by
  unfold DirectCommitIn at hc ⊢
  refine le_trans hc (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨C, hC, hvC⟩ := Finset.mem_image.mp hw
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCA := (Finset.mem_filter.mp hCc).1
  have hCU : C ∈ U.ids := (mem_blocksAt.mp hCA).1
  have hCr : (U.block C).round = r + 2 := (mem_blocksAt.mp hCA).2
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨(mem_certificates_band h hCU hCr hrr hr hhi).mpr hCc,
      hV C hCV (by omega) (by omega)⟩, ?_⟩
  rw [(band_block h hCU (by omega) (by omega)).2]; exact hvC

theorem directSkipSlotIn_band (h : AgreeBand mysticetiRule U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {k k' : ℕ} (hkk : S.slotRound k + g = S'.slotRound k' + g')
    (hlead : S.leader k = S'.leader k') (hlo : lo = S.slotRound k + g)
    (hhi : S.slotRound k + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    (hs : DirectSkipSlotIn (S := S) U V k) : DirectSkipSlotIn (S := S') U' V' k' := by
  unfold DirectSkipSlotIn at hs ⊢
  refine le_trans hs (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  simp only [slotBlamers, Finset.mem_filter] at hqf
  obtain ⟨hqA, hqn⟩ := hqf
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.block q).round = S.slotRound k + 1 := (mem_blocksAt.mp hqA).2
  refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
  · simp only [Finset.mem_inter, slotBlamers, Finset.mem_filter]
    refine ⟨⟨blocksAt_band h (by omega) (by omega) (by omega) hqA, ?_⟩,
      hV q hqV (by omega) (by omega)⟩
    rw [band_refs h hqU (by omega) (by omega)]
    intro j hj hjL
    have hjU : j ∈ U.ids := U.complete q hqU j hj
    exact hqn j hj (isLeaderBlock_band_old h hkk hlead (by omega) (by omega) hjU hjL)
  · rw [(band_block h hqU (by omega) (by omega)).2]; exact hvq

theorem certifiedIn_band (h : AgreeBand mysticetiRule U U' lo hi g g') {A L : BlockId}
    {r r' : ℕ} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hrr : r + g = r' + g')
    (hr : lo ≤ r + g) (hrhi : r + 2 + g ≤ hi) :
    CertifiedIn U' A L r' ↔ CertifiedIn U A L r := by
  unfold CertifiedIn
  constructor
  · rintro ⟨C, hC, hre⟩
    have hCr' : (U'.block C).round = r' + 2 := (mem_blocksAt.mp (Finset.mem_filter.mp hC).1).2
    have hCrR : (mysticetiRule.block U' C).round = r' + 2 := hCr'
    obtain ⟨hCU, hreU, hCeq⟩ :=
      AgreeBand.reaches_old causal h hA hAlo hAhi hre (by omega)
    have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
    exact ⟨C, (mem_certificates_band h hCU (by omega) hrr hr hrhi).mp hC, hreU⟩
  · rintro ⟨C, hC, hre⟩
    have hCA := (Finset.mem_filter.mp hC).1
    have hCU : C ∈ U.ids := (mem_blocksAt.mp hCA).1
    have hCr : (U.block C).round = r + 2 := (mem_blocksAt.mp hCA).2
    have hCrR : (mysticetiRule.block U C).round = r + 2 := hCr
    exact ⟨C, (mem_certificates_band h hCU hCr hrr hr hrhi).mpr hC,
      AgreeBand.reaches_of causal h hA hAhi hre (by omega)⟩

/-- **A candidate the band did not carry is certified by nothing an old
anchor can see.** -/
theorem not_certifiedIn_band_novel (h : AgreeBand mysticetiRule U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hrr : r + g = r' + g')
    (hr : lo ≤ r + g) (hrhi : r + 2 + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ CertifiedIn U' A L r' := by
  rintro ⟨C, hC, hre⟩
  have hCr' : (U'.block C).round = r' + 2 := (mem_blocksAt.mp (Finset.mem_filter.mp hC).1).2
  have hCrR : (mysticetiRule.block U' C).round = r' + 2 := hCr'
  obtain ⟨hCU, -, hCeq⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hre (by omega)
  have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
  have hcert : Certifies U' C L := (Finset.mem_filter.mp hC).2
  rw [certifies_band h hCU (by omega) (by omega)] at hcert
  unfold Certifies at hcert
  have hempty : votesIn U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqref, hqv⟩ := Finset.mem_filter.mp hq
    exact hL (U.complete q (U.complete C hCU q hqref) L hqv)
  rw [hempty] at hcert
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty, Nat.le_zero] at hcert
  exact absurd hcert (Nat.pos_iff_ne_zero.mp quorumCard_pos)

end Band


/-! ### Persistence -/

/-- **Every verdict of the core reads a band of rounds**, from the slot's
own round up to a top the derivation determines: any universe carrying
that band, and any view holding the band's blocks, decides the slot the
same way.

One induction, four cases, and the two properties the mechanisms consume
are corollaries of it. The direct cases read two rounds above the slot
and stop. The indirect cases read their anchor's derivation and the
intermediates', and the top is the largest of those, which is where the
band's upper end comes from and why it cannot be fixed in advance.

Nothing here supposes that the larger universe adds no candidates. Where
one appears the anchor cannot see it, because the anchor's cone stays
inside the band it came from (`not_certifiedIn_band_novel`), and the
slot-level skip does not look for it at all. -/
theorem banded_aux [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (hd : Decided U V k v) :
    ∃ top, S.slotRound k + 2 ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : Slots Validator)
        (U' : BlockUniverse Validator BlockId Payload)
        (V' : View Validator BlockId Payload U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand mysticetiRule U U' (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        Decided (S := S') U' V' k' v := by
  classical
  induction hd with
  | @directCommit k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine Decided.directCommit (S := S')
        (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL) ?_
      exact directCommitIn_band hab hkk (by omega) (by omega)
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hc
  | @directSkip k hs =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact Decided.directSkip (S := S')
        (directSkipSlotIn_band hab hkk hlk rfl (by omega)
          (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hs)
  | @indirectCommit k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U j A := isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Decided.indirectCommit (S := S') (by omega) (by
          have := helig; unfold Eligible decisionRound at this ⊢; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_
        (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL) ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' :=
          hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Eligible Validator (S := S) k (i' - k' + k) := by
          have := h3; unfold Eligible decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        have := hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
        exact this
      · exact certifiedIn_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega) |>.mpr hcert
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U j A := isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Decided.indirectSkip (S := S') (by omega) (by
          have := helig; unfold Eligible decisionRound at this ⊢; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3; unfold Eligible decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · intro L hL' hc'
        by_cases hLo : L ∈ U.ids
        · exact hnone L (isLeaderBlock_band_old hab hkk hlk (by omega) (by omega) hLo hL')
            ((certifiedIn_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mp hc')
        · exact not_certifiedIn_band_novel hab hAL.1 hAlo hAhi hkk (by omega) (by omega)
            hLo hc'

/-- **The core reads a band.** -/
theorem banded : Banded
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := S) hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' U' V' k' hkd hsch hlead hab hV⟩

/-- The carrier's coverage predicate is the core's, on the nose. -/
theorem coversUpto_eq {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {N : ℕ} :
    Properties.CoversUpto mysticetiRule V N ↔ V.CoversUpto N := Iff.rfl

/-- **A caught-up validator reaches every verdict.** Whatever any view
decides, a view covering far enough decides too — the round being the
band's own ceiling rather than a rule-specific `r + 2`. What a
view-level mechanism has to deliver, for this protocol. -/
theorem exists_coversUpto_decides [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload}
    {W : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (hW : Decided U W k v) :
    ∃ N, ∀ V : View Validator BlockId Payload U, V.CoversUpto N → Decided U V k v :=
  Properties.exists_coversUpto_decides banded hW

/-- **A commit names the slot's candidate.** `isLeaderBlock_of_decided`
under the property's name — one of seven such lemmas across the
protocols, and the reason `Properties/Candidate.lean` exists. -/
theorem commitsCandidate : CommitsCandidate
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  fun S _ _ _ _ hd => isLeaderBlock_of_decided (S := S) hd

/-- **The core persists unconditionally**, as an evidence-backed rule
must — now a corollary of the band rather than an induction of its own.
The grade `Quorate` that stood here before was not a property of the
protocol but the missing half of its skip rule. -/
theorem persist : Persist
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Persist.of_banded banded

/-- **L2 re-derived, with no induction of its own.** View monotonicity
(`decided_mono`, four cases in `Liveness.lean`) is the band read at a
fixed universe. The consumer test for `banded`: an existing induction
recovered from the property. -/
theorem decided_mono_of_band [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload}
    {V V' : View Validator BlockId Payload U} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {v : Option BlockId} (hd : Decided U V k v) : Decided U V' k v :=
  Properties.decided_mono_of_banded banded hsub hd

end PersistProof

/-! ## Skippability, at a correct quorum

The core's direct skip quantifies over candidates and, for each, counts
the voting-round blocks that do *not* reference it. If every `T`-block
at the voting round references none of the slot's candidates, every one
of them is a blamer for every candidate at once, so `quorumCard ≤ |T|`
is enough — **a correct quorum skips an unsupported slot**.

Hydrozoan reaches no skip from a correct quorum: its slot-level `qFast`
count is a higher threshold, which is the price of the unconditional
persistence the core had to be repaired to reach. -/

section Skip

variable {U : BlockUniverse Validator BlockId Payload} [S : Slots Validator]

/-- Every member of `T` blames the slot: its voting-round block is in
view and references no candidate, which is what `Unsupported` says. -/
theorem subset_blamers {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hpres : PresentAt mysticetiRule V T (S.slotRound k + 1))
    (huns : Unsupported mysticetiRule S U V T k) :
    T ⊆ creatorsOf U.block (slotBlamers U k ∩ V.ids) := by
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
  have hcU : c ∈ U.ids := V.subset_ids hcV
  refine Finset.mem_image.mpr ⟨c, ?_, hcc⟩
  rw [Finset.mem_inter, slotBlamers, Finset.mem_filter]
  exact ⟨⟨mem_blocksAt.mpr ⟨hcU, hcr⟩,
    fun j hj hjL => huns c hcV (by rw [hcc]; exact hv) hcr j hjL hj⟩, hcV⟩

/-- **The core skips an unsupported slot from a correct quorum.** -/
theorem skipsUnsupported :
    SkipsUnsupported (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun T => quorumCard Validator ≤ T.card) :=
  fun S U V T k hq hpres huns =>
    Decided.directSkip (le_trans hq (Finset.card_le_card (subset_blamers (S := S) hpres huns)))

end Skip

end MysticetiProperties

/-! ## The core's bounded decision relation

`Decided`, with every slot the derivation mentions — the decided slot,
the anchor, the eligible intermediates — strictly below a bound `B`.
It is the protocol's own tool, not part of any interface: the mechanism
reads `Properties.DecidedBelow`, and `decidedBelow_of_decidedWithin`
carries this into that. What it adds is a **tight** bound, which the
semantic form cannot recover.

The bound lives in the relation because it cannot live anywhere else: a
`Decided` derivation is a proof of a `Prop` and its anchors cannot be
recovered from it. -/

section BoundedRelation

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- **The bounded decision relation.** `Decided`, with every slot the
derivation mentions strictly below `B`. -/
inductive DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      k < B → IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- The direct rule skips the slot. -/
  | directSkip {k : ℕ} :
      k < B → DirectSkipSlotIn U V k →
      DecidedWithin U V B k none
  /-- Anchored on the nearest eligible committed slot below the bound. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- Anchored likewise, no candidate is in reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      DecidedWithin U V B k none

namespace DecidedWithin

variable {V : View Validator BlockId Payload U} {B B' k : ℕ} {v : Option BlockId}

/-- Forgetting the bound: every bounded derivation is a `Decided`
derivation, so the base safety development — M1–M6 in particular —
applies to bounded verdicts without restatement. -/
theorem toDecided (h : DecidedWithin U V B k v) : Decided U V k v := by
  induction h with
  | directCommit _ hL hdc => exact Decided.directCommit hL hdc
  | directSkip _ hall => exact Decided.directSkip hall
  | indirectCommit hkj _ helig _ _ hL hcert ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hL hcert
  | indirectSkip hkj _ helig _ _ hnone ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnone

/-- The decided slot lies below the bound. -/
theorem lt_bound (h : DecidedWithin U V B k v) : k < B := by
  cases h with
  | directCommit hk _ _ => exact hk
  | directSkip hk _ => exact hk
  | indirectCommit hkj hj _ _ _ _ _ => omega
  | indirectSkip hkj hj _ _ _ _ => omega

/-- The bound relaxes upward. -/
theorem mono (h : DecidedWithin U V B k v) (hBB : B ≤ B') :
    DecidedWithin U V B' k v := by
  induction h with
  | directCommit hk hL hdc => exact directCommit (by omega) hL hdc
  | directSkip hk hall => exact directSkip (by omega) hall
  | indirectCommit hkj hj helig _ _ hL hcert ihj ihmid =>
      exact indirectCommit hkj (by omega) helig ihj (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        hL hcert
  | indirectSkip hkj hj helig _ _ hnone ihj ihmid =>
      exact indirectSkip hkj (by omega) helig ihj (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        hnone

/-- Two bounded verdicts agree — M6, through the embedding. -/
theorem agree {V₁ V₂ : View Validator BlockId Payload U} {B₁ B₂ k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : DecidedWithin U V₁ B₁ k v₁)
    (h₂ : DecidedWithin U V₂ B₂ k v₂) : v₁ = v₂ :=
  decided_agree h₁.toDecided h₂.toDecided

end DecidedWithin

omit S in
/-- **Congruence below the bound**, for any two schedules with one round
structure. Only `IsLeaderBlock` consults the leaders, and only at slots
below `B`; eligibility, decision rounds and every counting predicate
read the rounds, which are shared. -/
theorem decidedWithin_congr_of_slotRound {S₁ S₂ : Slots Validator}
    (hround : S₁.slotRound = S₂.slotRound) {V : View Validator BlockId Payload U}
    {B k : ℕ} {v : Option BlockId} (ha : ∀ m, m < B → S₁.leader m = S₂.leader m)
    (h : DecidedWithin (S := S₁) U V B k v) : DecidedWithin (S := S₂) U V B k v := by
  obtain ⟨sr, ld, hmono, hunb, hkeyed⟩ := S₁
  obtain ⟨sr', ld', hmono', hunb', hkeyed'⟩ := S₂
  simp only at hround
  subst hround
  induction h with
  | @directCommit k L hk hL hdc =>
      exact DecidedWithin.directCommit (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hk
        (isLeaderBlock_congr (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k hk) hL) hdc
  | @directSkip k hk hall =>
      exact DecidedWithin.directSkip (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hk
        (directSkipSlotIn_congr (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k hk) hall)
  | @indirectCommit k j A L hkj hj helig _ _ hL hcert ihj ihmid =>
      exact DecidedWithin.indirectCommit (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hkj hj helig
        ihj (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        (isLeaderBlock_congr (S₁ := ⟨sr, ld, hmono, hunb, hkeyed⟩)
          (S₂ := ⟨sr, ld', hmono', hunb', hkeyed'⟩) rfl (ha k (by omega)) hL) hcert
  | @indirectSkip k j A hkj hj helig _ _ hnone ihj ihmid =>
      exact DecidedWithin.indirectSkip (S := ⟨sr, ld', hmono', hunb', hkeyed'⟩) hkj hj helig
        ihj (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        (fun L hL => hnone L (isLeaderBlock_congr (S₁ := ⟨sr, ld', hmono', hunb', hkeyed'⟩)
          (S₂ := ⟨sr, ld, hmono, hunb, hkeyed⟩) rfl (ha k (by omega)).symm hL))

end BoundedRelation

/-! ## Conformance to the schedule family

Two properties, where there were five. `Agree` for safety;
`LeaderCommits` under the timed precondition `coreLive`, and `Descends`
under `SpansEligible`, for liveness. `Bounded` and `SchedLocal` are
gone: `DecidedBelow` is a definition over `DagRule`, so its laws are
theorems and no protocol proves them. -/

namespace MysticetiProperties

open Properties

section Bounded

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **M6 as a property.** -/
theorem agree :
    Agree (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) := by
  intro S U V₁ V₂ k v₁ v₂ h₁ h₂
  exact decided_agree (S := S) (U := U) h₁ h₂

/-- **The timed core's liveness precondition**, over a slot window: a
quorum `T` synchronised from some round `R₀` at or below the window's
first slot, the DAG populated by `T` from `R₀` to a horizon `N`, the
view caught up to `N`, and every slot of the window two rounds under
`N`. It reads no leader, so it holds under every schedule with the same
rounds. -/
def coreLive (S : Slots Validator) {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧
    ∃ R₀ N, SynchronisedOn U T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) ∧ V.CoversUpto N ∧
      ∀ k, k < K → S.slotRound k + 2 ≤ N

/-- **L4 as a property**: a `T`-led slot in the window commits, and the
commit reads one leader, so its bound is one above the slot. -/
theorem leaderCommits :
    LeaderCommits (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => coreLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := hlive
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk := hN k hK
  obtain ⟨L, hL, hdc⟩ := directCommit_of_leader_mem (S := S) (U := U) hcard hs hRk
    (hpop _ hRk (by omega)) (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega)) hlead
  have hin : DirectCommitIn U V L (S.slotRound k) :=
    directCommitIn_of_coversUpto hdc (hcov.mono hNk)
  refine ⟨L, by omega, Decided.directCommit hL hin, ?_⟩
  intro S' hround hlead'
  obtain ⟨hm, hr, hcr⟩ := hL
  refine Decided.directCommit (S := S') ⟨hm, by rw [hround]; exact hr,
    by rw [hlead' k (by omega)]; exact hcr⟩ ?_
  rw [hround]; exact hin

/-- **The core's own bounded relation lands in the derived one.**
`DecidedWithin` still names the slots a derivation mentions, which is
the tight information `LeaderCommits` and `Descends` need; this says
that carrying it implies the semantic bound the mechanism reads. The
old `BoundedRule` field asked the carrier for the relation itself. -/
theorem decidedBelow_of_decidedWithin [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {B k : ℕ} {v : Option BlockId} (h : DecidedWithin (S := S) U V B k v) :
    DecidedBelow mysticetiRule S B V k v :=
  ⟨h.lt_bound, h.toDecided, fun S' hround hlead =>
    (decidedWithin_congr_of_slotRound (S₁ := S) (S₂ := S') hround.symm
      (fun m hm => (hlead m hm).symm) h).toDecided⟩

/-- **The committed-run descent.** `c` consecutive commits decide every
slot below them, and the derivations depend on no leader at or above the
run's top — which is what `DecidedBelow` records, and what the old
`DecidedWithin` relation was carried to record.

The argument is the base `decided_below_of_committed_run`; what is added
is that each derivation is rebuilt under any schedule sharing the round
structure and the leader prefix, which is immediate because every slot
the derivation names lies under the bound. -/
theorem decidedBelow_of_committed_run [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n →
      ∃ B', DecidedBelow mysticetiRule S (n + 1) V j (some B')) :
    ∀ i, i < b → ∃ v, DecidedBelow mysticetiRule S (n + 1) V i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d →
      ∃ v, DecidedBelow mysticetiRule S (n + 1) V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, Eligible Validator i j ∧
          ∃ B', DecidedBelow mysticetiRule S (n + 1) V j (some B') :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      have hle : Nat.find hex ≤ n :=
        Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B', hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex → Eligible Validator i i' →
          DecidedBelow mysticetiRule S (n + 1) V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, DecidedBelow mysticetiRule S (n + 1) V i' (some C) :=
          fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hi'b : i' < b := by
          by_contra hge
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      have hin : i < n + 1 := by omega
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U B' L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        refine ⟨some L, hin, Decided.indirectCommit (lt_of_eligible helig) helig
          hB.toDecided (fun i' h1 h2 h3 => (hmid i' h1 h2 h3).toDecided) hL hcert, ?_⟩
        intro S' hround hlead
        have heq : ∀ x y, Eligible Validator (S := S') x y ↔ Eligible Validator (S := S) x y := by
          intro x y; simp only [Eligible, decisionRound, hround]
        have hL' : IsLeaderBlock (S := S') U i L := by
          obtain ⟨hm, hr, hcr⟩ := hL
          exact ⟨hm, by rw [hround]; exact hr, by rw [hlead i hin]; exact hcr⟩
        refine Decided.indirectCommit (S := S') (lt_of_eligible (S := S) helig)
          ((heq _ _).mpr helig)
          (hB.2.2 S' hround hlead)
          (fun i' h1 h2 h3 => (hmid i' h1 h2 ((heq _ _).mp h3)).2.2 S' hround hlead) hL' ?_
        · rw [hround]; exact hcert
      · push Not at hc
        refine ⟨none, hin, Decided.indirectSkip (lt_of_eligible helig) helig
          hB.toDecided (fun i' h1 h2 h3 => (hmid i' h1 h2 h3).toDecided) hc, ?_⟩
        intro S' hround hlead
        have heq : ∀ x y, Eligible Validator (S := S') x y ↔ Eligible Validator (S := S) x y := by
          intro x y; simp only [Eligible, decisionRound, hround]
        refine Decided.indirectSkip (S := S') (lt_of_eligible (S := S) helig)
          ((heq _ _).mpr helig)
          (hB.2.2 S' hround hlead)
          (fun i' h1 h2 h3 => (hmid i' h1 h2 ((heq _ _).mp h3)).2.2 S' hround hlead) ?_
        intro L hL'
        have hL : IsLeaderBlock (S := S) U i L := by
          obtain ⟨hm, hr, hcr⟩ := hL'
          exact ⟨hm, by rw [← hround]; exact hr, by rw [← hlead i hin]; exact hcr⟩
        rw [hround]
        exact hc L hL
  intro i hi
  exact key (b - i) i hi (le_refl _)

/-- **The descent as a property**, under the spanning hypothesis on the
round structure. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : SpansEligible (Validator := Validator) (S := S) c) :
    Descends (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c := by
  intro U V b hrun i hi
  have hbc : b + c - 1 + 1 = b + c := by omega
  have hrun' : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B', DecidedBelow mysticetiRule S (b + c - 1 + 1) V j (some B') := by
    intro j hj1 hj2
    obtain ⟨L, hL⟩ := hrun j hj1 (by omega)
    exact ⟨L, by rw [hbc]; exact hL⟩
  obtain ⟨v, hv⟩ := decidedBelow_of_committed_run (S := S) (U := U) (V := V) (b := b)
    (n := b + c - 1) (by omega) (fun i hi => hspans b i hi) hrun' i hi
  exact ⟨v, by rw [← hbc]; exact hv⟩

end Bounded

end MysticetiProperties

end LeanDag
