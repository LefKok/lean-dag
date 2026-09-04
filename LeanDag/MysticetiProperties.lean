import LeanDag.Properties.Sustain
import LeanDag.Properties.Persist
import LeanDag.Properties.Skip
import LeanDag.Properties.Commit
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

/-! ## Persistence, at the core's grade

The second protocol to prove `Persist`, and the one that tests the
grading. Hydrozoan needed no condition because its skip counts blames at
the slot. The core's skip quantifies over candidates, so a slot with no
candidate is skipped *vacuously* — and an extension can supply one. The
condition below is what makes the new candidate skippable rather than
merely present: the view already holds a quorum at the voting round of
every slot the extension gives a candidate to, and every one of those
blocks blames it, since old blocks reference only old blocks.

This is `SafeSkip.QuorateOverGap`'s content, stated without the skip
message: `QuorateOverGap` asks for the quorum at every gap round, and
the gap rounds are exactly where a fill's candidates land. The condition
is on the **view**, which is why `Persist`'s `Ok` had to see one. -/

section Persist

/-- The core's grade: at every slot the extension gives a new candidate,
the view holds a quorum at the voting round. -/
def Quorate (S : Slots Validator) (U U' : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : Prop :=
  ∀ k L, IsLeaderBlock (S := S) U' k L → L ∉ U.ids →
    quorumCard Validator ≤ (creatorsOf U.block ((blocksAt U (S.slotRound k + 1)) ∩ V.ids)).card

end Persist

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

/-! ### Persistence -/

/-- **The core's verdicts survive every extension.** Four cases, none of
them conditional. A commit is evidence a larger view still holds; a skip
is a count of blockers that reference no candidate, and the blocks
behind it neither move nor acquire references; the two indirect cases
read an old anchor's causal history, which an extension cannot grow. -/
theorem persist_aux [S : Slots Validator] (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids)
    {k : ℕ} {v : Option BlockId} (hd : Decided U V k v) : Decided U' V' k v := by
  induction hd with
  | @directCommit k L hL hc =>
      exact Decided.directCommit (isLeaderBlock_mono he hL) (directCommitIn_mono he hV hc)
  | @directSkip k hs =>
      -- **The case the grade used to pay for.** A slot-level blamer
      -- references no candidate, and an old block's references are old,
      -- so a candidate the extension introduces is referenced by none of
      -- them: the same blockers blame the same slot in `U'`.
      have hblk : ∀ b, b ∈ U.ids → U'.block b = U.block b := fun b hb => he.block b hb
      have hids : ∀ b, b ∈ U.ids → b ∈ U'.ids := fun b hb => he.subset b hb
      refine Decided.directSkip (le_trans hs (Finset.card_le_card ?_))
      intro a ha
      rw [mem_creatorsOf] at ha ⊢
      obtain ⟨q, hq, hqc⟩ := ha
      rw [Finset.mem_inter, slotBlamers, Finset.mem_filter] at hq
      obtain ⟨⟨hqb, hqn⟩, hqV⟩ := hq
      rw [mem_blocksAt] at hqb
      refine ⟨q, ?_, ?_⟩
      · rw [Finset.mem_inter, slotBlamers, Finset.mem_filter]
        refine ⟨⟨mem_blocksAt.mpr ⟨hids q hqb.1, ?_⟩, fun j hj hjL => ?_⟩, hV hqV⟩
        · rw [hblk q hqb.1]; exact hqb.2
        · rw [hblk q hqb.1] at hj
          exact hqn j hj (isLeaderBlock_old he (U.complete q hqb.1 j hj) hjL)
      · rw [hblk q hqb.1]; exact hqc
  | @indirectCommit k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      have hA : A ∈ U.ids := (isLeaderBlock_of_decided hanchor).1
      exact Decided.indirectCommit hkj helig ihj (fun i h1 h2 he' => ihmid i h1 h2 he')
        (isLeaderBlock_mono he hL) ((certifiedIn_old he hA).mpr hcert)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert ihj ihmid =>
      have hA : A ∈ U.ids := (isLeaderBlock_of_decided hanchor).1
      refine Decided.indirectSkip hkj helig ihj (fun i h1 h2 he' => ihmid i h1 h2 he') ?_
      intro L hL hc
      by_cases hLo : L ∈ U.ids
      · exact hnocert L (isLeaderBlock_old he hLo hL) ((certifiedIn_old he hA).mp hc)
      · exact not_certifiedIn_novel he hA hLo hc

/-- **The core persists unconditionally**, as an evidence-backed rule
must. The grade `Quorate` that stood here before was not a property of
the protocol but the missing half of its skip rule, since recovered
into `Decided.directSkip`. -/
theorem persist_unconditional : Persist.Unconditional
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  fun S U U' he V V' _ hV k v hd => persist_aux (S := S) he hV hd

/-- The graded form, for consumers that carry a condition. -/
theorem persist : Persist (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (fun S U U' V => Quorate S U U' V) :=
  Persist.of_unconditional persist_unconditional

end PersistProof

/-! ## Skippability, at a correct quorum

The core's direct skip quantifies over candidates and, for each, counts
the voting-round blocks that do *not* reference it. If every `T`-block
at the voting round references none of the slot's candidates, every one
of them is a blamer for every candidate at once, so `quorumCard ≤ |T|`
is enough — **a correct quorum skips an unsupported slot**.

Set beside `Persist`, this inverts. The same per-candidate skip that
needs `Quorate` to keep a *vacuous* skip alive under extension is what
makes any *specific* unsupported candidate trivially blamed. Hydrozoan
is the mirror image: its slot-level `qFast` count survives every
extension unconditionally and reaches no skip from a correct quorum.
One mechanism, opposite grades on the two properties. -/

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
This is what `Properties.BoundedRule` asks a protocol for, and it lives
with the protocol because it is *its* relation: the adaptive mechanism
reads only the properties proved of it below.

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

omit [DecidableEq BlockId] S in
/-- Only the leader clause of `IsLeaderBlock` consults the schedule's
leaders, at the slot itself. -/
theorem isLeaderBlock_congr {S₁ S₂ : Slots Validator} {k : ℕ} {L : BlockId}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : IsLeaderBlock (S := S₁) U k L) : IsLeaderBlock (S := S₂) U k L := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [← hround]; exact h2, by rw [← hk]; exact h3⟩

omit S in
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

omit S in
/-- The count that reads it is therefore the same count. -/
theorem directSkipSlotIn_congr {S₁ S₂ : Slots Validator}
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : DirectSkipSlotIn (S := S₁) U V k) : DirectSkipSlotIn (S := S₂) U V k := by
  unfold DirectSkipSlotIn at h ⊢
  rwa [slotBlamers_congr hround hk] at h

omit S in
/-- **Congruence below the bound**, for any two schedules with one round
structure. Only `IsLeaderBlock` consults the leaders, and only at slots
below `B`; eligibility, decision rounds and every counting predicate
read the rounds, which are shared. This is the core's
`Properties.SchedLocal`. -/
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

/-- **The committed-run descent, bounded.** The base
`decided_below_of_committed_run`, restated with the anchors' bound in
the conclusion: the derivation the base proof builds already anchors at
or below the run's top, so carrying `n + 1` through is a restatement,
not a new argument. -/
theorem decidedWithin_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B', DecidedWithin U V (n + 1) j (some B')) :
    ∀ i, i < b → ∃ v, DecidedWithin U V (n + 1) i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, DecidedWithin U V (n + 1) i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, Eligible Validator i j ∧
          ∃ B', DecidedWithin U V (n + 1) j (some B') :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      have hle : Nat.find hex ≤ n :=
        Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B', hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex → Eligible Validator i i' →
          DecidedWithin U V (n + 1) i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, DecidedWithin U V (n + 1) i' (some C) :=
          fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hi'b : i' < b := by
          by_contra hge
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U B' L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        exact ⟨some L, DecidedWithin.indirectCommit (lt_of_eligible helig)
          (by omega) helig hB hmid hL hcert⟩
      · push Not at hc
        exact ⟨none, DecidedWithin.indirectSkip (lt_of_eligible helig)
          (by omega) helig hB hmid hc⟩
  intro i hi
  exact key (b - i) i hi (le_refl _)

end BoundedRelation

/-! ## Conformance to the schedule family

The core as a `BoundedRule`, and the five properties the adaptive
mechanism reads: `Agree`, `Bounded`, `SchedLocal` for safety;
`LeaderCommits` under the timed precondition `coreLive`, and `Descends`
under `SpansEligible`, for liveness. -/

namespace MysticetiProperties

open Properties

section Bounded

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The core rule with its bounded relation. -/
def mysticetiBounded : BoundedRule Validator BlockId Payload where
  toDagRule := mysticetiRule
  DecidedWithin := fun S B {U} V k v => DecidedWithin (S := S) U V B k v

/-- **M6 as a property.** -/
theorem agree :
    Agree (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) := by
  intro S U V₁ V₂ k v₁ v₂ h₁ h₂
  exact decided_agree (S := S) (U := U) h₁ h₂

theorem bounded :
    Bounded (mysticetiBounded (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S B U V k v h
    exact DecidedWithin.toDecided (S := S) (U := U) h
  · intro S B U V k v h
    exact DecidedWithin.lt_bound (S := S) (U := U) h
  · intro S B B' U V k v h hBB
    exact DecidedWithin.mono (S := S) (U := U) h hBB

/-- **The core reads the schedule only below the bound.** -/
theorem schedLocal :
    SchedLocal (mysticetiBounded (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) := by
  intro S₁ S₂ hround B ha U V k v h
  exact decidedWithin_congr_of_slotRound (S₁ := S₁) (S₂ := S₂) (U := U) hround ha h

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

/-- **L4 as a property**: a `T`-led slot in the window commits, within
a bound one above it. -/
theorem leaderCommits :
    LeaderCommits (mysticetiBounded (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => coreLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := hlive
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk := hN k hK
  obtain ⟨L, hL, hdc⟩ := directCommit_of_leader_mem (S := S) (U := U) hcard hs hRk
    (hpop _ hRk (by omega)) (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega)) hlead
  exact ⟨L, DecidedWithin.directCommit (S := S) (U := U) (by omega) hL
    (directCommitIn_of_coversUpto hdc (hcov.mono hNk))⟩

/-- **The descent as a property**, under the spanning hypothesis on the
round structure. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : SpansEligible (Validator := Validator) (S := S) c) :
    Descends (mysticetiBounded (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c := by
  intro U V b hrun i hi
  have hbc : b + c - 1 + 1 = b + c := by omega
  have hrun' : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B', DecidedWithin (S := S) (U := U) V (b + c - 1 + 1) j (some B') := by
    intro j hj1 hj2
    obtain ⟨L, hL⟩ := hrun j hj1 (by omega)
    exact ⟨L, by rw [hbc]; exact hL⟩
  obtain ⟨v, hv⟩ := decidedWithin_below_of_committed_run (S := S) (U := U) (V := V) (b := b)
    (n := b + c - 1) (by omega) (fun i hi => hspans b i hi) hrun' i hi
  exact ⟨v, by rw [← hbc]; exact hv⟩

end Bounded

end MysticetiProperties

end LeanDag
