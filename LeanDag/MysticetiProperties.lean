import LeanDag.Properties.Sustain
import LeanDag.Properties.Persist
import LeanDag.Properties.Skip
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

/-- **The core's verdicts survive an extension the grade admits.** Four
cases; the condition is consumed in exactly one of them, for exactly the
candidates the extension introduced. -/
theorem persist_aux [S : Slots Validator] (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hok : Quorate S U U' V) (hV : V.ids ⊆ V'.ids)
    {k : ℕ} {v : Option BlockId} (hd : Decided U V k v) : Decided U' V' k v := by
  induction hd with
  | @directCommit k L hL hc =>
      exact Decided.directCommit (isLeaderBlock_mono he hL) (directCommitIn_mono he hV hc)
  | @directSkip k hs =>
      refine Decided.directSkip fun L hL => ?_
      by_cases hLo : L ∈ U.ids
      · exact directSkipIn_mono he hV (hs L (isLeaderBlock_old he hLo hL))
      · exact directSkipIn_novel he hV hLo (hok k L hL hLo)
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

/-- **The core persists, at grade `Quorate`.** -/
theorem persist : Persist (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (fun S U U' V => Quorate S U U' V) :=
  fun S U U' he V V' hok hV k v hd => persist_aux (S := S) he hok hV hd

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

/-- Every member of `T` blames every candidate of the slot. -/
theorem subset_blamers {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hpres : PresentAt mysticetiRule V T (S.slotRound k + 1))
    (huns : Unsupported mysticetiRule S U V T k) {L : BlockId} (hL : IsLeaderBlock U k L) :
    T ⊆ creatorsOf U.block
      (((blocksAt U (S.slotRound k + 1)).filter fun q => L ∉ (U.block q).refs) ∩ V.ids) := by
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
  have hcU : c ∈ U.ids := V.subset_ids hcV
  refine Finset.mem_image.mpr ⟨c, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨mem_blocksAt.mpr ⟨hcU, hcr⟩, huns c hcV (by rw [hcc]; exact hv) hcr L hL⟩, hcV⟩, hcc⟩

/-- **The core skips an unsupported slot from a correct quorum.** -/
theorem skipsUnsupported :
    SkipsUnsupported (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun T => quorumCard Validator ≤ T.card) :=
  fun S U V T k hq hpres huns =>
    Decided.directSkip fun L hL =>
      le_trans hq (Finset.card_le_card (subset_blamers (S := S) hpres huns hL))

end Skip

end MysticetiProperties

end LeanDag
