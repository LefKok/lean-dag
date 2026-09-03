import LeanDag.Hydrozoan.Properties.Statement
import LeanDag.Hydrozoan.Helpers.SlotAgreement

/-!
# Hydrozoan conforms to the target properties — proof

`Causal` is HI3's argument in the shared vocabulary and is discharged in
`Helpers/Carrier.lean`. What is proved here is persistence, and the
argument has one idea in it.

**Everything an old anchor can see is old.** `Properties.Extends`
guarantees only that the extension holds every old block and denotes it
unchanged, and from that `Extends.reaches_old` derives that nothing new
enters the causal history of anything old. Every premise a Hydrozoan
derivation carries is then either monotone — the fast and slow paths
count votes and certificates a view holds, and a larger view holds more
— or is read from the anchor's history, where the extension has changed
nothing. The negative premises of the graded rungs survive for the same
reason: a new candidate cannot be certified or weak-linked from an old
anchor, because the blocks that would witness it are not in the
anchor's history.

**The direct skip is where a protocol can fail this**, and Hydrozoan
does not. A blame is a voting-round block referencing no candidate of
the slot; an extension can add candidates, but an old block's references
are unchanged and old, so it references none of them and remains a
blame. The count does not move. The core's rule quantifies over
candidates instead, and a slot skipped because it had none is not
skipped once one appears — which is why the core will need a condition
where this arc needs none.
-/

namespace LeanDag

namespace Hydrozoan

namespace Properties

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-! ## What an extension does to a block -/

/-- The three fields, read off the carrier's equation. -/
theorem ext_fields (he : Extends rule U U') {b : BlockId} (hb : b ∈ U.ids) :
    (U'.block b).round = (U.block b).round ∧
      (U'.block b).author = (U.block b).author ∧
      (U'.block b).parents = (U.block b).parents := by
  have h := he.block b hb
  simp only [rule, adaptBlock, LeanDag.Block.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem ext_round (he : Extends rule U U') {b : BlockId} (hb : b ∈ U.ids) :
    (U'.block b).round = (U.block b).round := (ext_fields he hb).1

theorem ext_author (he : Extends rule U U') {b : BlockId} (hb : b ∈ U.ids) :
    (U'.block b).author = (U.block b).author := (ext_fields he hb).2.1

theorem ext_parents (he : Extends rule U U') {b : BlockId} (hb : b ∈ U.ids) :
    (U'.block b).parents = (U.block b).parents := (ext_fields he hb).2.2

theorem ext_mem (he : Extends rule U U') {b : BlockId} (hb : b ∈ U.ids) : b ∈ U'.ids :=
  he.subset b hb

/-- A vote cast by an old block is the vote it was. -/
theorem isVote_old (he : Extends rule U U') {b L : BlockId} (hb : b ∈ U.ids) :
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
  rw [ext_parents he hb]

/-- And an old block votes for nothing the extension added. -/
theorem not_isVote_novel (he : Extends rule U U') {b L : BlockId}
    (hb : b ∈ U.ids) (hL : L ∉ U.ids) : ¬ LeanDag.Hydrozoan.IsVote U' b L := by
  rw [isVote_old he hb]
  exact fun hv => hL (U.complete b hb L hv)

/-- Reachability from an old block is unchanged, and stays old — the
carrier-level lemma read in Hydrozoan's own vocabulary. -/
theorem reaches_old (he : Extends rule U U') {A B : BlockId} (hA : A ∈ U.ids)
    (h : LeanDag.Hydrozoan.Reaches U' A B) :
    LeanDag.Hydrozoan.Reaches U A B ∧ B ∈ U.ids :=
  Extends.reaches_old causal he hA h

/-! ## The direct rules -/

theorem blocksAt_subset (he : Extends rule U U') (r : ℕ) :
    LeanDag.Hydrozoan.blocksAt U r ⊆ LeanDag.Hydrozoan.blocksAt U' r := by
  intro b hb
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hb ⊢
  exact ⟨ext_mem he hb.1, by rw [ext_round he hb.1]; exact hb.2⟩

/-- Authors of an old set are the authors they were. -/
theorem authorsOf_old (he : Extends rule U U') {s : Finset BlockId} (hs : ↑s ⊆ (U.ids : Set BlockId)) :
    LeanDag.Hydrozoan.authorsOf U'.block s = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i hi => ext_author he (hs hi)

variable [S : LeanDag.Hydrozoan.Slots Replica]

/-- A candidate of the old universe is a candidate of the extension. -/
theorem isLeaderBlock_mono (he : Extends rule U U') {k : ℕ} {L : BlockId}
    (h : LeanDag.Hydrozoan.IsLeaderBlock U k L) : LeanDag.Hydrozoan.IsLeaderBlock U' k L := by
  obtain ⟨hm, hr, ha⟩ := h
  exact ⟨ext_mem he hm, by rw [ext_round he hm]; exact hr, by rw [ext_author he hm]; exact ha⟩

/-- And an *old* candidate of the extension is one of the original. -/
theorem isLeaderBlock_old (he : Extends rule U U') {k : ℕ} {L : BlockId} (hL : L ∈ U.ids)
    (h : LeanDag.Hydrozoan.IsLeaderBlock U' k L) : LeanDag.Hydrozoan.IsLeaderBlock U k L := by
  obtain ⟨_, hr, ha⟩ := h
  rw [ext_round he hL] at hr
  rw [ext_author he hL] at ha
  exact ⟨hL, hr, ha⟩

/-! ## The counting rules are monotone

A larger view of a larger universe holds every block the smaller pair
held, and those blocks are unchanged, so every count can only rise. -/

theorem supportersInView_mono (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids) (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.supportersInView U V L r ⊆
      LeanDag.Hydrozoan.supportersInView U' V' L r := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨blocksAt_subset he r hbA, (isVote_old he hbU).mpr hbv⟩, hV hbV⟩, ?_⟩
  rw [ext_author he hbU]; exact hab

/-- The votes an old block casts are the votes it cast. -/
theorem voteBlocks_old (he : Extends rule U U') {C L : BlockId} (hC : C ∈ U.ids) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [ext_parents he hC]
  refine Finset.filter_congr fun b hb => ?_
  simpa using isVote_old he (U.complete C hC b hb)

/-- So an old certificate is still a certificate, and no old block
becomes one. -/
theorem isCertificate_old (he : Extends rule U U') {C L : BlockId} (hC : C ∈ U.ids) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [voteBlocks_old he hC, authorsOf_old he]
  intro b hb
  exact U.complete C hC b (Finset.mem_filter.mp hb).1

theorem certificates_old (he : Extends rule U U') {C L : BlockId} {r : ℕ} (hC : C ∈ U.ids) :
    C ∈ LeanDag.Hydrozoan.certificates U' L r ↔ C ∈ LeanDag.Hydrozoan.certificates U L r := by
  simp only [LeanDag.Hydrozoan.certificates, Finset.mem_filter, LeanDag.Hydrozoan.blocksAt]
  rw [ext_round he hC, isCertificate_old he hC]
  exact ⟨fun h => ⟨⟨hC, h.1.2⟩, h.2⟩, fun h => ⟨⟨ext_mem he hC, h.1.2⟩, h.2⟩⟩

theorem certifiersInView_mono (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids) (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.certifiersInView U V L r ⊆
      LeanDag.Hydrozoan.certifiersInView U' V' L r := by
  intro a ha
  obtain ⟨C, hC, haC⟩ := Finset.mem_image.mp ha
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCU : C ∈ U.ids :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).1
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨(certificates_old he hCU).mpr hCc, hV hCV⟩, ?_⟩
  rw [ext_author he hCU]; exact haC

/-- **The blame count does not move.** A blame is a voting-round block
referencing no candidate of the slot. An extension can add candidates,
but an old block's references are unchanged and old, so it references
none of them and is a blame still. This is the clause a per-candidate
skip rule cannot match. -/
theorem blamesInView_mono (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids) (k : ℕ) :
    LeanDag.Hydrozoan.blamesInView U V k ⊆ LeanDag.Hydrozoan.blamesInView U' V' k := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hblame⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨blocksAt_subset he _ hbA, ?_⟩, hV hbV⟩, ?_⟩
  · intro j hj hL
    rw [ext_parents he hbU] at hj
    exact hblame j hj (isLeaderBlock_old he (U.complete b hbU j hj) hL)
  · rw [ext_author he hbU]; exact hab

theorem fastCommitInView_mono (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ}
    (h : LeanDag.Hydrozoan.FastCommitInView U V L r) :
    LeanDag.Hydrozoan.FastCommitInView U' V' L r :=
  le_trans h (Finset.card_le_card (supportersInView_mono he hV L (r + 1)))

theorem slowCommitInView_mono (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ}
    (h : LeanDag.Hydrozoan.SlowCommitInView U V L r) :
    LeanDag.Hydrozoan.SlowCommitInView U' V' L r :=
  le_trans h (Finset.card_le_card (certifiersInView_mono he hV L r))

theorem skippedLeaderInView_mono (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids) {k : ℕ}
    (h : LeanDag.Hydrozoan.SkippedLeaderInView U V k) :
    LeanDag.Hydrozoan.SkippedLeaderInView U' V' k :=
  le_trans h (Finset.card_le_card (blamesInView_mono he hV k))

/-! ## The rung tests, at an old anchor

Every rung asks what is in reach of the anchor, and a derivation over
the old universe has an old anchor — so the extension has changed
nothing the rungs read, in either direction. -/

theorem certifiedIn_old (he : Extends rule U U') {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.CertifiedIn U' A L r ↔ LeanDag.Hydrozoan.CertifiedIn U A L r := by
  constructor
  · rintro ⟨C, hC, hreach⟩
    obtain ⟨hreachU, hCU⟩ := reaches_old he hA hreach
    exact ⟨C, (certificates_old he hCU).mp hC, hreachU⟩
  · rintro ⟨C, hC, hreach⟩
    have hCU : C ∈ U.ids := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1
    exact ⟨C, (certificates_old he hCU).mpr hC, (Extends.reaches_iff causal he hA).mpr hreach⟩

theorem weakLinked_old (he : Extends rule U U') {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.WeakLinked U' A L r ↔ LeanDag.Hydrozoan.WeakLinked U A L r := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U.ids := fun b hb => (reaches_old he hA (hs b hb).2.2).2
    refine ⟨s, fun b hb => ?_, ?_⟩
    · obtain ⟨hbA, hbv, hbr⟩ := hs b hb
      have hbU := hsU b hb
      refine ⟨?_, (isVote_old he hbU).mp hbv, (reaches_old he hA hbr).1⟩
      simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hbA ⊢
      exact ⟨hbU, by rw [← ext_round he hbU]; exact hbA.2⟩
    · rwa [authorsOf_old he (by intro b hb; exact hsU b hb)] at hcard
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U.ids := fun b hb =>
      (Finset.mem_filter.mp (hs b hb).1).1
    refine ⟨s, fun b hb => ?_, ?_⟩
    · obtain ⟨hbA, hbv, hbr⟩ := hs b hb
      have hbU := hsU b hb
      refine ⟨blocksAt_subset he _ hbA, (isVote_old he hbU).mpr hbv,
        (Extends.reaches_iff causal he hA).mpr hbr⟩
    · rwa [authorsOf_old he (by intro b hb; exact hsU b hb)]

/-- **A new candidate is certified by nothing an old anchor can see.**
A certificate for it would have to reference it, and an old block's
references are old. -/
theorem not_certifiedIn_novel (he : Extends rule U U') {A L : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) (hL : L ∉ U.ids) : ¬ LeanDag.Hydrozoan.CertifiedIn U' A L r := by
  rintro ⟨C, hC, hreach⟩
  obtain ⟨_, hCU⟩ := reaches_old he hA hreach
  have hcert := (isCertificate_old he hCU).mp (Finset.mem_filter.mp hC).2
  have hempty : LeanDag.Hydrozoan.voteBlocks U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    exact hL (U.complete b (U.complete C hCU b hbp) L hbv)
  unfold LeanDag.Hydrozoan.IsCertificate at hcert
  rw [hempty] at hcert
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcert
  exact absurd hcert (by unfold LeanDag.Hydrozoan.qCert; omega)

/-- And weak-linked by nothing either, for the same reason. -/
theorem not_weakLinked_novel (he : Extends rule U U') {A L : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) (hL : L ∉ U.ids) : ¬ LeanDag.Hydrozoan.WeakLinked U' A L r := by
  rintro ⟨s, hs, hcard⟩
  have hempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨_, hbv, hbr⟩ := hs b hb
    exact not_isVote_novel he (reaches_old he hA hbr).2 hL hbv
  rw [hempty] at hcard
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcard
  exact absurd hcard (by unfold LeanDag.Hydrozoan.qWeak; omega)

/-! ## Persistence -/

/-- **Hydrozoan's verdicts survive every extension.** The induction, six
cases, each a transfer lemma above applied. -/
theorem persist_aux (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids)
    {k : ℕ} {v : Option BlockId} (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided U' V' k v := by
  induction h with
  | @directFast k L hL hc =>
      exact LeanDag.Hydrozoan.Decided.directFast (isLeaderBlock_mono he hL)
        (fastCommitInView_mono he hV hc)
  | @directSlow k L hL hc =>
      exact LeanDag.Hydrozoan.Decided.directSlow (isLeaderBlock_mono he hL)
        (slowCommitInView_mono he hV hc)
  | @directSkip k hs =>
      exact LeanDag.Hydrozoan.Decided.directSkip (skippedLeaderInView_mono he hV hs)
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      have hA : A ∈ U.ids := (LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor).1
      exact LeanDag.Hydrozoan.Decided.indirectCert hkj helig ihj
        (fun i h1 h2 he' => ihmid i h1 h2 he') (isLeaderBlock_mono he hL)
        ((certifiedIn_old he hA).mpr hcert)
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      have hA : A ∈ U.ids := (LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak hkj helig ihj
        (fun i h1 h2 he' => ihmid i h1 h2 he') ?_ (isLeaderBlock_mono he hL)
        ((weakLinked_old he hA).mpr hweak) ?_
      · intro L' hL' hc
        by_cases hL'o : L' ∈ U.ids
        · exact hnocert L' (isLeaderBlock_old he hL'o hL') ((certifiedIn_old he hA).mp hc)
        · exact not_certifiedIn_novel he hA hL'o hc
      · intro L' hL' hw
        by_cases hL'o : L' ∈ U.ids
        · exact hmin L' (isLeaderBlock_old he hL'o hL') ((weakLinked_old he hA).mp hw)
        · exact absurd hw (not_weakLinked_novel he hA hL'o)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      have hA : A ∈ U.ids := (LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip hkj helig ihj
        (fun i h1 h2 he' => ihmid i h1 h2 he') ?_ ?_
      · intro L' hL' hc
        by_cases hL'o : L' ∈ U.ids
        · exact hnocert L' (isLeaderBlock_old he hL'o hL') ((certifiedIn_old he hA).mp hc)
        · exact not_certifiedIn_novel he hA hL'o hc
      · intro L' hL' hw
        by_cases hL'o : L' ∈ U.ids
        · exact hnoweak L' (isLeaderBlock_old he hL'o hL') ((weakLinked_old he hA).mp hw)
        · exact absurd hw (not_weakLinked_novel he hA hL'o)

/-- **HZ9.** -/
theorem holds : Statement := by
  intro Replica _ _ BlockId _ _ _
  refine ⟨causal, ?_⟩
  intro S U U' he _ V V' hV k v h
  exact persist_aux (S := ofCoreSlots S) he hV h

end Properties

end Hydrozoan

end LeanDag
