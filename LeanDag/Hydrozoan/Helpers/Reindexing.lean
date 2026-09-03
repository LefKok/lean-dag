import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Properties.Reindex

/-!
# Hydrozoan's rules commute with a renumbering

Not part of the audit surface. The transfer lemmas
`Properties.Reindex` needs of this protocol.

A renumbering removes nothing and adds nothing: the same blocks, the
same authors, the same references, with every round lower by `G` and
every slot lower by `d`. So each lemma below is an **equality** rather
than an inclusion, and the whole file is arithmetic — every predicate
Hydrozoan reads names a round, and each of those rounds moves by `G`
exactly once.

The one place to be careful is the anchor. A derivation at slot `d + k`
anchors at a slot strictly above it, which is therefore also at or above
`d`, so it too has a name under the new numbering. That is why the
induction is stated over an arbitrary slot with the correspondence
threaded as an equation, rather than over `d + k` directly.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {S S' : LeanDag.Hydrozoan.Slots Replica} {G d : ℕ}

/-- The shift, in Hydrozoan's vocabulary. `Shifted` is stated over the
carrier, whose `Slots` is the core's; these are the same records. -/
structure ShiftedHZ (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (S S' : LeanDag.Hydrozoan.Slots Replica) (G d : ℕ) : Prop where
  mem : ∀ b, b ∈ U.ids ↔ b ∈ U'.ids
  round : ∀ b, b ∈ U.ids → (U'.block b).round + G = (U.block b).round
  author : ∀ b, b ∈ U.ids → (U'.block b).author = (U.block b).author
  parents : ∀ b, b ∈ U.ids → (U'.block b).parents = (U.block b).parents
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  leader : ∀ k, S'.leader k = S.leader (d + k)

namespace ShiftedHZ

theorem blocksAt_eq (h : ShiftedHZ U U' S S' G d) (n : ℕ) :
    LeanDag.Hydrozoan.blocksAt U' n = LeanDag.Hydrozoan.blocksAt U (n + G) := by
  ext b
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hbr⟩
    have hbU := (h.mem b).mpr hb
    exact ⟨hbU, by have := h.round b hbU; omega⟩
  · rintro ⟨hb, hbr⟩
    exact ⟨(h.mem b).mp hb, by have := h.round b hb; omega⟩

theorem isVote_eq (h : ShiftedHZ U U' S S' G d) {b L : BlockId} (hb : b ∈ U.ids) :
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote; rw [h.parents b hb]

theorem authorsOf_eq (h : ShiftedHZ U U' S S' G d) {s : Finset BlockId} (hs : ∀ b ∈ s, b ∈ U.ids) :
    LeanDag.Hydrozoan.authorsOf U'.block s = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i hi => h.author i (hs i hi)

theorem reaches_eq (h : ShiftedHZ U U' S S' G d) {A C : BlockId} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.Reaches U' A C ↔ LeanDag.Hydrozoan.Reaches U A C := by
  constructor
  · intro hre
    induction hre with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hAb hstep ih =>
        have hb : b ∈ U.ids := (causal U).mem_ids_of_reaches hA ih
        refine ih.tail ?_
        have hstep' : c ∈ (U'.block b).parents := hstep
        rw [h.parents b hb] at hstep'
        exact hstep'
  · intro hre
    induction hre with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hAb hstep ih =>
        have hb : b ∈ U.ids := (causal U).mem_ids_of_reaches hA hAb
        refine ih.tail ?_
        have hstep' : c ∈ (U.block b).parents := hstep
        show c ∈ (U'.block b).parents
        rw [h.parents b hb]; exact hstep'

theorem voteBlocks_eq (h : ShiftedHZ U U' S S' G d) {C L : BlockId} (hC : C ∈ U.ids) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [h.parents C hC]
  exact Finset.filter_congr fun b hb => by simpa using h.isVote_eq (U.complete C hC b hb)

theorem isCertificate_eq (h : ShiftedHZ U U' S S' G d) {C L : BlockId} (hC : C ∈ U.ids) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [h.voteBlocks_eq hC, h.authorsOf_eq]
  intro b hb
  exact U.complete C hC b (Finset.mem_filter.mp hb).1

theorem certificates_eq (h : ShiftedHZ U U' S S' G d) {L : BlockId} (n : ℕ) :
    LeanDag.Hydrozoan.certificates U' L n = LeanDag.Hydrozoan.certificates U L (n + G) := by
  unfold LeanDag.Hydrozoan.certificates
  have hb : n + 2 + G = n + G + 2 := by omega
  rw [h.blocksAt_eq (n + 2), hb]
  refine Finset.filter_congr fun C hC => ?_
  simpa using h.isCertificate_eq (Finset.mem_filter.mp hC).1

theorem certifiedIn_eq (h : ShiftedHZ U U' S S' G d) {A L : BlockId} {n : ℕ} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.CertifiedIn U' A L n ↔ LeanDag.Hydrozoan.CertifiedIn U A L (n + G) := by
  unfold LeanDag.Hydrozoan.CertifiedIn
  rw [h.certificates_eq n]
  exact ⟨fun ⟨C, hC, hre⟩ => ⟨C, hC, (h.reaches_eq hA).mp hre⟩,
    fun ⟨C, hC, hre⟩ => ⟨C, hC, (h.reaches_eq hA).mpr hre⟩⟩

theorem weakLinked_eq (h : ShiftedHZ U U' S S' G d) {A L : BlockId} {n : ℕ} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.WeakLinked U' A L n ↔ LeanDag.Hydrozoan.WeakLinked U A L (n + G) := by
  unfold LeanDag.Hydrozoan.WeakLinked
  have hb : n + 1 + G = n + G + 1 := by omega
  constructor
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U.ids := fun b hb' => by
      have := (hs b hb').1; rw [h.blocksAt_eq] at this
      exact (Finset.mem_filter.mp this).1
    refine ⟨s, fun b hb' => ?_, by rwa [h.authorsOf_eq hsU] at hcard⟩
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb'
    rw [h.blocksAt_eq, hb] at hbA
    exact ⟨hbA, (h.isVote_eq (hsU b hb')).mp hbv, (h.reaches_eq hA).mp hbre⟩
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U.ids := fun b hb' =>
      (Finset.mem_filter.mp (hs b hb').1).1
    refine ⟨s, fun b hb' => ?_, by rw [h.authorsOf_eq hsU]; exact hcard⟩
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb'
    refine ⟨by rw [h.blocksAt_eq, hb]; exact hbA,
      (h.isVote_eq (hsU b hb')).mpr hbv, (h.reaches_eq hA).mpr hbre⟩

theorem isLeaderBlock_eq (h : ShiftedHZ U U' S S' G d) {k : ℕ} {L : BlockId} :
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S' U' k L
      ↔ @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U (d + k) L := by
  constructor
  · rintro ⟨hm, hr, ha⟩
    have hU := (h.mem L).mpr hm
    refine ⟨hU, ?_, ?_⟩
    · have := h.round L hU; have := h.slotRound k; omega
    · rw [← h.author L hU, ha, h.leader k]
  · rintro ⟨hm, hr, ha⟩
    refine ⟨(h.mem L).mp hm, ?_, ?_⟩
    · have := h.round L hm; have := h.slotRound k; omega
    · rw [h.author L hm, ha, ← h.leader k]

theorem eligible_eq (h : ShiftedHZ U U' S S' G d) {k j : ℕ} :
    @LeanDag.Hydrozoan.EligibleAsAnchor Replica S' k j
      ↔ @LeanDag.Hydrozoan.EligibleAsAnchor Replica S (d + k) (d + j) := by
  unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound
  have hk := h.slotRound k
  have hj := h.slotRound j
  omega

/-! ## The view-level counts -/

theorem supportersInView_eq (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) (L : BlockId) (m : ℕ) :
    LeanDag.Hydrozoan.supportersInView U' V' L m
      = LeanDag.Hydrozoan.supportersInView U V L (m + G) := by
  unfold LeanDag.Hydrozoan.supportersInView
  have hset : ((LeanDag.Hydrozoan.blocksAt U' m).filter
        fun b => LeanDag.Hydrozoan.IsVote U' b L) ∩ V'.ids
      = ((LeanDag.Hydrozoan.blocksAt U (m + G)).filter
        fun b => LeanDag.Hydrozoan.IsVote U b L) ∩ V.ids := by
    rw [h.blocksAt_eq, ← hv]
    congr 1
    refine Finset.filter_congr fun b hb => ?_
    simpa using h.isVote_eq (Finset.mem_filter.mp hb).1
  rw [hset]
  refine h.authorsOf_eq ?_
  intro b hb
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).1).1

theorem certifiersInView_eq (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) (L : BlockId) (m : ℕ) :
    LeanDag.Hydrozoan.certifiersInView U' V' L m
      = LeanDag.Hydrozoan.certifiersInView U V L (m + G) := by
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
  rw [h.certificates_eq, ← hv]
  refine h.authorsOf_eq ?_
  intro b hb
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).1).1

theorem blamesInView_eq (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) (k : ℕ) :
    @LeanDag.Hydrozoan.blamesInView _ _ _ _ _ _ S' U' V' k
      = @LeanDag.Hydrozoan.blamesInView _ _ _ _ _ _ S U V (d + k) := by
  have hvr : LeanDag.Hydrozoan.votingRound Replica (S := S') k + G
      = LeanDag.Hydrozoan.votingRound Replica (S := S) (d + k) := by
    unfold LeanDag.Hydrozoan.votingRound; have := h.slotRound k; omega
  ext a
  simp only [LeanDag.Hydrozoan.blamesInView, LeanDag.Hydrozoan.authorsOf,
    Finset.mem_image, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨b, ⟨⟨hbA, hbl⟩, hbV⟩, rfl⟩
    rw [h.blocksAt_eq, hvr] at hbA
    have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
    refine ⟨b, ⟨⟨hbA, ?_⟩, ?_⟩, (h.author b hbU).symm⟩
    · intro j hj hL
      rw [← h.parents b hbU] at hj
      exact hbl j hj (h.isLeaderBlock_eq.mpr hL)
    · rw [hv]; exact hbV
  · rintro ⟨b, ⟨⟨hbA, hbl⟩, hbV⟩, rfl⟩
    have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
    refine ⟨b, ⟨⟨?_, ?_⟩, ?_⟩, h.author b hbU⟩
    · rw [h.blocksAt_eq, hvr]; exact hbA
    · intro j hj hL
      rw [h.parents b hbU] at hj
      exact hbl j hj (h.isLeaderBlock_eq.mp hL)
    · rw [← hv]; exact hbV

theorem fastCommitInView_eq (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) (L : BlockId) (k : ℕ) :
    LeanDag.Hydrozoan.FastCommitInView U' V' L (S'.slotRound k)
      ↔ LeanDag.Hydrozoan.FastCommitInView U V L (S.slotRound (d + k)) := by
  unfold LeanDag.Hydrozoan.FastCommitInView
  rw [h.supportersInView_eq hv]
  have := h.slotRound k
  have harg : S'.slotRound k + 1 + G = S.slotRound (d + k) + 1 := by omega
  rw [harg]

theorem slowCommitInView_eq (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) (L : BlockId) (k : ℕ) :
    LeanDag.Hydrozoan.SlowCommitInView U' V' L (S'.slotRound k)
      ↔ LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound (d + k)) := by
  unfold LeanDag.Hydrozoan.SlowCommitInView
  rw [h.certifiersInView_eq hv, h.slotRound k]

theorem skippedLeaderInView_eq (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) (k : ℕ) :
    @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S' U' V' k
      ↔ @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S U V (d + k) := by
  simp [LeanDag.Hydrozoan.SkippedLeaderInView, h.blamesInView_eq hv]

/-! ## Re-indexing

The slot is threaded as an equation rather than substituted, so the
induction can move through anchors: an anchor of a derivation at
`d + k` sits above it, hence also at or above `d`, and so has a name
under the new numbering. -/

theorem reindex_aux (h : ShiftedHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : V.ids = V'.ids) {n : ℕ} {v : Option BlockId}
    (hd : @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S U V n v) :
    ∀ k, n = d + k → @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S' U' V' k v := by
  induction hd with
  | @directFast n L hL hc =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directFast (S := S') (h.isLeaderBlock_eq.mpr hL)
        ((h.fastCommitInView_eq hv L k).mpr hc)
  | @directSlow n L hL hc =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directSlow (S := S') (h.isLeaderBlock_eq.mpr hL)
        ((h.slowCommitInView_eq hv L k).mpr hc)
  | @directSkip n hs =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directSkip (S := S')
        ((h.skippedLeaderInView_eq hv k).mpr hs)
  | @indirectCert n j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hanchor
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := S') (by omega)
        (h.eligible_eq.mpr helig) (ihj j' rfl) ?_ (h.isLeaderBlock_eq.mpr hL)
        ((h.certifiedIn_eq hA.1).mpr (by rw [← h.slotRound k] at hcert; exact hcert))
      intro i' h1 h2 he
      exact ihmid (d + i') (by omega) (by omega) (h.eligible_eq.mp he) i' rfl
  | @indirectWeak n j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hanchor
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') (by omega)
        (h.eligible_eq.mpr helig) (ihj j' rfl) ?_ ?_ (h.isLeaderBlock_eq.mpr hL)
        ((h.weakLinked_eq hA.1).mpr (by rw [← h.slotRound k] at hweak; exact hweak)) ?_
      · intro i' h1 h2 he
        exact ihmid (d + i') (by omega) (by omega) (h.eligible_eq.mp he) i' rfl
      · intro L' hL' hc
        refine hnocert L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]
        exact (h.certifiedIn_eq hA.1).mp hc
      · intro L' hL' hw
        refine hmin L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]
        exact (h.weakLinked_eq hA.1).mp hw
  | @indirectSkip n j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hanchor
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') (by omega)
        (h.eligible_eq.mpr helig) (ihj j' rfl) ?_ ?_ ?_
      · intro i' h1 h2 he
        exact ihmid (d + i') (by omega) (by omega) (h.eligible_eq.mp he) i' rfl
      · intro L' hL' hc
        refine hnocert L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]
        exact (h.certifiedIn_eq hA.1).mp hc
      · intro L' hL' hw
        refine hnoweak L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]
        exact (h.weakLinked_eq hA.1).mp hw

end ShiftedHZ

end Hydrozoan

end LeanDag
