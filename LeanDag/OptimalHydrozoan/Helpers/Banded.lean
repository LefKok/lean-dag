import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.OptimalHydrozoan.Helpers.SlotAgreement

/-!
# Optimal-Hydrozoan's rules read a band of rounds

Not part of the audit surface. What `Properties.Banded` needs of this
protocol, on top of Hydrozoan's band file: Optimal shares Hydrozoan's
blocks, votes, certificates and blames, so `Hydrozoan/Helpers/Banded.lean`
carries the whole direct layer and rung 1 unchanged, and what is left is
the fast path — fast evidence, the no-evidence quorum, and the anchored
evidence rung.

**Every new rule is a count over one block's parents**, which is what
makes them transportable. `IsFastEvidence U k C L` reads `C`'s parents
and the votes they cast, so a band two rounds above the floor fixes it
exactly, for *every* candidate whatever — old ones because references
are unchanged, and ones the band added because an old block's parents
reference only old blocks, so a new candidate collects no votes at all.

**That is what saves the skip.** `IsNoFastEvidence` quantifies over the
slot's candidates and denies evidence for each, and a band may add a
candidate — the shape §3.2 recorded as a defect in the core and §3.12 in
Odontoceti. Here the added candidate has an empty vote count and both
`tPlain` and `tEquiv` are at least one, so no old block is evidence for
it and the quorum survives. The same argument disposes of the two
negative clauses of the graded rungs.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan
open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [O : OptimalFaults Replica]
variable [S : LeanDag.Hydrozoan.Slots Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {lo hi g g' : ℕ}

/-! ## The votes a decision-round block references -/

/-- **A block's parents vote the same way in both universes**, for every
candidate whatever. Two rounds of slack, as for a certificate: the count
reads the parents' own parents. -/
theorem votesFor_bnd (h : AgreeBand rule U U' lo hi g g') {C : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) (L : BlockId) :
    votesFor U' C L = votesFor U C L := by
  unfold votesFor
  rw [voteBlocks_bnd h hC h1 h2, authorsOf_bnd h]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  have := (U.valid C hC).predecessor b hbp
  exact ⟨U.complete C hC b hbp, by omega, by omega⟩

/-- **And a candidate the band added collects none.** An old block's
parents are old and reference only old blocks. -/
theorem votesFor_eq_empty_of_novel (h : AgreeBand rule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) (hL : L ∉ U.ids) :
    votesFor U' C L = ∅ := by
  rw [votesFor_bnd h hC h1 h2]
  have hempty : voteBlocks U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    exact hL (U.complete b (U.complete C hC b hbp) L hbv)
  unfold votesFor
  rw [hempty]
  simp [LeanDag.Hydrozoan.authorsOf]

/-- **Witnessing an equivocation is the same event.** Both directions: a
witness on the larger side is voted for by an old parent, so it is a
candidate the band already had. -/
theorem witnessesEquivocation_bnd (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (hk1 : lo ≤ S.slotRound k + g) (hk2 : S.slotRound k + g ≤ hi)
    {C : BlockId} (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    WitnessesEquivocation (S := S') U' k' C ↔ WitnessesEquivocation (S := S) U k C := by
  have hpar : (U'.block C).parents = (U.block C).parents := bnd_parents h hC (by omega) h2
  have hold : ∀ j ∈ (U.block C).parents,
      j ∈ U.ids ∧ (U.block j).round + 1 = (U.block C).round :=
    fun j hj => ⟨U.complete C hC j hj, (U.valid C hC).predecessor j hj⟩
  constructor
  · rintro ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    rw [hpar] at hj₁ hj₂
    obtain ⟨hj₁U, hj₁r⟩ := hold j₁ hj₁
    obtain ⟨hj₂U, hj₂r⟩ := hold j₂ hj₂
    have hv₁U : IsVote U j₁ L₁ := (isVote_bnd h hj₁U (by omega) (by omega)).mp hv₁
    have hv₂U : IsVote U j₂ L₂ := (isVote_bnd h hj₂U (by omega) (by omega)).mp hv₂
    exact ⟨L₁, L₂,
      isLeaderBlock_bnd_old h hkk hlead hk1 hk2 (U.complete j₁ hj₁U L₁ hv₁U) hL₁,
      isLeaderBlock_bnd_old h hkk hlead hk1 hk2 (U.complete j₂ hj₂U L₂ hv₂U) hL₂,
      hne, ⟨j₁, hj₁, hv₁U⟩, ⟨j₂, hj₂, hv₂U⟩⟩
  · rintro ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    obtain ⟨hj₁U, hj₁r⟩ := hold j₁ hj₁
    obtain ⟨hj₂U, hj₂r⟩ := hold j₂ hj₂
    exact ⟨L₁, L₂, isLeaderBlock_bnd h hkk hlead hk1 hk2 hL₁,
      isLeaderBlock_bnd h hkk hlead hk1 hk2 hL₂, hne,
      ⟨j₁, by rw [hpar]; exact hj₁, (isVote_bnd h hj₁U (by omega) (by omega)).mpr hv₁⟩,
      ⟨j₂, by rw [hpar]; exact hj₂,
        (isVote_bnd h hj₂U (by omega) (by omega)).mpr hv₂⟩⟩

/-- **Fast evidence is the same evidence.** The counts are equal, the
equivocation test is the same test, and the rival clause survives the
band's new candidates because they collect no votes and `t_equiv` is at
least one. -/
theorem isFastEvidence_bnd (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (hk1 : lo ≤ S.slotRound k + g) (hk2 : S.slotRound k + g ≤ hi)
    {C : BlockId} (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) (L : BlockId) :
    IsFastEvidence (S := S') U' k' C L ↔ IsFastEvidence (S := S) U k C L := by
  have htE : 1 ≤ tEquiv Replica := by
    unfold tEquiv pOpt; omega
  have hwit := witnessesEquivocation_bnd h hkk hlead hk1 hk2 hC h1 h2
  unfold IsFastEvidence
  constructor
  · rintro ⟨hp, he⟩
    refine ⟨fun hnw => ?_, fun hw => ?_⟩
    · rw [← votesFor_bnd h hC h1 h2]
      exact hp (fun hx => hnw (hwit.mp hx))
    · obtain ⟨hc, hriv⟩ := he (hwit.mpr hw)
      refine ⟨by rw [← votesFor_bnd h hC h1 h2]; exact hc, fun L' hL' hne => ?_⟩
      rw [← votesFor_bnd h hC h1 h2]
      exact hriv L' (isLeaderBlock_bnd h hkk hlead hk1 hk2 hL') hne
  · rintro ⟨hp, he⟩
    refine ⟨fun hnw => ?_, fun hw => ?_⟩
    · rw [votesFor_bnd h hC h1 h2]
      exact hp (fun hx => hnw (hwit.mpr hx))
    · obtain ⟨hc, hriv⟩ := he (hwit.mp hw)
      refine ⟨by rw [votesFor_bnd h hC h1 h2]; exact hc, fun L' hL' hne => ?_⟩
      by_cases hLo : L' ∈ U.ids
      · rw [votesFor_bnd h hC h1 h2]
        exact hriv L' (isLeaderBlock_bnd_old h hkk hlead hk1 hk2 hLo hL') hne
      · rw [votesFor_eq_empty_of_novel h hC h1 h2 hLo]
        simp only [Finset.card_empty]
        omega

/-- **A block that was evidence for no candidate still is.** The old
candidates by the equivalence above, and a candidate the band added
because it collects no votes and both thresholds are at least one. -/
theorem isNoFastEvidence_bnd (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (hk1 : lo ≤ S.slotRound k + g) (hk2 : S.slotRound k + g ≤ hi)
    {C : BlockId} (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi)
    (hne : IsNoFastEvidence (S := S) U k C) : IsNoFastEvidence (S := S') U' k' C := by
  intro L hL hfe
  by_cases hLo : L ∈ U.ids
  · exact hne L (isLeaderBlock_bnd_old h hkk hlead hk1 hk2 hLo hL)
      ((isFastEvidence_bnd h hkk hlead hk1 hk2 hC h1 h2 L).mp hfe)
  · have hempty := votesFor_eq_empty_of_novel h hC h1 h2 hLo
    obtain ⟨hp, hq⟩ := hfe
    by_cases hw : WitnessesEquivocation (S := S') U' k' C
    · have htE : 1 ≤ tEquiv Replica := by unfold tEquiv pOpt; omega
      have := (hq hw).1
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega
    · have htP := tPlain_pos (Replica := Replica)
      have := hp hw
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega

/-! ## The direct rules of the fast path -/

/-- The fast commit is Hydrozoan's vote count at a lower threshold, so
Hydrozoan's containment carries it. -/
theorem fastCommitOptInView_bnd (h : AgreeBand rule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo ≤ n + g)
    (h2 : n + 1 + g ≤ hi) (hc : FastCommitOptInView U V L n) :
    FastCommitOptInView U' V' L n' :=
  le_trans hc (Finset.card_le_card
    (supportersInView_bnd h hv (n := n + 1) (n' := n' + 1) (by omega) (by omega) (by omega)))

/-- **The no-evidence quorum is carried across.** Each block of it stays
at the decision round, stays in view, and stays evidence for no
candidate — the last by `isNoFastEvidence_bnd`, which is where a
candidate the band added is disposed of. -/
theorem noEvidenceQuorumInView_bnd (h : AgreeBand rule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    (hq : NoEvidenceQuorumInView (S := S) U V k) :
    NoEvidenceQuorumInView (S := S') U' V' k' := by
  have hdr : LeanDag.Hydrozoan.decisionRound (S := S) Replica k = S.slotRound k + 2 := rfl
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := hq
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = S.slotRound k + 2 := by
    intro b hb
    obtain ⟨hbA, -, -⟩ := hs b hb
    exact ⟨(Finset.mem_filter.mp hbA).1, (Finset.mem_filter.mp hbA).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbV, hbn⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    exact ⟨blocksAt_bnd h (n := LeanDag.Hydrozoan.decisionRound (S := S) Replica k)
        (n' := LeanDag.Hydrozoan.decisionRound (S := S') Replica k')
        (by omega) (by omega) (by omega) hbA,
      hv b hbV (by omega) (by omega),
      isNoFastEvidence_bnd h hkk hlead h1 (by omega) hbU (by omega) (by omega) hbn⟩
  · rw [authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

/-- **And so is the direct skip.** Blames by Hydrozoan's containment, the
no-evidence half by the one above. -/
theorem skippedLeaderOptInView_bnd (h : AgreeBand rule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    (hs : SkippedLeaderOptInView (S := S) U V k) :
    SkippedLeaderOptInView (S := S') U' V' k' :=
  ⟨le_trans hs.1 (Finset.card_le_card
      (blamesInView_bnd h hv hkk hlead h1 (by omega))),
    noEvidenceQuorumInView_bnd h hv hkk hlead h1 h2 hs.2⟩

/-! ## The anchored evidence rung

Three parts, as for Hydrozoan's two anchored tests: forward, back for a
candidate the band already had, and — the clause a one-directional band
forces — that a candidate the band did not carry passes the test on
neither side, because the anchor's cone never leaves the blocks the band
had and an old block's parents vote only for old blocks. -/

theorem evidenceLinked_bnd (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    {A L : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    (he : EvidenceLinked (S := S) U A L k) : EvidenceLinked (S := S') U' A L k' := by
  have hdr : LeanDag.Hydrozoan.decisionRound (S := S) Replica k = S.slotRound k + 2 := rfl
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := he
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = S.slotRound k + 2 := by
    intro b hb
    obtain ⟨hbA, -, -⟩ := hs b hb
    exact ⟨(Finset.mem_filter.mp hbA).1, (Finset.mem_filter.mp hbA).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (rule.block U b).round = (U.block b).round := rfl
    exact ⟨blocksAt_bnd h (n := LeanDag.Hydrozoan.decisionRound (S := S) Replica k)
        (n' := LeanDag.Hydrozoan.decisionRound (S := S') Replica k')
        (by omega) (by omega) (by omega) hbA,
      (isFastEvidence_bnd h hkk hlead h1 (by omega) hbU (by omega) (by omega) L).mpr hbe,
      AgreeBand.reaches_of causal h hA hAhi hbre (by omega)⟩
  · rw [authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem evidenceLinked_bnd_old (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    {A L : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    (he : EvidenceLinked (S := S') U' A L k') : EvidenceLinked (S := S) U A L k := by
  have hdr : LeanDag.Hydrozoan.decisionRound (S := S) Replica k = S.slotRound k + 2 := rfl
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := he
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = S.slotRound k + 2 := by
    intro b hb
    obtain ⟨hbA, -, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = S'.slotRound k' + 2 := (Finset.mem_filter.mp hbA).2
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hbre (by omega)
    have hbe : (U.block b).round + g = (U'.block b).round + g' := hbeq
    exact ⟨hbU, by omega⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    have hbr'' : (U'.block b).round = S'.slotRound k' + 2 := (Finset.mem_filter.mp hbA).2
    obtain ⟨-, hbreU, -⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hbre (by omega)
    exact ⟨Finset.mem_filter.mpr ⟨hbU, by omega⟩,
      (isFastEvidence_bnd h hkk hlead h1 (by omega) hbU (by omega) (by omega) L).mp hbe,
      hbreU⟩
  · rw [← authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem not_evidenceLinked_bnd_novel (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    {A L : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ EvidenceLinked (S := S') U' A L k' := by
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  have htE : 1 ≤ tEquiv Replica := by unfold tEquiv pOpt; omega
  have htP := tPlain_pos (Replica := Replica)
  rintro ⟨s, hs, hcard⟩
  have hsempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = S'.slotRound k' + 2 := (Finset.mem_filter.mp hbA).2
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hbre (by omega)
    have hbe' : (U.block b).round + g = (U'.block b).round + g' := hbeq
    have hbr : (U.block b).round = S.slotRound k + 2 := by omega
    have hempty := votesFor_eq_empty_of_novel h hbU (by omega) (by omega) hL
    obtain ⟨hp, hq⟩ := hbe
    by_cases hw : WitnessesEquivocation (S := S') U' k' b
    · have := (hq hw).1
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega
    · have := hp hw
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega
  rw [hsempty] at hcard
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcard
  have : 0 < LeanDag.Hydrozoan.qCert Replica := by
    unfold LeanDag.Hydrozoan.qCert; omega
  omega

/-! ## Reading the schedule at one slot

The fast path's rules consult the leaders only at the slot being
decided, so two schedules naming the same round and leader there agree
on them. This is the tightness `Properties.Indirect` and
`Properties.DecidedBelow` ask for. -/

omit S [LinearOrder BlockId] in
theorem witnessesEquivocation_sched {S₁ S₂ : LeanDag.Hydrozoan.Slots Replica} {k : ℕ}
    {b : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    WitnessesEquivocation (S := S₁) U k b ↔ WitnessesEquivocation (S := S₂) U k b := by
  unfold WitnessesEquivocation
  constructor <;> rintro ⟨L₁, L₂, hL₁, hL₂, hne, hv₁, hv₂⟩
  · exact ⟨L₁, L₂, LeanDag.Hydrozoan.isLeaderBlock_sched hround hk hL₁,
      LeanDag.Hydrozoan.isLeaderBlock_sched hround hk hL₂, hne, hv₁, hv₂⟩
  · exact ⟨L₁, L₂, LeanDag.Hydrozoan.isLeaderBlock_sched hround.symm hk.symm hL₁,
      LeanDag.Hydrozoan.isLeaderBlock_sched hround.symm hk.symm hL₂, hne, hv₁, hv₂⟩

omit S [LinearOrder BlockId] in
theorem isFastEvidence_sched {S₁ S₂ : LeanDag.Hydrozoan.Slots Replica} {k : ℕ}
    {C L : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    IsFastEvidence (S := S₁) U k C L ↔ IsFastEvidence (S := S₂) U k C L := by
  have hw := witnessesEquivocation_sched (U := U) (b := C) hround hk
  unfold IsFastEvidence
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨fun hnw => hp (fun hx => hnw (hw.mp hx)), fun hx => ?_⟩
    obtain ⟨hc, hriv⟩ := hq (hw.mpr hx)
    exact ⟨hc, fun L' hL' hne =>
      hriv L' (LeanDag.Hydrozoan.isLeaderBlock_sched hround.symm hk.symm hL') hne⟩
  · rintro ⟨hp, hq⟩
    refine ⟨fun hnw => hp (fun hx => hnw (hw.mpr hx)), fun hx => ?_⟩
    obtain ⟨hc, hriv⟩ := hq (hw.mp hx)
    exact ⟨hc, fun L' hL' hne =>
      hriv L' (LeanDag.Hydrozoan.isLeaderBlock_sched hround hk hL') hne⟩

omit S [LinearOrder BlockId] in
theorem evidenceLinked_sched {S₁ S₂ : LeanDag.Hydrozoan.Slots Replica} {k : ℕ}
    {A L : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    EvidenceLinked (S := S₁) U A L k ↔ EvidenceLinked (S := S₂) U A L k := by
  have hdr₁ : LeanDag.Hydrozoan.decisionRound (S := S₁) Replica k = S₁.slotRound k + 2 := rfl
  have hdr₂ : LeanDag.Hydrozoan.decisionRound (S := S₂) Replica k = S₂.slotRound k + 2 := rfl
  have hfe := fun C : BlockId => isFastEvidence_sched (U := U) (C := C) (L := L) hround hk
  unfold EvidenceLinked
  constructor <;> rintro ⟨s, hs, hcard⟩ <;> refine ⟨s, fun b hb => ?_, hcard⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    have hbr : (U.block b).round = S₁.slotRound k + 2 := (Finset.mem_filter.mp hbA).2
    exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbA).1, by omega⟩,
      (hfe b).mp hbe, hbre⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    have hbr : (U.block b).round = S₂.slotRound k + 2 := (Finset.mem_filter.mp hbA).2
    exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbA).1, by omega⟩,
      (hfe b).mpr hbe, hbre⟩

/-! ## The band a verdict reads

One induction over the six constructors. The three anchored ones are
Hydrozoan's argument unchanged — the `top` a verdict reads is the
maximum of the anchor's and the skipped slots' between — and what is new
is only which rules are transported at the leaves. -/

theorem bandedOpt_aux {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (hle : ∀ b ∈ U.ids, ∀ m, (U.block b).round = LeanDag.Hydrozoan.decisionRound Replica m →
      WitnessesEquivocation U m b →
      ∀ j ∈ (U.block b).parents, (U.block j).author ≠ S.leader m)
    {V : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId}
    (hd : DecidedOpt { U with leader_excluded := hle } V k v) :
    ∃ top, S.slotRound k + 2 ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : LeanDag.Hydrozoan.Slots Replica)
        (U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
        (hle' : ∀ b ∈ U'.ids, ∀ m,
          (U'.block b).round = LeanDag.Hydrozoan.decisionRound (S := S') Replica m →
          WitnessesEquivocation (S := S') U' m b →
          ∀ j ∈ (U'.block b).parents, (U'.block j).author ≠ S'.leader m)
        (V' : LeanDag.Hydrozoan.View U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand rule U U' (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        DecidedOpt (S := S') { U' with leader_excluded := hle' } V' k' v := by
  classical
  induction hd with
  | @directFast k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' hle' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact DecidedOpt.directFast (S := S')
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL)
        (fastCommitOptInView_bnd hab (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k) (n' := S'.slotRound k') (by omega) (by omega) (by omega) hc)
  | @directSlow k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' hle' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine DecidedOpt.directSlow (S := S')
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL) ?_
      exact le_trans hc (Finset.card_le_card
        (certifiersInView_bnd hab (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k) (n' := S'.slotRound k') (by omega) (by omega) (by omega)))
  | @directSkip k hs =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' hle' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact DecidedOpt.directSkip (S := S')
        (skippedLeaderOptInView_bnd hab (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          hkk hlk (by omega) (by omega) hs)
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : LeanDag.Hydrozoan.IsLeaderBlock U j A :=
        isLeaderBlock_of_decidedOpt hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j)
          (h3 : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' hle' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by
        rw [hAL.2.1]; omega
      have helig' : LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' (j - k + k') := by
        have := helig
        unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
        omega
      have hanch := hjt g g' d d' S' U' hle' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' i' →
          DecidedOpt (S := S') { U' with leader_excluded := hle' } V' i' none := by
        intro i' hh1 hh2 hh3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' := hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k (i' - k' + k) := by
          have := hh3
          unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
          omega
        have hk2 := hkey _ hki hij helg
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        exact hit g g' d d' S' U' hle' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hlsOld : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L' →
          L' ∈ U.ids → LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' :=
        fun L' hL' hLo => isLeaderBlock_bnd_old hab hkk hlk (by omega) (by omega) hLo hL'
      exact DecidedOpt.indirectCert (S := S') (by omega) helig' hanch hmid'
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL)
        (certifiedIn_bnd hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hcert)
  | @indirectEvidence k j A L hkj helig hanchor hmid hnocert hL hev ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : LeanDag.Hydrozoan.IsLeaderBlock U j A :=
        isLeaderBlock_of_decidedOpt hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j)
          (h3 : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' hle' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by
        rw [hAL.2.1]; omega
      have helig' : LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' (j - k + k') := by
        have := helig
        unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
        omega
      have hanch := hjt g g' d d' S' U' hle' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' i' →
          DecidedOpt (S := S') { U' with leader_excluded := hle' } V' i' none := by
        intro i' hh1 hh2 hh3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' := hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k (i' - k' + k) := by
          have := hh3
          unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
          omega
        have hk2 := hkey _ hki hij helg
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        exact hit g g' d d' S' U' hle' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hlsOld : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L' →
          L' ∈ U.ids → LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' :=
        fun L' hL' hLo => isLeaderBlock_bnd_old hab hkk hlk (by omega) (by omega) hLo hL'
      refine DecidedOpt.indirectEvidence (S := S') (by omega) helig' hanch hmid' ?_
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL)
        (evidenceLinked_bnd hab hkk hlk (by omega) (by omega) hAL.1 hAlo hAhi hev)
      intro L' hL' hc'
      by_cases hLo : L' ∈ U.ids
      · exact hnocert L' (hlsOld L' hL' hLo)
          (certifiedIn_bnd_old hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hc')
      · exact not_certifiedIn_bnd_novel hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hLo hc'
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoev ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : LeanDag.Hydrozoan.IsLeaderBlock U j A :=
        isLeaderBlock_of_decidedOpt hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j)
          (h3 : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' hle' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by
        rw [hAL.2.1]; omega
      have helig' : LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' (j - k + k') := by
        have := helig
        unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
        omega
      have hanch := hjt g g' d d' S' U' hle' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' i' →
          DecidedOpt (S := S') { U' with leader_excluded := hle' } V' i' none := by
        intro i' hh1 hh2 hh3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' := hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k (i' - k' + k) := by
          have := hh3
          unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
          omega
        have hk2 := hkey _ hki hij helg
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        exact hit g g' d d' S' U' hle' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hlsOld : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L' →
          L' ∈ U.ids → LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' :=
        fun L' hL' hLo => isLeaderBlock_bnd_old hab hkk hlk (by omega) (by omega) hLo hL'
      refine DecidedOpt.indirectSkip (S := S') (by omega) helig' hanch hmid' ?_ ?_
      · intro L' hL' hc'
        by_cases hLo : L' ∈ U.ids
        · exact hnocert L' (hlsOld L' hL' hLo)
            (certifiedIn_bnd_old hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hc')
        · exact not_certifiedIn_bnd_novel hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hLo hc'
      · intro L' hL' he'
        by_cases hLo : L' ∈ U.ids
        · exact hnoev L' (hlsOld L' hL' hLo)
            (evidenceLinked_bnd_old hab hkk hlk (by omega) (by omega) hAL.1 hAlo hAhi he')
        · exact absurd he' (not_evidenceLinked_bnd_novel hab hkk hlk (by omega) (by omega)
            hAL.1 hAlo hAhi hLo)

end OptimalHydrozoan

end LeanDag
