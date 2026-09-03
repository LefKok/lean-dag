import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Properties.Local

/-!
# Hydrozoan's rules read nothing below a round

Not part of the audit surface. The transfer lemmas
`Properties.Local` needs of this protocol: every predicate a derivation
at slot `k` inspects is read from blocks at round `S.slotRound k` or
above, so two universes agreeing above any `r ≤ S.slotRound k` cannot
disagree about it.

The guards are worth stating once. A **candidate** is read at the slot's
own round, so `r ≤ round` suffices. A **vote** is read from a block's
references, and `AgreeAbove` compares references only strictly above
`r`, so anything counting votes needs `r < round`. A **certificate**
counts votes cast by its own parents, so it needs `r + 1 < round` —
two rounds of slack. Every use site has them: votes are at
`slotRound k + 1` and certificates at `slotRound k + 2`.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {r : ℕ}

/-! ## Blocks -/

theorem agr_mem (h : AgreeAbove rule U U' r) {b : BlockId}
    (hb : b ∈ U.ids) (hr : r ≤ (U.block b).round) : b ∈ U'.ids :=
  ((h.mem b).mp ⟨hb, hr⟩).1

theorem agr_round (h : AgreeAbove rule U U' r) {b : BlockId}
    (hb : b ∈ U.ids) (hr : r ≤ (U.block b).round) :
    (U'.block b).round = (U.block b).round := h.round b hb hr

theorem agr_author (h : AgreeAbove rule U U' r) {b : BlockId}
    (hb : b ∈ U.ids) (hr : r ≤ (U.block b).round) :
    (U'.block b).author = (U.block b).author := h.creator b hb hr

theorem agr_parents (h : AgreeAbove rule U U' r) {b : BlockId}
    (hb : b ∈ U.ids) (hr : r < (U.block b).round) :
    (U'.block b).parents = (U.block b).parents := h.refs b hb hr

/-- Membership read from the other side. -/
theorem agr_mem' (h : AgreeAbove rule U U' r) {b : BlockId}
    (hb : b ∈ U'.ids) (hr : r ≤ (U'.block b).round) :
    b ∈ U.ids ∧ r ≤ (U.block b).round := (h.mem b).mpr ⟨hb, hr⟩

/-- The blocks of a round at or above the horizon are the same blocks. -/
theorem blocksAt_agr (h : AgreeAbove rule U U' r) {n : ℕ} (hn : r ≤ n) :
    LeanDag.Hydrozoan.blocksAt U n = LeanDag.Hydrozoan.blocksAt U' n := by
  ext b
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hbr⟩
    exact ⟨agr_mem h hb (by omega), by rw [agr_round h hb (by omega)]; exact hbr⟩
  · rintro ⟨hb, hbr⟩
    obtain ⟨hbU, hbUr⟩ := agr_mem' h hb (by omega)
    refine ⟨hbU, ?_⟩
    rw [← agr_round h hbU hbUr]; exact hbr

/-- A vote cast strictly above the horizon is the vote it was. -/
theorem isVote_agr (h : AgreeAbove rule U U' r) {b L : BlockId}
    (hb : b ∈ U.ids) (hr : r < (U.block b).round) :
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
  rw [agr_parents h hb hr]

/-- Authors of a set that lies at or above the horizon. -/
theorem authorsOf_agr (h : AgreeAbove rule U U' r) {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ r ≤ (U.block b).round) :
    LeanDag.Hydrozoan.authorsOf U'.block s = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i hi => agr_author h (hs i hi).1 (hs i hi).2

/-- Reachability between blocks above the horizon, in Hydrozoan's
vocabulary. -/
theorem reaches_agr (h : AgreeAbove rule U U' r) {A C : BlockId}
    (hA : A ∈ U.ids) (hAr : r ≤ (U.block A).round)
    (hC : C ∈ U.ids) (hCr : r ≤ (U.block C).round) :
    LeanDag.Hydrozoan.Reaches U' A C ↔ LeanDag.Hydrozoan.Reaches U A C :=
  AgreeAbove.reaches_iff causal h hA hAr hC hCr

variable [S : LeanDag.Hydrozoan.Slots Replica]

/-! ## The slot's candidates -/

theorem isLeaderBlock_agr (h : AgreeAbove rule U U' r) {k : ℕ} (hk : r ≤ S.slotRound k)
    {L : BlockId} :
    LeanDag.Hydrozoan.IsLeaderBlock U' k L ↔ LeanDag.Hydrozoan.IsLeaderBlock U k L := by
  constructor
  · rintro ⟨hm, hr, ha⟩
    obtain ⟨hU, hUr⟩ := agr_mem' h hm (by omega)
    refine ⟨hU, ?_, ?_⟩
    · rw [← agr_round h hU hUr]; exact hr
    · rw [← agr_author h hU hUr]; exact ha
  · rintro ⟨hm, hr, ha⟩
    have hmr : r ≤ (U.block L).round := by omega
    exact ⟨agr_mem h hm hmr, by rw [agr_round h hm hmr]; exact hr,
      by rw [agr_author h hm hmr]; exact ha⟩

/-! ## The counting rules -/

/-- What a block at a round above the horizon supplies: presence in the
original, and its round. -/
theorem of_mem_blocksAt' (h : AgreeAbove rule U U' r) {b : BlockId} {n : ℕ} (hn : r ≤ n)
    (hb : b ∈ LeanDag.Hydrozoan.blocksAt U' n) :
    b ∈ U.ids ∧ (U.block b).round = n := by
  obtain ⟨hbm, hbr⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbU, hbUr⟩ := agr_mem' h hbm (by omega)
  rw [agr_round h hbU hbUr] at hbr
  exact ⟨hbU, hbr⟩

theorem votesSet_agr (h : AgreeAbove rule U U' r) {L : BlockId} {n : ℕ} (hn : r < n) :
    ((LeanDag.Hydrozoan.blocksAt U n).filter fun b => LeanDag.Hydrozoan.IsVote U b L)
      = ((LeanDag.Hydrozoan.blocksAt U' n).filter fun b => LeanDag.Hydrozoan.IsVote U' b L) := by
  rw [blocksAt_agr h (le_of_lt hn)]
  refine Finset.filter_congr fun b hb => ?_
  obtain ⟨hbU, hbr⟩ := of_mem_blocksAt' h (le_of_lt hn) hb
  simpa using (isVote_agr h hbU (by omega)).symm

theorem supportersInView_agr (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {L : BlockId} {n : ℕ} (hn : r < n) :
    LeanDag.Hydrozoan.supportersInView U V L n
      = LeanDag.Hydrozoan.supportersInView U' V' L n := by
  unfold LeanDag.Hydrozoan.supportersInView
  have hset : ((LeanDag.Hydrozoan.blocksAt U n).filter
        fun b => LeanDag.Hydrozoan.IsVote U b L) ∩ V.ids
      = ((LeanDag.Hydrozoan.blocksAt U' n).filter
        fun b => LeanDag.Hydrozoan.IsVote U' b L) ∩ V'.ids := by
    rw [← votesSet_agr h hn]
    ext b
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hbA, hbv⟩, hbV⟩
      obtain ⟨hbm, hbrd⟩ := Finset.mem_filter.mp hbA
      exact ⟨⟨hbA, hbv⟩, (hv b hbm (by show r ≤ (U.block b).round; omega)).mp hbV⟩
    · rintro ⟨⟨hbA, hbv⟩, hbV⟩
      obtain ⟨hbm, hbrd⟩ := Finset.mem_filter.mp hbA
      exact ⟨⟨hbA, hbv⟩, (hv b hbm (by show r ≤ (U.block b).round; omega)).mpr hbV⟩
  rw [hset, authorsOf_agr h]
  intro b hb
  obtain ⟨hbA, _⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbU, hbr⟩ := of_mem_blocksAt' h (le_of_lt hn) (Finset.mem_filter.mp hbA).1
  exact ⟨hbU, by omega⟩

/-- Two rounds of slack: a certificate counts votes cast by its own
parents, so the block itself must sit strictly above the round the
references are compared at. -/
theorem voteBlocks_agr (h : AgreeAbove rule U U' r) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : r + 1 < (U.block C).round) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [agr_parents h hC (by omega)]
  refine Finset.filter_congr fun b hb => ?_
  have hbU := U.complete C hC b hb
  have hbr := (U.valid C hC).predecessor b hb
  simpa using isVote_agr h hbU (by omega)

theorem isCertificate_agr (h : AgreeAbove rule U U' r) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : r + 1 < (U.block C).round) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [voteBlocks_agr h hC hCr, authorsOf_agr h]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  exact ⟨U.complete C hC b hbp, by have := (U.valid C hC).predecessor b hbp; omega⟩

theorem certificates_agr (h : AgreeAbove rule U U' r) {L : BlockId} {n : ℕ} (hn : r ≤ n) :
    LeanDag.Hydrozoan.certificates U L n = LeanDag.Hydrozoan.certificates U' L n := by
  unfold LeanDag.Hydrozoan.certificates
  rw [blocksAt_agr h (show r ≤ n + 2 by omega)]
  refine Finset.filter_congr fun C hC => ?_
  obtain ⟨hCU, hCr⟩ := of_mem_blocksAt' h (show r ≤ n + 2 by omega) hC
  simpa using (isCertificate_agr h hCU (by omega)).symm

/-- What membership in the certificate set supplies. -/
theorem mem_certificates_bounds {L : BlockId} {n : ℕ} {C : BlockId}
    (hC : C ∈ LeanDag.Hydrozoan.certificates U L n) :
    C ∈ U.ids ∧ (U.block C).round = n + 2 := by
  obtain ⟨hCb, -⟩ := Finset.mem_filter.mp hC
  exact ⟨(Finset.mem_filter.mp hCb).1, (Finset.mem_filter.mp hCb).2⟩

theorem certifiersInView_agr (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {L : BlockId} {n : ℕ} (hn : r ≤ n) :
    LeanDag.Hydrozoan.certifiersInView U V L n
      = LeanDag.Hydrozoan.certifiersInView U' V' L n := by
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
  have hset : LeanDag.Hydrozoan.certificates U L n ∩ V.ids
      = LeanDag.Hydrozoan.certificates U' L n ∩ V'.ids := by
    rw [← certificates_agr h hn]
    ext C
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hCc, hCV⟩
      obtain ⟨hCU, hCr⟩ := mem_certificates_bounds hCc
      exact ⟨hCc, (hv C hCU (by show r ≤ (U.block C).round; omega)).mp hCV⟩
    · rintro ⟨hCc, hCV⟩
      obtain ⟨hCU, hCr⟩ := mem_certificates_bounds hCc
      exact ⟨hCc, (hv C hCU (by show r ≤ (U.block C).round; omega)).mpr hCV⟩
  rw [hset, authorsOf_agr h]
  intro C hC
  obtain ⟨hCc, -⟩ := Finset.mem_inter.mp hC
  rw [← certificates_agr h hn] at hCc
  obtain ⟨hCU, hCr⟩ := mem_certificates_bounds hCc
  exact ⟨hCU, by omega⟩

/-- **The blame set is the same set.** Blames sit one round above the
slot, and what they must *not* reference are the slot's candidates,
which agreement fixes. -/
theorem blamesInView_agr (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {k : ℕ} (hk : r ≤ S.slotRound k) :
    LeanDag.Hydrozoan.blamesInView U V k = LeanDag.Hydrozoan.blamesInView U' V' k := by
  unfold LeanDag.Hydrozoan.blamesInView
  have hvr : r < LeanDag.Hydrozoan.votingRound Replica k := by
    unfold LeanDag.Hydrozoan.votingRound; omega
  have hset : ((LeanDag.Hydrozoan.blocksAt U (LeanDag.Hydrozoan.votingRound Replica k)).filter
        fun b => ∀ j ∈ (U.block b).parents, ¬ LeanDag.Hydrozoan.IsLeaderBlock U k j) ∩ V.ids
      = ((LeanDag.Hydrozoan.blocksAt U' (LeanDag.Hydrozoan.votingRound Replica k)).filter
        fun b => ∀ j ∈ (U'.block b).parents, ¬ LeanDag.Hydrozoan.IsLeaderBlock U' k j) ∩ V'.ids := by
    rw [blocksAt_agr h (le_of_lt hvr)]
    ext b
    simp only [Finset.mem_inter, Finset.mem_filter]
    have hbcase : b ∈ LeanDag.Hydrozoan.blocksAt U'
        (LeanDag.Hydrozoan.votingRound Replica k) →
        b ∈ U.ids ∧ (U.block b).round = LeanDag.Hydrozoan.votingRound Replica k :=
      of_mem_blocksAt' h (le_of_lt hvr)
    constructor
    · rintro ⟨⟨hbA, hbl⟩, hbV⟩
      obtain ⟨hbU, hbr⟩ := hbcase hbA
      refine ⟨⟨hbA, ?_⟩, (hv b hbU (by show r ≤ (U.block b).round; omega)).mp hbV⟩
      intro j hj hL
      rw [agr_parents h hbU (by omega)] at hj
      exact hbl j hj ((isLeaderBlock_agr h hk).mp hL)
    · rintro ⟨⟨hbA, hbl⟩, hbV⟩
      obtain ⟨hbU, hbr⟩ := hbcase hbA
      refine ⟨⟨hbA, ?_⟩, (hv b hbU (by show r ≤ (U.block b).round; omega)).mpr hbV⟩
      intro j hj hL
      exact hbl j (by rw [agr_parents h hbU (by omega)]; exact hj)
        ((isLeaderBlock_agr h hk).mpr hL)
  rw [hset, authorsOf_agr h]
  intro b hb
  obtain ⟨hbA, _⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbU, hbr⟩ := of_mem_blocksAt' h (le_of_lt hvr) (Finset.mem_filter.mp hbA).1
  exact ⟨hbU, by omega⟩

/-! ## The rung tests -/

theorem certifiedIn_agr (h : AgreeAbove rule U U' r) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAr : r ≤ (U.block A).round) (hn : r ≤ n) :
    LeanDag.Hydrozoan.CertifiedIn U' A L n ↔ LeanDag.Hydrozoan.CertifiedIn U A L n := by
  unfold LeanDag.Hydrozoan.CertifiedIn
  rw [← certificates_agr h hn]
  constructor
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hCU, hCr⟩ := mem_certificates_bounds hC
    exact ⟨C, hC, (reaches_agr h hA hAr hCU (by omega)).mp hre⟩
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hCU, hCr⟩ := mem_certificates_bounds hC
    exact ⟨C, hC, (reaches_agr h hA hAr hCU (by omega)).mpr hre⟩

theorem weakLinked_agr (h : AgreeAbove rule U U' r) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAr : r ≤ (U.block A).round) (hn : r ≤ n) :
    LeanDag.Hydrozoan.WeakLinked U' A L n ↔ LeanDag.Hydrozoan.WeakLinked U A L n := by
  unfold LeanDag.Hydrozoan.WeakLinked
  constructor
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := fun b hb =>
      of_mem_blocksAt' h (show r ≤ n + 1 by omega) (hs b hb).1
    refine ⟨s, fun b hb => ?_, ?_⟩
    · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
      obtain ⟨hbU, hbr⟩ := hsU b hb
      refine ⟨by rw [blocksAt_agr h (show r ≤ n + 1 by omega)]; exact hbA,
        (isVote_agr h hbU (by omega)).mp hbv,
        (reaches_agr h hA hAr hbU (by omega)).mp hbre⟩
    · rw [← authorsOf_agr h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega⟩)]
      exact hcard
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := fun b hb =>
      ⟨(Finset.mem_filter.mp (hs b hb).1).1, (Finset.mem_filter.mp (hs b hb).1).2⟩
    refine ⟨s, fun b hb => ?_, ?_⟩
    · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
      obtain ⟨hbU, hbr⟩ := hsU b hb
      refine ⟨by rw [← blocksAt_agr h (show r ≤ n + 1 by omega)]; exact hbA,
        (isVote_agr h hbU (by omega)).mpr hbv,
        (reaches_agr h hA hAr hbU (by omega)).mpr hbre⟩
    · rw [authorsOf_agr h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega⟩)]
      exact hcard

/-! ## The three direct rules -/

theorem fastCommitInView_agr (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {L : BlockId} {n : ℕ} (hn : r ≤ n) :
    LeanDag.Hydrozoan.FastCommitInView U V L n
      ↔ LeanDag.Hydrozoan.FastCommitInView U' V' L n := by
  unfold LeanDag.Hydrozoan.FastCommitInView
  rw [supportersInView_agr h hv (show r < n + 1 by omega)]

theorem slowCommitInView_agr (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {L : BlockId} {n : ℕ} (hn : r ≤ n) :
    LeanDag.Hydrozoan.SlowCommitInView U V L n
      ↔ LeanDag.Hydrozoan.SlowCommitInView U' V' L n := by
  unfold LeanDag.Hydrozoan.SlowCommitInView
  rw [certifiersInView_agr h hv hn]

theorem skippedLeaderInView_agr (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {k : ℕ} (hk : r ≤ S.slotRound k) :
    LeanDag.Hydrozoan.SkippedLeaderInView U V k
      ↔ LeanDag.Hydrozoan.SkippedLeaderInView U' V' k := by
  unfold LeanDag.Hydrozoan.SkippedLeaderInView
  rw [blamesInView_agr h hv hk]

/-! ## Locality

The induction. Every recursive call sits at a slot above the one being
decided, so the round condition is inherited by the schedule's
monotonicity and never has to be re-established. -/

theorem local_aux (h : AgreeAbove rule U U' r)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ViewAgreeAbove rule V V' r) {k : ℕ} {v : Option BlockId}
    (hd : LeanDag.Hydrozoan.Decided U V k v) :
    r ≤ S.slotRound k → LeanDag.Hydrozoan.Decided U' V' k v := by
  induction hd with
  | @directFast k L hL hc =>
      intro hk
      exact LeanDag.Hydrozoan.Decided.directFast ((isLeaderBlock_agr h hk).mpr hL)
        ((fastCommitInView_agr h hv hk).mp hc)
  | @directSlow k L hL hc =>
      intro hk
      exact LeanDag.Hydrozoan.Decided.directSlow ((isLeaderBlock_agr h hk).mpr hL)
        ((slowCommitInView_agr h hv hk).mp hc)
  | @directSkip k hs =>
      intro hk
      exact LeanDag.Hydrozoan.Decided.directSkip ((skippedLeaderInView_agr h hv hk).mp hs)
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      intro hk
      have hjk : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
      have hAr : r ≤ (U.block A).round := by rw [hA.2.1]; omega
      exact LeanDag.Hydrozoan.Decided.indirectCert hkj helig (ihj (by omega))
        (fun i h1 h2 he => ihmid i h1 h2 he (by have := S.mono (le_of_lt h1); omega))
        ((isLeaderBlock_agr h hk).mpr hL)
        ((certifiedIn_agr h hA.1 hAr hk).mpr hcert)
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      intro hk
      have hjk : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
      have hAr : r ≤ (U.block A).round := by rw [hA.2.1]; omega
      refine LeanDag.Hydrozoan.Decided.indirectWeak hkj helig (ihj (by omega))
        (fun i h1 h2 he => ihmid i h1 h2 he (by have := S.mono (le_of_lt h1); omega))
        ?_ ((isLeaderBlock_agr h hk).mpr hL)
        ((weakLinked_agr h hA.1 hAr hk).mpr hweak) ?_
      · intro L' hL' hc
        exact hnocert L' ((isLeaderBlock_agr h hk).mp hL')
          ((certifiedIn_agr h hA.1 hAr hk).mp hc)
      · intro L' hL' hw
        exact hmin L' ((isLeaderBlock_agr h hk).mp hL')
          ((weakLinked_agr h hA.1 hAr hk).mp hw)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      intro hk
      have hjk : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
      have hAr : r ≤ (U.block A).round := by rw [hA.2.1]; omega
      refine LeanDag.Hydrozoan.Decided.indirectSkip hkj helig (ihj (by omega))
        (fun i h1 h2 he => ihmid i h1 h2 he (by have := S.mono (le_of_lt h1); omega)) ?_ ?_
      · intro L' hL' hc
        exact hnocert L' ((isLeaderBlock_agr h hk).mp hL')
          ((certifiedIn_agr h hA.1 hAr hk).mp hc)
      · intro L' hL' hw
        exact hnoweak L' ((isLeaderBlock_agr h hk).mp hL')
          ((weakLinked_agr h hA.1 hAr hk).mp hw)

end Hydrozoan

end LeanDag
