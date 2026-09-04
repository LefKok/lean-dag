import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Properties.Witness
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Hydrozoan's rules read a band of rounds

Not part of the audit surface. The transfer lemmas `Properties.Banded`
needs of this protocol, replacing the two families this file was split
from: one for `Persist`, over extensions, and one for `Local`, over
agreement above a round. `AgreeBand` covers both, so there is one family
and one induction, and persistence and locality are corollaries.

**One-directionality is the whole difference.** `AgreeAbove` compares
membership with an iff, and the lemmas it supported were equalities of
sets. A band is one-directional — the larger universe may hold blocks
the band did not, which is what a fill does — so those become
containments, which is all the counting rules need, and the negative
clauses of the two anchored skips need a new argument: a candidate the
band did not carry is invisible to an old anchor, because the anchor's
cone never leaves the blocks the band already had.

The guards are the ones the earlier file recorded. A **candidate** is
read at the slot's own round, so `lo ≤ round` suffices. A **vote** is
read from a block's parents, and a band compares parents only strictly
above `lo`, so counting votes needs `lo < round`. A **certificate**
counts votes cast by its own parents, so it needs `lo + 1 < round`. The
ceiling is new and uniform: every read must also sit at or below `hi`.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {lo hi : ℕ}

/-! ## Blocks -/

theorem bnd_mem (h : AgreeBand rule U U' lo hi) {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo ≤ (U.block b).round) (h2 : (U.block b).round ≤ hi) : b ∈ U'.ids :=
  h.mem b hb h1 h2

theorem bnd_round (h : AgreeBand rule U U' lo hi) {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo ≤ (U.block b).round) (h2 : (U.block b).round ≤ hi) :
    (U'.block b).round = (U.block b).round := (h.block b hb (Or.inl ⟨h1, h2⟩)).1

theorem bnd_author (h : AgreeBand rule U U' lo hi) {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo ≤ (U.block b).round) (h2 : (U.block b).round ≤ hi) :
    (U'.block b).author = (U.block b).author := (h.block b hb (Or.inl ⟨h1, h2⟩)).2

theorem bnd_parents (h : AgreeBand rule U U' lo hi) {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo < (U.block b).round) (h2 : (U.block b).round ≤ hi) :
    (U'.block b).parents = (U.block b).parents := h.refs b hb h1 h2

/-- Read from the other side, for a block the band already had. -/
theorem bnd_round' (h : AgreeBand rule U U' lo hi) {b : BlockId} (hb : b ∈ U.ids)
    (hb' : b ∈ U'.ids) (h1 : lo ≤ (U'.block b).round) (h2 : (U'.block b).round ≤ hi) :
    (U'.block b).round = (U.block b).round ∧ (U'.block b).author = (U.block b).author :=
  h.block b hb (Or.inr ⟨hb', h1, h2⟩)

/-- A round layer inside the band is carried across. Containment, not
equality: `U'` may hold blocks there that `U` did not. -/
theorem blocksAt_bnd (h : AgreeBand rule U U' lo hi) {n : ℕ} (h1 : lo ≤ n) (h2 : n ≤ hi) :
    LeanDag.Hydrozoan.blocksAt U n ⊆ LeanDag.Hydrozoan.blocksAt U' n := by
  intro b hb
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hb ⊢
  exact ⟨bnd_mem h hb.1 (by omega) (by omega),
    by rw [bnd_round h hb.1 (by omega) (by omega)]; exact hb.2⟩

theorem isVote_bnd (h : AgreeBand rule U U' lo hi) {b L : BlockId} (hb : b ∈ U.ids)
    (h1 : lo < (U.block b).round) (h2 : (U.block b).round ≤ hi) :
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
  rw [bnd_parents h hb h1 h2]

theorem authorsOf_bnd (h : AgreeBand rule U U' lo hi) {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round ∧ (U.block b).round ≤ hi) :
    LeanDag.Hydrozoan.authorsOf U'.block s = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i hi' =>
    bnd_author h (hs i hi').1 (hs i hi').2.1 (hs i hi').2.2

/-- What a block of `U'` at a band round supplies, when it is a block
the band already had. -/
theorem of_mem_blocksAt_old (h : AgreeBand rule U U' lo hi) {b : BlockId} {n : ℕ}
    (h1 : lo ≤ n) (h2 : n ≤ hi) (hbU : b ∈ U.ids)
    (hb : b ∈ LeanDag.Hydrozoan.blocksAt U' n) : (U.block b).round = n := by
  obtain ⟨hbm, hbr⟩ := Finset.mem_filter.mp hb
  rw [(bnd_round' h hbU hbm (by omega) (by omega)).1] at hbr
  exact hbr


variable [S : LeanDag.Hydrozoan.Slots Replica]

/-! ## The slot's candidates -/

theorem isLeaderBlock_bnd (h : AgreeBand rule U U' lo hi) {k : ℕ}
    (h1 : lo ≤ S.slotRound k) (h2 : S.slotRound k ≤ hi) {L : BlockId}
    (hL : LeanDag.Hydrozoan.IsLeaderBlock U k L) :
    LeanDag.Hydrozoan.IsLeaderBlock U' k L := by
  obtain ⟨hm, hr, ha⟩ := hL
  exact ⟨bnd_mem h hm (by omega) (by omega),
    by rw [bnd_round h hm (by omega) (by omega)]; exact hr,
    by rw [bnd_author h hm (by omega) (by omega)]; exact ha⟩

/-- The other direction, for a candidate the band already had. Nothing
says the larger universe has no fresh candidates; the anchored skips
below dispose of those separately. -/
theorem isLeaderBlock_bnd_old (h : AgreeBand rule U U' lo hi) {k : ℕ}
    (h1 : lo ≤ S.slotRound k) (h2 : S.slotRound k ≤ hi) {L : BlockId} (hLU : L ∈ U.ids)
    (hL : LeanDag.Hydrozoan.IsLeaderBlock U' k L) :
    LeanDag.Hydrozoan.IsLeaderBlock U k L := by
  obtain ⟨hm, hr, ha⟩ := hL
  have hb := bnd_round' h hLU hm (by omega) (by omega)
  exact ⟨hLU, by rw [← hb.1]; exact hr, by rw [← hb.2]; exact ha⟩

/-! ## The counting rules -/

theorem votesSet_bnd (h : AgreeBand rule U U' lo hi) {L : BlockId} {n : ℕ}
    (h1 : lo < n) (h2 : n ≤ hi) :
    ((LeanDag.Hydrozoan.blocksAt U n).filter fun b => LeanDag.Hydrozoan.IsVote U b L)
      ⊆ ((LeanDag.Hydrozoan.blocksAt U' n).filter fun b => LeanDag.Hydrozoan.IsVote U' b L) := by
  intro b hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = n := (Finset.mem_filter.mp hbA).2
  exact Finset.mem_filter.mpr ⟨blocksAt_bnd h (by omega) h2 hbA,
    (isVote_bnd h hbU (by omega) (by omega)).mpr hbv⟩

theorem supportersInView_bnd (h : AgreeBand rule U U' lo hi)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round → (U.block b).round ≤ hi → b ∈ V'.ids)
    {L : BlockId} {n : ℕ} (h1 : lo < n) (h2 : n ≤ hi) :
    LeanDag.Hydrozoan.supportersInView U V L n
      ⊆ LeanDag.Hydrozoan.supportersInView U' V' L n := by
  intro a ha
  unfold LeanDag.Hydrozoan.supportersInView LeanDag.Hydrozoan.authorsOf at ha ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = n := (Finset.mem_filter.mp hbA).2
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨blocksAt_bnd h (by omega) h2 hbA,
      (isVote_bnd h hbU (by omega) (by omega)).mpr hbv⟩,
    hv b hbV (by omega) (by omega)⟩, ?_⟩
  rw [bnd_author h hbU (by omega) (by omega)]; exact hba

/-- Two rounds of slack: a certificate counts votes cast by its own
parents. -/
theorem voteBlocks_bnd (h : AgreeBand rule U U' lo hi) {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round) (h2 : (U.block C).round ≤ hi) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [bnd_parents h hC (by omega) h2]
  refine Finset.filter_congr fun b hb => ?_
  have hbU := U.complete C hC b hb
  have hbr := (U.valid C hC).predecessor b hb
  simpa using isVote_bnd h hbU (by omega) (by omega)

theorem isCertificate_bnd (h : AgreeBand rule U U' lo hi) {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round) (h2 : (U.block C).round ≤ hi) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [voteBlocks_bnd h hC h1 h2, authorsOf_bnd h]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  have := (U.valid C hC).predecessor b hbp
  exact ⟨U.complete C hC b hbp, by omega, by omega⟩

theorem certificates_bnd (h : AgreeBand rule U U' lo hi) {L : BlockId} {n : ℕ}
    (h1 : lo ≤ n) (h2 : n + 2 ≤ hi) :
    LeanDag.Hydrozoan.certificates U L n ⊆ LeanDag.Hydrozoan.certificates U' L n := by
  intro C hC
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCU : C ∈ U.ids := (Finset.mem_filter.mp hCA).1
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp hCA).2
  exact Finset.mem_filter.mpr ⟨blocksAt_bnd h (by omega) (by omega) hCA,
    (isCertificate_bnd h hCU (by omega) (by omega)).mpr hCc⟩

/-- And back, for a certificate the band already had. -/
theorem certificates_bnd_old (h : AgreeBand rule U U' lo hi) {L : BlockId} {n : ℕ}
    (h1 : lo ≤ n) (h2 : n + 2 ≤ hi) {C : BlockId} (hCU : C ∈ U.ids)
    (hC : C ∈ LeanDag.Hydrozoan.certificates U' L n) :
    C ∈ LeanDag.Hydrozoan.certificates U L n := by
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCr : (U.block C).round = n + 2 := of_mem_blocksAt_old h (by omega) (by omega) hCU hCA
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hCU, hCr⟩,
    (isCertificate_bnd h hCU (by omega) (by omega)).mp hCc⟩

theorem certifiersInView_bnd (h : AgreeBand rule U U' lo hi)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round → (U.block b).round ≤ hi → b ∈ V'.ids)
    {L : BlockId} {n : ℕ} (h1 : lo ≤ n) (h2 : n + 2 ≤ hi) :
    LeanDag.Hydrozoan.certifiersInView U V L n
      ⊆ LeanDag.Hydrozoan.certifiersInView U' V' L n := by
  intro a ha
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
    LeanDag.Hydrozoan.authorsOf at ha ⊢
  obtain ⟨C, hC, hCa⟩ := Finset.mem_image.mp ha
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCU : C ∈ U.ids := (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).1
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).2
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨certificates_bnd h h1 h2 hCc, hv C hCV (by omega) (by omega)⟩, ?_⟩
  rw [bnd_author h hCU (by omega) (by omega)]; exact hCa

/-- **The blame set is carried across.** A blamer references no
candidate, its parents are the parents it had, and a candidate the band
did not carry is not among them — so it blames the slot still. -/
theorem blamesInView_bnd (h : AgreeBand rule U U' lo hi)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round → (U.block b).round ≤ hi → b ∈ V'.ids)
    {k : ℕ} (h1 : lo ≤ S.slotRound k) (h2 : S.slotRound k + 1 ≤ hi) :
    LeanDag.Hydrozoan.blamesInView U V k ⊆ LeanDag.Hydrozoan.blamesInView U' V' k := by
  intro a ha
  unfold LeanDag.Hydrozoan.blamesInView LeanDag.Hydrozoan.authorsOf at ha ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbn⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = LeanDag.Hydrozoan.votingRound Replica k :=
    (Finset.mem_filter.mp hbA).2
  have hvr : LeanDag.Hydrozoan.votingRound Replica k = S.slotRound k + 1 := rfl
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨blocksAt_bnd h (by omega) (by omega) hbA, ?_⟩, hv b hbV (by omega) (by omega)⟩, ?_⟩
  · rw [bnd_parents h hbU (by omega) (by omega)]
    intro j hj hjL
    have hjU : j ∈ U.ids := U.complete b hbU j hj
    exact hbn j hj (isLeaderBlock_bnd_old h h1 (by omega) hjU hjL)
  · rw [bnd_author h hbU (by omega) (by omega)]; exact hba

/-! ## The two anchored tests

Each in three parts: forward, back for a candidate the band already
had, and — the clause a one-directional band forces and the earlier
`AgreeAbove` family never needed — that a candidate the band did not
carry passes neither test, because the anchor's cone never leaves the
blocks the band had and an old voter names only old blocks. -/

theorem certifiedIn_bnd (h : AgreeBand rule U U' lo hi) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round) (hAhi : (U.block A).round ≤ hi)
    (h1 : lo ≤ n) (h2 : n + 2 ≤ hi)
    (hc : LeanDag.Hydrozoan.CertifiedIn U A L n) :
    LeanDag.Hydrozoan.CertifiedIn U' A L n := by
  obtain ⟨C, hC, hre⟩ := hc
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (rule.block U C).round = (U.block C).round := rfl
  exact ⟨C, certificates_bnd h h1 h2 hC,
    AgreeBand.reaches_of causal h hA hAhi hre (by omega)⟩

theorem certifiedIn_bnd_old (h : AgreeBand rule U U' lo hi) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round) (hAhi : (U.block A).round ≤ hi)
    (h1 : lo ≤ n) (h2 : n + 2 ≤ hi)
    (hc : LeanDag.Hydrozoan.CertifiedIn U' A L n) :
    LeanDag.Hydrozoan.CertifiedIn U A L n := by
  obtain ⟨C, hC, hre⟩ := hc
  have hCr' : (U'.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (rule.block U' C).round = (U'.block C).round := rfl
  obtain ⟨hCU, hreU, -⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hre (by omega)
  exact ⟨C, certificates_bnd_old h h1 h2 hCU hC, hreU⟩

theorem not_certifiedIn_bnd_novel (h : AgreeBand rule U U' lo hi) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round) (hAhi : (U.block A).round ≤ hi)
    (h1 : lo ≤ n) (h2 : n + 2 ≤ hi) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.CertifiedIn U' A L n := by
  rintro ⟨C, hC, hre⟩
  have hCr' : (U'.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (rule.block U' C).round = (U'.block C).round := rfl
  obtain ⟨hCU, -, hCeq⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hre (by omega)
  have hCr : (U.block C).round = n + 2 := by
    have : (U.block C).round = (U'.block C).round := hCeq
    omega
  have hcert : LeanDag.Hydrozoan.IsCertificate U' C L := (Finset.mem_filter.mp hC).2
  rw [isCertificate_bnd h hCU (by omega) (by omega)] at hcert
  unfold LeanDag.Hydrozoan.IsCertificate at hcert
  have hempty : LeanDag.Hydrozoan.voteBlocks U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    exact hL (U.complete b (U.complete C hCU b hbp) L hbv)
  rw [hempty] at hcert
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcert
  have : 0 < LeanDag.Hydrozoan.qCert Replica := by
    unfold LeanDag.Hydrozoan.qCert; omega
  omega

theorem weakLinked_bnd (h : AgreeBand rule U U' lo hi) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round) (hAhi : (U.block A).round ≤ hi)
    (h1 : lo ≤ n) (h2 : n + 1 ≤ hi)
    (hw : LeanDag.Hydrozoan.WeakLinked U A L n) :
    LeanDag.Hydrozoan.WeakLinked U' A L n := by
  obtain ⟨s, hs, hcard⟩ := hw
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := fun b hb =>
    ⟨(Finset.mem_filter.mp (hs b hb).1).1, (Finset.mem_filter.mp (hs b hb).1).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (rule.block U b).round = (U.block b).round := rfl
    exact ⟨blocksAt_bnd h (by omega) (by omega) hbA,
      (isVote_bnd h hbU (by omega) (by omega)).mpr hbv,
      AgreeBand.reaches_of causal h hA hAhi hbre (by omega)⟩
  · rw [authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem weakLinked_bnd_old (h : AgreeBand rule U U' lo hi) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round) (hAhi : (U.block A).round ≤ hi)
    (h1 : lo ≤ n) (h2 : n + 1 ≤ hi)
    (hw : LeanDag.Hydrozoan.WeakLinked U' A L n) :
    LeanDag.Hydrozoan.WeakLinked U A L n := by
  obtain ⟨s, hs, hcard⟩ := hw
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := by
    intro b hb
    obtain ⟨hbA, -, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = n + 1 := (Finset.mem_filter.mp hbA).2
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hbre (by omega)
    have : (U.block b).round = (U'.block b).round := hbeq
    exact ⟨hbU, by omega⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    have hbr'' : (U'.block b).round = n + 1 := (Finset.mem_filter.mp hbA).2
    obtain ⟨-, hbreU, -⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hbre (by omega)
    exact ⟨Finset.mem_filter.mpr ⟨hbU, hbr⟩,
      (isVote_bnd h hbU (by omega) (by omega)).mp hbv, hbreU⟩
  · rw [← authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem not_weakLinked_bnd_novel (h : AgreeBand rule U U' lo hi) {A L : BlockId} {n : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round) (hAhi : (U.block A).round ≤ hi)
    (h1 : lo ≤ n) (h2 : n + 1 ≤ hi) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.WeakLinked U' A L n := by
  rintro ⟨s, hs, hcard⟩
  have hsempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = n + 1 := (Finset.mem_filter.mp hbA).2
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old causal h hA hAlo hAhi hbre (by omega)
    have hbr : (U.block b).round = n + 1 := by
      have : (U.block b).round = (U'.block b).round := hbeq
      omega
    have hbvU : LeanDag.Hydrozoan.IsVote U b L :=
      (isVote_bnd h hbU (by omega) (by omega)).mp hbv
    exact hL (U.complete b hbU L hbvU)
  rw [hsempty] at hcard
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcard
  have : 0 < LeanDag.Hydrozoan.qWeak Replica := by
    unfold LeanDag.Hydrozoan.qWeak; omega
  omega

/-! ## Reading the schedule at one slot

The direct rules consult the leaders only at the slot being decided, so
two schedules naming the same round and leader there agree on them. -/

theorem isLeaderBlock_sched {S₁ S₂ : LeanDag.Hydrozoan.Slots Replica} {k : ℕ} {L : BlockId}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : LeanDag.Hydrozoan.IsLeaderBlock (S := S₁) U k L) :
    LeanDag.Hydrozoan.IsLeaderBlock (S := S₂) U k L := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [← hround]; exact h2, by rw [← hk]; exact h3⟩

theorem blamesInView_sched {S₁ S₂ : LeanDag.Hydrozoan.Slots Replica}
    {V : LeanDag.Hydrozoan.View U} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k) :
    LeanDag.Hydrozoan.blamesInView (S := S₁) U V k
      = LeanDag.Hydrozoan.blamesInView (S := S₂) U V k := by
  unfold LeanDag.Hydrozoan.blamesInView
  congr 1
  ext b
  simp only [Finset.mem_inter, Finset.mem_filter, LeanDag.Hydrozoan.blocksAt,
    LeanDag.Hydrozoan.votingRound, hround]
  constructor
  · rintro ⟨⟨⟨hbm, hbr⟩, hbn⟩, hbV⟩
    exact ⟨⟨⟨hbm, hbr⟩, fun j hj hjL => hbn j hj (isLeaderBlock_sched hround.symm hk.symm hjL)⟩,
      hbV⟩
  · rintro ⟨⟨⟨hbm, hbr⟩, hbn⟩, hbV⟩
    exact ⟨⟨⟨hbm, hbr⟩, fun j hj hjL => hbn j hj (isLeaderBlock_sched hround hk hjL)⟩, hbV⟩

/-! ## The band a verdict reads

One induction over the six constructors, replacing the two this file was
split from. -/

theorem banded_aux {V : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId}
    (hd : LeanDag.Hydrozoan.Decided U V k v) :
    ∃ top, S.slotRound k + 2 ≤ top ∧
      ∀ (S' : LeanDag.Hydrozoan.Slots Replica)
        (U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
        (V' : LeanDag.Hydrozoan.View U'),
        S'.slotRound = S.slotRound →
        (∀ m, S.slotRound m ≤ top → S'.leader m = S.leader m) →
        AgreeBand rule U U' (S.slotRound k) top →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        LeanDag.Hydrozoan.Decided (S := S') U' V' k v := by
  classical
  induction hd with
  | @directFast k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro S' U' V' hround hlead hab hV
      have hsk : ∀ x, S'.slotRound x = S.slotRound x := fun x => by rw [hround]
      have hlk : S.leader k = S'.leader k := (hlead k (by omega)).symm
      have hLb : LeanDag.Hydrozoan.IsLeaderBlock (S := S) U' k L :=
        isLeaderBlock_bnd (S := S) hab (le_refl _) (by omega) hL
      refine LeanDag.Hydrozoan.Decided.directFast (S := S')
        (isLeaderBlock_sched (S₁ := S) (S₂ := S') (hsk k).symm hlk hLb) ?_
      rw [hsk k]
      exact le_trans hc (Finset.card_le_card
        (supportersInView_bnd (S := S) hab hV (by omega) (by omega)))
  | @directSlow k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro S' U' V' hround hlead hab hV
      have hsk : ∀ x, S'.slotRound x = S.slotRound x := fun x => by rw [hround]
      have hlk : S.leader k = S'.leader k := (hlead k (by omega)).symm
      have hLb : LeanDag.Hydrozoan.IsLeaderBlock (S := S) U' k L :=
        isLeaderBlock_bnd (S := S) hab (le_refl _) (by omega) hL
      refine LeanDag.Hydrozoan.Decided.directSlow (S := S')
        (isLeaderBlock_sched (S₁ := S) (S₂ := S') (hsk k).symm hlk hLb) ?_
      rw [hsk k]
      exact le_trans hc (Finset.card_le_card
        (certifiersInView_bnd (S := S) hab hV (le_refl _) (by omega)))
  | @directSkip k hs =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro S' U' V' hround hlead hab hV
      have hsk : ∀ x, S'.slotRound x = S.slotRound x := fun x => by rw [hround]
      have hlk : S.leader k = S'.leader k := (hlead k (by omega)).symm
      refine LeanDag.Hydrozoan.Decided.directSkip (S := S') ?_
      unfold LeanDag.Hydrozoan.SkippedLeaderInView at hs ⊢
      rw [← blamesInView_sched (S₁ := S) (S₂ := S') (hsk k).symm hlk]
      exact le_trans hs (Finset.card_le_card
        (blamesInView_bnd (S := S) hab hV (le_refl _) (by omega)))
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j)
          (h3 : LeanDag.Hydrozoan.EligibleAsAnchor Replica k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro S' U' V' hround hlead hab hV
      have hsk : ∀ x, S'.slotRound x = S.slotRound x := fun x => by rw [hround]
      have hlk : S.leader k = S'.leader k := (hlead k (by omega)).symm
      have heq : ∀ x y, LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica x y ↔
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica x y := by
        intro x y
        simp only [LeanDag.Hydrozoan.EligibleAsAnchor, LeanDag.Hydrozoan.decisionRound, hround]
      have hAlo : S.slotRound k ≤ (U.block A).round := by rw [hA.2.1]; exact hkj'
      have hAhi : (U.block A).round ≤ top := by rw [hA.2.1]; omega
      have hanch : LeanDag.Hydrozoan.Decided (S := S') U' V' j (some A) :=
        hjt S' U' V' hround (fun m hm => hlead m (by omega))
          (hab.mono hkj' htj) (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i, k < i → i < j →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k i →
          LeanDag.Hydrozoan.Decided (S := S') U' V' i none := by
        intro i h1 h2 h3
        have h3' := (heq _ _).mp h3
        have hki : S.slotRound k ≤ S.slotRound i := S.mono (by omega)
        have hk2 := hkey i h1 h2 h3'
        obtain ⟨htopi, hit⟩ := (ihmid i h1 h2 h3').choose_spec
        exact hit S' U' V' hround (fun m hm => hlead m (by omega)) (hab.mono hki hk2)
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := S') hkj ((heq _ _).mpr helig)
        hanch hmid' (isLeaderBlock_sched (S₁ := S) (S₂ := S') (hsk k).symm hlk
          (isLeaderBlock_bnd (S := S) hab (le_refl _) (by omega) hL)) ?_
      rw [hsk k]
      exact certifiedIn_bnd hab hA.1 hAlo hAhi (le_refl _) (by omega) hcert
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j)
          (h3 : LeanDag.Hydrozoan.EligibleAsAnchor Replica k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro S' U' V' hround hlead hab hV
      have hsk : ∀ x, S'.slotRound x = S.slotRound x := fun x => by rw [hround]
      have hlk : S.leader k = S'.leader k := (hlead k (by omega)).symm
      have heq : ∀ x y, LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica x y ↔
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica x y := by
        intro x y
        simp only [LeanDag.Hydrozoan.EligibleAsAnchor, LeanDag.Hydrozoan.decisionRound, hround]
      have hAlo : S.slotRound k ≤ (U.block A).round := by rw [hA.2.1]; exact hkj'
      have hAhi : (U.block A).round ≤ top := by rw [hA.2.1]; omega
      have hanch : LeanDag.Hydrozoan.Decided (S := S') U' V' j (some A) :=
        hjt S' U' V' hround (fun m hm => hlead m (by omega))
          (hab.mono hkj' htj) (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i, k < i → i < j →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k i →
          LeanDag.Hydrozoan.Decided (S := S') U' V' i none := by
        intro i h1 h2 h3
        have h3' := (heq _ _).mp h3
        have hki : S.slotRound k ≤ S.slotRound i := S.mono (by omega)
        have hk2 := hkey i h1 h2 h3'
        obtain ⟨htopi, hit⟩ := (ihmid i h1 h2 h3').choose_spec
        exact hit S' U' V' hround (fun m hm => hlead m (by omega)) (hab.mono hki hk2)
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hnocert' : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k L' →
          ¬ LeanDag.Hydrozoan.CertifiedIn U' A L' (S'.slotRound k) := by
        intro L' hL' hc'
        rw [hsk k] at hc'
        have hL'S := isLeaderBlock_sched (S₁ := S') (S₂ := S) (hsk k) hlk.symm hL'
        by_cases hLo : L' ∈ U.ids
        · exact hnocert L' (isLeaderBlock_bnd_old (S := S) hab (le_refl _) (by omega) hLo hL'S)
            (certifiedIn_bnd_old hab hA.1 hAlo hAhi (le_refl _) (by omega) hc')
        · exact not_certifiedIn_bnd_novel hab hA.1 hAlo hAhi (le_refl _) (by omega) hLo hc'
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') hkj ((heq _ _).mpr helig)
        hanch hmid' hnocert' (isLeaderBlock_sched (S₁ := S) (S₂ := S') (hsk k).symm hlk
          (isLeaderBlock_bnd (S := S) hab (le_refl _) (by omega) hL)) ?_ ?_
      · rw [hsk k]
        exact weakLinked_bnd hab hA.1 hAlo hAhi (le_refl _) (by omega) hweak
      · intro L' hL' hw'
        rw [hsk k] at hw'
        have hL'S := isLeaderBlock_sched (S₁ := S') (S₂ := S) (hsk k) hlk.symm hL'
        by_cases hLo : L' ∈ U.ids
        · exact hmin L' (isLeaderBlock_bnd_old (S := S) hab (le_refl _) (by omega) hLo hL'S)
            (weakLinked_bnd_old hab hA.1 hAlo hAhi (le_refl _) (by omega) hw')
        · exact absurd hw' (not_weakLinked_bnd_novel hab hA.1 hAlo hAhi (le_refl _)
            (by omega) hLo)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hA := LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j)
          (h3 : LeanDag.Hydrozoan.EligibleAsAnchor Replica k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have htopk : S.slotRound k + 2 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro S' U' V' hround hlead hab hV
      have hsk : ∀ x, S'.slotRound x = S.slotRound x := fun x => by rw [hround]
      have hlk : S.leader k = S'.leader k := (hlead k (by omega)).symm
      have heq : ∀ x y, LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica x y ↔
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica x y := by
        intro x y
        simp only [LeanDag.Hydrozoan.EligibleAsAnchor, LeanDag.Hydrozoan.decisionRound, hround]
      have hAlo : S.slotRound k ≤ (U.block A).round := by rw [hA.2.1]; exact hkj'
      have hAhi : (U.block A).round ≤ top := by rw [hA.2.1]; omega
      have hanch : LeanDag.Hydrozoan.Decided (S := S') U' V' j (some A) :=
        hjt S' U' V' hround (fun m hm => hlead m (by omega))
          (hab.mono hkj' htj) (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i, k < i → i < j →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k i →
          LeanDag.Hydrozoan.Decided (S := S') U' V' i none := by
        intro i h1 h2 h3
        have h3' := (heq _ _).mp h3
        have hki : S.slotRound k ≤ S.slotRound i := S.mono (by omega)
        have hk2 := hkey i h1 h2 h3'
        obtain ⟨htopi, hit⟩ := (ihmid i h1 h2 h3').choose_spec
        exact hit S' U' V' hround (fun m hm => hlead m (by omega)) (hab.mono hki hk2)
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hnocert' : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k L' →
          ¬ LeanDag.Hydrozoan.CertifiedIn U' A L' (S'.slotRound k) := by
        intro L' hL' hc'
        rw [hsk k] at hc'
        have hL'S := isLeaderBlock_sched (S₁ := S') (S₂ := S) (hsk k) hlk.symm hL'
        by_cases hLo : L' ∈ U.ids
        · exact hnocert L' (isLeaderBlock_bnd_old (S := S) hab (le_refl _) (by omega) hLo hL'S)
            (certifiedIn_bnd_old hab hA.1 hAlo hAhi (le_refl _) (by omega) hc')
        · exact not_certifiedIn_bnd_novel hab hA.1 hAlo hAhi (le_refl _) (by omega) hLo hc'
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') hkj ((heq _ _).mpr helig)
        hanch hmid' hnocert' ?_
      intro L' hL' hw'
      rw [hsk k] at hw'
      have hL'S := isLeaderBlock_sched (S₁ := S') (S₂ := S) (hsk k) hlk.symm hL'
      by_cases hLo : L' ∈ U.ids
      · exact hnoweak L' (isLeaderBlock_bnd_old (S := S) hab (le_refl _) (by omega) hLo hL'S)
          (weakLinked_bnd_old hab hA.1 hAlo hAhi (le_refl _) (by omega) hw')
      · exact absurd hw' (not_weakLinked_bnd_novel hab hA.1 hAlo hAhi (le_refl _)
          (by omega) hLo)

omit S in
/-- **Hydrozoan reads a band.** The property stated at the core's
schedule vocabulary, which `ofCoreSlots` carries into Hydrozoan's. -/
theorem banded : Banded (rule (Replica := Replica) (BlockId := BlockId)) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := ofCoreSlots S) hd
  refine ⟨top, fun S' U' V' hround hlead hab hV => ?_⟩
  exact ht (ofCoreSlots S') U' V' hround (fun m hm => hlead m hm) hab hV

omit S in
/-- Views hold blocks of their universe. -/
theorem viewSound : ViewSound (rule (Replica := Replica) (BlockId := BlockId)) :=
  fun V => V.subset_ids

end Hydrozoan

end LeanDag
