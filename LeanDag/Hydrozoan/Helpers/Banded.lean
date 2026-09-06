import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Properties.Band
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
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {lo hi g g' : ℕ}

/-! ## Blocks -/

theorem bnd_mem (h : AgreeBand rule U U' lo hi g g') {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) : b ∈ U'.ids :=
  h.mem b hb h1 h2

theorem bnd_round (h : AgreeBand rule U U' lo hi g g') {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g := (h.block b hb (Or.inl ⟨h1, h2⟩)).1

theorem bnd_author (h : AgreeBand rule U U' lo hi g g') {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).author = (U.block b).author := (h.block b hb (Or.inl ⟨h1, h2⟩)).2

theorem bnd_parents (h : AgreeBand rule U U' lo hi g g') {b : BlockId} (hb : b ∈ U.ids)
    (h1 : lo < (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).parents = (U.block b).parents := h.refs b hb h1 h2

/-- Read from the other side, for a block the band already had. -/
theorem bnd_round' (h : AgreeBand rule U U' lo hi g g') {b : BlockId} (hb : b ∈ U.ids)
    (hb' : b ∈ U'.ids) (h1 : lo ≤ (U'.block b).round + g')
    (h2 : (U'.block b).round + g' ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).author = (U.block b).author :=
  h.block b hb (Or.inr ⟨hb', h1, h2⟩)

/-- A round layer inside the band is carried across. Containment, not
equality: `U'` may hold blocks there that `U` did not. -/
theorem blocksAt_bnd (h : AgreeBand rule U U' lo hi g g') {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + g ≤ hi) :
    LeanDag.Hydrozoan.blocksAt U n ⊆ LeanDag.Hydrozoan.blocksAt U' n' := by
  intro b hb
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hb ⊢
  have hbr := bnd_round h hb.1 (by omega) (by omega)
  exact ⟨bnd_mem h hb.1 (by omega) (by omega), by omega⟩

theorem isVote_bnd (h : AgreeBand rule U U' lo hi g g') {b L : BlockId} (hb : b ∈ U.ids)
    (h1 : lo < (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
  rw [bnd_parents h hb h1 h2]

theorem authorsOf_bnd (h : AgreeBand rule U U' lo hi g g') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round + g ∧ (U.block b).round + g ≤ hi) :
    LeanDag.Hydrozoan.authorsOf U'.block s = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i hi' =>
    bnd_author h (hs i hi').1 (hs i hi').2.1 (hs i hi').2.2

/-- What a block of `U'` at a band round supplies, when it is a block
the band already had. -/
theorem of_mem_blocksAt_old (h : AgreeBand rule U U' lo hi g g') {b : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + g ≤ hi) (hbU : b ∈ U.ids)
    (hb : b ∈ LeanDag.Hydrozoan.blocksAt U' n') : (U.block b).round = n := by
  obtain ⟨hbm, hbr⟩ := Finset.mem_filter.mp hb
  have := (bnd_round' h hbU hbm (by omega) (by omega)).1
  omega


variable [S : LeanDag.Hydrozoan.Slots Replica]

/-! ## The slot's candidates -/

theorem isLeaderBlock_bnd (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi) {L : BlockId}
    (hL : LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L) :
    LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L := by
  obtain ⟨hm, hr, ha⟩ := hL
  have hbr := bnd_round h hm (by omega) (by omega)
  exact ⟨bnd_mem h hm (by omega) (by omega), by omega,
    by rw [bnd_author h hm (by omega) (by omega), ha, hlead]⟩

/-- The other direction, for a candidate the band already had. Nothing
says the larger universe has no fresh candidates; the anchored skips
below dispose of those separately. -/
theorem isLeaderBlock_bnd_old (h : AgreeBand rule U U' lo hi g g')
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi) {L : BlockId}
    (hLU : L ∈ U.ids) (hL : LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L) :
    LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L := by
  obtain ⟨hm, hr, ha⟩ := hL
  have hb := bnd_round' h hLU hm (by omega) (by omega)
  exact ⟨hLU, by omega, by rw [← hb.2, ha, ← hlead]⟩

/-! ## The counting rules -/

theorem votesSet_bnd (h : AgreeBand rule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) :
    ((LeanDag.Hydrozoan.blocksAt U n).filter fun b => LeanDag.Hydrozoan.IsVote U b L)
      ⊆ ((LeanDag.Hydrozoan.blocksAt U' n').filter fun b =>
          LeanDag.Hydrozoan.IsVote U' b L) := by
  intro b hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = n := (Finset.mem_filter.mp hbA).2
  exact Finset.mem_filter.mpr ⟨blocksAt_bnd h hnn (by omega) (by omega) hbA,
    (isVote_bnd h hbU (by omega) (by omega)).mpr hbv⟩

theorem supportersInView_bnd (h : AgreeBand rule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) :
    LeanDag.Hydrozoan.supportersInView U V L n
      ⊆ LeanDag.Hydrozoan.supportersInView U' V' L n' := by
  intro a ha
  unfold LeanDag.Hydrozoan.supportersInView LeanDag.Hydrozoan.authorsOf at ha ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = n := (Finset.mem_filter.mp hbA).2
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨blocksAt_bnd h hnn (by omega) (by omega) hbA,
      (isVote_bnd h hbU (by omega) (by omega)).mpr hbv⟩,
    hv b hbV (by omega) (by omega)⟩, ?_⟩
  rw [bnd_author h hbU (by omega) (by omega)]; exact hba

/-- Two rounds of slack: a certificate counts votes cast by its own
parents. -/
theorem voteBlocks_bnd (h : AgreeBand rule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [bnd_parents h hC (by omega) h2]
  refine Finset.filter_congr fun b hb => ?_
  have hbU := U.complete C hC b hb
  have hbr := (U.valid C hC).predecessor b hb
  simpa using isVote_bnd h hbU (by omega) (by omega)

theorem isCertificate_bnd (h : AgreeBand rule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [voteBlocks_bnd h hC h1 h2, authorsOf_bnd h]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  have := (U.valid C hC).predecessor b hbp
  exact ⟨U.complete C hC b hbp, by omega, by omega⟩

theorem certificates_bnd (h : AgreeBand rule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi) :
    LeanDag.Hydrozoan.certificates U L n ⊆ LeanDag.Hydrozoan.certificates U' L n' := by
  intro C hC
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCU : C ∈ U.ids := (Finset.mem_filter.mp hCA).1
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp hCA).2
  exact Finset.mem_filter.mpr ⟨blocksAt_bnd h (by omega) (by omega) (by omega) hCA,
    (isCertificate_bnd h hCU (by omega) (by omega)).mpr hCc⟩

/-- And back, for a certificate the band already had. -/
theorem certificates_bnd_old (h : AgreeBand rule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi) {C : BlockId}
    (hCU : C ∈ U.ids) (hC : C ∈ LeanDag.Hydrozoan.certificates U' L n') :
    C ∈ LeanDag.Hydrozoan.certificates U L n := by
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCr : (U.block C).round = n + 2 :=
    of_mem_blocksAt_old h (n := n + 2) (n' := n' + 2) (by omega) (by omega) (by omega) hCU hCA
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hCU, hCr⟩,
    (isCertificate_bnd h hCU (by omega) (by omega)).mp hCc⟩

theorem certifiersInView_bnd (h : AgreeBand rule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo ≤ n + g)
    (h2 : n + 2 + g ≤ hi) :
    LeanDag.Hydrozoan.certifiersInView U V L n
      ⊆ LeanDag.Hydrozoan.certifiersInView U' V' L n' := by
  intro a ha
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
    LeanDag.Hydrozoan.authorsOf at ha ⊢
  obtain ⟨C, hC, hCa⟩ := Finset.mem_image.mp ha
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCU : C ∈ U.ids := (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).1
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).2
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨certificates_bnd h hnn h1 h2 hCc, hv C hCV (by omega) (by omega)⟩, ?_⟩
  rw [bnd_author h hCU (by omega) (by omega)]; exact hCa

/-- **The blame set is carried across.** A blamer references no
candidate, its parents are the parents it had, and a candidate the band
did not carry is not among them — so it blames the slot still. -/
theorem blamesInView_bnd (h : AgreeBand rule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {S S' : LeanDag.Hydrozoan.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 1 + g ≤ hi) :
    LeanDag.Hydrozoan.blamesInView (S := S) U V k
      ⊆ LeanDag.Hydrozoan.blamesInView (S := S') U' V' k' := by
  intro a ha
  unfold LeanDag.Hydrozoan.blamesInView LeanDag.Hydrozoan.authorsOf at ha ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbn⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = LeanDag.Hydrozoan.votingRound (S := S) Replica k :=
    (Finset.mem_filter.mp hbA).2
  have hvr : LeanDag.Hydrozoan.votingRound (S := S) Replica k = S.slotRound k + 1 := rfl
  have hvr' : LeanDag.Hydrozoan.votingRound (S := S') Replica k' = S'.slotRound k' + 1 := rfl
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨blocksAt_bnd h (n := LeanDag.Hydrozoan.votingRound (S := S) Replica k)
        (n' := LeanDag.Hydrozoan.votingRound (S := S') Replica k')
        (by omega) (by omega) (by omega) hbA,
      ?_⟩, hv b hbV (by omega) (by omega)⟩, ?_⟩
  · rw [bnd_parents h hbU (by omega) (by omega)]
    intro j hj hjL
    have hjU : j ∈ U.ids := U.complete b hbU j hj
    exact hbn j hj (isLeaderBlock_bnd_old h hkk hlead (by omega) (by omega) hjU hjL)
  · rw [bnd_author h hbU (by omega) (by omega)]; exact hba

/-! ## The two anchored tests

Each in three parts: forward, back for a candidate the band already
had, and — the clause a one-directional band forces and the earlier
`AgreeAbove` family never needed — that a candidate the band did not
carry passes neither test, because the anchor's cone never leaves the
blocks the band had and an old voter names only old blocks. -/

theorem certifiedIn_bnd (h : AgreeBand rule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi)
    (hc : LeanDag.Hydrozoan.CertifiedIn U A L n) :
    LeanDag.Hydrozoan.CertifiedIn U' A L n' := by
  obtain ⟨C, hC, hre⟩ := hc
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (rule.block U C).round = (U.block C).round := rfl
  exact ⟨C, certificates_bnd h hnn h1 h2 hC,
    AgreeBand.reaches_of h hA hAhi hre (by omega)⟩

theorem certifiedIn_bnd_old (h : AgreeBand rule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi)
    (hc : LeanDag.Hydrozoan.CertifiedIn U' A L n') :
    LeanDag.Hydrozoan.CertifiedIn U A L n := by
  obtain ⟨C, hC, hre⟩ := hc
  have hCr' : (U'.block C).round = n' + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (rule.block U' C).round = (U'.block C).round := rfl
  obtain ⟨hCU, hreU, -⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
  exact ⟨C, certificates_bnd_old h hnn h1 h2 hCU hC, hreU⟩

theorem not_certifiedIn_bnd_novel (h : AgreeBand rule U U' lo hi g g') {A L : BlockId}
    {n n' : ℕ} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.CertifiedIn U' A L n' := by
  rintro ⟨C, hC, hre⟩
  have hCr' : (U'.block C).round = n' + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (rule.block U' C).round = (U'.block C).round := rfl
  obtain ⟨hCU, -, hCeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
  have hCr : (U.block C).round = n + 2 := by
    have hce : (U.block C).round + g = (U'.block C).round + g' := hCeq
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

theorem weakLinked_bnd (h : AgreeBand rule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 1 + g ≤ hi)
    (hw : LeanDag.Hydrozoan.WeakLinked U A L n) :
    LeanDag.Hydrozoan.WeakLinked U' A L n' := by
  obtain ⟨s, hs, hcard⟩ := hw
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := fun b hb =>
    ⟨(Finset.mem_filter.mp (hs b hb).1).1, (Finset.mem_filter.mp (hs b hb).1).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (rule.block U b).round = (U.block b).round := rfl
    exact ⟨blocksAt_bnd h (n := n + 1) (n' := n' + 1) (by omega) (by omega) (by omega) hbA,
      (isVote_bnd h hbU (by omega) (by omega)).mpr hbv,
      AgreeBand.reaches_of h hA hAhi hbre (by omega)⟩
  · rw [authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem weakLinked_bnd_old (h : AgreeBand rule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 1 + g ≤ hi)
    (hw : LeanDag.Hydrozoan.WeakLinked U' A L n') :
    LeanDag.Hydrozoan.WeakLinked U A L n := by
  obtain ⟨s, hs, hcard⟩ := hw
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := by
    intro b hb
    obtain ⟨hbA, -, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = n' + 1 := (Finset.mem_filter.mp hbA).2
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    have hbe : (U.block b).round + g = (U'.block b).round + g' := hbeq
    exact ⟨hbU, by omega⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    have hbr'' : (U'.block b).round = n' + 1 := (Finset.mem_filter.mp hbA).2
    obtain ⟨-, hbreU, -⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    exact ⟨Finset.mem_filter.mpr ⟨hbU, hbr⟩,
      (isVote_bnd h hbU (by omega) (by omega)).mp hbv, hbreU⟩
  · rw [← authorsOf_bnd h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem not_weakLinked_bnd_novel (h : AgreeBand rule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 1 + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.WeakLinked U' A L n' := by
  rintro ⟨s, hs, hcard⟩
  have hsempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = n' + 1 := (Finset.mem_filter.mp hbA).2
    have hlink : (rule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    have hbr : (U.block b).round = n + 1 := by
      have hbe : (U.block b).round + g = (U'.block b).round + g' := hbeq
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

omit S [LinearOrder BlockId] in
theorem isLeaderBlock_sched {S₁ S₂ : LeanDag.Hydrozoan.Slots Replica} {k : ℕ} {L : BlockId}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : LeanDag.Hydrozoan.IsLeaderBlock (S := S₁) U k L) :
    LeanDag.Hydrozoan.IsLeaderBlock (S := S₂) U k L := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [← hround]; exact h2, by rw [← hk]; exact h3⟩

omit S in
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
      ∀ (g g' d d' : ℕ) (S' : LeanDag.Hydrozoan.Slots Replica)
        (U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
        (V' : LeanDag.Hydrozoan.View U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand rule U U' (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        LeanDag.Hydrozoan.Decided (S := S') U' V' k' v := by
  classical
  induction hd with
  | @directFast k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine LeanDag.Hydrozoan.Decided.directFast (S := S')
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL) ?_
      exact le_trans hc (Finset.card_le_card
        (supportersInView_bnd hab (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k + 1) (n' := S'.slotRound k' + 1) (by omega) (by omega)
          (by omega)))
  | @directSlow k L hL hc =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine LeanDag.Hydrozoan.Decided.directSlow (S := S')
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL) ?_
      exact le_trans hc (Finset.card_le_card
        (certifiersInView_bnd hab (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k) (n' := S'.slotRound k') (by omega) (by omega) (by omega)))
  | @directSkip k hs =>
      refine ⟨S.slotRound k + 2, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine LeanDag.Hydrozoan.Decided.directSkip (S := S') ?_
      exact le_trans hs (Finset.card_le_card
        (blamesInView_bnd hab (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          hkk hlk (by omega) (by omega)))
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : LeanDag.Hydrozoan.IsLeaderBlock (S := S) U j A :=
        LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
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
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      have helig' : LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' (j - k + k') := by
        have := helig
        unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
        omega
      have hanch := hjt g g' d d' S' U' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' i' →
          LeanDag.Hydrozoan.Decided (S := S') U' V' i' none := by
        intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' := hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k (i' - k' + k) := by
          have := h3
          unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
          omega
        have hk2 := hkey _ hki hij helg
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hlsOld : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L' → L' ∈ U.ids →
          LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' := fun L' hL' hLo =>
        isLeaderBlock_bnd_old hab hkk hlk (by omega) (by omega) hLo hL'
      exact LeanDag.Hydrozoan.Decided.indirectCert (S := S') (by omega) helig' hanch hmid'
        (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL)
        (certifiedIn_bnd hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hcert)
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : LeanDag.Hydrozoan.IsLeaderBlock (S := S) U j A :=
        LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
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
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      have helig' : LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' (j - k + k') := by
        have := helig
        unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
        omega
      have hanch := hjt g g' d d' S' U' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' i' →
          LeanDag.Hydrozoan.Decided (S := S') U' V' i' none := by
        intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' := hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k (i' - k' + k) := by
          have := h3
          unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
          omega
        have hk2 := hkey _ hki hij helg
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hlsOld : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L' → L' ∈ U.ids →
          LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' := fun L' hL' hLo =>
        isLeaderBlock_bnd_old hab hkk hlk (by omega) (by omega) hLo hL'
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') (by omega) helig' hanch hmid'
        ?_ (isLeaderBlock_bnd hab hkk hlk (by omega) (by omega) hL)
        (weakLinked_bnd hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hweak) ?_
      · intro L' hL' hc'
        by_cases hLo : L' ∈ U.ids
        · exact hnocert L' (hlsOld L' hL' hLo)
            (certifiedIn_bnd_old hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hc')
        · exact not_certifiedIn_bnd_novel hab hAL.1 hAlo hAhi hkk (by omega) (by omega)
            hLo hc'
      · intro L' hL' hw'
        by_cases hLo : L' ∈ U.ids
        · exact hmin L' (hlsOld L' hL' hLo)
            (weakLinked_bnd_old hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hw')
        · exact absurd hw' (not_weakLinked_bnd_novel hab hAL.1 hAlo hAhi hkk (by omega)
            (by omega) hLo)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : LeanDag.Hydrozoan.IsLeaderBlock (S := S) U j A :=
        LeanDag.Hydrozoan.isLeaderBlock_of_decided hanchor
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
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      have helig' : LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' (j - k + k') := by
        have := helig
        unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
        omega
      have hanch := hjt g g' d d' S' U' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica k' i' →
          LeanDag.Hydrozoan.Decided (S := S') U' V' i' none := by
        intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hii : S.slotRound (i' - k' + k) + g = S'.slotRound i' + g' := hsch _ i' hi'd
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k (i' - k' + k) := by
          have := h3
          unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound at this ⊢
          omega
        have hk2 := hkey _ hki hij helg
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have hlsOld : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U' k' L' → L' ∈ U.ids →
          LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' := fun L' hL' hLo =>
        isLeaderBlock_bnd_old hab hkk hlk (by omega) (by omega) hLo hL'
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') (by omega) helig' hanch hmid'
        ?_ ?_
      · intro L' hL' hc'
        by_cases hLo : L' ∈ U.ids
        · exact hnocert L' (hlsOld L' hL' hLo)
            (certifiedIn_bnd_old hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hc')
        · exact not_certifiedIn_bnd_novel hab hAL.1 hAlo hAhi hkk (by omega) (by omega)
            hLo hc'
      · intro L' hL' hw'
        by_cases hLo : L' ∈ U.ids
        · exact hnoweak L' (hlsOld L' hL' hLo)
            (weakLinked_bnd_old hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hw')
        · exact absurd hw' (not_weakLinked_bnd_novel hab hAL.1 hAlo hAhi hkk (by omega)
            (by omega) hLo)

omit S in
/-- **Hydrozoan reads a band.** The property stated at the core's
schedule vocabulary, which `ofCoreSlots` carries into Hydrozoan's. -/
theorem banded : Banded (rule (Replica := Replica) (BlockId := BlockId)) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := ofCoreSlots S) hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' (ofCoreSlots S') U' V' k' hkd hsch hlead hab hV⟩

end Hydrozoan

end LeanDag
