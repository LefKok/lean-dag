import LeanDag.Hydrozoan.Helpers.Locality
import LeanDag.Properties.Truncate

/-!
# Hydrozoan's rules across a truncation

Not part of the audit surface. The transfer lemmas
`Properties.LocalTruncate` needs of this protocol: a truncation prunes
below a horizon **and** renumbers what remains from it, and every
predicate Hydrozoan reads moves by the horizon exactly once.

**The guards read cleanly in the truncation's own numbering.** A block
of the truncation at round `m` sits at round `m + G` in the original, so
the horizon guard `G < round` becomes `0 < m`: the block is not in the
retained bottom layer. A certificate counts votes cast by its own
parents, so it needs `1 < m`. Both are supplied at every use site —
votes sit one round above a slot and certificates two, so in the
truncation's numbering they are at `slotRound k + 1 ≥ 1` and
`slotRound k + 2 ≥ 2`.

**The dead end, kept as a record.** `no_base_of_naive_shift` below is
why this file states one relation rather than two. A *pure* renumbering
— every block kept, every round lower by `G` — puts the bottom layer at
round zero carrying the references it had at round `G`, and validity
allows a round-zero block none. Any non-empty valid universe has a
round-zero block, by descending the predecessor condition from any block
at all. So a pure shift by a positive horizon has no non-empty model,
and a property quantified over such shifts is vacuous. Only the
combination below has models.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {S S' : LeanDag.Hydrozoan.Slots Replica} {G d : ℕ}

/-! ## The dead end -/

/-- A pure renumbering: every block kept, every round lower by `G`. -/
structure NaiveShift (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    Prop where
  mem : ∀ b, b ∈ U.ids ↔ b ∈ U'.ids
  round : ∀ b, b ∈ U.ids → (U'.block b).round + G = (U.block b).round
  parents : ∀ b, b ∈ U.ids → (U'.block b).parents = (U.block b).parents

/-- A block at round zero has no parents: the predecessor condition is
unsatisfiable there. -/
theorem parents_empty_of_round_zero {b : BlockId} (hb : b ∈ U.ids)
    (hr : (U.block b).round = 0) : (U.block b).parents = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have := (U.valid b hb).predecessor j hj
  omega

/-- **A pure shift by a positive horizon admits no round-zero block**,
and a non-empty valid universe must have one. So the naive factoring of
a truncation into a restriction and a renumbering has no models, and a
property quantified over it is vacuously true. -/
theorem no_base_of_naive_shift (h : NaiveShift U U' G) (hG : 0 < G)
    (hq : 0 < LeanDag.Hydrozoan.q Replica)
    (b : BlockId) (hb : b ∈ U'.ids) : (U'.block b).round ≠ 0 := by
  intro hr
  have hbU : b ∈ U.ids := (h.mem b).mpr hb
  have hround : (U.block b).round = G := by have := h.round b hbU; omega
  have hparU : (U.block b).parents = ∅ := by
    rw [← h.parents b hbU]; exact parents_empty_of_round_zero hb hr
  have hqq := (U.valid b hbU).quorum (by omega)
  simp only [LeanDag.Hydrozoan.authors, LeanDag.Hydrozoan.authorsOf, hparU,
    Finset.image_empty, Finset.card_empty, Nat.le_zero] at hqq
  omega

/-! ## The relation that does have models -/

/-- The truncation, in Hydrozoan's vocabulary. -/
structure TruncatesHZ (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (S S' : LeanDag.Hydrozoan.Slots Replica) (G d : ℕ) : Prop where
  mem : ∀ b, b ∈ U'.ids ↔ (b ∈ U.ids ∧ G ≤ (U.block b).round)
  round : ∀ b, b ∈ U'.ids → (U'.block b).round + G = (U.block b).round
  author : ∀ b, b ∈ U'.ids → (U'.block b).author = (U.block b).author
  parents : ∀ b, b ∈ U'.ids → 0 < (U'.block b).round →
    (U'.block b).parents = (U.block b).parents
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  leader : ∀ k, S'.leader k = S.leader (d + k)
  base : G ≤ S.slotRound d

namespace TruncatesHZ

theorem memU (h : TruncatesHZ U U' S S' G d) {b : BlockId} (hb : b ∈ U'.ids) :
    b ∈ U.ids := ((h.mem b).mp hb).1

theorem roundU (h : TruncatesHZ U U' S S' G d) {b : BlockId} (hb : b ∈ U'.ids) :
    (U.block b).round = (U'.block b).round + G := (h.round b hb).symm

/-- Blocks of the truncation at round `n` are the original's at `n + G`. -/
theorem blocksAt_eq (h : TruncatesHZ U U' S S' G d) (n : ℕ) :
    LeanDag.Hydrozoan.blocksAt U' n = LeanDag.Hydrozoan.blocksAt U (n + G) := by
  ext b
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hbr⟩
    exact ⟨h.memU hb, by have := h.round b hb; omega⟩
  · rintro ⟨hb, hbr⟩
    have hb' : b ∈ U'.ids := (h.mem b).mpr ⟨hb, by omega⟩
    exact ⟨hb', by have := h.round b hb'; omega⟩

theorem isVote_eq (h : TruncatesHZ U U' S S' G d) {b L : BlockId}
    (hb : b ∈ U'.ids) (hm : 0 < (U'.block b).round) :
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote; rw [h.parents b hb hm]

theorem authorsOf_eq (h : TruncatesHZ U U' S S' G d) {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U'.ids) :
    LeanDag.Hydrozoan.authorsOf U'.block s = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i hi => h.author i (hs i hi)

/-- Causal history inside the truncation is the history it was. A path
descends one round at a time, so every block on it but the last sits
above the retained layer, which is where references still agree. -/
theorem reaches_of (h : TruncatesHZ U U' S S' G d) {A : BlockId} (hA : A ∈ U'.ids) :
    ∀ {C : BlockId}, LeanDag.Hydrozoan.Reaches U' A C → LeanDag.Hydrozoan.Reaches U A C := by
  intro C hre
  induction hre with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hAb hstep ih =>
      have hb : b ∈ U'.ids := (causal U').mem_ids_of_reaches hA hAb
      have hstep' : c ∈ (U'.block b).parents := hstep
      have hbpos : 0 < (U'.block b).round := by
        by_contra hz
        have : (U'.block b).parents = ∅ :=
          parents_empty_of_round_zero hb (by omega)
        rw [this] at hstep'; exact absurd hstep' (Finset.notMem_empty _)
      refine ih.tail ?_
      show c ∈ (U.block b).parents
      rw [← h.parents b hb hbpos]; exact hstep'

theorem reaches_to (h : TruncatesHZ U U' S S' G d) {A : BlockId} (hA : A ∈ U'.ids) :
    ∀ {C : BlockId}, LeanDag.Hydrozoan.Reaches U A C → G ≤ (U.block C).round →
      LeanDag.Hydrozoan.Reaches U' A C := by
  intro C hre
  induction hre with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hAb hstep ih =>
      intro hcr
      have hbU : b ∈ U.ids := (causal U).mem_ids_of_reaches (h.memU hA) hAb
      have hstep' : c ∈ (U.block b).parents := hstep
      have hbr := (U.valid b hbU).predecessor c hstep'
      have hb' : b ∈ U'.ids := (h.mem b).mpr ⟨hbU, by omega⟩
      have hpos : 0 < (U'.block b).round := by have := h.round b hb'; omega
      refine (ih (by omega)).tail ?_
      show c ∈ (U'.block b).parents
      rw [h.parents b hb' hpos]
      exact hstep'

theorem reaches_eq (h : TruncatesHZ U U' S S' G d) {A C : BlockId}
    (hA : A ∈ U'.ids) (hC : G ≤ (U.block C).round) :
    LeanDag.Hydrozoan.Reaches U' A C ↔ LeanDag.Hydrozoan.Reaches U A C :=
  ⟨h.reaches_of hA, fun hre => h.reaches_to hA hre hC⟩

/-! ## The slot's candidates, and the schedule -/

theorem isLeaderBlock_eq (h : TruncatesHZ U U' S S' G d) {k : ℕ} {L : BlockId} :
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S' U' k L
      ↔ @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U (d + k) L := by
  have hs := h.slotRound k
  constructor
  · rintro ⟨hm, hr, ha⟩
    refine ⟨h.memU hm, ?_, ?_⟩
    · have := h.round L hm; omega
    · rw [← h.author L hm, ha, h.leader k]
  · rintro ⟨hm, hr, ha⟩
    have hm' : L ∈ U'.ids := (h.mem L).mpr ⟨hm, by omega⟩
    refine ⟨hm', ?_, ?_⟩
    · have := h.round L hm'; omega
    · rw [h.author L hm', ha, ← h.leader k]

theorem eligible_eq (h : TruncatesHZ U U' S S' G d) {k j : ℕ} :
    @LeanDag.Hydrozoan.EligibleAsAnchor Replica S' k j
      ↔ @LeanDag.Hydrozoan.EligibleAsAnchor Replica S (d + k) (d + j) := by
  unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound
  have hk := h.slotRound k
  have hj := h.slotRound j
  omega

/-! ## The counting rules -/

theorem supportersInView_eq (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) (L : BlockId) {m : ℕ} (hm : 0 < m) :
    LeanDag.Hydrozoan.supportersInView U' V' L m
      = LeanDag.Hydrozoan.supportersInView U V L (m + G) := by
  have hset : ((LeanDag.Hydrozoan.blocksAt U' m).filter
        fun b => LeanDag.Hydrozoan.IsVote U' b L) ∩ V'.ids
      = ((LeanDag.Hydrozoan.blocksAt U (m + G)).filter
        fun b => LeanDag.Hydrozoan.IsVote U b L) ∩ V.ids := by
    ext b
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hbA, hbv⟩, hbV⟩
      have hb' : b ∈ U'.ids := (Finset.mem_filter.mp hbA).1
      have hbrd : (U'.block b).round = m := (Finset.mem_filter.mp hbA).2
      refine ⟨⟨by rw [← h.blocksAt_eq]; exact hbA, ?_⟩, (hv b hb').mp hbV⟩
      exact (h.isVote_eq hb' (by omega)).mp hbv
    · rintro ⟨⟨hbA, hbv⟩, hbV⟩
      rw [← h.blocksAt_eq] at hbA
      have hb' : b ∈ U'.ids := (Finset.mem_filter.mp hbA).1
      have hbrd : (U'.block b).round = m := (Finset.mem_filter.mp hbA).2
      refine ⟨⟨hbA, ?_⟩, (hv b hb').mpr hbV⟩
      exact (h.isVote_eq hb' (by omega)).mpr hbv
  unfold LeanDag.Hydrozoan.supportersInView
  rw [hset]
  refine h.authorsOf_eq ?_
  intro b hb
  rw [← h.blocksAt_eq] at hb
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).1).1

theorem voteBlocks_eq (h : TruncatesHZ U U' S S' G d) {C L : BlockId}
    (hC : C ∈ U'.ids) (hCm : 1 < (U'.block C).round) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [h.parents C hC (by omega)]
  refine Finset.filter_congr fun b hb => ?_
  have hbU : b ∈ U.ids := U.complete C (h.memU hC) b hb
  have hbr := (U.valid C (h.memU hC)).predecessor b hb
  have hCr := h.round C hC
  have hb' : b ∈ U'.ids := (h.mem b).mpr ⟨hbU, by omega⟩
  simpa using h.isVote_eq hb' (by have := h.round b hb'; omega)

theorem isCertificate_eq (h : TruncatesHZ U U' S S' G d) {C L : BlockId}
    (hC : C ∈ U'.ids) (hCm : 1 < (U'.block C).round) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [h.voteBlocks_eq hC hCm, h.authorsOf_eq]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  have hbU : b ∈ U.ids := U.complete C (h.memU hC) b hbp
  have hbr := (U.valid C (h.memU hC)).predecessor b hbp
  have hCr := h.round C hC
  exact (h.mem b).mpr ⟨hbU, by omega⟩

theorem certificates_eq (h : TruncatesHZ U U' S S' G d) {L : BlockId} (n : ℕ) :
    LeanDag.Hydrozoan.certificates U' L n = LeanDag.Hydrozoan.certificates U L (n + G) := by
  unfold LeanDag.Hydrozoan.certificates
  have harg : n + 2 + G = n + G + 2 := by omega
  rw [h.blocksAt_eq (n + 2), harg]
  refine Finset.filter_congr fun C hC => ?_
  rw [← harg, ← h.blocksAt_eq] at hC
  have hC' : C ∈ U'.ids := (Finset.mem_filter.mp hC).1
  have hCr : (U'.block C).round = n + 2 := (Finset.mem_filter.mp hC).2
  simpa using (h.isCertificate_eq hC' (by omega))

theorem certifiersInView_eq (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) (L : BlockId) (n : ℕ) :
    LeanDag.Hydrozoan.certifiersInView U' V' L n
      = LeanDag.Hydrozoan.certifiersInView U V L (n + G) := by
  have hmemC : ∀ C, C ∈ LeanDag.Hydrozoan.certificates U' L n → C ∈ U'.ids := by
    intro C hC
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1
  have hset : LeanDag.Hydrozoan.certificates U' L n ∩ V'.ids
      = LeanDag.Hydrozoan.certificates U L (n + G) ∩ V.ids := by
    ext C
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hCc, hCV⟩
      exact ⟨by rw [← h.certificates_eq]; exact hCc, (hv C (hmemC C hCc)).mp hCV⟩
    · rintro ⟨hCc, hCV⟩
      rw [← h.certificates_eq] at hCc
      exact ⟨hCc, (hv C (hmemC C hCc)).mpr hCV⟩
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
  rw [hset]
  refine h.authorsOf_eq ?_
  intro C hC
  obtain ⟨hCc, -⟩ := Finset.mem_inter.mp hC
  rw [← h.certificates_eq] at hCc
  exact hmemC C hCc

theorem blamesInView_eq (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) (k : ℕ) :
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
    have hb' : b ∈ U'.ids := (Finset.mem_filter.mp hbA).1
    have hbrd : (U'.block b).round
        = LeanDag.Hydrozoan.votingRound Replica (S := S') k :=
      (Finset.mem_filter.mp hbA).2
    rw [h.blocksAt_eq, hvr] at hbA
    refine ⟨b, ⟨⟨hbA, ?_⟩, (hv b hb').mp hbV⟩, (h.author b hb').symm⟩
    intro j hj hL
    rw [← h.parents b hb' (by unfold LeanDag.Hydrozoan.votingRound at hbrd; omega)] at hj
    exact hbl j hj (h.isLeaderBlock_eq.mpr hL)
  · rintro ⟨b, ⟨⟨hbA, hbl⟩, hbV⟩, rfl⟩
    rw [← hvr, ← h.blocksAt_eq] at hbA
    have hb' : b ∈ U'.ids := (Finset.mem_filter.mp hbA).1
    have hbrd : (U'.block b).round
        = LeanDag.Hydrozoan.votingRound Replica (S := S') k :=
      (Finset.mem_filter.mp hbA).2
    refine ⟨b, ⟨⟨hbA, ?_⟩, (hv b hb').mpr hbV⟩, h.author b hb'⟩
    intro j hj hL
    rw [h.parents b hb' (by unfold LeanDag.Hydrozoan.votingRound at hbrd; omega)] at hj
    exact hbl j hj (h.isLeaderBlock_eq.mp hL)

/-! ## The rung tests -/

theorem certifiedIn_eq (h : TruncatesHZ U U' S S' G d) {A L : BlockId}
    (hA : A ∈ U'.ids) (n : ℕ) :
    LeanDag.Hydrozoan.CertifiedIn U' A L n
      ↔ LeanDag.Hydrozoan.CertifiedIn U A L (n + G) := by
  unfold LeanDag.Hydrozoan.CertifiedIn
  rw [h.certificates_eq n]
  constructor
  · rintro ⟨C, hC, hre⟩
    exact ⟨C, hC, h.reaches_of hA hre⟩
  · rintro ⟨C, hC, hre⟩
    have hCr : (U.block C).round = n + G + 2 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
    exact ⟨C, hC, h.reaches_to hA hre (by omega)⟩

theorem weakLinked_eq (h : TruncatesHZ U U' S S' G d) {A L : BlockId}
    (hA : A ∈ U'.ids) (n : ℕ) :
    LeanDag.Hydrozoan.WeakLinked U' A L n
      ↔ LeanDag.Hydrozoan.WeakLinked U A L (n + G) := by
  unfold LeanDag.Hydrozoan.WeakLinked
  have harg : n + 1 + G = n + G + 1 := by omega
  constructor
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U'.ids := fun b hb =>
      (Finset.mem_filter.mp (hs b hb).1).1
    refine ⟨s, fun b hb => ?_, by rw [← h.authorsOf_eq hsU]; exact hcard⟩
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    have hb' := hsU b hb
    have hbrd : (U'.block b).round = n + 1 := (Finset.mem_filter.mp hbA).2
    rw [h.blocksAt_eq, harg] at hbA
    exact ⟨hbA, (h.isVote_eq hb' (by omega)).mp hbv, h.reaches_of hA hbre⟩
  · rintro ⟨s, hs, hcard⟩
    have hsU : ∀ b ∈ s, b ∈ U'.ids := by
      intro b hb
      have := (hs b hb).1
      rw [← harg, ← h.blocksAt_eq] at this
      exact (Finset.mem_filter.mp this).1
    refine ⟨s, fun b hb => ?_, by rw [h.authorsOf_eq hsU]; exact hcard⟩
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    have hb' := hsU b hb
    have hbA' : b ∈ LeanDag.Hydrozoan.blocksAt U' (n + 1) := by
      rw [h.blocksAt_eq, harg]; exact hbA
    have hbrd : (U'.block b).round = n + 1 := (Finset.mem_filter.mp hbA').2
    have hbr : (U.block b).round = n + G + 1 := (Finset.mem_filter.mp hbA).2
    exact ⟨hbA', (h.isVote_eq hb' (by omega)).mpr hbv,
      h.reaches_to hA hbre (by omega)⟩

/-! ## The three direct rules -/

theorem fastCommitInView_eq (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) (L : BlockId) (k : ℕ) :
    LeanDag.Hydrozoan.FastCommitInView U' V' L (S'.slotRound k)
      ↔ LeanDag.Hydrozoan.FastCommitInView U V L (S.slotRound (d + k)) := by
  unfold LeanDag.Hydrozoan.FastCommitInView
  rw [h.supportersInView_eq hv L (show 0 < S'.slotRound k + 1 by omega)]
  have := h.slotRound k
  have harg : S'.slotRound k + 1 + G = S.slotRound (d + k) + 1 := by omega
  rw [harg]

theorem slowCommitInView_eq (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) (L : BlockId) (k : ℕ) :
    LeanDag.Hydrozoan.SlowCommitInView U' V' L (S'.slotRound k)
      ↔ LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound (d + k)) := by
  unfold LeanDag.Hydrozoan.SlowCommitInView
  rw [h.certifiersInView_eq hv L (S'.slotRound k), h.slotRound k]

theorem skippedLeaderInView_eq (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) (k : ℕ) :
    @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S' U' V' k
      ↔ @LeanDag.Hydrozoan.SkippedLeaderInView _ _ _ _ _ _ S U V (d + k) := by
  simp [LeanDag.Hydrozoan.SkippedLeaderInView, h.blamesInView_eq hv]

/-! ## Truncation invariance, both ways -/

/-- The anchor of a derivation lies above the base slot, hence above the
horizon, hence survives the cut. -/
theorem anchor_mem (h : TruncatesHZ U U' S S' G d) {j : ℕ} {A : BlockId}
    (hA : @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ S U (d + j) A) : A ∈ U'.ids := by
  refine (h.mem A).mpr ⟨hA.1, ?_⟩
  have hmono : S.slotRound d ≤ S.slotRound (d + j) := S.mono (Nat.le_add_right d j)
  have := h.base
  rw [hA.2.1]; omega

theorem decided_to (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) {n : ℕ} {v : Option BlockId}
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
      have hA := h.anchor_mem (LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hanchor)
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := S') (by omega)
        (h.eligible_eq.mpr helig) (ihj j' rfl) ?_ (h.isLeaderBlock_eq.mpr hL)
        ((h.certifiedIn_eq hA _).mpr (by rw [h.slotRound k]; exact hcert))
      intro i' h1 h2 he
      exact ihmid (d + i') (by omega) (by omega) (h.eligible_eq.mp he) i' rfl
  | @indirectWeak n j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA := h.anchor_mem (LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hanchor)
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') (by omega)
        (h.eligible_eq.mpr helig) (ihj j' rfl) ?_ ?_ (h.isLeaderBlock_eq.mpr hL)
        ((h.weakLinked_eq hA _).mpr (by rw [h.slotRound k]; exact hweak)) ?_
      · intro i' h1 h2 he
        exact ihmid (d + i') (by omega) (by omega) (h.eligible_eq.mp he) i' rfl
      · intro L' hL' hc
        refine hnocert L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]; exact (h.certifiedIn_eq hA _).mp hc
      · intro L' hL' hw
        refine hmin L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]; exact (h.weakLinked_eq hA _).mp hw
  | @indirectSkip n j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA := h.anchor_mem (LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hanchor)
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') (by omega)
        (h.eligible_eq.mpr helig) (ihj j' rfl) ?_ ?_ ?_
      · intro i' h1 h2 he
        exact ihmid (d + i') (by omega) (by omega) (h.eligible_eq.mp he) i' rfl
      · intro L' hL' hc
        refine hnocert L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]; exact (h.certifiedIn_eq hA _).mp hc
      · intro L' hL' hw
        refine hnoweak L' (h.isLeaderBlock_eq.mp hL') ?_
        rw [← h.slotRound k]; exact (h.weakLinked_eq hA _).mp hw

theorem decided_from (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) {k : ℕ} {v : Option BlockId}
    (hd : @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S' U' V' k v) :
    @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S U V (d + k) v := by
  induction hd with
  | @directFast k L hL hc =>
      exact LeanDag.Hydrozoan.Decided.directFast (S := S) (h.isLeaderBlock_eq.mp hL)
        ((h.fastCommitInView_eq hv L k).mp hc)
  | @directSlow k L hL hc =>
      exact LeanDag.Hydrozoan.Decided.directSlow (S := S) (h.isLeaderBlock_eq.mp hL)
        ((h.slowCommitInView_eq hv L k).mp hc)
  | @directSkip k hs =>
      exact LeanDag.Hydrozoan.Decided.directSkip (S := S)
        ((h.skippedLeaderInView_eq hv k).mp hs)
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      have hA := (LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S') hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := S) (by omega)
        (h.eligible_eq.mp helig) ihj ?_ (h.isLeaderBlock_eq.mp hL) ?_
      · intro i h1 h2 he
        obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
        exact ihmid i' (by omega) (by omega) (h.eligible_eq.mpr he)
      · rw [← h.slotRound k]; exact (h.certifiedIn_eq hA _).mp hcert
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      have hA := (LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S') hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S) (by omega)
        (h.eligible_eq.mp helig) ihj ?_ ?_ (h.isLeaderBlock_eq.mp hL) ?_ ?_
      · intro i h1 h2 he
        obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
        exact ihmid i' (by omega) (by omega) (h.eligible_eq.mpr he)
      · intro L' hL' hc
        refine hnocert L' (h.isLeaderBlock_eq.mpr hL') ?_
        refine (h.certifiedIn_eq hA _).mpr ?_
        rw [h.slotRound k]; exact hc
      · rw [← h.slotRound k]; exact (h.weakLinked_eq hA _).mp hweak
      · intro L' hL' hw
        refine hmin L' (h.isLeaderBlock_eq.mpr hL') ?_
        refine (h.weakLinked_eq hA _).mpr ?_
        rw [h.slotRound k]; exact hw
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      have hA := (LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S') hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S) (by omega)
        (h.eligible_eq.mp helig) ihj ?_ ?_ ?_
      · intro i h1 h2 he
        obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
        exact ihmid i' (by omega) (by omega) (h.eligible_eq.mpr he)
      · intro L' hL' hc
        refine hnocert L' (h.isLeaderBlock_eq.mpr hL') ?_
        refine (h.certifiedIn_eq hA _).mpr ?_
        rw [h.slotRound k]; exact hc
      · intro L' hL' hw
        refine hnoweak L' (h.isLeaderBlock_eq.mpr hL') ?_
        refine (h.weakLinked_eq hA _).mpr ?_
        rw [h.slotRound k]; exact hw

/-- **Truncation invariance for Hydrozoan.** -/
theorem decided_iff (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U'.ids → (b ∈ V'.ids ↔ b ∈ V.ids)) {k : ℕ} {v : Option BlockId} :
    @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S U V (d + k) v
      ↔ @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ S' U' V' k v :=
  ⟨fun hd => h.decided_to hv hd k rfl, fun hd => h.decided_from hv hd⟩

end TruncatesHZ

end Hydrozoan

end LeanDag
