import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.SafeSkip.Basic
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.Liveness
import LeanDag.GC.ChopDecided

/-!
# Garbage collection and crash recovery for Hydrozoan

Hydrozoan keeps its own universe record — blocks with an author and
parents, a DAG quorum `q`, non-equivocation for the non-Byzantine — so
it builds its own cut and its own fill on the shared data, as Nemo and
FinWhale do, and discharges its own invariants. What it reaches through
them is the generic theorems: verdict transport and agreement from
`Banded` and `Agree`, the liveness precondition from `hzSupport`.

This replaces `Integration/Hydrozoan/`, which reached the same cells by
carrying Hydrozoan universes into the core's and back (`toCore`,
`ofCore`, under a self-parent side condition) and then transporting
every rule predicate across the core's transformers one lemma at a
time. None of that is needed: the cut is `chopBlkHZ`, the fill is
`SkipData.copyBlock` at Hydrozoan's block type, and the invariants are
three clauses each.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {S : Slots Replica} {G d : ℕ}

/-! ## The cut -/

/-- One block of the truncation, at Hydrozoan's block type: the round
rebased by `−G`, and at or below the cut the parents dropped. -/
def chopBlkHZ (blk : BlockId → LeanDag.Hydrozoan.Block Replica BlockId) (G : ℕ) (i : BlockId) :
    LeanDag.Hydrozoan.Block Replica BlockId :=
  if (blk i).round ≤ G then ⟨(blk i).round - G, (blk i).author, ∅⟩
  else ⟨(blk i).round - G, (blk i).author, (blk i).parents⟩

variable {blk : BlockId → LeanDag.Hydrozoan.Block Replica BlockId} {i : BlockId}

@[simp] theorem chopBlkHZ_round : (chopBlkHZ blk G i).round = (blk i).round - G := by
  unfold chopBlkHZ; split <;> rfl

@[simp] theorem chopBlkHZ_author : (chopBlkHZ blk G i).author = (blk i).author := by
  unfold chopBlkHZ; split <;> rfl

theorem chopBlkHZ_parents_of_le (h : (blk i).round ≤ G) : (chopBlkHZ blk G i).parents = ∅ := by
  unfold chopBlkHZ; rw [if_pos h]

theorem chopBlkHZ_parents_of_lt (h : G < (blk i).round) :
    (chopBlkHZ blk G i).parents = (blk i).parents := by
  unfold chopBlkHZ; rw [if_neg (by omega)]

theorem authorsOf_chopBlkHZ (s : Finset BlockId) :
    LeanDag.Hydrozoan.authorsOf (chopBlkHZ blk G) s = LeanDag.Hydrozoan.authorsOf blk s :=
  Finset.image_congr fun i _ => chopBlkHZ_author

/-- **The cut, at Hydrozoan's universe.** -/
def chopHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlkHZ U.block G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlkHZ_parents_of_lt h] at hj
      have := (U.valid i hi.1).predecessor j hj
      exact Finset.mem_filter.mpr ⟨U.complete i hi.1 j hj, by omega⟩
    · rw [chopBlkHZ_parents_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hv := U.valid i hi.1
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · refine ⟨?_, ?_, ?_⟩
      · intro j hj
        rw [chopBlkHZ_parents_of_lt h] at hj
        have := hv.predecessor j hj
        rw [chopBlkHZ_round, chopBlkHZ_round]
        omega
      · intro a ha b hb hab
        rw [chopBlkHZ_parents_of_lt h] at ha hb
        rw [chopBlkHZ_author, chopBlkHZ_author] at hab
        exact hv.distinct_authors a ha b hb hab
      · intro _
        have hcr : LeanDag.Hydrozoan.authors (chopBlkHZ U.block G) (chopBlkHZ U.block G i) =
            LeanDag.Hydrozoan.authors U.block (U.block i) := by
          unfold LeanDag.Hydrozoan.authors
          rw [chopBlkHZ_parents_of_lt h, authorsOf_chopBlkHZ]
        rw [hcr]
        exact hv.quorum (by omega)
    · refine ⟨?_, ?_, ?_⟩
      · intro j hj
        rw [chopBlkHZ_parents_of_le h] at hj
        exact absurd hj (Finset.notMem_empty j)
      · intro a ha
        rw [chopBlkHZ_parents_of_le h] at ha
        exact absurd ha (Finset.notMem_empty a)
      · intro hr
        rw [chopBlkHZ_round] at hr
        omega
  no_equivocation := by
    intro i hi j hj hib hcc hrr
    rw [Finset.mem_filter] at hi hj
    rw [chopBlkHZ_author] at hib hcc
    rw [chopBlkHZ_author] at hcc
    rw [chopBlkHZ_round, chopBlkHZ_round] at hrr
    exact U.no_equivocation i hi.1 j hj.1 hib hcc (by omega)

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

@[simp] theorem mem_chopHZ_ids {i : BlockId} :
    i ∈ (chopHZ U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  Finset.mem_filter

@[simp] theorem chopHZ_block : (chopHZ U G).block = chopBlkHZ U.block G := rfl

/-- The truncated view: keep what clears the cut. -/
def chopViewHZ (V : LeanDag.Hydrozoan.View U) (G : ℕ) : LeanDag.Hydrozoan.View (chopHZ U G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chopHZ_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    have hj' : j ∈ (chopBlkHZ U.block G i).parents := hj
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlkHZ_parents_of_lt h] at hj'
      have := (U.valid i (V.subset_ids hi.1)).predecessor j hj'
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj', by omega⟩
    · rw [chopBlkHZ_parents_of_le h] at hj'
      exact absurd hj' (Finset.notMem_empty j)

/-- **The cut is a truncation of Hydrozoan's carrier.** -/
theorem truncates_chop_hz (hd : G ≤ S.slotRound d) :
    Truncates (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U (chopHZ U G) S (S.chop G d hd) G d where
  mem := fun b => by
    show (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chopHZ U G).ids ∧ G ≤ (chopBlkHZ U.block G b).round + G)
    rw [mem_chopHZ_ids, chopBlkHZ_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by
    have hr' : G ≤ (U.block b).round := hr
    show (chopBlkHZ U.block G b).round + G = (U.block b).round
    rw [chopBlkHZ_round]; omega
  creator := fun b _ _ => by
    show (chopBlkHZ U.block G b).author = (U.block b).author
    rw [chopBlkHZ_author]
  refs := fun b _ hr => by
    have hr' : G < (U.block b).round := hr
    show (chopBlkHZ U.block G b).parents = (U.block b).parents
    exact chopBlkHZ_parents_of_lt hr'
  slotRound := fun k => by
    have := horizon_le_slotRound hd k
    show S.slotRound (d + k) - G + G = S.slotRound (d + k)
    omega
  leader := fun _ => rfl
  base := hd

/-- **The chopped view agrees with the original above the cut.** -/
theorem viewAgreeAbove_chop_hz {V : LeanDag.Hydrozoan.View U} :
    ViewAgreeAbove (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      V (chopViewHZ V G) G :=
  fun b _ hr => by
    show b ∈ V.ids ↔ b ∈ V.ids.filter fun i => G ≤ (U.block i).round
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **Verdict transport across the cut, for Hydrozoan.** -/
theorem decided_chop_iff_hz (hd : G ≤ S.slotRound d) {V : LeanDag.Hydrozoan.View U}
    {k : ℕ} {v : Option BlockId} :
    (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V (d + k) v ↔
      (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided
        (S.chop G d hd) (chopViewHZ V G) k v :=
  LocalTruncate.of_banded LeanDag.Hydrozoan.banded
    S (S.chop G d hd) U (chopHZ U G) G d (truncates_chop_hz hd) V (chopViewHZ V G)
    viewAgreeAbove_chop_hz k v

/-- **And cross-cut agreement.** -/
theorem decided_agree_chop_hz (hd : G ≤ S.slotRound d)
    {W : LeanDag.Hydrozoan.View (chopHZ U G)} {V : LeanDag.Hydrozoan.View U}
    {k : ℕ} {w v : Option BlockId}
    (hW : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided
      (S.chop G d hd) W k w)
    (hV : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided
      S V (d + k) v) : w = v :=
  decided_agree_truncate LeanDag.Hydrozoan.agree
    (LocalTruncate.of_banded LeanDag.Hydrozoan.banded)
    (truncates_chop_hz hd) viewAgreeAbove_chop_hz hW hV

/-! ## The fill -/

/-- A Hydrozoan universe's blocks, read as core blocks with no payload —
the shape a Safe Skip message is stated over. -/
def hzBlk (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    BlockId → Block Replica BlockId Unit :=
  fun i => LeanDag.Hydrozoan.adaptBlock (U.block i)

theorem hzBlk_round (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (i : BlockId) :
    (hzBlk U i).round = (U.block i).round := rfl

/-- **The copy fill, at Hydrozoan's universe.** One block per gap round,
by the recovering replica, carrying the donor's parents at that round. -/
def copyFillHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (sk : SkipData U.ids (hzBlk U)) : LeanDag.Hydrozoan.BlockUniverse Replica BlockId where
  ids := U.ids ∪ sk.freshIds
  block b := if b ∈ U.ids then U.block b
    else ⟨sk.idx b, sk.v1, (U.block (sk.line (sk.idx b))).parents⟩
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho] at hj
      exact Finset.mem_union_left _ (U.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hj
      exact Finset.mem_union_left _
        (U.complete _ (sk.hline_mem k (by omega) hk2) j hj)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho]
      have hv := U.valid i ho
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (U.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro a ha b hb hab
        rw [if_pos (U.complete i ho a ha), if_pos (U.complete i ho b hb)] at hab
        exact hv.distinct_authors a ha b hb hab
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold LeanDag.Hydrozoan.authors LeanDag.Hydrozoan.authorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete i ho j hj)]
        exact hjc
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_neg (sk.hfresh_new k), sk.hidx]
      have hlm := sk.hline_mem k (by omega) hk2
      have hlv := U.valid _ hlm
      have hlr : (U.block (sk.line k)).round = k := sk.hline_round k (by omega) hk2
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        simp only at hj ⊢
        rw [if_pos (U.complete _ hlm j hj)]
        have := hlv.predecessor j hj
        omega
      · intro a ha b hb hab
        simp only at ha hb
        rw [if_pos (U.complete _ hlm a ha), if_pos (U.complete _ hlm b hb)] at hab
        exact hlv.distinct_authors a ha b hb hab
      · intro _
        have hq := hlv.quorum (by omega)
        refine le_trans hq (Finset.card_le_card ?_)
        intro c hc
        unfold LeanDag.Hydrozoan.authors LeanDag.Hydrozoan.authorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete _ hlm j hj)]
        exact hjc
  no_equivocation := by
    intro i hi j hj hib hcc hrr
    rcases Finset.mem_union.mp hi with ho | hf <;>
      rcases Finset.mem_union.mp hj with ho' | hf'
    · rw [if_pos ho] at hib hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact U.no_equivocation i ho j ho' hib hcc hrr
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_pos ho] at hcc hrr
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      have hi := hzBlk_round U i
      exact (sk.hgap i ho hcc (by simp only at hrr; omega) (by simp only at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      rw [if_pos ho'] at hcc hrr
      have hj := hzBlk_round U j
      exact (sk.hgap j ho' hcc.symm (by simp only at hrr; omega)
        (by simp only at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hrr
      rw [if_neg (sk.hfresh_new l), sk.hidx] at hrr
      simp only at hrr
      exact hrr ▸ rfl

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {sk : SkipData U.ids (hzBlk U)}

@[simp] theorem copyFillHZ_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (copyFillHZ U sk).block b = U.block b := if_pos hb

@[simp] theorem copyFillHZ_block_fresh {k : ℕ} :
    (copyFillHZ U sk).block (sk.fresh k) =
      ⟨k, sk.v1, (U.block (sk.line k)).parents⟩ := by
  simp only [copyFillHZ, if_neg (sk.hfresh_new k), sk.hidx]

/-- An old block's parents are old. -/
theorem copyFillHZ_parents_old {b : BlockId} (hb : b ∈ U.ids) :
    ∀ j ∈ ((copyFillHZ U sk).block b).parents, j ∈ U.ids := by
  rw [copyFillHZ_block_old hb]
  exact U.complete b hb

/-- **The fill is an extension of Hydrozoan's carrier.** -/
theorem extends_copyFillHZ {sk : SkipData U.ids (hzBlk U)} :
    Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U (copyFillHZ U sk) where
  subset := fun _ h => Finset.mem_union_left _ h
  block := fun b hb => by
    show LeanDag.Hydrozoan.adaptBlock ((copyFillHZ U sk).block b) =
      LeanDag.Hydrozoan.adaptBlock (U.block b)
    rw [copyFillHZ_block_old hb]

/-- **What the fill sustains**: from the top of its gap. -/
theorem sustains_copyFillHZ {sk : SkipData U.ids (hzBlk U)} :
    Sustains (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U (copyFillHZ U sk) 0 (sk.r + 1) where
  mem := fun b => by
    show (b ∈ U.ids ∧ sk.r + 1 ≤ (U.block b).round) ↔
      (b ∈ (copyFillHZ U sk).ids ∧ sk.r + 1 ≤ ((copyFillHZ U sk).block b).round + 0)
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨Finset.mem_union_left _ hb, by rw [copyFillHZ_block_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      have hbU : b ∈ U.ids := by
        rcases Finset.mem_union.mp hb with ho | hfr
        · exact ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr
          rw [copyFillHZ_block_fresh] at hr
          simp only at hr
          omega
      exact ⟨hbU, by rw [copyFillHZ_block_old hbU] at hr; omega⟩
  round := fun b hb _ => by
    show ((copyFillHZ U sk).block b).round + 0 = (U.block b).round
    rw [copyFillHZ_block_old hb]; omega
  creator := fun b hb _ => by
    show ((copyFillHZ U sk).block b).author = (U.block b).author
    rw [copyFillHZ_block_old hb]
  refs := fun b hb _ => by
    show ((copyFillHZ U sk).block b).parents = (U.block b).parents
    rw [copyFillHZ_block_old hb]

/-- **Verdicts survive the recovery, for Hydrozoan.** -/
theorem decided_copyFillHZ {sk : SkipData U.ids (hzBlk U)} (S : Slots Replica)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View (copyFillHZ U sk)}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {u : Option BlockId}
    (h : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V k u) :
    (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V' k u :=
  Persist.of_banded LeanDag.Hydrozoan.banded S U _ extends_copyFillHZ V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_copyFillHZ {sk : SkipData U.ids (hzBlk U)} (S : Slots Replica)
    {V : LeanDag.Hydrozoan.View U} {V' V'' : LeanDag.Hydrozoan.View (copyFillHZ U sk)}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {u u' : Option BlockId}
    (h : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V k u)
    (h' : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V'' k u') :
    u = u' :=
  decided_agree_extends LeanDag.Hydrozoan.agree (Persist.of_banded LeanDag.Hydrozoan.banded)
    extends_copyFillHZ (V' := V') hsub h h'

end Integration

end LeanDag
