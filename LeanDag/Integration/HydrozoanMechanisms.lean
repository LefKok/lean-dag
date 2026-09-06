import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Hydrozoan.Helpers.Skippability
import LeanDag.SafeSkip.Basic
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Extension
import LeanDag.GC.ChopDecided
import LeanDag.Hydrozoan.Helpers.Record

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

/-- One block of the truncation, at Hydrozoan's block type: the record's
cut, read through the adapter. -/
def chopBlkHZ (blk : BlockId → LeanDag.Hydrozoan.Block Replica BlockId) (G : ℕ) (i : BlockId) :
    LeanDag.Hydrozoan.Block Replica BlockId :=
  LeanDag.Hydrozoan.unadapt (chopBlk (fun j => LeanDag.Hydrozoan.adaptBlock (blk j)) G i)

variable {blk : BlockId → LeanDag.Hydrozoan.Block Replica BlockId} {i : BlockId}

@[simp] theorem chopBlkHZ_round : (chopBlkHZ blk G i).round = (blk i).round - G :=
  chopBlk_round

@[simp] theorem chopBlkHZ_author : (chopBlkHZ blk G i).author = (blk i).author :=
  chopBlk_creator

theorem chopBlkHZ_parents_of_le (h : (blk i).round ≤ G) : (chopBlkHZ blk G i).parents = ∅ :=
  chopBlk_refs_of_le h

theorem chopBlkHZ_parents_of_lt (h : G < (blk i).round) :
    (chopBlkHZ blk G i).parents = (blk i).parents :=
  chopBlk_refs_of_lt h

theorem authorsOf_chopBlkHZ (s : Finset BlockId) :
    LeanDag.Hydrozoan.authorsOf (chopBlkHZ blk G) s = LeanDag.Hydrozoan.authorsOf blk s :=
  Finset.image_congr fun i _ => chopBlkHZ_author

/-- **The cut, at Hydrozoan's universe**: the record's, through the
adapter. -/
def chopHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  LeanDag.Hydrozoan.onRecord.chop U G

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

@[simp] theorem mem_chopHZ_ids {i : BlockId} :
    i ∈ (chopHZ U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  BlockRecord.mem_chop_ids

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
      U (chopHZ U G) S (S.chop G d hd) G d :=
  LeanDag.Hydrozoan.onRecord.truncates_chop U hd

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

/-- **The copy fill, at Hydrozoan's universe**: the record's, through
the adapter. One block per gap round, by the recovering replica,
carrying the donor's parents at that round. -/
def copyFillHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (sk : SkipData U.ids (hzBlk U)) : LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  LeanDag.Hydrozoan.onRecord.copyFill U sk

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {sk : SkipData U.ids (hzBlk U)}

@[simp] theorem copyFillHZ_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (copyFillHZ U sk).block b = U.block b := by
  change LeanDag.Hydrozoan.unadapt (sk.fillMap _ b) = U.block b
  rw [SkipData.fillMap_old hb]; rfl

@[simp] theorem copyFillHZ_block_fresh {k : ℕ} :
    (copyFillHZ U sk).block (sk.fresh k) =
      ⟨k, sk.v1, (U.block (sk.line k)).parents⟩ := by
  change LeanDag.Hydrozoan.unadapt (sk.fillMap _ (sk.fresh k)) = _
  rw [SkipData.fillMap_fresh]; rfl

/-- An old block's parents are old. -/
theorem copyFillHZ_parents_old {b : BlockId} (hb : b ∈ U.ids) :
    ∀ j ∈ ((copyFillHZ U sk).block b).parents, j ∈ U.ids := by
  rw [copyFillHZ_block_old hb]
  exact U.complete b hb

/-- **The fill is an extension of Hydrozoan's carrier.** -/
theorem extends_copyFillHZ {sk : SkipData U.ids (hzBlk U)} :
    Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U (copyFillHZ U sk) :=
  LeanDag.Hydrozoan.onRecord.extends_copyFill U sk

/-- **The copy fill does not restore coverage either.** The generic
refutation at `extends_copyFillHZ`: a reliable set holding the
recovering replica is uncovered at every gap round, for the same reason
the fill is safe. -/
theorem not_synchronisedOn_copyFillHZ {sk : SkipData U.ids (hzBlk U)} {T : Finset Replica}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).author ∈ T) :
    ¬ Timed.SynchronisedOn (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      (copyFillHZ U sk) T R :=
  Timed.not_synchronisedOn_of_extends extends_copyFillHZ hk
    (f := sk.fresh k)
    ⟨Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩), sk.hfresh_new k⟩
    (by simp [copyFillHZ_block_fresh]) (by simpa [copyFillHZ_block_fresh] using hv1)
    hb hbround hbc

/-- **What the fill sustains**: from the top of its gap. -/
theorem sustains_copyFillHZ {sk : SkipData U.ids (hzBlk U)} :
    Sustains (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U (copyFillHZ U sk) 0 (sk.r + 1) :=
  LeanDag.Hydrozoan.onRecord.sustains_copyFill U sk

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

/-! ## Promptness: the fill cannot conjure a commit, for Hydrozoan -/

/-- The old view, read in the filled universe: the same ids, closed
because old blocks keep their parents. -/
def liftViewHZ (sk : SkipData U.ids (hzBlk U)) (V : LeanDag.Hydrozoan.View U) :
    LeanDag.Hydrozoan.View (copyFillHZ U sk) where
  ids := V.ids
  subset_ids := fun i hi => Finset.mem_union_left _ (V.subset_ids hi)
  complete := by
    intro i hi j hj
    have hj' : j ∈ ((copyFillHZ U sk).block i).parents := hj
    rw [copyFillHZ_block_old (V.subset_ids hi)] at hj'
    exact V.complete i hi j hj'

/-- **Every candidate of a slot the recovering replica leads, at a gap
round, is a filled block.** -/
theorem candidates_fresh_hz (S : Slots Replica) {k : ℕ}
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    {L : BlockId}
    (hL : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).IsCandidate S
      (copyFillHZ U sk) k L) : L ∉ U.ids := by
  intro hLU
  obtain ⟨-, hLr, hLc⟩ := hL
  have hLr' : (LeanDag.Hydrozoan.adaptBlock ((copyFillHZ U sk).block L)).round = S.slotRound k := hLr
  have hLc' : (LeanDag.Hydrozoan.adaptBlock ((copyFillHZ U sk).block L)).creator = S.leader k := hLc
  rw [copyFillHZ_block_old hLU] at hLr' hLc'
  exact sk.hgap L hLU (by rw [← hlead]; exact hLc')
    (by change sk.r0 < (LeanDag.Hydrozoan.adaptBlock (U.block L)).round; omega)
    (by change (LeanDag.Hydrozoan.adaptBlock (U.block L)).round ≤ sk.r; omega)

/-- **SS3 for Hydrozoan**, from its `SkipsUnsupported`: the slot the
recovering replica leads at a gap round is skipped at once, at the grade
`qFast ≤ |T|`. -/
theorem decided_none_fresh_hz (S : Slots Replica) {V : LeanDag.Hydrozoan.View U}
    {T : Finset Replica} {k : ℕ} (hq : LeanDag.Hydrozoan.qFast Replica ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)) V T
      (S.slotRound k + 1)) :
    (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S
      (U := copyFillHZ U sk) (liftViewHZ sk V) k none :=
  decided_none_of_novel LeanDag.Hydrozoan.skipsUnsupported extends_copyFillHZ S hq
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ U.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (LeanDag.Hydrozoan.adaptBlock ((copyFillHZ U sk).block c)).creator = v
        rw [copyFillHZ_block_old hcU]; exact hcc
      · show (LeanDag.Hydrozoan.adaptBlock ((copyFillHZ U sk).block c)).round = S.slotRound k + 1
        rw [copyFillHZ_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh_hz S hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict.** -/
theorem decided_none_fresh_agree_hz (S : Slots Replica) {V : LeanDag.Hydrozoan.View U}
    {T : Finset Replica} {k : ℕ} (hq : LeanDag.Hydrozoan.qFast Replica ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)) V T
      (S.slotRound k + 1))
    {U'' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (he' : Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      (copyFillHZ U sk) U'')
    {V'' W : LeanDag.Hydrozoan.View U''} (hsub : (liftViewHZ sk V).ids ⊆ V''.ids)
    {v : Option BlockId}
    (hW : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S
      (U := U'') W k v) : v = none :=
  (decided_agree_extends LeanDag.Hydrozoan.agree (Persist.of_banded LeanDag.Hydrozoan.banded)
    he' (V := liftViewHZ sk V) (V' := V'') hsub (decided_none_fresh_hz S hq hlead hk1 hk2 hpres) hW).symm

end Integration

end LeanDag
