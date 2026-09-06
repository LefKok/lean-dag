import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Hydrozoan.Helpers.Skippability
import LeanDag.Hydrozoan.Helpers.Record
import LeanDag.Properties.Arcs.Record
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Extension

/-!
# Garbage collection, crash recovery and re-genesis for Hydrozoan

Hydrozoan's universe is a block record through the adapter between its
block type and the shared one (`Hydrozoan/Helpers/Record.lean`), and
its carrier reads as records by that adapter and its inverse. Every
mechanism cell is `Arcs/Record.lean` at `Hydrozoan.onRecord`: the
constructions below are the record's, read back through the adapter,
and the witnesses and verdict theorems hold with nothing written per
cell. What Hydrozoan supplied is that its validity, read through the
adapter, is `Mechanised` and `CopyStable`.

What is stated here beyond the constructions is what no property
states: the shape of a truncated block in Hydrozoan's own vocabulary,
which Optimal-Hydrozoan's exclusion proof reads; the coverage
refutation at the copy fill; and the prompt skip, from Hydrozoan's
`SkipsUnsupported`.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {S : Slots Replica} {G d : ℕ}

/-! ## The cut -/

/-- **The cut, at Hydrozoan's universe**: the record's, through the
adapter. -/
def chopHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  LeanDag.Hydrozoan.onRecord.chop U G

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {i : BlockId}

@[simp] theorem mem_chopHZ_ids :
    i ∈ (chopHZ U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  BlockRecord.mem_chop_ids

/-- A truncated block, in Hydrozoan's vocabulary: the round rebased. -/
@[simp] theorem chopHZ_round : ((chopHZ U G).block i).round = (U.block i).round - G :=
  chopBlk_round

/-- The creator kept. -/
@[simp] theorem chopHZ_creator : ((chopHZ U G).block i).creator = (U.block i).creator :=
  chopBlk_creator

/-- Refs dropped at or below the horizon. -/
theorem chopHZ_refs_of_le (h : (U.block i).round ≤ G) :
    ((chopHZ U G).block i).refs = ∅ :=
  chopBlk_refs_of_le h

/-- And kept strictly above it. -/
theorem chopHZ_refs_of_lt (h : G < (U.block i).round) :
    ((chopHZ U G).block i).refs = (U.block i).refs :=
  chopBlk_refs_of_lt h

/-- The truncated view: the record's. -/
def chopViewHZ (V : LeanDag.Hydrozoan.View U) (G : ℕ) : LeanDag.Hydrozoan.View (chopHZ U G) :=
  LeanDag.Hydrozoan.onRecord.chopView V G

/-! ## The fill -/

/-- **The copy fill, at Hydrozoan's universe**: the record's, through
the adapter. One block per gap round, by the recovering replica,
carrying the donor's refs at that round. -/
def copyFillHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (sk : SkipData U.ids U.block) : LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  LeanDag.Hydrozoan.onRecord.copyFill U sk

variable {sk : SkipData U.ids U.block}

theorem mem_copyFillHZ_ids {b : BlockId} :
    b ∈ (copyFillHZ U sk).ids ↔ b ∈ U.ids ∨ b ∈ sk.freshIds := Finset.mem_union

@[simp] theorem copyFillHZ_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (copyFillHZ U sk).block b = U.block b := by
  change sk.fillMap _ b = U.block b
  rw [SkipData.fillMap_old hb]

@[simp] theorem copyFillHZ_block_fresh {k : ℕ} :
    (copyFillHZ U sk).block (sk.fresh k) = sk.copyBlock k := by
  change sk.fillMap _ (sk.fresh k) = _
  rw [SkipData.fillMap_fresh]; rfl

/-- An old block's refs are old. -/
theorem copyFillHZ_refs_old {b : BlockId} (hb : b ∈ U.ids) :
    ∀ j ∈ ((copyFillHZ U sk).block b).refs, j ∈ U.ids := by
  rw [copyFillHZ_block_old hb]
  exact U.complete b hb

/-- The old view, read in the filled universe: the record's. -/
def liftViewHZ (sk : SkipData U.ids U.block) (V : LeanDag.Hydrozoan.View U) :
    LeanDag.Hydrozoan.View (copyFillHZ U sk) :=
  LeanDag.Hydrozoan.onRecord.liftViewCopy sk V

/-- **The fill is an extension of Hydrozoan's carrier**: the record's
witness, at the fill's own name. -/
theorem extends_copyFillHZ :
    Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U (copyFillHZ U sk) :=
  LeanDag.Hydrozoan.onRecord.extends_copyFill U sk

/-- **The copy fill does not restore coverage either.** The generic
refutation at `extends_copyFillHZ`: a reliable set holding the
recovering replica is uncovered at every gap round, for the same reason
the fill is safe. -/
theorem not_synchronisedOn_copyFillHZ {sk : SkipData U.ids U.block} {T : Finset Replica}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ Timed.SynchronisedOn (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      (copyFillHZ U sk) T R :=
  Timed.not_synchronisedOn_of_extends extends_copyFillHZ hk
    (f := sk.fresh k)
    ⟨Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩), sk.hfresh_new k⟩
    (by simp [copyFillHZ_block_fresh, SkipData.copyBlock])
    (by simpa [copyFillHZ_block_fresh, SkipData.copyBlock] using hv1)
    hb hbround hbc

/-! ## Re-genesis -/

/-- **Re-genesis, at Hydrozoan's universe**: the record's. -/
def addGenesisHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (v : Replica) (g : BlockId)
    (hg : g ∉ U.ids) (hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  LeanDag.Hydrozoan.onRecord.addGenesis U v g () hg hsev

variable {v : Replica} {g : BlockId}
variable {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}

theorem mem_addGenesisHZ_ids {b : BlockId} :
    b ∈ (addGenesisHZ U v g hg hsev).ids ↔ b = g ∨ b ∈ U.ids := Finset.mem_insert

@[simp] theorem addGenesisHZ_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (addGenesisHZ U v g hg hsev).block b = U.block b := by
  change (if b ∈ U.ids then _ else _) = U.block b
  rw [if_pos hb]; rfl

@[simp] theorem addGenesisHZ_block_new :
    (addGenesisHZ U v g hg hsev).block g = ⟨0, v, ∅, ()⟩ := by
  change (if g ∈ U.ids then _ else _) = _
  rw [if_neg hg]

/-! ## Promptness: the fill cannot conjure a commit, for Hydrozoan -/

/-- **Every candidate of a slot the recovering replica leads, at a gap
round, is a filled block.** -/
theorem candidates_fresh_hz (S : Slots Replica) {k : ℕ}
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    {L : BlockId}
    (hL : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).IsCandidate S
      (copyFillHZ U sk) k L) : L ∉ U.ids := by
  intro hLU
  obtain ⟨-, hLr, hLc⟩ := hL
  have hLr' : (((copyFillHZ U sk).block L)).round = S.slotRound k := hLr
  have hLc' : (((copyFillHZ U sk).block L)).creator = S.leader k := hLc
  rw [copyFillHZ_block_old hLU] at hLr' hLc'
  exact sk.hgap L hLU (by rw [← hlead]; exact hLc')
    (by change sk.r0 < ((U.block L)).round; omega)
    (by change ((U.block L)).round ≤ sk.r; omega)

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
      · show (((copyFillHZ U sk).block c)).creator = v
        rw [copyFillHZ_block_old hcU]; exact hcc
      · show (((copyFillHZ U sk).block c)).round = S.slotRound k + 1
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
