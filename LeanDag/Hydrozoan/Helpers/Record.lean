import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Properties.Record

/-!
# Hydrozoan's universe as a block record

Not part of the audit surface. Hydrozoan's block has `author` and
`parents` where the shared block has `creator` and `refs`, and no
payload; the two are in bijection (`adaptBlock`, `unadapt`), and a
Hydrozoan universe is a block record through it, at Hydrozoan's
validity read through the adapter and with non-equivocation asked of
the non-Byzantine replicas. The carrier's `OnRecord` is the pair of
maps, every equation `rfl`. The mechanisms of
`Integration/HydrozoanMechanisms.lean` are then the record's.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]

/-- The block adapter's inverse. -/
def unadapt (b : LeanDag.Block Replica BlockId Unit) : LeanDag.Hydrozoan.Block Replica BlockId :=
  ⟨b.round, b.creator, b.refs⟩

@[simp] theorem unadapt_adapt (b : LeanDag.Hydrozoan.Block Replica BlockId) :
    unadapt (adaptBlock b) = b := rfl

@[simp] theorem adapt_unadapt (b : LeanDag.Block Replica BlockId Unit) :
    adaptBlock (unadapt b) = b := rfl

@[simp] theorem unadapt_round (b : LeanDag.Block Replica BlockId Unit) :
    (unadapt b).round = b.round := rfl
@[simp] theorem unadapt_author (b : LeanDag.Block Replica BlockId Unit) :
    (unadapt b).author = b.creator := rfl
@[simp] theorem unadapt_parents (b : LeanDag.Block Replica BlockId Unit) :
    (unadapt b).parents = b.refs := rfl

/-- **Hydrozoan's validity, read through the adapter.** -/
def validity : Validity Replica BlockId Unit :=
  fun blk b => ValidWrt (fun i => unadapt (blk i)) (unadapt b)

omit [LinearOrder BlockId] in
theorem authorsOf_unadapt_chopBlk (blk : BlockId → LeanDag.Block Replica BlockId Unit) (G : ℕ)
    (s : Finset BlockId) :
    authorsOf (fun i => unadapt (chopBlk blk G i)) s = authorsOf (fun i => unadapt (blk i)) s := by
  simp only [authorsOf, unadapt_author, chopBlk_creator]

omit [LinearOrder BlockId] in
/-- **Hydrozoan's validity is mechanised.** -/
instance validity.mechanised :
    Validity.Mechanised (validity (Replica := Replica) (BlockId := BlockId)) where
  pred := fun _ _ h => h.predecessor
  reads := by
    intro blk blk' ids b _ hb hagree h
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      change (unadapt (blk' j)).round + 1 = (unadapt b).round
      rw [hagree j (hb j hj)]; exact h.predecessor j hj
    · intro j hj l hl hjl
      change (unadapt (blk' j)).author = (unadapt (blk' l)).author at hjl
      rw [hagree j (hb j hj), hagree l (hb l hl)] at hjl
      exact h.distinct_authors j hj l hl hjl
    · intro hr
      refine le_trans (h.quorum hr) (Finset.card_le_card ?_)
      intro c hc
      unfold authors authorsOf at hc ⊢
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
      refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
      change (unadapt (blk' j)).author = c
      rw [hagree j (hb j hj)]; exact hjc
  base := by
    intro blk b h0 hr
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; change j ∈ b.refs at hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro j hj; change j ∈ b.refs at hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro h; change 0 < b.round at h; rw [h0] at h; exact absurd h (lt_irrefl 0)
  chops := by
    intro blk G b h hG
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have h1 := h.predecessor j hj
      change (blk j).round + 1 = b.round at h1
      change (chopBlk blk G j).round + 1 = b.round - G
      rw [chopBlk_round]; omega
    · intro j hj l hl hjl
      change (chopBlk blk G j).creator = (chopBlk blk G l).creator at hjl
      simp only [chopBlk_creator] at hjl
      exact h.distinct_authors j hj l hl hjl
    · intro hr
      change 0 < b.round - G at hr
      change q Replica ≤ (authorsOf (fun i => unadapt (chopBlk blk G i)) b.refs).card
      rw [authorsOf_unadapt_chopBlk]
      exact h.quorum (by change 0 < b.round; omega)

omit [LinearOrder BlockId] in
/-- **And does not read the author.** -/
instance validity.copyStable : Validity.CopyStable (validity (Replica := Replica) (BlockId := BlockId)) where
  copy := fun _ _ _ h => ⟨h.predecessor, h.distinct_authors, h.quorum⟩

/-- A Hydrozoan universe as a record. -/
def toRecord (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    BlockRecord Replica BlockId Unit validity (NonByzantine : Finset Replica) where
  ids := U.ids
  block := fun i => adaptBlock (U.block i)
  complete := U.complete
  valid := fun i hi => U.valid i hi
  no_equivocation := U.no_equivocation

/-- A record as a Hydrozoan universe. -/
def ofRecord (W : BlockRecord Replica BlockId Unit validity (NonByzantine : Finset Replica)) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId where
  ids := W.ids
  block := fun i => unadapt (W.block i)
  complete := W.complete
  valid := fun i hi => W.valid i hi
  no_equivocation := W.no_equivocation

@[simp] theorem ofRecord_ids (W : BlockRecord Replica BlockId Unit validity (NonByzantine : Finset Replica)) :
    (ofRecord W).ids = W.ids := rfl
@[simp] theorem ofRecord_block (W : BlockRecord Replica BlockId Unit validity (NonByzantine : Finset Replica))
    (i : BlockId) : (ofRecord W).block i = unadapt (W.block i) := rfl
@[simp] theorem toRecord_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    (toRecord U).ids = U.ids := rfl
@[simp] theorem toRecord_block (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (i : BlockId) :
    (toRecord U).block i = adaptBlock (U.block i) := rfl

/-- **The carrier, on the record.** -/
def onRecord : (rule (Replica := Replica) (BlockId := BlockId)).OnRecord validity
    (NonByzantine : Finset Replica) BlockRecord.Any where
  toRec := toRecord
  inv := fun _ => True.intro
  ofRec := fun W _ => ofRecord W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  ofView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

end Hydrozoan

end LeanDag
