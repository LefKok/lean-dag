import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.Properties.Extends
import LeanDag.Record.Chop
import LeanDag.Record.Fill
import LeanDag.Record.Genesis
import LeanDag.GC.ChopDecided

/-!
# A carrier on the block record, and the witnesses every mechanism owes

A rule whose universes are block records — every rule with a carrier —
gets its cut, fill and re-genesis from `Record/`, and the witnesses
those mechanisms owe the properties (`Truncates`, `Extends`,
`Sustains`) are proved here once, for any such rule.

`DagRule.OnRecord` says how a carrier's universes are read as records:
a map each way, with the carrier's ids and block map agreeing with the
record's. For the core, Nemo and FinWhale both maps are the identity;
for Hydrozoan they are the block adapter and its inverse. Nothing here
mentions views or verdicts, which is why one structure serves rules
with different view types.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A carrier read as block records.** -/
structure DagRule.OnRecord (R : DagRule Validator BlockId Payload)
    (P : Validity Validator BlockId Payload) (honest : Finset Validator) where
  /-- A universe, as a record. -/
  toRec : R.Universe → BlockRecord Validator BlockId Payload P honest
  /-- A record, as a universe. -/
  ofRec : BlockRecord Validator BlockId Payload P honest → R.Universe
  ids_to : ∀ U, (toRec U).ids = R.ids U
  block_to : ∀ U, (toRec U).block = R.block U
  ids_of : ∀ W, R.ids (ofRec W) = W.ids
  block_of : ∀ W, R.block (ofRec W) = W.block

/-- The core's cut rebases the schedule: a schedule fact with no universe
in it. -/
theorem rebases_chop {S : Slots Validator} {G d : ℕ} (hd : G ≤ S.slotRound d) :
    Rebases S (S.chop G d hd) G d where
  slotRound := fun k => by
    simp only [Slots.chop_slotRound]
    have := horizon_le_slotRound hd k
    omega
  leader := fun _ => rfl
  base := hd

namespace DagRule.OnRecord

variable {R : DagRule Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable (c : R.OnRecord P honest) [P.Mechanised]

/-! ## The cut -/

/-- The cut, at the carrier. -/
def chop (U : R.Universe) (G : ℕ) : R.Universe := c.ofRec ((c.toRec U).chop G)

variable {G d : ℕ} {S : Slots Validator}

theorem ids_chop (U : R.Universe) : R.ids (c.chop U G) = (R.ids U).filter fun i => G ≤ (R.block U i).round := by
  rw [chop, c.ids_of, BlockRecord.chop_ids, c.ids_to, c.block_to]

theorem block_chop (U : R.Universe) : R.block (c.chop U G) = chopBlk (R.block U) G := by
  rw [chop, c.block_of, BlockRecord.chop_block, c.block_to]

/-- **The cut sustains the carrier from its horizon.** -/
theorem sustains_chop (U : R.Universe) : Sustains R U (c.chop U G) G G where
  mem := fun b => by
    rw [c.ids_chop, c.block_chop, Finset.mem_filter, chopBlk_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by rw [c.block_chop, chopBlk_round]; omega
  creator := fun b _ _ => by rw [c.block_chop, chopBlk_creator]
  refs := fun b _ hr => by rw [c.block_chop, chopBlk_refs_of_lt hr]

/-- **The cut is a truncation of the carrier.** -/
theorem truncates_chop (U : R.Universe) (hd : G ≤ S.slotRound d) :
    Truncates R U (c.chop U G) S (S.chop G d hd) G d :=
  { c.sustains_chop U, rebases_chop hd with }

/-! ## The fill -/

/-- The fill, at the carrier, under a reading of the filled blocks. -/
def fill (U : R.Universe) (sk : SkipData (c.toRec U).ids (c.toRec U).block) (B : sk.Blocks)
    (hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k)) : R.Universe :=
  c.ofRec (BlockRecord.fill (c.toRec U) sk B hB)

variable {U : R.Universe} {sk : SkipData (c.toRec U).ids (c.toRec U).block} {B : sk.Blocks}
variable {hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k)}

/-- Membership, read through the record. -/
theorem mem_toRec {b : BlockId} : b ∈ (c.toRec U).ids ↔ b ∈ R.ids U := by rw [c.ids_to]

theorem ids_fill : R.ids (c.fill U sk B hB) = (c.toRec U).ids ∪ sk.freshIds := by
  rw [fill, c.ids_of, BlockRecord.fill_ids]

theorem block_fill : R.block (c.fill U sk B hB) = sk.fillMap B := by
  rw [fill, c.block_of, BlockRecord.fill_block]

theorem block_fill_old {b : BlockId} (hb : b ∈ R.ids U) :
    R.block (c.fill U sk B hB) b = R.block U b := by
  rw [c.block_fill, ← c.block_to]
  exact SkipData.fillMap_old (c.mem_toRec.mpr hb)

/-- **The fill is an extension of the carrier.** -/
theorem extends_fill : Extends R U (c.fill U sk B hB) where
  subset := fun b hb => by
    rw [c.ids_fill]; exact Finset.mem_union_left _ (c.mem_toRec.mpr hb)
  block := fun b hb => c.block_fill_old hb

/-- **And it sustains the carrier from the top of its gap.** -/
theorem sustains_fill : Sustains R U (c.fill U sk B hB) 0 (sk.r + 1) where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      refine ⟨by rw [c.ids_fill]; exact Finset.mem_union_left _ (c.mem_toRec.mpr hb), ?_⟩
      rw [c.block_fill_old hb]; omega
    · rintro ⟨hb, hr⟩
      rw [c.ids_fill] at hb
      have hbU : b ∈ R.ids U := by
        rcases Finset.mem_union.mp hb with ho | hf
        · exact c.mem_toRec.mp ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
          rw [c.block_fill, SkipData.fillMap_fresh, B.round] at hr
          omega
      exact ⟨hbU, by rw [c.block_fill_old hbU] at hr; omega⟩
  round := fun b hb _ => by rw [c.block_fill_old hb]; omega
  creator := fun b hb _ => by rw [c.block_fill_old hb]
  refs := fun b hb _ => by rw [c.block_fill_old hb]

/-- The copy fill, at a carrier whose validity does not read the author. -/
def copyFill [P.CopyStable] (U : R.Universe) (sk : SkipData (c.toRec U).ids (c.toRec U).block) :
    R.Universe :=
  c.ofRec (BlockRecord.copyFill (c.toRec U) sk)

theorem copyFill_eq [P.CopyStable] (U : R.Universe) (sk : SkipData (c.toRec U).ids (c.toRec U).block) :
    c.copyFill U sk = c.fill U sk (sk.copyBlocks (c.toRec U).complete)
      (fun _ hk1 hk2 => BlockRecord.copyBlock_valid (c.toRec U) sk hk1 hk2) := rfl

theorem extends_copyFill [P.CopyStable] (U : R.Universe)
    (sk : SkipData (c.toRec U).ids (c.toRec U).block) : Extends R U (c.copyFill U sk) :=
  c.extends_fill

theorem sustains_copyFill [P.CopyStable] (U : R.Universe)
    (sk : SkipData (c.toRec U).ids (c.toRec U).block) :
    Sustains R U (c.copyFill U sk) 0 (sk.r + 1) :=
  c.sustains_fill

/-! ## Re-genesis -/

/-- Re-genesis, at the carrier. -/
def addGenesis (U : R.Universe) (v : Validator) (g : BlockId) (p : Payload)
    (hg : g ∉ (c.toRec U).ids) (hsev : ∀ b ∈ (c.toRec U).ids, ((c.toRec U).block b).creator ≠ v) :
    R.Universe :=
  c.ofRec (BlockRecord.addGenesis (c.toRec U) v g p hg hsev)

variable {v : Validator} {g : BlockId} {p : Payload}
variable {hg : g ∉ (c.toRec U).ids} {hsev : ∀ b ∈ (c.toRec U).ids, ((c.toRec U).block b).creator ≠ v}

theorem ids_addGenesis : R.ids (c.addGenesis U v g p hg hsev) = insert g (R.ids U) := by
  rw [addGenesis, c.ids_of, BlockRecord.addGenesis_ids, c.ids_to]

theorem block_addGenesis_old {b : BlockId} (hb : b ∈ R.ids U) :
    R.block (c.addGenesis U v g p hg hsev) b = R.block U b := by
  rw [addGenesis, c.block_of, ← c.block_to]
  exact BlockRecord.addGenesis_block_old (by rw [c.ids_to]; exact hb)

theorem block_addGenesis_new :
    R.block (c.addGenesis U v g p hg hsev) g = ⟨0, v, ∅, p⟩ := by
  rw [addGenesis, c.block_of]
  exact BlockRecord.addGenesis_block_new

/-- **Re-genesis is an extension of the carrier.** -/
theorem extends_addGenesis : Extends R U (c.addGenesis U v g p hg hsev) where
  subset := fun b hb => by rw [c.ids_addGenesis]; exact Finset.mem_insert_of_mem hb
  block := fun b hb => c.block_addGenesis_old hb

/-- **And it sustains the carrier from round one.** -/
theorem sustains_addGenesis : Sustains R U (c.addGenesis U v g p hg hsev) 0 1 where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨by rw [c.ids_addGenesis]; exact Finset.mem_insert_of_mem hb,
        by rw [c.block_addGenesis_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      rw [c.ids_addGenesis] at hb
      rcases Finset.mem_insert.mp hb with rfl | ho
      · rw [c.block_addGenesis_new] at hr
        simp at hr
      · exact ⟨ho, by rw [c.block_addGenesis_old ho] at hr; omega⟩
  round := fun b hb _ => by rw [c.block_addGenesis_old hb]; omega
  creator := fun b hb _ => by rw [c.block_addGenesis_old hb]
  refs := fun b hb _ => by rw [c.block_addGenesis_old hb]

end DagRule.OnRecord

end Properties

end LeanDag
