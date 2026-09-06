import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.FinWhale.Carrier
import LeanDag.Properties.Record

/-!
# Garbage collection and crash recovery for FinWhale

FinWhale's DAG is the block record at `ValidHere`, so its cut and its
fill are the record's (`Record/`) and the witnesses the properties read
are the carrier bridge's (`Properties/Record.lean`). What FinWhale
supplied is `ValidHere.mechanised` and `ValidHere.copyStable`, in
`FinWhale/Model/Rule.lean`; its views are a subtype of id sets, so the
two view lifts are stated here.

**The fill copies the donor's references and adds nothing.** The self
reference the core's fill adds is exactly what `ValidHere.leader_clause`
would object to: it grafts the anchor's reference set onto the donor's,
and the clause constrains what a pair of references may see together.
With the donor's references copied, validity is the donor's verbatim.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ}
variable {D : Dag Validator BlockId Payload}

/-! ## The cut -/

/-- **FinWhale's carrier, on the record**: both maps the identity. -/
def finWhaleOnRecord :
    (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).OnRecord ValidHere (Correct : Finset Validator) where
  toRec := fun D => D
  ofRec := fun W => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ => rfl
  block_of := fun _ => rfl

/-- **The cut, at FinWhale's DAG**: the record's. -/
def chopFinWhale (D : Dag Validator BlockId Payload) (G : ℕ) :
    Dag Validator BlockId Payload :=
  BlockRecord.chop D G

@[simp] theorem mem_chopFinWhale_ids {i : BlockId} :
    i ∈ (chopFinWhale D G).ids ↔ i ∈ D.ids ∧ G ≤ (D.block i).round :=
  BlockRecord.mem_chop_ids

@[simp] theorem chopFinWhale_block :
    (chopFinWhale D G).block = chopBlk D.block G := rfl

/-- The truncated view: keep what clears the cut. -/
def chopViewFinWhale (V : {V : Finset BlockId // IsView D V}) (G : ℕ) :
    {V : Finset BlockId // IsView (chopFinWhale D G) V} :=
  ⟨V.val.filter fun i => G ≤ (D.block i).round, by
    constructor
    · intro i hi
      rw [Finset.mem_filter] at hi
      exact mem_chopFinWhale_ids.mpr ⟨V.property.subset hi.1, hi.2⟩
    · intro i hi j hj
      rw [Finset.mem_filter] at hi
      have hj' : j ∈ (chopBlk D.block G i).refs := hj
      rcases Nat.lt_or_ge G (D.block i).round with h | h
      · rw [chopBlk_refs_of_lt h] at hj'
        have := (D.valid i (V.property.subset hi.1)).predecessor j hj'
        exact Finset.mem_filter.mpr ⟨V.property.closed i hi.1 j hj', by omega⟩
      · rw [chopBlk_refs_of_le h] at hj'
        exact absurd hj' (Finset.notMem_empty j)⟩

/-- **The cut is a truncation of FinWhale's carrier.** -/
theorem truncates_chop_finwhale (hd : G ≤ S.slotRound d) :
    Truncates (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) D (chopFinWhale D G) S
      (S.chop G d hd) G d :=
  finWhaleOnRecord.truncates_chop D hd

/-- **The chopped view agrees with the original above the cut.** -/
theorem viewAgreeAbove_chop_finwhale {V : {V : Finset BlockId // IsView D V}} :
    ViewAgreeAbove (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) V (chopViewFinWhale V G) G :=
  fun b _ hr => by
    show b ∈ V.val ↔ b ∈ V.val.filter fun i => G ≤ (D.block i).round
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **Verdict transport across the cut, for FinWhale.** -/
theorem decided_chop_iff_finwhale (hd : G ≤ S.slotRound d)
    {V : {V : Finset BlockId // IsView D V}} {k : ℕ} {v : Option BlockId} :
    (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V (d + k) v ↔
      (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided (S.chop G d hd)
        (chopViewFinWhale V G) k v :=
  LocalTruncate.of_banded FinWhaleProperties.banded
    S (S.chop G d hd) D (chopFinWhale D G) G d (truncates_chop_finwhale hd)
    V (chopViewFinWhale V G) viewAgreeAbove_chop_finwhale k v

/-- **And cross-cut agreement**, from an arbitrary view of the
truncation. -/
theorem decided_agree_chop_finwhale (hd : G ≤ S.slotRound d)
    {W : {W : Finset BlockId // IsView (chopFinWhale D G) W}}
    {V : {V : Finset BlockId // IsView D V}} {k : ℕ} {w v : Option BlockId}
    (hW : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided
      (S.chop G d hd) W k w)
    (hV : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V (d + k) v) :
    w = v :=
  decided_agree_truncate FinWhaleProperties.agree
    (LocalTruncate.of_banded FinWhaleProperties.banded)
    (truncates_chop_finwhale hd) viewAgreeAbove_chop_finwhale hW hV

/-! ## The fill -/

/-- **The recovery, at FinWhale's DAG**: the record's copy fill. -/
def skipFillFinWhale (D : Dag Validator BlockId Payload)
    (sk : SkipData D.ids D.block) : Dag Validator BlockId Payload :=
  BlockRecord.copyFill D sk

variable {sk : SkipData D.ids D.block}

@[simp] theorem skipFillFinWhale_block_old {b : BlockId} (hb : b ∈ D.ids) :
    (skipFillFinWhale D sk).block b = D.block b := if_pos hb

@[simp] theorem skipFillFinWhale_block_fresh {k : ℕ} :
    (skipFillFinWhale D sk).block (sk.fresh k) = sk.copyBlock k := SkipData.fillMap_fresh

/-- The pre-crash view, read in the repaired DAG: the same ids, and
every one of them old. -/
def liftViewFinWhale (V : {V : Finset BlockId // IsView D V}) :
    {V : Finset BlockId // IsView (skipFillFinWhale D sk) V} :=
  ⟨V.val, by
    constructor
    · exact fun _ hb => Finset.mem_union_left _ (V.property.subset hb)
    · intro i hi j hj
      rw [skipFillFinWhale_block_old (V.property.subset hi)] at hj
      exact V.property.closed i hi j hj⟩

/-- **The fill is an extension of FinWhale's carrier.** -/
theorem extends_skipFill_finwhale :
    Extends (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) D (skipFillFinWhale D sk) :=
  finWhaleOnRecord.extends_copyFill D sk

/-- **What the fill sustains.** Above `sk.r` the fill added nothing, so
every block there is old and unchanged. -/
theorem sustains_skipFill_finwhale :
    Sustains (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) D (skipFillFinWhale D sk) 0 (sk.r + 1) :=
  finWhaleOnRecord.sustains_copyFill D sk

/-- **Verdicts survive the recovery, for FinWhale.** -/
theorem decided_skipFill_finwhale {V : {V : Finset BlockId // IsView D V}}
    {k : ℕ} {v : Option BlockId}
    (h : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k v) :
    (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S
      (liftViewFinWhale (sk := sk) V) k v :=
  Persist.of_banded FinWhaleProperties.banded S D (skipFillFinWhale D sk)
    extends_skipFill_finwhale V (liftViewFinWhale V) (fun _ hb => hb) k v h

/-- **And agreement across it**: a validator that recovered agrees with
one that did not, from any view of the fill. -/
theorem decided_agree_skipFill_finwhale {V : {V : Finset BlockId // IsView D V}}
    {W : {W : Finset BlockId // IsView (skipFillFinWhale D sk) W}}
    {k : ℕ} {v w : Option BlockId}
    (hV : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k v)
    (hW : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S W k w) :
    v = w :=
  decided_agree_extends FinWhaleProperties.agree
    (Persist.of_banded FinWhaleProperties.banded) extends_skipFill_finwhale
    (V' := liftViewFinWhale V) (fun _ hb => hb) hV hW

end Integration

end LeanDag
