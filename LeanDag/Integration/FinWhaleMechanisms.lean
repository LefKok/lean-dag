import LeanDag.Properties.Arcs.Record
import LeanDag.FinWhale.Carrier

/-!
# Garbage collection, crash recovery and re-genesis for FinWhale

FinWhale's DAG is the block record at `ValidHere` and its views are the
record's, so its carrier reads as records by the identity. Every mechanism cell is
`Arcs/Record.lean` at that instance. What FinWhale supplied is
`ValidHere.mechanised` and `ValidHere.copyStable`, in
`FinWhale/Model/Rule.lean`.

**The fill copies the donor's references and adds nothing.** The self
reference the core's fill adds is exactly what `ValidHere.leader_clause`
would object to: it grafts the anchor's reference set onto the donor's,
and the clause constrains what a pair of references may see together.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **FinWhale's carrier, on the record**: the identity on universes,
repacking on views. -/
def finWhaleOnRecord :
    (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).OnRecord ValidHere (Correct : Finset Validator)
      BlockRecord.Any where
  toRec := fun D => D
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

/-- **The cut, at FinWhale's DAG**: the record's. -/
def chopFinWhale (D : Dag Validator BlockId Payload) (G : ℕ) :
    Dag Validator BlockId Payload :=
  finWhaleOnRecord.chop D G

/-- **The recovery, at FinWhale's DAG**: the record's copy fill. -/
def skipFillFinWhale (D : Dag Validator BlockId Payload)
    (sk : SkipData D.ids D.block) : Dag Validator BlockId Payload :=
  finWhaleOnRecord.copyFill D sk

/-- **Re-genesis, at FinWhale's DAG**: the record's. -/
def addGenesisFinWhale (D : Dag Validator BlockId Payload) (v : Validator) (g : BlockId)
    (p : Payload) (hg : g ∉ D.ids) (hsev : ∀ b ∈ D.ids, (D.block b).creator ≠ v) :
    Dag Validator BlockId Payload :=
  finWhaleOnRecord.addGenesis D v g p hg hsev

end Integration

end LeanDag
