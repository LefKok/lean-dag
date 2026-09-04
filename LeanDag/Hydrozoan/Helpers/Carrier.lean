import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist

/-!
# Hydrozoan as a `Properties.DagRule`

Not part of the audit surface. The carrier Hydrozoan presents to
`docs/target-properties.md`, so that its conformance can be stated
beside the protocol.

**Why the two adapters are restated here.** Hydrozoan's arc imports
only Mathlib, so any carrier needs a block adapter and a schedule
coercion, and both already exist elsewhere —
`Barnacle/Helpers/Hydrozoan.lean` has `adapt`, and
`Integration/Hydrozoan/Schedule.lean` has the schedule identification.
Reaching for either would make this protocol's conformance depend on a
*mechanism*, which is the one thing the arc's layering rule forbids:
remove the adaptive leader count and Hydrozoan's conformance should not
break. The maps are three and six lines, they are forced by the field
names, and the tidier end state is for the other two to be derived from
here rather than the reverse.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- A Hydrozoan block in the shared vocabulary: its author is the
creator, its parents the references, and it carries no payload. -/
def adaptBlock (b : LeanDag.Hydrozoan.Block Replica BlockId) :
    LeanDag.Block Replica BlockId Unit :=
  { round := b.round, creator := b.author, refs := b.parents, payload := () }

/-- A core schedule read as a Hydrozoan one. The two records have the
same fields, so every projection is the identity. -/
@[reducible] def ofCoreSlots (S : LeanDag.Slots Replica) : LeanDag.Hydrozoan.Slots Replica where
  slotRound := S.slotRound
  leader := S.leader
  mono := S.mono
  unbounded := S.unbounded
  keyed := S.keyed

/-- And back. `ofCoreSlots (toCoreSlots S) = S` by `rfl`, which is what
lets a Hydrozoan statement be handed to a generic one. -/
@[reducible] def toCoreSlots (S : LeanDag.Hydrozoan.Slots Replica) : LeanDag.Slots Replica where
  slotRound := S.slotRound
  leader := S.leader
  mono := S.mono
  unbounded := S.unbounded
  keyed := S.keyed

/-- **Hydrozoan as a carrier.** -/
def rule : Properties.DagRule Replica BlockId Unit where
  Universe := LeanDag.Hydrozoan.BlockUniverse Replica BlockId
  View := fun U => LeanDag.Hydrozoan.View U
  block := fun U i => adaptBlock (U.block i)
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  Decided := fun S _ V k v =>
    @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ (ofCoreSlots S) _ V k v

@[simp] theorem rule_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    (rule (BlockId := BlockId)).ids U = U.ids := rfl

@[simp] theorem rule_block_round (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : ((rule (BlockId := BlockId)).block U i).round = (U.block i).round := rfl

@[simp] theorem rule_block_creator (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : ((rule (BlockId := BlockId)).block U i).creator = (U.block i).author := rfl

@[simp] theorem rule_block_refs (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : ((rule (BlockId := BlockId)).block U i).refs = (U.block i).parents := rfl

@[simp] theorem rule_viewIds {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (V : LeanDag.Hydrozoan.View U) : (rule (BlockId := BlockId)).viewIds V = V.ids := rfl

/-- **Hydrozoan's universes are block DAGs**, which is `HI3` in the
shared vocabulary: the two fields are the universe's own `complete` and
the `predecessor` half of its validity. -/
theorem causal : Properties.Causal (rule (Replica := Replica) (BlockId := BlockId)) :=
  fun U =>
    { complete := fun i hi j hj => U.complete i hi j hj
      refs_round := fun i hi j hj => (U.valid i hi).predecessor j hj }

end Hydrozoan

end LeanDag
