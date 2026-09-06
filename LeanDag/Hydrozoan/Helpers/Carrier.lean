import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Optional.Quorate

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
variable [F : LeanDag.Hydrozoan.Faults Replica]

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
  viewComplete := fun V => V.complete
  causal := fun U =>
    { complete := fun i hi j hj => U.complete i hi j hj
      refs_round := fun i hi j hj => (U.valid i hi).predecessor j hj }
  Decided := fun S _ V k v =>
    @LeanDag.Hydrozoan.Decided _ _ _ _ _ _ _ (ofCoreSlots S) _ V k v

/-- **Hydrozoan's fault model, as a counting parameter.** The slack is
`f + c` — Byzantine and crashed together are what `Correct` excludes —
and `n ≥ 3f + 2c + k + 1` makes it a minority. -/
def hzReliability (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [F : LeanDag.Hydrozoan.Faults Replica] : LeanDag.Reliability Replica where
  correct := (LeanDag.Hydrozoan.Correct : Finset Replica)
  slack := F.f + F.c
  covers := by
    have hc : (LeanDag.Hydrozoan.Correct : Finset Replica)ᶜ = F.byzantine ∪ F.crashed := by
      simp [LeanDag.Hydrozoan.Correct]
    rw [hc]
    exact le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add F.card_byzantine F.card_crashed)
  minority := by have := F.card_replicas; omega

/-- **Hydrozoan's universes are quorate**: `ValidWrt.quorum`, which asks
for `q = n − f − c` distinct authors, read at the carrier. -/
theorem quorate : Properties.Quorate (rule (Replica := Replica) (BlockId := BlockId))
    (hzReliability Replica) := by
  intro U b hb hr
  have hq : LeanDag.Hydrozoan.q Replica = Fintype.card Replica - (F.f + F.c) := by
    unfold LeanDag.Hydrozoan.q; omega
  show Fintype.card Replica - (F.f + F.c) ≤
    (LeanDag.Hydrozoan.authors U.block (U.block b)).card
  rw [← hq]
  exact (U.valid b hb).quorum hr

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

end Hydrozoan

end LeanDag
