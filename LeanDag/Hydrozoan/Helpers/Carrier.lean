import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Optional.Quorate

/-!
# Hydrozoan as a `Properties.DagRule`

Not part of the audit surface. The carrier Hydrozoan presents to
`docs/target-properties.md`, so that its conformance can be stated
beside the protocol.

Hydrozoan's universe is the block record at its own validity, so the
carrier's block map and ids are the record's, and its schedule is the
shared `Slots`.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]

/-- **Hydrozoan as a carrier.** -/
def rule : Properties.DagRule Replica BlockId Unit where
  Universe := LeanDag.Hydrozoan.BlockUniverse Replica BlockId
  View := fun U => LeanDag.Hydrozoan.View U
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U =>
    { complete := fun i hi j hj => U.complete i hi j hj
      refs_round := fun i hi j hj => (U.valid i hi).predecessor j hj }
  Decided := fun S _ V k v => LeanDag.Hydrozoan.Decided (S := S) _ V k v

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
for `q = n − f − c` distinct creators, read at the carrier. -/
theorem quorate : Properties.Quorate (rule (Replica := Replica) (BlockId := BlockId))
    (hzReliability Replica) := by
  intro U b hb hr
  have hq : LeanDag.Hydrozoan.q Replica = Fintype.card Replica - (F.f + F.c) := by
    unfold LeanDag.Hydrozoan.q; omega
  show Fintype.card Replica - (F.f + F.c) ≤
    (creators U.block (U.block b)).card
  rw [← hq]
  exact (U.valid b hb).quorum hr

@[simp] theorem rule_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    (rule (BlockId := BlockId)).ids U = U.ids := rfl

@[simp] theorem rule_block_round (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : ((rule (BlockId := BlockId)).block U i).round = (U.block i).round := rfl

@[simp] theorem rule_block_creator (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : ((rule (BlockId := BlockId)).block U i).creator = (U.block i).creator := rfl

@[simp] theorem rule_block_refs (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : ((rule (BlockId := BlockId)).block U i).refs = (U.block i).refs := rfl

@[simp] theorem rule_viewIds {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (V : LeanDag.Hydrozoan.View U) : (rule (BlockId := BlockId)).viewIds V = V.ids := rfl

end Hydrozoan

end LeanDag
