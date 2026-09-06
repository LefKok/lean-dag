import LeanDag.Block
import LeanDag.Hydrozoan.Model.Faults

/-!
# Blocks and validity

Hydrozoan's block is the shared one, `LeanDag.Block Replica BlockId Unit`:
a round, a creator, the ids of the blocks it references from the
preceding round, and no payload. `BlockId` is the block's identity —
two blocks by the same creator in the same round (equivocation) are
simply two distinct ids.

**Fidelity gap** (stated once, here): references point only to the
immediately preceding round — the model has no weak links.
-/

namespace LeanDag

namespace Hydrozoan

/-- A Hydrozoan block: the shared block with no payload. -/
abbrev Block (Replica BlockId : Type*) := LeanDag.Block Replica BlockId Unit

section Validity

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [F : LeanDag.Hydrozoan.Faults Replica]

/-- Block validity, relative to a lookup function — the paper's
"referencing `≥ q` distinct valid blocks from the previous round".

The predecessor condition is additive (`+ 1 =`, never `− 1`): this avoids
natural-number subtraction, and it makes the genesis case derivable
rather than assumed — at round `0` the equation `(blk i).round + 1 = 0`
is unsatisfiable, so `refs = ∅` follows. Only the quorum condition
needs a round guard.

The quorum counts **creators**, not `refs.card`: the protocol means `q`
distinct *replicas'* blocks, and the creator-set form is what every
counting argument consumes (with `distinct_creators` the two coincide). -/
structure ValidWrt (blk : BlockId → Block Replica BlockId)
    (b : Block Replica BlockId) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- A block never references the same creator twice. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs,
    (blk i).creator = (blk j).creator → i = j
  /-- Non-genesis blocks reference a DAG quorum of distinct creators. -/
  quorum : 0 < b.round → q Replica ≤ (creators blk b).card

end Validity

end Hydrozoan

end LeanDag
