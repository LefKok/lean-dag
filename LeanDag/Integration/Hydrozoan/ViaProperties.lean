import LeanDag.Hydrozoan.Properties.Proof
import LeanDag.Integration.Hydrozoan.FillDecided

/-!
# The fill, re-derived through the target properties

`docs/target-properties.md` G3's test, and the reason to believe the
arc pays. `FillDecided.lean` proves `decided_fillHZ` by a
six-constructor induction over Hydrozoan's decision relation, with
transfer lemmas threaded through it for that one transformer. HZ9
proves the same protocol persists under **every** extension, once.

Below, the fill is shown to be an extension — two fields, each a simp
lemma the arc already had — and the original theorem follows with **no
induction of its own**. Any further extension-shaped mechanism costs
Hydrozoan nothing beyond what HZ9 already established.

The bespoke proof stays where it is: `Stack.lean` and `Liveness.lean`
consume it, and `integration.md` §4.2 prescribes generalising with the
old statements kept as corollaries.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica] [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {hsp : SelfParenting U}

/-- **The fill is an extension.** It holds every block the original held
and denotes each of them unchanged. -/
theorem extends_skipFillHZ (sk : SkipMsg (toCore U hsp)) :
    Extends LeanDag.Hydrozoan.rule U (skipFillHZ U hsp sk) where
  subset := fun b hb => by
    show b ∈ (skipFillHZ U hsp sk).ids
    simp only [skipFillHZ, transport_ids, SkipMsg.skipFill]
    exact Finset.mem_union_left _ hb
  block := fun b hb => by
    show LeanDag.Hydrozoan.adaptBlock ((skipFillHZ U hsp sk).block b)
       = LeanDag.Hydrozoan.adaptBlock (U.block b)
    congr 1
    exact skipFillHZ_block_old hb

/-- **HI9's transport, from HZ9.** The same statement as
`decided_fillHZ`, reached without an induction: persistence is proved
once for the protocol, and the fill is one extension among others. -/
theorem decided_fillHZ_of_persist (sk : SkipMsg (toCore U hsp))
    [S : LeanDag.Hydrozoan.Slots Replica] {V : LeanDag.Hydrozoan.View U}
    {k : ℕ} {v : Option BlockId} (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k v :=
  LeanDag.Hydrozoan.Properties.persist_aux (extends_skipFillHZ sk)
    (by
      intro b hb
      show b ∈ (liftViewHZ U hsp sk V).ids
      simpa using hb) h

end Hydrozoan

end Integration

end LeanDag
