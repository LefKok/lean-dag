import LeanDag.Hydrozoan.Model.Block
import LeanDag.BlockRecord

/-!
# The block universe

Trusted core: every block that exists across the whole execution —
authored by anyone, Byzantine, crashed, or correct. Later phases carve
per-replica views out of this universe; the safety theorems quantify
over it.

Here "exists" means **accepted by the DAG-building layer**, not merely
emitted: per `sections/algorithms.tex`, a replica stores a block only
after its entire causal history has been validated, and the decision
rules operate on stored blocks alone. Malformed Byzantine emissions —
dangling parent ids, wrong rounds, duplicate creators — are filtered
before entering any DAG, which is why `complete` and `valid` below hold
for Byzantine-authored blocks too. The Byzantine power that survives the
filter, and that the model does represent, is equivocation and the
adversarial choice of refs, votes, and withholding. The filtering
itself is assumed from Mysticeti, not formalized.

Non-equivocation is stated **here**, at the universe level, rather than
on any individual local DAG. Per-DAG would be too weak: two local DAGs
could each satisfy "at most one block per honest creator per round" while
holding *different* such blocks — which is exactly that creator
equivocating, with both DAGs looking well-formed.

The guard is `NonByzantine`, not `Correct`: crashed replicas follow the
protocol until they halt — they may creator *fewer* blocks (or none), but
never two in one round. Only Byzantine replicas are unconstrained, so
equivocation by them is representable; the witness models exhibit it.
-/

namespace LeanDag

namespace Hydrozoan

/-- **The block universe**: the block record at Hydrozoan's validity,
with non-equivocation asked of the non-Byzantine replicas. `block` is
total, with junk outside `ids`; every clause quantifies over `i ∈ ids`,
so the junk is never observed. -/
abbrev BlockUniverse (Replica BlockId : Type*) [Fintype Replica]
    [DecidableEq Replica] [F : LeanDag.Hydrozoan.Faults Replica] :=
  BlockRecord Replica BlockId Unit ValidWrt (NonByzantine : Finset Replica)

section Mechanised

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : Faults Replica]

/-- **Hydrozoan's validity is mechanised.** -/
instance ValidWrt.mechanised :
    Validity.Mechanised (ValidWrt (Replica := Replica) (BlockId := BlockId)) where
  pred := fun _ _ h => h.predecessor
  reads := by
    intro blk blk' ids b _ hb hagree h
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; rw [hagree j (hb j hj)]; exact h.predecessor j hj
    · intro j hj l hl
      rw [hagree j (hb j hj), hagree l (hb l hl)]
      exact h.distinct_creators j hj l hl
    · intro hr
      refine le_trans (h.quorum hr) (Finset.card_le_card ?_)
      intro c hc
      unfold creators creatorsOf at hc ⊢
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨j, hj, by rw [hagree j (hb j hj)]; exact hjc⟩
  base := by
    intro blk b h0 hr
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro j hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro h; omega
  chops := by
    intro blk G b h hG
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have := h.predecessor j hj
      change (chopBlk blk G j).round + 1 = b.round - G
      rw [chopBlk_round]; omega
    · intro j hj l hl hjl
      simp only [chopBlk_creator] at hjl
      exact h.distinct_creators j hj l hl hjl
    · intro hr
      change q Replica ≤ (creatorsOf (chopBlk blk G) b.refs).card
      rw [creatorsOf_chopBlk]
      exact h.quorum (by change 0 < b.round - G at hr; omega)

/-- **And does not read the creator.** -/
instance ValidWrt.copyStable :
    Validity.CopyStable (ValidWrt (Replica := Replica) (BlockId := BlockId)) where
  copy := fun _ _ _ h => ⟨h.predecessor, h.distinct_creators, h.quorum⟩

end Mechanised

end Hydrozoan

end LeanDag
