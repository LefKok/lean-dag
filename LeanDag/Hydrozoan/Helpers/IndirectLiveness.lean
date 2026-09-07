import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Hydrozoan.Helpers.DirectRules
import LeanDag.Common.Anchored.Bounded
/-!
# Helpers: indirect liveness

Generated: what the anchored relation's totality and descent ask of the
graded rule — a choice at every nonempty rung. Rung `0` has no tie, so
any certified candidate is its choice; rung `1`'s tie is the order, so
the least weak-linked candidate is (the relation's `exists_least_of_lt`,
`Finset.min'` over the candidates). Totality, the descent below a
committed run, and view-monotonicity are the relation's theorems at
this choice and at `hydrozoanLaws`.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica] {U : BlockUniverse Replica BlockId}

/-- **Each rung has a choice.** -/
theorem exists_least {A : BlockId} {i k : ℕ} (hi : i < (hydrozoanAnchored Replica BlockId).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧
      (hydrozoanAnchored Replica BlockId).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧ (hydrozoanAnchored Replica BlockId).Link i U A L S k ∧
      (hydrozoanAnchored Replica BlockId).Least (S := S) U A i k L := by
  rcases i with _ | _ | i
  · obtain ⟨L, hL, hl⟩ := h
    exact ⟨L, hL, hl, AnchoredRule.least_of_no_tie (fun _ _ h => h)⟩
  · exact AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h
  · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)

end Hydrozoan

end LeanDag
