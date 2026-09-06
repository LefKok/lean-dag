import LeanDag.Hybrid.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent

/-!
# Hybrid as a carrier, and the three properties its own rules give

`docs/porting-plan.md` step 2. The carrier at indirect threshold `k`,
and the properties whose proof is a single Hybrid theorem apiece.

**The universe is a subtype, and that is the whole difficulty.**
`Hybrid.decided_unique` is conditional on `HonestNoEquiv U`: the fault
model is Byzantine, so agreement is not a fact about every DAG.
`Properties.Agree` is unconditional and has no graded form, so the
hypothesis has to become part of the *object* rather than a premise of
the theorem. Taking `Universe := {U // HonestNoEquiv U}` does that, and
`Agree` then holds outright. Barnacle's `orcaella` carrier already had
this shape; the plan predicted the obstacle and this is the answer it
predicted.

`Admissible Validator k` stays a hypothesis of the two theorems that
need it, not of the carrier: a rule is a carrier before it has proved
anything, and the threshold's admissibility is a fact about the
committee rather than about the DAG.
-/

namespace LeanDag

namespace HybridProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Hybrid as a carrier**, one per indirect threshold. -/
def hybridRule (k : ℕ) : DagRule Validator BlockId Payload where
  Universe := {U : BlockUniverse Validator BlockId Payload // HonestNoEquiv U}
  View := fun U => View Validator BlockId Payload U.val
  block := fun U i => U.val.block i
  ids := fun U => U.val.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U => U.val.causal
  Decided := fun S U V s v => Hybrid.Decided (S := S) k U.val V s v

/-- **Hybrid's universes are quorate**, at the derived fault model:
`f = fb + fc`, so a quorum of `n − fb − fc` distinct authors is what
validity already asks for. -/
theorem quorate (k : ℕ) : Quorate (hybridRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) k) (coreReliability Validator) :=
  fun U => U.val.quorateOn

/-- **P3′ at the carrier.** -/
theorem selfParent (k : ℕ) : SelfParent (hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) k) :=
  fun U b hb hr => (U.val.valid b hb).self_parent hr

/-- **One block per correct author per round.** -/
theorem noEquiv (k : ℕ) : NoEquiv (hybridRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) k) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.val.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** H6 under the property's name, and
unconditional because non-equivocation is now a field of the universe
rather than a premise. -/
theorem agree {k : ℕ} (hk : Hybrid.Admissible Validator k) :
    Agree (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k) :=
  fun S U V₁ V₂ _ _ _ h₁ h₂ =>
    Hybrid.decided_unique (S := S) U.property hk h₁ V₂ _ h₂

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate (k : ℕ) : CommitsCandidate
    (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k) :=
  fun S _ _ _ _ hd => Hybrid.isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict**, at Hybrid's own direct
predicate. -/
theorem commitsDirect (k : ℕ) : CommitsDirect
    (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k)
    (fun {U} V L r => Hybrid.DirectCommitIn U.val V L r) :=
  fun S _ _ _ _ hc hd => Hybrid.Decided.directCommit (S := S) hc hd

end HybridProperties

end LeanDag
