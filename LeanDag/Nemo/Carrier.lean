import LeanDag.Nemo.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate

/-!
# Nemo as a carrier, and the three properties its own rules give

`docs/target-properties.md` §8, `docs/porting-plan.md` step 1. The
carrier and the properties whose proof is a single Nemo theorem apiece:
`Agree` is Nemo's `decided_unique`, `CommitsCandidate` is
`isLeaderBlock_of_decided`, `CommitsDirect` is the direct constructor.

**Nemo's agreement is hypothesis-free**, which is not true of every rule
here — non-equivocation is a field of Nemo's `Universe` rather than a
premise, because the model is crash-only. That is what lets `Agree`
hold at the bare universe; Hybrid, whose faults are Byzantine, needs a
subtype carrier for the same property.

**`SkipsUnsupported` is not owed.** Nemo has three constructors and no
direct skip: a slot with no candidate waits for an anchor rather than
being settled at once. The property is optional precisely for this case
(§11.4c).

This file sits upstream of every mechanism, which is not optional — a
conformance layer downstream of a mechanism cannot serve one
(`docs/bespoke-links.md`).
-/

namespace LeanDag

namespace NemoProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Nemo as a carrier**, at its own namespace rather than through
`Barnacle.nemoRule`: a protocol's conformance should not route through a
mechanism. -/
def nemoRule : DagRule Validator BlockId Payload where
  Universe := Nemo.Universe Validator BlockId Payload
  View := fun U => Nemo.View Validator BlockId Payload U
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  Decided := fun S _ V k v => Nemo.Decided (S := S) _ V k v

@[simp] theorem nemoRule_ids (U : Nemo.Universe Validator BlockId Payload) :
    (nemoRule (Payload := Payload)).ids U = U.ids := rfl

@[simp] theorem nemoRule_block (U : Nemo.Universe Validator BlockId Payload) :
    (nemoRule (Payload := Payload)).block U = U.block := rfl

@[simp] theorem nemoRule_viewIds {U : Nemo.Universe Validator BlockId Payload}
    (V : Nemo.View Validator BlockId Payload U) :
    (nemoRule (Payload := Payload)).viewIds V = V.ids := rfl

/-- **Nemo's fault model, as a counting parameter.** Nemo is crash-only
and nobody equivocates, so the reliable set is everyone and the slack is
what a majority may miss. A committee of at least one makes it a
minority, which is all the count needs. -/
def nemoReliability (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (hn : 0 < Fintype.card Validator) : LeanDag.Reliability Validator where
  correct := Finset.univ
  slack := Fintype.card Validator - Nemo.majority Validator
  covers := by simp
  minority := by unfold Nemo.majority; omega

/-- **Nemo's universes are quorate**: `ValidWrt.quorum`, which asks for a
majority of distinct authors, read at the carrier. -/
theorem quorate (hn : 0 < Fintype.card Validator) :
    Quorate (nemoRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (nemoReliability Validator hn) := by
  intro U b hb hr
  have h := (U.valid b hb).quorum hr
  have hq : Nemo.majority Validator
      = Fintype.card Validator - (nemoReliability Validator hn).slack := by
    show Nemo.majority Validator = Fintype.card Validator - (Fintype.card Validator - _)
    unfold Nemo.majority; omega
  rw [hq] at h
  exact h

/-- Nemo's universes are block DAGs. Completeness is a field; the round
condition comes from validity, where the core reads it off directly. -/
theorem causal : Causal (nemoRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun U =>
    { complete := fun i hi j hj => U.complete i hi j hj
      refs_round := fun i hi j hj => U.round_of_mem_refs hi hj }

/-- **Two views decide alike.** Nemo's `decided_unique` under the
property's name. -/
theorem agree : Agree (nemoRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun S _ V₁ V₂ _ _ _ h₁ h₂ => Nemo.decided_unique (S := S) h₁ V₂ _ h₂

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate : CommitsCandidate
    (nemoRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  fun S _ _ _ _ hd => Nemo.isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict**, at Nemo's own direct
predicate. -/
theorem commitsDirect : CommitsDirect
    (nemoRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {U} V L r => Nemo.DirectCommitIn U V L r) :=
  fun S _ _ _ _ hc hd => Nemo.Decided.directCommit (S := S) hc hd

end NemoProperties

end LeanDag
