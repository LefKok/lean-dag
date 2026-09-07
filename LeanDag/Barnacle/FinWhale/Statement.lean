import LeanDag.Barnacle.Model.Heads
import LeanDag.FinWhale.Carrier
/-!
# Barnacle over FinWhale — statement

FinWhale as a base rule with its laws, as a live rule with its descent
laws at slack `f`, and A4 for it under round-robin. The universe is
FinWhale's own `Dag` and a view is a reference-closed subset of it, so
the history view is the causal history of the anchor, closed by
construction. The wave length is three, which is what the rule's
eligibility reads; the direct predicate is the one the carrier's
`CommitsDirect` is stated at.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **FinWhale as a base rule** — the data. -/
def finWhale : BaseRule Validator BlockId Payload where
  toDagRule := FinWhaleProperties.finWhaleRule
  full := fun D => ⟨D.ids, Finset.Subset.rfl, D.complete⟩
  historyView := fun D A hA =>
    ⟨historyFrom D.block A,
      fun i hi => (LeanDag.FinWhale.causalStructure D).mem_ids_of_reaches hA
        (((LeanDag.FinWhale.causalStructure D).mem_history_iff hA).mp hi),
      fun i hi j hj => ((LeanDag.FinWhale.causalStructure D).mem_history_iff hA).mpr
        (Relation.ReflTransGen.tail
          (((LeanDag.FinWhale.causalStructure D).mem_history_iff hA).mp hi) hj)⟩
  waveLength := 3
  DirectCommitIn := fun V L _ => LeanDag.FinWhale.DirectCommit (V.toRecord) L
  decDirect := fun V L _ => inferInstanceAs (Decidable
    (LeanDag.FinWhale.DirectCommit (V.toRecord) L))

/-- **FinWhale as a live rule**: a DAG is good when a correct quorum is
synchronised from `Rnd` and populates the rounds to `N`. -/
def finWhaleLive : LiveRule Validator BlockId Payload :=
  { finWhale with
    Good := fun D Rnd N => ∃ T ⊆ (Correct : Finset Validator),
      quorumCard Validator ≤ T.card ∧ SynchronisedFrom D.block D.ids T Rnd ∧
      ∀ r, Rnd ≤ r → r ≤ N → PopulatedFrom D.block D.ids T r }

namespace FinWhale

/-- **FinWhale satisfies the laws.** -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LeanDag.FinWhale.Params Validator] [LinearOrder BlockId],
    BaseRule.Laws (finWhale (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

/-- **FinWhale has the descent laws at slack `f`.** -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LeanDag.FinWhale.Params Validator] [LinearOrder BlockId],
    (finWhaleLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **FinWhale under round-robin is live at every count**, with gap `n + 2`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)] [LeanDag.FinWhale.Params (Fin n)]
    (BlockId Payload : Type) [LinearOrder BlockId]
    (W : ℕ) (hk : Keyed (roundRobin n hn) W) (m : ℕ) (hm : 0 < m) (hmax : m ≤ W),
    (finWhaleLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 2)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end FinWhale

end Barnacle

end LeanDag
