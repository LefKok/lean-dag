import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Helpers.Mysticeti
import LeanDag.MahiMahi.Carrier

/-!
# Barnacle over Mahi-Mahi — statement

The wave-`w` rule as a base rule with its laws, as a live rule with its
descent laws at slack `f`, and A4 for it under round-robin. The
universe and views are the core's, so the history view is
`historyViewOf`; the wave length is `w`, which is what the rule's
indirect eligibility reads.

Every statement carries `w` as a parameter, as the carrier does, and
the committee bound round-robin needs — `w · f + 1 ≤ n` — is taken as
a hypothesis: the fault model gives `3f + 1 ≤ n`, and a wave longer than
three asks for more.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Mahi-Mahi as a base rule** — the data, at wave `w`. -/
def mahiMahi [Faults Validator] (w : ℕ) : BaseRule Validator BlockId Payload where
  Universe := BlockUniverse Validator BlockId Payload
  View := fun U => LeanDag.View Validator BlockId Payload U
  block := fun U => U.block
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U => U.causal
  full := fun U => LeanDag.View.full U
  historyView := fun U A hA => historyViewOf U A hA
  waveLength := w
  DirectCommitIn := fun V L r => MahiMahi.DirectCommitIn _ V w L r
  decDirect := fun _ _ _ => inferInstance
  Decided := fun S {U} V k v => MahiMahi.Decided (S := S) w U V k v

/-- **Mahi-Mahi as a live rule**: a DAG is good when a correct quorum is
synchronised from `Rnd` and populates the rounds to `N`. -/
def mahiMahiLive [Faults Validator] (w : ℕ) : LiveRule Validator BlockId Payload :=
  { mahiMahi w with
    Good := fun U Rnd N => ∃ T ⊆ (Correct : Finset Validator),
      quorumCard Validator ≤ T.card ∧ SynchronisedOn U T Rnd ∧
      ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn U T r }

namespace MahiMahi

/-- **Mahi-Mahi satisfies the laws** at every wave of length at least two. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (w : ℕ), 2 ≤ w →
    BaseRule.Laws (mahiMahi (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)

/-- **Mahi-Mahi has the descent laws at slack `f`**, at every wave of
length at least four — the length its support's coverage law needs. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] (w : ℕ), 4 ≤ w →
    (mahiMahiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w).Descent
      F.f

/-- **Mahi-Mahi under round-robin is live at every count**, with gap
`n + w − 1`, on a committee of at least `w · f + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (w : ℕ), 4 ≤ w → w * F.f + 1 ≤ n →
    ∀ (W : ℕ) (hk : Keyed (roundRobin n hn) W) (m : ℕ) (hm : 0 < m) (hmax : m ≤ W),
    (mahiMahiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload) w).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + w - 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end MahiMahi

end Barnacle

end LeanDag
