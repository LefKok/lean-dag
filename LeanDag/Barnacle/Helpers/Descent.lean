import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Derived.Descent

/-!
# The descent laws, from the target properties

Not part of the audit surface. `docs/target-properties.md` §11.2's
tier 3: what a protocol has to show, in the properties' vocabulary, for
Barnacle's liveness mechanism to run over it.

The answer is **two properties and one bridge**, and the bridge is the
only rule-specific part.

* `LiveRule.Descent.indirect` **is** `Properties.Indirect` at the
  eligibility every Barnacle rule uses — an anchor a wave above the slot
  — read at the schedule it is given. Nothing is lost and nothing added:
  the property's extra clause, that the verdict survives a reassignment
  of leaders elsewhere, is what `Descends` needs and this law does not.

* `LiveRule.Descent.goodLeaders` is `Properties.LeaderCommits` at the
  one-slot window `[κ, κ + 1)`, with the bound thrown away. `LeaderCommits`
  is the stronger claim: it produces the commit at a tight bound, which
  the mechanism's own law never asked for.

* The bridge says the rule's notion of a **good DAG** implies the
  protocol's own liveness precondition. That cannot be generic: `Good`
  is a field of `LiveRule` and `Live` is a parameter of `LeaderCommits`,
  and each rule chooses both. What the bridge is not allowed to do is
  prove anything about verdicts, and it cannot — it never sees
  `Decided`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A Barnacle rule's eligibility**, as the properties read it: an
anchor decides a slot when it sits a full wave above it. Every rule of
the development uses this and differs only in the wave. -/
def LiveRule.elig (R : LiveRule Validator BlockId Payload) : (ℕ → ℕ) → ℕ → ℕ → Prop :=
  fun sr i j => sr i + R.waveLength ≤ sr j

/-- **What a good DAG must give the protocol.** The rule-specific half
of the bridge: on a DAG the rule calls good from `Rnd` to `N` there is a
set `T` missing at most `slack` validators, and for a `T`-led slot whose
wave fits under the horizon the protocol's own liveness precondition
holds over that one slot. -/
def LiveRule.GoodGives (R : LiveRule Validator BlockId Payload) (slack : ℕ)
    (Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop) :
    Prop :=
  ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ (S : Slots Validator) (V : R.View U) (κ : ℕ), R.toBaseRule.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N → S.leader κ ∈ T →
        Live S V T κ (κ + 1)

/-- **The descent laws, from the properties.** A rule that shows
`LeaderCommits` and `Indirect`, and whose good DAGs meet its own
liveness precondition, has Barnacle's liveness interface — and so, by
`Heads/Proof.lean`, `LiveOn` under round-robin at every leader count,
with no further argument about its decision relation. -/
theorem descent_of_properties (R : LiveRule Validator BlockId Payload) {slack : ℕ}
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop}
    (hlc : Properties.LeaderCommits R.toBaseRule.toDagRule Live)
    (hind : Properties.Indirect R.toBaseRule.toDagRule R.elig)
    (hgood : R.GoodGives slack Live) : R.Descent slack where
  goodLeaders := by
    intro U Rnd N hg
    obtain ⟨T, hcard, hT⟩ := hgood U Rnd N hg
    refine ⟨T, hcard, ?_⟩
    intro S V κ hcov hRnd hN hlead
    obtain ⟨L, hL⟩ := hlc S V T κ (κ + 1) (hT S V κ hcov hRnd hN hlead) κ le_rfl
      (Nat.lt_succ_self κ) hlead
    exact ⟨L, hL.2.1⟩
  indirect := by
    intro S U V i j A hij hj hmid
    exact hind.decided S V hij hj hmid

end Barnacle

end LeanDag
