import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Coverage

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

/-- **A good DAG, in the properties' terms**: some quorum of the fault
model has covered it from `Rnd` and populated it to `N`. Every rule's
`Good` is this at its own quorum, and the bridge each rule supplies is
the identity up to how its quorum is spelled. -/
def GoodOf (R : Properties.DagRule Validator BlockId Payload) (rel : Reliability Validator)
    (U : R.Universe) (Rnd N : ℕ) : Prop :=
  ∃ T, rel.IsQuorum T ∧ Timed.SynchronisedOn R U T Rnd ∧
    ∀ r, Rnd ≤ r → r ≤ N → Properties.PopulatedOn R U T r

/-- **The descent laws, from a support.** A rule with `OfCoverage` and
`Commits` at a fault model, `Indirect` at its eligibility, a wave no
longer than the rule's, and good DAGs that are good in the properties'
sense has Barnacle's liveness interface at the model's slack — and so,
by `Heads/Proof.lean`, `LiveOn` under round-robin at every leader count.
No `LeaderCommits` and no precondition of the rule's own appear: A4 is
`Timed.exists_decided_of_coverage` at the quorum a good DAG names. -/
theorem descent_of_support (R : LiveRule Validator BlockId Payload)
    (sp : Properties.Support R.toBaseRule.toDagRule) {rel : Reliability Validator}
    (hcov : Timed.OfCoverage sp rel) (hlc : sp.Commits rel)
    (hind : Properties.Indirect R.toBaseRule.toDagRule R.elig)
    (hwave : sp.wave ≤ R.waveLength)
    (hgood : ∀ U Rnd N, R.Good U Rnd N → GoodOf R.toBaseRule.toDagRule rel U Rnd N) :
    R.Descent rel.slack where
  goodLeaders := by
    intro U Rnd N hg
    obtain ⟨T, hq, hs, hpop⟩ := hgood U Rnd N hg
    refine ⟨T, by have := hq.2; omega, ?_⟩
    intro S V κ hcovV hRnd hN hlead
    obtain ⟨L, hL⟩ := Timed.exists_decided_of_coverage sp hcov hlc hq hs hpop S V κ
      (fun b hb hr => hcovV b hb hr) hRnd (by omega) hlead
    exact ⟨L, hL.2.1⟩
  indirect := by
    intro S U V i j A hij hj hmid
    exact hind.decided S V hij hj hmid

end Barnacle

end LeanDag
