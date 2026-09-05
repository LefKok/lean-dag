import LeanDag.Properties.Commit
import LeanDag.Properties.Sustain
import LeanDag.Properties.Deliver
import LeanDag.Density

/-!
# The liveness precondition is reachable

`LeaderCommits R Live` says that *wherever* the protocol's own
precondition `Live` holds, a slot led by a reliable validator commits.
It does not say that `Live` ever holds. `Live` is a parameter of the
property, supplied by the rule, so a rule that chose an unsatisfiable
precondition would prove `LeaderCommits` with nothing in it — and
`decidedBelow_of_run`, `Arcs/Quality.lean`'s chain quality and
Barnacle's `LiveOn` would all inherit the emptiness. That is the
vacuity of `docs/target-properties.md` §3.4 and §3.6, on the liveness
side.

`LiveReachable` is the guard. It is not "prove `Live`", which would be
false and should be: `Live` is a precondition, and on a DAG where the
network stalled it does not hold. It is the implication from concrete
facts about the DAG to the rule's own precondition:

    synchronised + populated + the view caught up   ⟹   Live

Three hypotheses, all already stated at the carrier
(`Properties/Sustain.lean`, `Properties/Deliver.lean`), and no free
predicate: the antecedent is fixed, so the obligation cannot be met by
choosing a convenient one.

**The shape is not new.** `Barnacle.LiveRule.GoodGives` is this
implication, and six rules discharge it. Two things are gained by
stating it here instead. It becomes available to a rule with no
`LiveRule` instance — FinWhale and Mahi-Mahi have none, so neither can
write `GoodGives` at all. And it closes the vacuity rather than moving
it: `GoodGives` quantifies over `LiveRule.Good`, itself an opaque
field, so a rule could satisfy it with a `Good` nothing satisfies.

`exists_decided_of_reachable` is the consumer test. Its statement
mentions `Live` nowhere, which is the point: a rule with both
properties commits a reliably-led slot on any DAG the reliable set
produced and delivered, and no reader has to inspect the rule's
precondition to believe it.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **The rule's liveness precondition is reachable.** On a universe the
reliable set has populated over `[Rnd, N]` and delivered from `Rnd`, and
a view caught up to `N`, the rule's own `Live` holds at every slot from
`Rnd` whose wave fits under the horizon.

`wave` is the rule's, as `c` is in `Descends`: the core reads two rounds
above a slot, Odontoceti one, Mahi-Mahi `w − 1`. The window is the
single slot `[k, k + 1)`, which is what `LeaderCommits` needs to reach
that slot and the least a precondition can be asked to cover. -/
def LiveReachable (R : DagRule Validator BlockId Payload)
    (rel : Reliability Validator) (wave : ℕ)
    (Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop) :
    Prop :=
  ∀ (U : R.Universe) (Rnd N : ℕ),
    SynchronisedOn R U rel.correct Rnd →
    (∀ r, Rnd ≤ r → r ≤ N → PopulatedOn R U rel.correct r) →
    ∀ (S : Slots Validator) (V : R.View U) (k : ℕ),
      CoversUpto R V N → Rnd ≤ S.slotRound k → S.slotRound k + wave ≤ N →
        Live S V rel.correct k (k + 1)

/-- **A reliably-led slot commits on a DAG the reliable set produced.**
The consumer test for the pair, and the statement the vacuity guard
exists to make believable: the rule's precondition does not appear, so
the conclusion cannot be true by the precondition being empty. -/
theorem exists_decided_of_reachable {rel : Reliability Validator} {wave : ℕ}
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop}
    (hlc : LeaderCommits R Live) (hlr : LiveReachable R rel wave Live)
    {U : R.Universe} {Rnd N : ℕ} (hs : SynchronisedOn R U rel.correct Rnd)
    (hpop : ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn R U rel.correct r)
    (S : Slots Validator) (V : R.View U) (k : ℕ) (hcov : CoversUpto R V N)
    (hRnd : Rnd ≤ S.slotRound k) (hN : S.slotRound k + wave ≤ N)
    (hlead : S.leader k ∈ rel.correct) :
    ∃ L, DecidedBelow R S (k + 1) V k (some L) :=
  hlc S V rel.correct k (k + 1) (hlr U Rnd N hs hpop S V k hcov hRnd hN)
    k le_rfl (Nat.lt_succ_self k) hlead

end Properties

end LeanDag
