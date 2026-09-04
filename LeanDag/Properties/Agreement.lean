import LeanDag.Properties.Carrier

/-!
# Agreement above a round: the vocabulary locality is stated in

`docs/target-properties.md` §3.1, the property garbage collection rests
on.

*If two DAGs agree above round `r`, they decide alike at every slot
whose round is at least `r`.*

Stated as agreement rather than existence, which is what makes it worth
having: a protocol proving it gets garbage collection at **every**
admissible horizon, not at one. The indirect rule's recursion runs
upward from the slot — an anchor sits above what it decides — so the
region the hypothesis covers is closed under the recursion, which is
`Causal.refs_above`. The chain is unbounded above, so no window
formulation would serve; the condition has to be a genuine lower bound.

**What locality does not cover.** A truncation restricts *and* rebases:
it drops what lies below the horizon and renumbers what remains to
start at zero. Locality is about the restriction alone, and the
renumbering is `Reindex.lean`. The two compose only through the
universe that has been restricted and not yet renumbered, which
`Arcs/GC.lean` takes as a parameter and a protocol must exhibit.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Two views agree above a round.** Read at the source universe's
rounds, which `RebasedAbove` makes the target's shifted rounds wherever
the question arises.

A truncation asks exactly this of its views, so there is one definition
where there were two: `ViewTruncates` was the same proposition under
another name. -/
def ViewAgreeAbove (R : DagRule Validator BlockId Payload) {U U' : R.Universe}
    (V : R.View U) (V' : R.View U') (r : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (b ∈ R.viewIds V ↔ b ∈ R.viewIds V')


end Properties

end LeanDag
