import LeanDag.Barnacle.Model.Rule
import LeanDag.Causality

/-!
# The carrier a target property talks about

`docs/target-properties.md` G0. Before locality can be *stated* there
must be a way to say "two DAGs agree above round `r`", and the
protocols' carriers differ — the core's universe has a payload,
Hydrozoan's has none, Nemo's is a different structure again.

**The carrier already exists, and it is `Barnacle.BaseRule`.** That
record carries a universe type, a view type dependent on it, and the
projections `block` and `ids` into the shared `Block` vocabulary, plus
`viewIds` and the decision relation as a field. Six protocols
instantiate it. Nothing new is needed, and this file adds only what
`BaseRule` and `Laws` leave out.

**Why a record of uses is enough here, when `hydrozoan-integration.md`
§9 says it is not.** That section argues no `BaseRule`-shaped interface
can carry `decided_chop`, because `BaseRule.Decided` is a field with no
constructors while the transport proof is a structural induction over
derivations. The argument is correct and it does not apply to this arc,
because **nothing here inducts on `Decided`**. Locality and persistence
are *hypotheses*; a protocol discharges them by induction over its own
relation, where the constructors are available, and the mechanism
theorems then consume them without induction. §9 blocks deriving the
properties from the interface, not assuming them over it.

Two things this file supplies:

* `Causal` — that a rule's universes are closed under references and
  respect the predecessor condition. `Laws` states both of these for
  *views* (`view_complete`) and neither for universes, though every
  instance has them.
* `AgreeAbove` — the agreement notion locality is stated against.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A rule's universes are block DAGs.** The structural facts
`CausalStructure` names, which `Laws` states for views and not for
universes. -/
def Causal (R : Barnacle.BaseRule Validator BlockId Payload) : Prop :=
  ∀ U : R.Universe, CausalStructure (R.block U) (R.ids U)

/-- **Two universes agree above round `r`.** Everything a rule can read
of a block — its presence, round, author and references — is the same
in both, for blocks at round `r` and above.

`mem` pairs presence with the round condition rather than stating them
separately, which is what makes the relation symmetric: without it,
"present and above `r`" could be read in one universe and not the
other, and the definition would name a direction it does not mean.

References are compared **strictly** above `r`: a truncation retains
its bottom layer's blocks but empties their references, since what they
referenced is gone. Every rule reads a vote from a *parent*, so a block
at exactly `r` contributes its presence and its author but no vote,
which is what the clause says. -/
structure AgreeAbove (R : Barnacle.BaseRule Validator BlockId Payload)
    (U U' : R.Universe) (r : ℕ) : Prop where
  /-- The same blocks are present at and above `r`. -/
  mem : ∀ b, (b ∈ R.ids U ∧ r ≤ (R.block U b).round) ↔
    (b ∈ R.ids U' ∧ r ≤ (R.block U' b).round)
  /-- At and above `r`, a block sits at the same round. -/
  round : ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (R.block U' b).round = (R.block U b).round
  /-- And has the same author. -/
  creator : ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (R.block U' b).creator = (R.block U b).creator
  /-- Strictly above `r`, it references the same blocks. -/
  refs : ∀ b, b ∈ R.ids U → r < (R.block U b).round →
    (R.block U' b).refs = (R.block U b).refs

namespace AgreeAbove

variable {R : Barnacle.BaseRule Validator BlockId Payload} {U U' : R.Universe} {r : ℕ}

/-- Agreement is reflexive. -/
theorem refl : AgreeAbove R U U r :=
  { mem := fun _ => Iff.rfl
    round := fun _ _ _ => rfl
    creator := fun _ _ _ => rfl
    refs := fun _ _ _ => rfl }

/-- And symmetric — which the paired `mem` clause is what secures. -/
theorem symm (h : AgreeAbove R U U' r) : AgreeAbove R U' U r where
  mem := fun b => (h.mem b).symm
  round := fun b hb hr =>
    have hU := (h.mem b).mpr ⟨hb, hr⟩
    (h.round b hU.1 hU.2).symm
  creator := fun b hb hr =>
    have hU := (h.mem b).mpr ⟨hb, hr⟩
    (h.creator b hU.1 hU.2).symm
  refs := fun b hb hr =>
    have hU := (h.mem b).mpr ⟨hb, le_of_lt hr⟩
    have hround := h.round b hU.1 hU.2
    (h.refs b hU.1 (by omega)).symm

end AgreeAbove

/-- **What a block above the cut references is itself above the cut** —
a fact about causal structure alone, and the step an induction over a
derivation's anchors needs, since it says the region agreement covers
is closed under the recursion. -/
theorem Causal.refs_above {R : Barnacle.BaseRule Validator BlockId Payload}
    (hc : Causal R) {U : R.Universe} {r : ℕ}
    {b : BlockId} (hb : b ∈ R.ids U) (hr : r < (R.block U b).round)
    {j : BlockId} (hj : j ∈ (R.block U b).refs) :
    j ∈ R.ids U ∧ r ≤ (R.block U j).round := by
  refine ⟨(hc U).complete b hb j hj, ?_⟩
  have := (hc U).refs_round b hb j hj
  omega

end Properties

end LeanDag
