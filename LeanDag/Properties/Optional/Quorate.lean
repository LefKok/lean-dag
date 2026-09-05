import LeanDag.Properties.Carrier
import LeanDag.Density

/-!
# What a rule owes about its own validity

`docs/target-properties.md` §11.4, the carrier law chain quality asked
for. `Properties/Optional/` holds what a protocol **may** show and need
not, and this is the third such property.

**Who asks for it.** Chain quality
(`Properties/Arcs/Quality.lean`): every guarantee it makes rests on
density, and density rests on one clause of block validity — a
non-genesis block references a quorum of distinct authors one round
below. `Causal` states the other two clauses a DAG needs, references
being present and sitting one round down; this is the counting clause
that goes with them.

**Why a property and not a carrier field.** §11.4 predicted a field, on
the precedent of `viewSound` and `viewComplete`, which are fields
because every view type carries the proof already. Validity is the same
kind of fact, but `Causal` is the closer precedent and it is a `Prop`:
a structural claim about the universe, stated once and discharged per
rule, costing no carrier a change. Making it a field would also oblige
`Barnacle.BaseRule`, which has no validity clause either, and through it
six more instances. The content is identical; only the blast radius
differs.

**Why optional rather than a seventh obligation.** A rule that shows the
six composes with every mechanism in the development except this one.
Chain quality is a guarantee a deployment may or may not want to quote,
and `CommitsDirect` and `SkipsUnsupported` are already in this category
for the same reason. Every rule here can discharge it in a line, which
is the point: the cost of the mechanism is one projection, not an arc.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A rule's universes are quorate.** Every non-genesis block
references blocks by at least `n − slack` distinct authors — the
counting clause of validity, which is what density counts against.

The fault model comes in as a `Reliability`: which validators the count
is about, how many may be outside them, and that those are a minority.
Six fault classes are in play across the development and each supplies
one in a line, which is why neither this property nor `LeanDag.Density`
names any of them. -/
def Quorate (R : DagRule Validator BlockId Payload) (rel : Reliability Validator) : Prop :=
  ∀ U : R.Universe, QuorateOn (R.block U) (R.ids U) rel

end Properties

end LeanDag
