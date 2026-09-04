import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Mysticeti.Proof
import LeanDag.Barnacle.Nemo.Proof
import LeanDag.Barnacle.Odontoceti.Proof
import LeanDag.Barnacle.Hydrozoan.Proof
import LeanDag.Barnacle.OptimalHydrozoan.Proof
import LeanDag.Barnacle.Orcaella.Proof

/-!
# Six carriers at once

`docs/target-properties.md` §11.2. Ten decision rules in this
development and, until this file, two carriers — so the claim that the
properties are the right ones rested on two protocols.

**Barnacle's six instances are not six further protocols.** They are
Mysticeti, Odontoceti, Nemo, Hydrozoan, Optimal-Hydrozoan and Orcaella
presented through `BaseRule`, which is a superset of `DagRule`'s fields.
`BaseRule.toDagRule` therefore carries all six, and `Laws` — which each
already proves — is two of the six required properties verbatim: `agree`
is `Agree`, and `candidates` is `CommitsCandidate`.

**What this does not give, and the distinction is the point.** `Causal`
needs completeness and the round condition on references at the
*universe*, which `Laws` states only for views. `Banded` is the
induction a protocol owes and no interface can supply it. So six rules
gain two of six obligations here, and the remaining four are per-rule
work — which is the honest reading of what an interface buys: the laws
a protocol already had, renamed, and nothing deeper.

The carriers themselves are the gain. A rule with none shows nothing at
all; with one, every derivation in `Properties/Derived/` applies the
moment its band is proved.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## The carriers

`abbrev` rather than `def`, so a property stated at the carrier unfolds
to one stated at `toDagRule` and the generic bridges apply without a
rewrite. -/

section Mysticeti

variable [Faults Validator]

/-- Mysticeti as a `DagRule`, through Barnacle. -/
abbrev mysticetiRule : Properties.DagRule Validator BlockId Payload :=
  (mysticeti (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)).toDagRule

theorem mysticetiRule_agree :
    Properties.Agree (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) := agree_toDagRule _ (Mysticeti.holds _ _ _)

theorem mysticetiRule_commitsCandidate :
    Properties.CommitsCandidate (mysticetiRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) := commitsCandidate_toDagRule _ (Mysticeti.holds _ _ _)

end Mysticeti

section Nemo

/-- Nemo as a `DagRule`. -/
abbrev nemoRule : Properties.DagRule Validator BlockId Payload :=
  (nemo (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)).toDagRule

theorem nemoRule_agree :
    Properties.Agree (nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) := agree_toDagRule _ (Nemo.holds.1 _ _ _)

theorem nemoRule_commitsCandidate :
    Properties.CommitsCandidate (nemoRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) := commitsCandidate_toDagRule _ (Nemo.holds.1 _ _ _)

end Nemo

section Odontoceti

variable [Faults5 Validator] {B : Type} [LinearOrder B]

/-- Odontoceti as a `DagRule`. -/
abbrev odontocetiRule : Properties.DagRule Validator B Payload :=
  (odontoceti (Validator := Validator) (BlockId := B)
    (Payload := Payload)).toDagRule

theorem odontocetiRule_agree :
    Properties.Agree (odontocetiRule (Validator := Validator) (B := B)
      (Payload := Payload)) := agree_toDagRule _ (Odontoceti.holds.1 _ _ _)

theorem odontocetiRule_commitsCandidate :
    Properties.CommitsCandidate (odontocetiRule (Validator := Validator) (B := B)
      (Payload := Payload)) := commitsCandidate_toDagRule _ (Odontoceti.holds.1 _ _ _)

end Odontoceti

section Orcaella

variable [HybridFaults Validator] {B : Type} [LinearOrder B]

/-- Orcaella — the hybrid rule at threshold `k` — as a `DagRule`. The
threshold must be admissible, which is where the mixed fault bound
enters and why this carrier is one per `k` rather than one outright. -/
abbrev orcaellaRule (k : ℕ) (hk : Hybrid.Admissible Validator k) :
    Properties.DagRule Validator B Payload :=
  (orcaella (Validator := Validator) (BlockId := B)
    (Payload := Payload) k).toDagRule

theorem orcaellaRule_agree (k : ℕ) (hk : Hybrid.Admissible Validator k) :
    Properties.Agree (orcaellaRule (Validator := Validator) (B := B)
      (Payload := Payload) k hk) := agree_toDagRule _ (Orcaella.holds.1 _ _ _ k hk)

theorem orcaellaRule_commitsCandidate (k : ℕ) (hk : Hybrid.Admissible Validator k) :
    Properties.CommitsCandidate (orcaellaRule (Validator := Validator)
      (B := B) (Payload := Payload) k hk) := commitsCandidate_toDagRule _ (Orcaella.holds.1 _ _ _ k hk)

end Orcaella

section OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable [LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan as a `DagRule`**, which it had no way to be:
its verdicts are `DecidedOpt` over `OptUniverse`, and Barnacle's
instance is what puts them in the shared vocabulary. -/
abbrev optimalHydrozoanRule : Properties.DagRule Replica BlockId Unit :=
  (optimalHydrozoan (Replica := Replica) (BlockId := BlockId)).toDagRule

theorem optimalHydrozoanRule_agree :
    Properties.Agree (optimalHydrozoanRule (Replica := Replica) (BlockId := BlockId)) :=
  agree_toDagRule _ (OptimalHydrozoan.holds _ _)

theorem optimalHydrozoanRule_commitsCandidate :
    Properties.CommitsCandidate
      (optimalHydrozoanRule (Replica := Replica) (BlockId := BlockId)) :=
  commitsCandidate_toDagRule _ (OptimalHydrozoan.holds _ _)

end OptimalHydrozoan

/-! ## Hydrozoan is deliberately absent

`Barnacle/Hydrozoan/Statement.lean` instantiates `BaseRule` for it too,
so a carrier could be built here as well — and it would be a second
carrier for a protocol that already has one
(`Hydrozoan/Helpers/Carrier.lean`), proving two properties it already
proves. Two carriers for one rule is a way to make the conformance
audit read better than the development is, so it is not built. -/

end Barnacle

end LeanDag
