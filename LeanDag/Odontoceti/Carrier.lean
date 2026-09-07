import LeanDag.Odontoceti.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
/-!
# Odontoceti as a carrier, and the three properties its own rules give

`docs/target-properties.md` §8. The carrier and the properties whose
proof is a single Odontoceti theorem apiece: `Agree` is O5,
`CommitsCandidate` is `isLeaderBlock_of_decided`, `CommitsDirect` is the
direct constructor.

**Why these three sit here and not in `OdontocetiProperties.lean`.**
That file holds the band and everything the band gives, and it imports
the adaptive arc for the bounded relation — so it is downstream of a
mechanism. Anything a mechanism needs to consume has to be upstream of
every mechanism, and these three are consumed by the adaptive arc and by
Barnacle. Hydrozoan has had this shape since its own carrier was
written (`Hydrozoan/Helpers/Carrier.lean`); Odontoceti acquired it when
`scripts/audit-bespoke.py` found the adaptive arc reaching past it to
`Odontoceti.decided_unique`.
-/

namespace LeanDag

namespace OdontocetiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Odontoceti as a carrier**, at its own namespace rather than
through Barnacle's `odontoceti.toDagRule`, which now *is* this carrier: a protocol's conformance should not
route through a mechanism (`docs/target-properties.md` §8). -/
def odontocetiRule : DagRule Validator BlockId Payload :=
  (Odontoceti.odontocetiAnchored Validator BlockId Payload).toDagRule

/-- **Odontoceti's universes are quorate**: the core's `BlockUniverse`,
so the core's clause, at the five-fault committee. -/
theorem quorate : Quorate (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun U => BlockUniverse.quorateOn U

/-- **P3′ at the carrier.** -/
theorem selfParent : SelfParent (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun U b hb hr => (U.valid b hb).self_parent hr

/-- **One block per correct author per round.** -/
theorem noEquiv : NoEquiv (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** O5 under the property's name. -/
theorem agree : Agree (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.agree Odontoceti.odontocetiLaws

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate : CommitsCandidate
    (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.commitsCandidate

/-- **And a direct commit is a verdict**, at Odontoceti's own direct
predicate. -/
theorem commitsDirect : CommitsDirect
    (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {U} V L r => Odontoceti.DirectCommitIn U V L r) :=
  AnchoredRule.commitsDirect

end OdontocetiProperties

end LeanDag
