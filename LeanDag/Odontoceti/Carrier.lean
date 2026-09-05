import LeanDag.Odontoceti.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct

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
through `Barnacle.odontocetiRule`: a protocol's conformance should not
route through a mechanism (`docs/target-properties.md` §8). -/
def odontocetiRule : DagRule Validator BlockId Payload where
  Universe := BlockUniverse Validator BlockId Payload
  View := fun U => View Validator BlockId Payload U
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  Decided := fun S _ V k v => Odontoceti.Decided (S := S) _ V k v

/-- Odontoceti's universes are block DAGs — the same argument as the
core's, the universe type being the same. -/
theorem causal : Causal (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun U =>
    { complete := fun i hi j hj => U.complete i hi j hj
      refs_round := fun i hi j hj => U.round_of_mem_refs hi hj }

/-- **Two views decide alike.** O5 under the property's name. -/
theorem agree : Agree (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun S _ V₁ V₂ _ _ _ h₁ h₂ =>
    Odontoceti.decided_unique (S := S) h₁ V₂ _ h₂

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate : CommitsCandidate
    (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  fun S _ _ _ _ hd => Odontoceti.isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict**, at Odontoceti's own direct
predicate. -/
theorem commitsDirect : CommitsDirect
    (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {U} V L r => Odontoceti.DirectCommitIn U V L r) :=
  fun S _ _ _ _ hc hd => Odontoceti.Decided.directCommit (S := S) hc hd

end OdontocetiProperties

end LeanDag
