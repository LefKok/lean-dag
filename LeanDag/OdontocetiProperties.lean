import LeanDag.Odontoceti.Decision
import LeanDag.Properties.Band
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct

/-!
# Odontoceti conforms to the target properties

`docs/target-properties.md` §11.2. The third rule to be put through the
properties at its own carrier, and the first not written for them.

**Why this rule and not another.** Odontoceti mirrors the core
constructor for constructor at a shorter wavelength —
`decisionRound k = slotRound k + 1`, no certificate round — so if the
six obligations are the right six, the differences it does have should
be the only work. That is what a third instance is for.

**Four of the six are here.** `Banded` is not, and the reason is worth
recording: it was blocked, by a defect in the protocol rather than in
the properties, and the block is now cleared.

`Decided.directSkip` used to quantify over the candidates the universe
holds, so a slot with no candidate was skipped *vacuously*.
`AgreeBand`'s membership clause runs one way — a block of `U` in the
band is a block of `U'` — because a band must admit universes that hold
*more*. A candidate present in `U'` and absent from `U` was therefore
beyond reach, and the goal `L ∈ U.ids` could not be closed.

That was the core's own defect, before its repair
(`docs/target-properties.md` §3.2), and the repair transferred without
change: Odontoceti's `DirectSkipIn` and the core's are the same
predicate, so `Decided.directSkip` now takes `DirectSkipSlotIn` and the
band's case closes by `directSkipSlotIn_band`. What is left is the
induction itself, over four constructors.
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
