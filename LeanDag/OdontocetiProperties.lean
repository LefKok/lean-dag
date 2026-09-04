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

**Four of the six are here, and `Banded` is blocked** — by a defect in
the protocol, not in the properties. `Decided.directSkip` quantifies
over the candidates the universe holds:

```
| directSkip {k} : (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
    Decided U V k none
```

so a slot with no candidate is skipped *vacuously*. `AgreeBand`'s
membership clause runs one way — a block of `U` in the band is a block
of `U'` — because a band must admit universes that hold *more*. So a
candidate present in `U'` and not in `U` is beyond reach, and the skip
does not transport. The goal that cannot be closed is `L ∈ U.ids`, from
`L ∈ U'.ids`.

This is the core's own defect, before its repair: §3.2 records it, and
`Mysticeti.Decided.directSkip` now takes `DirectSkipSlotIn` — a count of
voting-round blocks referencing *no* candidate of the slot — which is a
fact about blocks `U` already holds, and so transports. Odontoceti's
`DirectSkipIn` counts blames against one candidate and has the same
shape the core's had.

The repair is the same shape too, and it is a change to Odontoceti's
decision relation rather than to this file, so it is not made here.
`docs/target-properties.md` §3.12 records what it would cost.
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
