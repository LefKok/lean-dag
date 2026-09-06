import LeanDag.MahiMahi.Helpers.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate

/-!
# Mahi-Mahi as a carrier, and the properties its rules give

The five that need no induction. `Banded` and the two liveness
properties are in `MahiMahiProperties.lean`, which is downstream of the
adaptive arc; this file is upstream of every mechanism, which is where a
conformance layer has to sit (`docs/target-properties.md` §11.2c).

**One carrier per wave width, and that is the whole of what was in the
way.** `DagRule.Decided` takes a schedule, a universe, a view, a slot
and a verdict — and no wave length, so `w` has to be fixed before the
rule is. `audit-conformance.py` recorded that as "needs a carrier per
width" and the row read `--` for three arcs afterwards. Hybrid had
already answered it: `hybridRule (k : ℕ)` is a carrier per indirect
threshold, and nothing about a per-width family costs anything. The
recorded reason had stopped being a reason and nothing re-read it —
which is `docs/target-properties.md` §11.2d's finding, one level up.

**The conditions travel with the rule, not inside the property.**
`Agree R` and `Banded R` are predicates on `R` alone, so a rule whose
agreement needs `2 ≤ w` cannot state it as a hypothesis *of the
property*; it states it as a hypothesis of the theorem, at a carrier
where `w` is already fixed. Hybrid's `agree` takes `Admissible` and its
`banded` takes `0 < kt` for the same reason. Every Mahi-Mahi result
assumes `3 ≤ w` or more, so the condition is free at every use site.
-/

namespace LeanDag

namespace MahiMahiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Mahi-Mahi as a carrier**, one per wave width. -/
def mahiMahiRule (w : ℕ) : DagRule Validator BlockId Payload where
  Universe := BlockUniverse Validator BlockId Payload
  View := fun U => View Validator BlockId Payload U
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U => U.causal
  Decided := fun S _ V k v => MahiMahi.Decided (S := S) w _ V k v

/-- **And they are quorate**, at the core's fault model: validity's
counting clause read at the carrier, which is what chain quality reads
(`Properties/Arcs/Quality.lean`). -/
theorem quorate (w : ℕ) : Quorate (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) w) (coreReliability Validator) :=
  fun U => U.quorateOn

/-- **Two views decide alike.** MM2 under the property's name, at the
widths its safety arc covers. -/
theorem agree {w : ℕ} (hw : 2 ≤ w) :
    Agree (mahiMahiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w) :=
  fun S _ V₁ V₂ _ _ _ h₁ h₂ => MahiMahi.decided_unique (S := S) hw h₁ V₂ _ h₂

/-- **A commit names the slot's candidate.** Both committing
constructors carry `IsLeaderBlock`. -/
theorem commitsCandidate (w : ℕ) :
    CommitsCandidate (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  fun S _ _ _ _ hd => MahiMahi.isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict**, at Mahi-Mahi's own direct
predicate. -/
theorem commitsDirect (w : ℕ) :
    CommitsDirect (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
      (fun {U} V L r => MahiMahi.DirectCommitIn U V w L r) :=
  fun S _ _ _ _ hL hc => MahiMahi.Decided.directCommit (S := S) hL hc

end MahiMahiProperties

end LeanDag
