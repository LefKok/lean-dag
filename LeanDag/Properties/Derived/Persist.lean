import LeanDag.Properties.Extends

/-!
# Persistence

`docs/target-properties.md` §11.4b. A statement a mechanism reads, and
no protocol proves directly any more: both instances obtain it from
`Banded` (`Derived/FromBand.lean`). It stays a named property because
that is what the crash-recovery arc consumes, and because a rule with
no band could still prove it on its own.

*Verdicts survive extension of the DAG.* This is not a consequence of
safety; it is the **prerequisite** for safety to mean anything as a DAG
grows. Every protocol's uniqueness theorem is stated for two views of
the *same* universe. To compare a replica that decided on the DAG it
held against one deciding later on a larger DAG, the first derivation
must be moved into the second universe, and that move is persistence.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Persistence, under a condition on the extension.** A verdict
reached on `V` is reached again on any larger view of any extension the
condition admits.

`Ok` is where the grading lives, and it sees the **source view** as
well as the two universes, since a condition of this kind is about what
a view *held* rather than about the universes alone.

**No protocol here now needs one.** The core once did: its skip
quantified over the candidates a universe holds, so a slot with none was
skipped for nothing and a later candidate broke the derivation, and the
grade named the quorum that would have blamed it. That premise was the
defect, not the grade — a skip resting on the absence of a candidate is
not final, which is the one thing a skip rule exists to be — and it has
been replaced by a count of blockers. Both instances are now
`Unconditional`. The parameter is kept for a rule that decides on the
absence of a block, rather than on the contents of blocks that are
present; such a rule would need it. -/
def Persist (R : DagRule Validator BlockId Payload)
    (Ok : Slots Validator → ∀ (U U' : R.Universe), R.View U → Prop) : Prop :=
  ∀ (S : Slots Validator) (U U' : R.Universe), Extends R U U' →
    ∀ (V : R.View U) (V' : R.View U'), Ok S U U' V → R.viewIds V ⊆ R.viewIds V' →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V k v → R.Decided S V' k v

namespace Persist

variable {Ok Ok' : Slots Validator → ∀ (U U' : R.Universe), R.View U → Prop}

/-- A protocol proving persistence under a weaker condition proves it
under a stronger one, so the grades are comparable. -/
theorem mono (h : Persist R Ok) (himp : ∀ S U U' V, Ok' S U U' V → Ok S U U' V) :
    Persist R Ok' :=
  fun S U U' he V V' hok hV k v hd => h S U U' he V V' (himp S U U' V hok) hV k v hd

/-- **The unconditional grade**, which is what an evidence-backed rule
should reach: verdicts survive every extension. -/
abbrev Unconditional (R : DagRule Validator BlockId Payload) : Prop :=
  Persist R fun _ _ _ _ => True

/-- An unconditional rule persists under any condition whatsoever. -/
theorem of_unconditional (h : Unconditional R) : Persist R Ok :=
  mono h fun _ _ _ _ _ => trivial

end Persist

end Properties

end LeanDag
