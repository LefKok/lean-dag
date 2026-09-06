import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist

/-!
# Skippability: settling an unsupported slot without an anchor

**Optional.** `docs/target-properties.md` §11.4c. A protocol may show
this and need not. It is a claim about *promptness*, not about liveness,
and the earlier reading of it as an obligation was wrong for a reason
worth recording.

## What it says

*If every block of `T` one round above a slot references none of that
slot's candidates, the protocol skips the slot* — with the size `T` must
reach left as a grade, since it differs by rule.

## Why it is not an obligation

It was introduced as the residue `Sustains` leaves behind. `Sustains`
says a mechanism destroys no vote and silences no producer, and the
crash-recovery fill still adds a *candidate*: the recovering replica's
block lands on a slot that replica leads. A candidate nothing old
references cannot be committed, and the concern was that for some rules
it could not be skipped either, leaving the slot dead.

That concern was inherited from a defect since fixed. Under the old
direct skip a candidate-less slot was decided `none` for nothing, so a
fill adding a candidate took a *decided* slot back to undecided and
something had to restore the verdict. The rule now counts blockers
(report §3.5), so the slot was never decided in the first place. It is
undecided until an anchor above resolves it, which is ordinary
operation.

**And the anchor does resolve it.** Every rule's anchored case splits on
whether some candidate is reachable from the anchor, and that split is
total: a fresh candidate falls on the negative side, so the slot is
skipped indirectly. It cannot fall on the positive side, because nothing
old references it and the anchor is old — which both protocols prove as
part of `Banded` (`not_certifiedIn_band_novel`, and for Hydrozoan
`not_weakLinked_bnd_novel`, which is what protects its minimality
tie-break). So eventual decision after a fill rests on `Descends`, an
obligation stated over the anchored rule that every protocol has, rather
than on a direct rule that only some do.

Demanding a direct skip would exclude rules that have none. Nemo has
none, and nothing in the setting says a rule must.

## What the grade still gives

Promptness, and a deployment condition. Hydrozoan needs `qFast ≤ |T|`,
because its skip is `qFast` blames at the slot. A quorum of correct
replicas has `q = n − f − c` and `qFast = n − p`, so a correct quorum
suffices exactly when `f + c ≤ p` — which is the condition `hydrozoan-integration.md` §2 records, as a grade.
The core reaches it at a correct quorum. Optimal-Hydrozoan's skip wants
`qCert` blames and a no-evidence quorum at the decision round, two
rounds of presence where this supplies one, so its instance would
reshape the statement.

`unsupported_of_novel` is the bridge from the mechanism's side: after an
extension, any slot all of whose candidates are novel is unsupported by
the old blocks, because an old block references only old blocks
(`Extends.old_refs_old`). A rule with this property settles such a slot
at once; a rule without it waits for an anchor.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A slot's candidates are unsupported by `T`**: every `T`-authored
block in view one round above the slot references none of them. -/
def Unsupported (R : DagRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (V : R.View U) (T : Finset Validator) (k : ℕ) : Prop :=
  ∀ c, c ∈ R.viewIds V → (R.block U c).creator ∈ T →
    (R.block U c).round = S.slotRound k + 1 →
    ∀ L, R.IsCandidate S U k L → L ∉ (R.block U c).refs

/-- **`T` is present at a round, in view**: each member has a block
there that the view holds. -/
def PresentAt (R : DagRule Validator BlockId Payload) {U : R.Universe} (V : R.View U)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ c, c ∈ R.viewIds V ∧ (R.block U c).creator = v ∧ (R.block U c).round = r

/-- **Skippability, graded.** A slot whose candidates `T` does not
support is skipped, provided `T` meets the protocol's condition. -/
def SkipsUnsupported (R : DagRule Validator BlockId Payload)
    (Ok : Finset Validator → Prop) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (T : Finset Validator) (k : ℕ),
    Ok T → PresentAt R V T (S.slotRound k + 1) → Unsupported R S U V T k →
    R.Decided S V k none

namespace SkipsUnsupported

variable {Ok Ok' : Finset Validator → Prop}

end SkipsUnsupported

/-- **The bridge from the mechanism.** After an extension, a slot all of
whose candidates are novel is unsupported by any `T` whose voting-round
blocks are old — because an old block references only old blocks. This
is the hypothesis a fill hands the protocol; `SkipsUnsupported`'s grade
says whether the protocol can use it. -/
theorem unsupported_of_novel {U U' : R.Universe} (he : Extends R U U')
    {S : Slots Validator} {V' : R.View U'} {T : Finset Validator} {k : ℕ}
    (hnov : ∀ L, R.IsCandidate S U' k L → Novel R U U' L)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U) :
    Unsupported R S U' V' T k := by
  intro c hcV hT hr L hL hmem
  exact (hnov L hL).2 (he.old_refs_old (hold c hcV hT hr) hmem)

end Properties

end LeanDag
