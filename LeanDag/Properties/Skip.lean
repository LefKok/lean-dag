import LeanDag.Properties.Persist

/-!
# Skippability: the residue `Sustains` leaves to the protocol

`docs/target-properties.md` §3.6's last paragraph, stated.

`Sustains` says a mechanism destroys no vote and silences no producer.
That is not enough for progress, and the fill shows why: it adds a
*candidate* — the recovering replica's block lands on a slot that
replica leads — and a candidate nothing old references can be neither
committed (no votes) nor, for some rules, skipped. Every vote survives,
every producer survives, and the slot is dead.

Whether it is dead is a fact about the **protocol's skip rule**, not
about the mechanism, so this obligation sits on the protocol side and is
graded, as `Persist` is by `Ok`. The question it asks: *if every block
of `T` one round above a slot references none of that slot's candidates,
does the protocol skip it, and what does it need of `T`?*

Hydrozoan needs `qFast ≤ |T|`, because its skip is `qFast` blames at
the slot. A quorum of correct replicas has `q = n − f − c`, and
`qFast = n − p`, so a correct quorum suffices exactly when
`f + c ≤ p` — which is `hydrozoan-integration.md` §5.1's condition,
recovered here as a grade. Optimal-Hydrozoan's skip is at `qCert ≤ q`
and OH5 discharges it from population alone.

`unsupported_of_novel` is the bridge from the mechanism's side: after an
extension, any slot all of whose candidates are novel is unsupported by
the old blocks, because an old block references only old blocks
(`Extends.old_refs_old`). So a mechanism that adds candidates hands the
protocol exactly this hypothesis, and the protocol's grade says whether
that is enough.
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

/-- A protocol skipping under a weaker condition skips under a stronger
one, so the grades compare. -/
theorem mono (h : SkipsUnsupported R Ok) (himp : ∀ T, Ok' T → Ok T) :
    SkipsUnsupported R Ok' :=
  fun S U V T k hok hp hu => h S U V T k (himp T hok) hp hu

end SkipsUnsupported

/-- **The bridge from the mechanism.** After an extension, a slot all of
whose candidates are novel is unsupported by any `T` whose voting-round
blocks are old — because an old block references only old blocks. This
is the hypothesis a fill hands the protocol; `SkipsUnsupported`'s grade
says whether the protocol can use it. -/
theorem unsupported_of_novel (hc : Causal R) {U U' : R.Universe} (he : Extends R U U')
    {S : Slots Validator} {V' : R.View U'} {T : Finset Validator} {k : ℕ}
    (hnov : ∀ L, R.IsCandidate S U' k L → Novel R U U' L)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U) :
    Unsupported R S U' V' T k := by
  intro c hcV hT hr L hL hmem
  exact (hnov L hL).2 (he.old_refs_old hc (hold c hcV hT hr) hmem)

end Properties

end LeanDag
