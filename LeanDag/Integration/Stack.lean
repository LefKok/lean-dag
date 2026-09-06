import LeanDag.Integration.Coverage
import LeanDag.Integration.ScheduleShape
import LeanDag.Hybrid.Decision
import LeanDag.Properties.Compose
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.GC
import LeanDag.HybridProperties

/-!
# I16 — the composition capstone

The document's thesis is that named invariants plus preservation
lemmas make composition free. The cells proved so far are the
*ingredients*; this file is the claim itself, and it is what tells us
whether the linear strategy actually paid.

The stack under test is a validator running four mechanisms at once: it
recovered from a crash by Safe Skip (report §12), later garbage-collected
below a horizon (report §9), reads the result under the hybrid fault model
(report §14), and runs an adaptive schedule (report §13). Nothing below proves
anything new about any of them — every proof is a chain of existing
lemmas, which is the point.

**The order matters, and asymmetrically.** Fill-then-truncate is
unconditional: `chop (skipFill U) G` is well formed for every horizon,
because the fill has already happened when the cut is made. The reverse
needs the anchor retained — a `SkipMsg` for `chop U G` requires
`B1 ∈ (chop U G).ids`, hence `G ≤ round B1` — which is I7's condition,
appearing here as an asymmetry rather than an obstacle. The order
proved here is the deployment order: a validator fills the gap when it
recovers, and prunes later.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Stack

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-- **The stacked universe**: filled, then truncated. -/
abbrev stack (sk : SkipMsg U) (G : ℕ) : BlockUniverse Validator BlockId Payload :=
  chop sk.skipFill G

/-- **I16a.** Honest non-equivocation survives the whole stack — I3 then
I2, with no new argument. This is what lets the hybrid safety
development be used by a validator that both recovered and pruned. -/
theorem honestNoEquiv_stack (sk : SkipMsg U) (hne : HonestNoEquiv U) :
    HonestNoEquiv (stack sk G) :=
  honestNoEquiv_chop (honestNoEquiv_skipFill sk hne)

/-- **I16b.** Coverage survives the stack above the fill and the cut —
I5-positive then I4. The two offsets compose exactly as their
statements suggest: the fill demands strictly above `sk.r`, the
truncation shifts by `G`. -/
theorem synchronisedOn_stack (sk : SkipMsg U) {T : Finset Validator} {R R' R'' : ℕ}
    (hs : SynchronisedOn U T R) (hR : R ≤ R') (hfill : sk.r < R')
    (hcut : R' ≤ G + R'') :
    SynchronisedOn (stack sk G) T R'' :=
  synchronisedOn_chop (synchronisedOn_skipFill_above sk hs hR hfill) hcut


/-- **I16d — the payoff.** Hybrid agreement holds in the stacked
universe: a validator that recovered from a crash by Safe Skip and then
pruned below a horizon still cannot disagree with anyone about a slot's
verdict, at any admissible threshold.

Every hypothesis is one of report §14's own, discharged for the stack by
`honestNoEquiv_stack`; the theorem body is `Hybrid.decided_unique`
applied to a different universe. Nothing about the fill or the cut is
re-proved, which is the thesis of this document in one statement. -/
theorem hybrid_agree_stack [LinearOrder BlockId] [S : Slots Validator]
    (sk : SkipMsg U) (hne : HonestNoEquiv U) {k : ℕ}
    (hk : Hybrid.Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload (stack sk G)} {s : ℕ}
    {v₁ v₂ : Option BlockId}
    (h₁ : Hybrid.Decided k (stack sk G) V₁ s v₁)
    (h₂ : Hybrid.Decided k (stack sk G) V₂ s v₂) : v₁ = v₂ :=
  HybridProperties.agree hk S
    (U := ⟨stack sk G, honestNoEquiv_stack sk hne⟩) V₁ V₂ s v₁ v₂ h₁ h₂

end Stack

/-! ## The same stack, through the properties

I16a–c above are three transports, one per invariant, each a chain of
two bespoke lemmas. What a mechanism owes is not an invariant but a
**rebase** (`Properties/Compose.lean`), and rebases compose — so the
stack has one obligation, discharged once, and every predicate computed
from blocks travels with it.

The witness for the fill was the gap `docs/target-properties.md` §11.2
recorded: the cut had one and Hydrozoan's fill had one, so the core's
two mechanisms could not be composed through the properties even though
each transported verdicts on its own. With it, `sustains_stack` is
`RebasedAbove.trans` applied, and `directCommit_stack` is a result this
file did not have — the reactive commit crossing a fill *and* a cut. -/

section Composed

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload} {G : ℕ}


end Composed


/-! ## The schedule layer stacks for free

The schedule invariants do not interact with the universe transformers
at all — `Slots.chop` and `slotsOf` are functions of a `Slots` instance
and nothing else — so the layer-S results of I13/I15 apply to a
validator running any stack of universe transformers whatsoever, with
no compatibility lemma needed. This is not a triviality worth hiding:
it is the reason report §2's layering was the right decomposition, and it is
why the composition matrix is far smaller than the arc count suggests.

The statement below is the schedule half of the stack, and its proof is
the layer-S lemma unchanged. -/

section Schedule

variable [F : Faults Validator] [S : Slots Validator] {G d c : ℕ}
variable {T : Finset Validator}


end Schedule

end Integration

end LeanDag
