import LeanDag.Properties.Arcs.Stack
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Integration.ReGenesisRules
import LeanDag.Integration.NemoMechanisms
import LeanDag.Integration.FinWhaleMechanisms

/-!
# Stacks, at the rules

`Properties/Arcs/Stack.lean` proves the composition theorem once. What
a rule contributes to it is nothing: the stack is assembled from the
witnesses its mechanisms already have — `Rebased.of_sustains` on a fill
or a re-genesis, `Rebased.of_truncates` on a cut — and
`Stack.safe_and_live` reads it. Three rules are shown below, one with
the core's universe and two with their own, in the order a deployment
takes: fill, then cut. A longer stack is one more
`Stack.step`.

What a stack gives is read by the headline: `Properties.Safe`, which
every rule instantiates once (`MysticetiProperties.safety` and the
rest), quantifies over every stack, so nothing is stated here beyond
the witnesses themselves. The per-rule `stack_*_safe_and_live` theorems
that once stood beside them were that headline at three stacks, and
are retired.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ}

/-! ## The core: fill, then cut -/

section Core

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload}

/-- **The core's fill-then-cut is a stack**, settling at the later of the
gap's top and the horizon, shifted by the horizon, re-indexed from the
base slot. -/
theorem stack_core (sk : SkipMsg U) (hd : G ≤ S.slotRound d) :
    Stack (MysticetiProperties.mysticetiRule (Payload := Payload)) U S
      (chop sk.skipFill G) (S.chop G d hd) G (max (sk.r + 1) G) d := by
  have st := Stack.step (Rebased.of_sustains (S := S) (sustains_skipFill (Payload := Payload) sk))
    (Stack.step (Rebased.of_truncates (truncates_chop (U := sk.skipFill) hd)) Stack.nil)
  simpa using st

end Core

/-! ## Nemo: its own universe, fill then cut -/

section Nemo

variable {U : Nemo.Universe Validator BlockId Payload}

theorem stack_nemo (sk : SkipData U.ids U.block) (hd : G ≤ S.slotRound d) :
    Stack (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U S (chopNemo (skipFillNemo U sk) G) (S.chop G d hd)
      G (max (sk.r + 1) G) d := by
  have st := Stack.step (Rebased.of_sustains (S := S) (sustains_skipFill_nemo (sk := sk)))
    (Stack.step (Rebased.of_truncates (truncates_chop_nemo (U := skipFillNemo U sk) hd))
      Stack.nil)
  simpa using st

end Nemo

/-! ## FinWhale: its own DAG, fill then cut -/

section FinWhale

open LeanDag.FinWhale

variable [Faults Validator] [LeanDag.FinWhale.Params Validator]
variable {B : Type} [LinearOrder B] {D : Dag Validator B Payload}

theorem stack_finwhale (sk : SkipData D.ids D.block) (hd : G ≤ S.slotRound d) :
    Stack (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) D S (chopFinWhale (skipFillFinWhale D sk) G) (S.chop G d hd)
      G (max (sk.r + 1) G) d := by
  have st := Stack.step (Rebased.of_sustains (S := S) (sustains_skipFill_finwhale (sk := sk)))
    (Stack.step (Rebased.of_truncates
      (truncates_chop_finwhale (D := skipFillFinWhale D sk) hd)) Stack.nil)
  simpa using st

end FinWhale

end Integration

end LeanDag
