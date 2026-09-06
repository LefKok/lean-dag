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
the core's universe and two with their own, and the deployment order
of `Integration/Stack.lean`: fill, then cut. A longer stack is one more
`Stack.step`.

`Integration/Stack.lean` composed the same two mechanisms by hand, one
invariant at a time, and reached a direct commit across them.
`stack_safe_and_live` reaches every verdict and the liveness
precondition, and is what that file's thesis claimed.
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

/-- **Safety and liveness across the core's stack**, from the properties. -/
theorem stack_core_safe_and_live (sk : SkipMsg U) (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload (chop sk.skipFill G)}
    (hv : ViewAgreeAbove (MysticetiProperties.mysticetiRule (Payload := Payload)) V V'
      (max (sk.r + 1) G)) :
    (∀ (k : ℕ) (v : Option BlockId), max (sk.r + 1) G ≤ S.slotRound (d + k) →
        (Decided U V (d + k) v ↔ Decided (S := S.chop G d hd) (chop sk.skipFill G) V' k v)) ∧
    (∀ (W : View Validator BlockId Payload (chop sk.skipFill G)) (k : ℕ) (w v : Option BlockId),
        max (sk.r + 1) G ≤ S.slotRound (d + k) →
        Decided (S := S.chop G d hd) (chop sk.skipFill G) W k w → Decided U V (d + k) v → w = v) ∧
    (∀ {rel : Reliability Validator} {T : Finset Validator} {lo K : ℕ},
        MysticetiProperties.coreSupport.live rel S (U := U) V T lo K →
        max (sk.r + 1) G ≤ S.slotRound lo → d ≤ lo → lo < K →
        (∀ N, G ≤ N → CoversUpto (MysticetiProperties.mysticetiRule (Payload := Payload)) V N →
          CoversUpto (MysticetiProperties.mysticetiRule (Payload := Payload)) V' (N - G)) →
        MysticetiProperties.coreSupport.live rel (S.chop G d hd) (U := chop sk.skipFill G) V' T
          (lo - d) (K - d)) :=
  Stack.safe_and_live MysticetiProperties.banded MysticetiProperties.agree
    MysticetiProperties.coreSupport MysticetiProperties.coreSupport_local (stack_core sk hd) hv

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

/-- **Safety and liveness across Nemo's stack.** -/
theorem stack_nemo_safe_and_live (hn : 0 < Fintype.card Validator)
    (sk : SkipData U.ids U.block) (hd : G ≤ S.slotRound d)
    {V : Nemo.View Validator BlockId Payload U}
    {V' : Nemo.View Validator BlockId Payload (chopNemo (skipFillNemo U sk) G)}
    (hv : ViewAgreeAbove (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) V V' (max (sk.r + 1) G)) :
    (∀ (k : ℕ) (v : Option BlockId), max (sk.r + 1) G ≤ S.slotRound (d + k) →
        (Nemo.Decided (S := S) U V (d + k) v ↔
          Nemo.Decided (S := S.chop G d hd) (chopNemo (skipFillNemo U sk) G) V' k v)) ∧
    (∀ (W : Nemo.View Validator BlockId Payload (chopNemo (skipFillNemo U sk) G)) (k : ℕ)
        (w v : Option BlockId), max (sk.r + 1) G ≤ S.slotRound (d + k) →
        Nemo.Decided (S := S.chop G d hd) (chopNemo (skipFillNemo U sk) G) W k w →
        Nemo.Decided (S := S) U V (d + k) v → w = v) ∧
    (∀ {rel : Reliability Validator} {T : Finset Validator} {lo K : ℕ},
        (voteSupport (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
          (Payload := Payload))).live rel S (U := U) V T lo K →
        max (sk.r + 1) G ≤ S.slotRound lo → d ≤ lo → lo < K →
        (∀ N, G ≤ N → CoversUpto (NemoProperties.nemoRule (Payload := Payload)) V N →
          CoversUpto (NemoProperties.nemoRule (Payload := Payload)) V' (N - G)) →
        (voteSupport (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
          (Payload := Payload))).live rel (S.chop G d hd) (U := chopNemo (skipFillNemo U sk) G)
          V' T (lo - d) (K - d)) :=
  Stack.safe_and_live NemoProperties.banded NemoProperties.agree (voteSupport _)
    voteSupport_local (stack_nemo sk hd) hv

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

/-- **Safety and liveness across FinWhale's stack.** -/
theorem stack_finwhale_safe_and_live (sk : SkipData D.ids D.block) (hd : G ≤ S.slotRound d)
    {V : {V : Finset B // IsView D V}}
    {V' : {V' : Finset B // IsView (chopFinWhale (skipFillFinWhale D sk) G) V'}}
    (hv : ViewAgreeAbove (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := B) (Payload := Payload)) V V' (max (sk.r + 1) G)) :
    (∀ (k : ℕ) (v : Option B), max (sk.r + 1) G ≤ S.slotRound (d + k) →
        ((FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V (d + k) v ↔
          (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided (S.chop G d hd) V' k v)) ∧
    (∀ (W : {W : Finset B // IsView (chopFinWhale (skipFillFinWhale D sk) G) W}) (k : ℕ)
        (w v : Option B), max (sk.r + 1) G ≤ S.slotRound (d + k) →
        (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided (S.chop G d hd) W k w →
        (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V (d + k) v → w = v) ∧
    (∀ {rel : Reliability Validator} {T : Finset Validator} {lo K : ℕ},
        FinWhaleProperties.fwSupport.live rel S (U := D) V T lo K →
        max (sk.r + 1) G ≤ S.slotRound lo → d ≤ lo → lo < K →
        (∀ N, G ≤ N → CoversUpto (FinWhaleProperties.finWhaleRule (Payload := Payload)) V N →
          CoversUpto (FinWhaleProperties.finWhaleRule (Payload := Payload)) V' (N - G)) →
        FinWhaleProperties.fwSupport.live rel (S.chop G d hd)
          (U := chopFinWhale (skipFillFinWhale D sk) G) V' T (lo - d) (K - d)) :=
  Stack.safe_and_live FinWhaleProperties.banded FinWhaleProperties.agree
    FinWhaleProperties.fwSupport FinWhaleProperties.fwSupport_local (stack_finwhale sk hd) hv

end FinWhale

end Integration

end LeanDag
