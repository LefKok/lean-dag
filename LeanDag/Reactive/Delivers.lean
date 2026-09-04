import LeanDag.ViewPace
import LeanDag.MysticetiProperties
import LeanDag.Properties.Deliver

/-!
# A paced validator delivers

The second witness for `Properties.DeliversOn`, from a mechanism with
different timing from the first. `DoS/Delivers.lean` exhibits it for a
rate limiter; this exhibits it for the pacing discipline that
`Reactive/Mysticeti.lean` runs on.

**The question this settles.** A reactive validator advances as soon as
a quorum has arrived, so it does not wait for every correct validator
and its *references* omit whatever was late — `Reactive/Mysticeti.lean`
says so, and gives up reference coverage deliberately. It looks as
though such a validator cannot promise to cover the reliable set, and so
cannot meet `DeliversOn`.

It can, because the early exit governs what a validator **references**
and not what it **holds**. `PaceCore.holds` is passive delivery; the
view is built from it (`viewAt`), and `holds_roundBlocks` already says
that after GST a paced validator holds every reliable block of a round.
`Synchronised` — reference coverage, a property of the *universe* — is
what the early exit costs, and it is not what the view obligation asks
for.

**That is the reason `CoversUpto` was the wrong predicate and `CoversOn`
is the right one**, and this arc is independent evidence: the reactive
commit was already stated in the `CoversOn` shape before the obligation
existed. `ViewPace.decided_local_of_certifiesAt` counts a reliable
quorum's certificates inside `viewAt v t` — the same counting
`Liveness.directCommitIn_of_certifiesAt` does and the same one
`DoS/Delivers.lean` consumes. Three arcs, one shape.
-/

namespace LeanDag

namespace PaceCore

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N : ℕ}

/-- A time by which every round up to `hi` has been built and delivered.
`latest` is not assumed monotone, so the bound is the supremum over the
window rather than its right end. -/
def settleBy (pc : PaceCore U T N) (hi : ℕ) : ℕ :=
  (Finset.range (hi + 1)).sup pc.latest + pc.delay

theorem le_settleBy (pc : PaceCore U T N) {n hi : ℕ} (hn : n ≤ hi) :
    pc.latest n + pc.delay ≤ pc.settleBy hi :=
  Nat.add_le_add_right
    (Finset.le_sup (f := pc.latest) (Finset.mem_range.mpr (by omega))) _

/-- **A paced validator's view covers the reliable set over a window.**
Every `T`-block from `lo` to `hi` is held by `settleBy hi`, one round at
a time by `holds_roundBlocks` and carried to the common time by
`holds_mono`. -/
theorem coversOn_viewAt (pc : PaceCore U T N) {v : Validator} (hv : v ∈ T)
    {lo hi : ℕ} (hhi : hi ≤ N)
    (hg : ∀ n, lo ≤ n → n ≤ hi → ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    Properties.CoversOn (MysticetiProperties.mysticetiRule (Payload := Payload))
      (pc.viewAt v (pc.settleBy hi)) T lo hi := by
  intro b hb hbc hlo hbhi
  have hlink : (MysticetiProperties.mysticetiRule.block U b).round = (U.block b).round := rfl
  refine pc.mem_viewAt (pc.holds_mono v _ _ (pc.le_settleBy (n := (U.block b).round)
    (by omega)) ?_)
  exact pc.holds_roundBlocks (n := (U.block b).round) (by omega)
    (fun u hu => hg _ (by omega) (by omega) u hu) v hv b hb hbc rfl

/-- **The witness.** A paced validator delivers the reliable set from
any round it has settled past — the obligation
`Properties/Deliver.lean` states, met by a discipline that never waits
for a straggler. -/
theorem deliversOn_viewAt (pc : PaceCore U T N) {v : Validator} (hv : v ∈ T)
    {lo : ℕ} (hN : ∀ n, lo ≤ n → n ≤ N → ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    Properties.DeliversOn (MysticetiProperties.mysticetiRule (Payload := Payload))
      (fun t => pc.viewAt v (pc.settleBy (min t N))) T lo :=
  fun hi => ⟨hi, by
    have h := coversOn_viewAt pc hv (lo := lo) (hi := min hi N) (min_le_right _ _)
      (fun n hn hnhi u hu => hN n hn (le_trans hnhi (min_le_right _ _)) u hu)
    intro b hb hbc hlo hbhi
    have hlink : (MysticetiProperties.mysticetiRule.block U b).round = (U.block b).round := rfl
    exact h b hb hbc hlo (by
      have := pc.rounds_le b hb
      omega)⟩

end PaceCore

end LeanDag
