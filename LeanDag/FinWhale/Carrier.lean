import LeanDag.FinWhale.View
import LeanDag.FinWhale.Pass
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct

/-!
# FinWhale as a carrier

`docs/porting-plan.md` step 4. FinWhale is the rule least like
Mysticeti, and the first thing the port has to settle is what its
`Decided` even is.

**FinWhale has no inductive decision relation.** Every other rule here
derives verdicts by an inductive definition; FinWhale assigns them by a
*function* `dec : ℕ → Verdict BlockId` constrained by `WellFormed` — the
paper's reverse pass, read as a condition rather than a construction.
So `Decided S U V r v` is *existential*: some well-formed assignment on
this view gives `v` at `r`.

Two conjuncts beyond well-formedness, and both are facts about a real
validator's assignment rather than restrictions invented here:

* **it commits only blocks of the slot**, which is what makes a commit
  name a candidate, and
* **it is finite** — nothing above some `N` is decided, which is what
  Lemma 12's downward induction consumes and what a finite DAG gives.

**The schedule comes from `Slots`, and nothing is pinned.** FinWhale
used to carry its leader function as a field of the `Dag` and index its
verdicts by round; both are gone. `slotBlocks` reads the round the
schedule gives a slot and the leader it names, `Anchor` is stated at an
eligibility rather than at `r + 2 < a`, and `Decided` passes `S` straight
through as `FinWhale.Sched`.

**Unpinning the schedule was two changes, not one.** Dropping the
leader from the `Dag` is what let `Decided` take the schedule it is
given; that alone left the *witness* pinned, because the reverse pass
enumerated its anchors over an interval and so was well formed only at
`r + 2 < a`. `anchorCands` now filters the eligible slots instead, and
the pass runs at whatever eligibility it is handed, which is
`Sched.Elig` — three rounds up — for both the protocol and this file.

The remaining gap was a horizon. A view bounds *rounds* and the pass
recurses down over *slots*, and only `Slots.slot_lt_of_slotRound_le`
relates the two: `keyed` and a finite validator set stop a schedule from
fitting unboundedly many slots below a round. With that, an assignment
exists at every schedule, so `Agree` is not vacuous and `CommitsDirect`
is provable — the property is quantified over all schedules, and until
the witness was, it was out of reach.
-/

namespace LeanDag

namespace FinWhaleProperties

open LeanDag.Properties
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- Membership of a round layer, unfolded once so the proofs below do
not have to. -/
theorem mem_blocksAt {D : Dag Validator BlockId Payload} {b : BlockId} {n : ℕ} :
    b ∈ LeanDag.FinWhale.blocksAt D n ↔ b ∈ D.ids ∧ (D.block b).round = n := by
  unfold LeanDag.FinWhale.blocksAt; exact Finset.mem_filter

/-- And of a slot's blocks. -/
theorem mem_slotBlocks {S : Sched Validator} {D : Dag Validator BlockId Payload}
    {b : BlockId} {n : ℕ} :
    b ∈ LeanDag.FinWhale.slotBlocks S D n ↔
      (b ∈ D.ids ∧ (D.block b).round = S.round n) ∧ (D.block b).creator = S.leader n := by
  unfold LeanDag.FinWhale.slotBlocks
  rw [Finset.mem_filter, mem_blocksAt]

/-- A verdict, as the property layer reads it: `some b` is a commit,
`none` a skip, and an undecided slot is not decided at all. -/
def VerdictIs (dec : ℕ → Verdict BlockId) (r : ℕ) (v : Option BlockId) : Prop :=
  match v with
  | some b => dec r = Verdict.commit b
  | none => dec r = Verdict.skip

/-- **What a validator's verdict assignment is**: well-formed on its own
view, committing only blocks of the slot, and finite. -/
structure Assignment (S : Sched Validator) (D : Dag Validator BlockId Payload)
    (V : Finset BlockId) (hV : IsView D V) (dec : ℕ → Verdict BlockId) : Prop where
  /-- The reverse pass, as a condition on the verdicts. -/
  wf : WellFormed (S.Elig) (viewCommit S D V hV) (viewSkip S D V hV) (chooseLeast S D) dec
  /-- A commit names a block of the slot. -/
  slot : ∀ s A, dec s = Verdict.commit A → A ∈ slotBlocks S D s
  /-- Nothing above some round is decided — the DAG is finite. -/
  finite : ∃ N, ∀ s, N ≤ s → dec s = Verdict.undecided

/-- The properties' schedule, read as FinWhale's. -/
def schedOf (S : Slots Validator) : Sched Validator :=
  ⟨S.slotRound, S.leader⟩

/-- **FinWhale as a carrier**, with the schedule passed through and
nothing pinned. -/
def finWhaleRule : DagRule Validator BlockId Payload where
  Universe := Dag Validator BlockId Payload
  View := fun D => {V : Finset BlockId // IsView D V}
  block := fun D i => D.block i
  ids := fun D => D.ids
  viewIds := fun V => V.val
  viewSound := fun V => V.property.subset
  viewComplete := fun V => V.property.closed
  Decided := fun S D V k v =>
    ∃ dec, Assignment (schedOf S) D V.val V.property dec ∧ VerdictIs dec k v

/-- FinWhale's DAGs are block DAGs. -/
theorem causal : Causal (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun D =>
    { complete := fun i hi j hj => D.complete i hi j hj
      refs_round := fun i hi j hj => (D.valid i hi).predecessor j hj }

/-- **Two views decide alike.** Lemma 12 under the property's name: the
exclusions come from the DAG, the deterministic rule is the least
candidate, and the downward induction runs on the two assignments'
finiteness bounds together. -/
theorem agree : Agree (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) := by
  rintro S D V₁ V₂ r v₁ v₂ ⟨dec₁, ha₁, hv₁⟩ ⟨dec₂, ha₂, hv₂⟩
  obtain ⟨N₁, hN₁⟩ := ha₁.finite
  obtain ⟨N₂, hN₂⟩ := ha₂.finite
  have habove : ∀ (dq : ℕ → Verdict BlockId),
      (∀ s A, dq s = Verdict.commit A → A ∈ slotBlocks (schedOf S) D s) →
      ∀ r a A, (schedOf S).Elig r a → dq a = Verdict.commit A →
        A ∈ D.ids ∧ (schedOf S).round r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have hA := hq a A hcom
    rw [mem_slotBlocks] at hA
    exact ⟨hA.1.1, by rw [hA.1.2]; exact hra⟩
  have hkey := lemma12 ha₁.wf ha₂.wf
    (exclusions_of_views V₁.property V₂.property chooseSound_least)
    (fun r a h => by
      by_contra hge
      have := S.mono (Nat.le_of_not_lt hge)
      have : (schedOf S).round a ≤ (schedOf S).round r := this
      have h' : (schedOf S).round r + 3 ≤ (schedOf S).round a := h
      omega)
    (habove dec₁ ha₁.slot) (habove dec₂ ha₂.slot)
    (N := max N₁ N₂)
    (fun s hs => ⟨hN₁ s (by omega), hN₂ s (by omega)⟩)
  have hne : ∀ (dq : ℕ → Verdict BlockId) (s : ℕ) (w : Option BlockId),
      VerdictIs dq s w → dq s ≠ Verdict.undecided := by
    intro dq s w h
    cases w <;> (rw [show dq s = _ from h]; simp)
  have heq := hkey r (hne dec₁ r v₁ hv₁) (hne dec₂ r v₂ hv₂)
  cases v₁ with
  | none =>
    cases v₂ with
    | none => rfl
    | some b₂ => rw [show dec₁ r = _ from hv₁, show dec₂ r = _ from hv₂] at heq; simp at heq
  | some b₁ =>
    cases v₂ with
    | none => rw [show dec₁ r = _ from hv₁, show dec₂ r = _ from hv₂] at heq; simp at heq
    | some b₂ =>
      rw [show dec₁ r = _ from hv₁, show dec₂ r = _ from hv₂] at heq
      simpa using heq

/-- **A commit names the slot's candidate.** The `slot` field of an
assignment, read at the property's `IsCandidate` — which is where the
schedule being pinned to the DAG earns its place. -/
theorem commitsCandidate : CommitsCandidate
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) := by
  rintro S D V r L ⟨dec, ha, hv⟩
  have hA := ha.slot r L hv
  rw [mem_slotBlocks] at hA
  exact ⟨hA.1.1, hA.1.2, hA.2⟩

/-! ## That the relation is inhabited, at every schedule

`Decided` is existential over assignments, so `Agree` would hold for
nothing if none existed. That is the vacuity trap this arc has been
caught by twice (§3.4, §3.6), and it matters most here: FinWhale is the
only rule whose decision relation is a condition on a function rather
than an inductive definition, so nothing about it is inhabited by
construction.

The witness is FinWhale's own reverse pass, and it now runs at the
schedule it is given — `anchorCands` filters the eligible slots rather
than an interval, so the pass is well formed at whatever eligibility it
is handed. That is what took the last pinning out. -/

/-- Eligible slots are above: a schedule's rounds are monotone, so three
rounds up is at least one slot up. -/
theorem lt_of_elig {S : Slots Validator} {r a : ℕ}
    (h : (schedOf S).Elig r a) : r < a := by
  by_contra hge
  have hm : S.slotRound a ≤ S.slotRound r := S.mono (Nat.le_of_not_lt hge)
  have h' : S.slotRound r + 3 ≤ S.slotRound a := h
  omega

/-- A view is finite, so its blocks stop at a round. -/
theorem view_bounded (D : Dag Validator BlockId Payload) (V : Finset BlockId)
    (hV : IsView D V) :
    ∀ b ∈ (LeanDag.FinWhale.restrict D V hV).ids,
      ((LeanDag.FinWhale.restrict D V hV).block b).round ≤
        V.sup (fun b => (D.block b).round) :=
  fun b hb => Finset.le_sup (f := fun b => (D.block b).round) hb

/-- A view's slot blocks are the universe's. -/
theorem slotBlocks_restrict_subset (S : Sched Validator)
    (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V) (r : ℕ) :
    LeanDag.FinWhale.slotBlocks S (LeanDag.FinWhale.restrict D V hV) r ⊆
      LeanDag.FinWhale.slotBlocks S D r := by
  intro b hb
  rw [mem_slotBlocks] at hb ⊢
  exact ⟨⟨hV.subset hb.1.1, hb.1.2⟩, hb.2⟩

/-- **The pass's horizon**: a slot index above every slot a view can
decide. `Slots.slot_lt_of_slotRound_le` is what makes one exist — the
view bounds the *rounds*, and a bound on rounds bounds the slots only
because a schedule cannot fit unboundedly many slots into them. -/
def viewHorizon (D : Dag Validator BlockId Payload) (V : Finset BlockId) : ℕ :=
  (V.sup (fun b => (D.block b).round) + 1) * Fintype.card Validator

/-- **A direct commit in view is a verdict**, at any schedule and with
no side condition. The reverse pass on the view is an assignment — well
formed by `wellFormed_decOf`, committing only blocks of the slot by
`mem_slotBlocks_of_decOf`, and finite because nothing above the horizon
is decided — and `WellFormed.direct_commit` reads the commit off it. -/
theorem decided_of_directCommit {D : Dag Validator BlockId Payload} {S : Slots Validator}
    {V : Finset BlockId} (hV : IsView D V) {k : ℕ} {L : BlockId}
    (hslot : L ∈ LeanDag.FinWhale.slotBlocks (schedOf S)
      (LeanDag.FinWhale.restrict D V hV) k)
    (hcom : LeanDag.FinWhale.DirectCommit (LeanDag.FinWhale.restrict D V hV) L) :
    (finWhaleRule (Payload := Payload)).Decided S (U := D) ⟨V, hV⟩ k (some L) := by
  classical
  have hrle : ∀ r, (schedOf S).round r ≤ V.sup (fun b => (D.block b).round) →
      r ≤ viewHorizon D V := fun r h =>
    Nat.le_of_lt (LeanDag.Slots.slot_lt_of_slotRound_le (S := S) h)
  refine ⟨decOf (schedOf S) ((schedOf S).Elig) (LeanDag.FinWhale.restrict D V hV)
    (chooseLeast (schedOf S) D) (viewHorizon D V), ?_, ?_⟩
  · exact
      { wf := wellFormed_decOf (view_bounded D V hV) (fun _ _ => lt_of_elig) hrle
          (chooseLeast (schedOf S) D)
        slot := fun s A h => mem_slotBlocks_of_decOf
          (slotBlocks_restrict_subset (schedOf S) D V hV) chooseSound_least
          (fun _ _ => lt_of_elig) h
        finite := ⟨viewHorizon D V + 1, fun s hs => decOf_of_gt (by omega)⟩ }
  · exact (wellFormed_decOf (view_bounded D V hV) (fun _ _ => lt_of_elig) hrle
      (chooseLeast (schedOf S) D)).direct_commit k L ⟨hslot, hcom⟩


/-! ## The direct rule

`CommitsDirect` is what tells a mechanism that a rule's direct-commit
predicate is a predicate about verdicts. Barnacle's leader count reads
it, and until the pass stopped pinning its schedule FinWhale could not
state it: the witness assignment existed only where the schedule was the
identity, so the property, which quantifies every schedule, was out of
reach. -/

/-- **FinWhale's direct-commit predicate, as a view sees it**: the block
is held, and the view's own restriction certifies it. The round is
carried to match the property's shape and is not read — `IsCandidate`
already says where the block sits. -/
def DirectCommitIn {D : Dag Validator BlockId Payload}
    (V : (finWhaleRule (Payload := Payload)).View D) (L : BlockId) (_r : ℕ) : Prop :=
  L ∈ V.val ∧ LeanDag.FinWhale.DirectCommit (LeanDag.FinWhale.restrict D V.val V.property) L

/-- **And a direct commit is a verdict**, at every schedule.
`IsCandidate` places the block at the slot, `DirectCommitIn` puts it in
the view and certifies it, and `decided_of_directCommit` runs the pass
that reads the commit off. -/
theorem commitsDirect : CommitsDirect
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {_} V L r => DirectCommitIn V L r) := by
  rintro S D V k L ⟨-, hround, hcreator⟩ ⟨hmem, hdir⟩
  exact decided_of_directCommit V.property
    (mem_slotBlocks.2 ⟨⟨hmem, hround⟩, hcreator⟩) hdir

end FinWhaleProperties

end LeanDag
