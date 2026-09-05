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

**The schedule comes from `Slots`, as it does for every other rule.**
FinWhale used to carry its leader function as a field of the `Dag`,
which put a schedule inside a universe and so put `Banded` out of reach:
a band is a statement about blocks, and two DAGs in one band could name
different leaders. The field is gone, the decision rules read the leader
they are given, and `Decided` needs no pinning of the schedule to the
DAG.

What is still pinned is the *indexing*: FinWhale's slots are its rounds,
so `Decided` asks for `S.slotRound s = s`. That is not a restriction on
FinWhale but a statement of what its slots are, and the band tolerates
it — `Banded` only requires the round shift to match the slot shift,
which for a rule whose slots are its rounds is exactly right.
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
theorem mem_slotBlocks {ld : ℕ → Validator} {D : Dag Validator BlockId Payload}
    {b : BlockId} {n : ℕ} :
    b ∈ LeanDag.FinWhale.slotBlocks ld D n ↔
      (b ∈ D.ids ∧ (D.block b).round = n) ∧ (D.block b).creator = ld n := by
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
structure Assignment (ld : ℕ → Validator) (D : Dag Validator BlockId Payload)
    (V : Finset BlockId) (hV : IsView D V) (dec : ℕ → Verdict BlockId) : Prop where
  /-- The reverse pass, as a condition on the verdicts. -/
  wf : WellFormed (viewCommit ld D V hV) (viewSkip ld D V hV) (chooseLeast ld D) dec
  /-- A commit names a block of the slot. -/
  slot : ∀ s A, dec s = Verdict.commit A → A ∈ slotBlocks ld D s
  /-- Nothing above some round is decided — the DAG is finite. -/
  finite : ∃ N, ∀ s, N ≤ s → dec s = Verdict.undecided

/-- **FinWhale as a carrier.** The leader comes from the schedule, as it
does for every other rule; what is pinned is that slots are rounds. -/
def finWhaleRule : DagRule Validator BlockId Payload where
  Universe := Dag Validator BlockId Payload
  View := fun D => {V : Finset BlockId // IsView D V}
  block := fun D i => D.block i
  ids := fun D => D.ids
  viewIds := fun V => V.val
  viewSound := fun V => V.property.subset
  viewComplete := fun V => V.property.closed
  Decided := fun S D V r v =>
    (∀ s, S.slotRound s = s) ∧
      ∃ dec, Assignment S.leader D V.val V.property dec ∧ VerdictIs dec r v

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
  rintro S D V₁ V₂ r v₁ v₂ ⟨-, dec₁, ha₁, hv₁⟩ ⟨-, dec₂, ha₂, hv₂⟩
  obtain ⟨N₁, hN₁⟩ := ha₁.finite
  obtain ⟨N₂, hN₂⟩ := ha₂.finite
  have habove : ∀ (dq : ℕ → Verdict BlockId),
      (∀ s A, dq s = Verdict.commit A → A ∈ slotBlocks S.leader D s) →
      ∀ r a A, r + 2 < a → dq a = Verdict.commit A →
        A ∈ D.ids ∧ r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have hA := hq a A hcom
    rw [mem_slotBlocks] at hA
    exact ⟨hA.1.1, by omega⟩
  have hkey := lemma12 ha₁.wf ha₂.wf
    (exclusions_of_views V₁.property V₂.property chooseSound_least)
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
  rintro S D V r L ⟨hround, dec, ha, hv⟩
  have hA := ha.slot r L hv
  rw [mem_slotBlocks] at hA
  exact ⟨hA.1.1, by rw [hround]; exact hA.1.2, hA.2⟩

/-! ## That the relation is inhabited

`Decided` is *existential over assignments*, so `Agree` would hold for
nothing if no assignment ever existed. That is the vacuity trap this arc
has twice been caught by (§3.4, §3.6), and it matters more here than
anywhere else: FinWhale is the only rule whose decision relation is a
condition on a function rather than an inductive definition, so nothing
about it is inhabited by construction.

**This is not `CommitsDirect`, and the reason is the finding of the
port.** `CommitsDirect R Direct` passes the direct predicate a view, a
block and a round — and never the schedule. FinWhale's rules read the
leader off the *DAG*, so relating them to `Slots` needs the pinning that
`Decided` carries, and `Direct` cannot carry it. `CommitsCandidate` needs
the same pinning and can have it, because `IsCandidate` is stated at `S`.
So the property that can be stated is stated, and the one that cannot is
replaced here by the theorem it would have followed from. -/

/-- A view is finite, so its blocks stop at a round. -/
theorem view_bounded (D : Dag Validator BlockId Payload) (V : Finset BlockId)
    (hV : IsView D V) :
    ∀ b ∈ (LeanDag.FinWhale.restrict D V hV).ids,
      ((LeanDag.FinWhale.restrict D V hV).block b).round ≤
        V.sup (fun b => (D.block b).round) :=
  fun b hb => Finset.le_sup (f := fun b => (D.block b).round) hb

/-- A view's slot blocks are the universe's. -/
theorem slotBlocks_restrict_subset (ld : ℕ → Validator) (D : Dag Validator BlockId Payload)
    (V : Finset BlockId) (hV : IsView D V) (r : ℕ) :
    LeanDag.FinWhale.slotBlocks ld (LeanDag.FinWhale.restrict D V hV) r ⊆
      LeanDag.FinWhale.slotBlocks ld D r := by
  intro b hb
  rw [mem_slotBlocks] at hb ⊢
  exact ⟨⟨hV.subset hb.1.1, hb.1.2⟩, hb.2⟩

/-- **The relation is inhabited: a direct commit in view is a verdict.**
FinWhale's own reverse pass, run on the view with the universe's
tie-break, is an assignment — well formed by `wellFormed_decOf`,
committing only blocks of the slot by `mem_slotBlocks_of_decOf`, and
finite because a view is a finite set of blocks — and
`WellFormed.direct_commit` reads the commit off it.

The one schedule hypothesis is the indexing `Decided` carries: slots are
rounds. The leader no longer has to be pinned to anything, the rules
reading the one they are given. -/
theorem decided_of_directCommit {D : Dag Validator BlockId Payload} {S : Slots Validator}
    (hround : ∀ s, S.slotRound s = s)
    {V : Finset BlockId} (hV : IsView D V)
    {k : ℕ} {L : BlockId}
    (hslot : L ∈ LeanDag.FinWhale.slotBlocks S.leader
      (LeanDag.FinWhale.restrict D V hV) k)
    (hcom : LeanDag.FinWhale.DirectCommit (LeanDag.FinWhale.restrict D V hV) L) :
    (finWhaleRule (Payload := Payload)).Decided S (U := D) ⟨V, hV⟩ k (some L) := by
  classical
  refine ⟨hround, decOf S.leader (LeanDag.FinWhale.restrict D V hV)
    (chooseLeast S.leader D) (V.sup (fun b => (D.block b).round)), ?_, ?_⟩
  · exact
      { wf := wellFormed_decOf (view_bounded D V hV)
          (chooseLeast S.leader D)
        slot := fun s A h => mem_slotBlocks_of_decOf
          (slotBlocks_restrict_subset S.leader D V hV) chooseSound_least h
        finite := ⟨V.sup (fun b => (D.block b).round) + 1,
          fun s hs => decOf_of_gt (by omega)⟩ }
  · exact (wellFormed_decOf (view_bounded D V hV)
      (chooseLeast S.leader D)).direct_commit k L ⟨hslot, hcom⟩

end FinWhaleProperties

end LeanDag
