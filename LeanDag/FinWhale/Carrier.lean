import LeanDag.FinWhale.View
import LeanDag.FinWhale.Band
import LeanDag.FinWhale.Pass
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support

import LeanDag.Timed.Coverage

import LeanDag.Properties.Arcs.Headline

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
through as `FinWhale.Slots`.

**Unpinning the schedule was two changes, not one.** Dropping the
leader from the `Dag` is what let `Decided` take the schedule it is
given; that alone left the *witness* pinned, because the reverse pass
enumerated its anchors over an interval and so was well formed only at
`r + 2 < a`. `anchorCands` now filters the eligible slots instead, and
the pass runs at whatever eligibility it is handed, which is
`Slots.Elig` — three rounds up — for both the protocol and this file.

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
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- And of a slot's blocks. -/
theorem mem_slotBlocks {S : Slots Validator} {D : Dag Validator BlockId Payload}
    {b : BlockId} {n : ℕ} :
    b ∈ LeanDag.FinWhale.slotBlocks S D n ↔
      (b ∈ D.ids ∧ (D.block b).round = S.slotRound n) ∧ (D.block b).creator = S.leader n := by
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
structure Assignment (S : Slots Validator) (D : Dag Validator BlockId Payload)
    (V : D.View) (dec : ℕ → Verdict BlockId) : Prop where
  /-- The reverse pass, as a condition on the verdicts. -/
  wf : WellFormed (S.Elig) (viewCommit S D V ) (viewSkip S D V ) (chooseLeast S D) dec
  /-- A commit names a block of the slot. -/
  slot : ∀ s A, dec s = Verdict.commit A → A ∈ slotBlocks S D s
  /-- Nothing above some round is decided — the DAG is finite. -/
  finite : ∃ N, ∀ s, N ≤ s → dec s = Verdict.undecided

/-- **FinWhale as a carrier**, with the schedule passed through and
nothing pinned. -/
def finWhaleRule : DagRule Validator BlockId Payload where
  Universe := Dag Validator BlockId Payload
  View := fun D => D.View
  block := fun D i => D.block i
  ids := fun D => D.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun D => LeanDag.FinWhale.causalStructure D
  Decided := fun S D V k v =>
    ∃ dec, Assignment S D V dec ∧ VerdictIs dec k v

/-- **FinWhale's DAGs are quorate**: `ValidHere.quorum`, which asks for
`n − f` distinct authors, read at the carrier. -/
theorem quorate : Quorate (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun D b hb hr => (D.valid b hb).quorum hr

/-- **One block per correct author per round**, from the DAG's
`no_equivocation`. -/
theorem noEquiv : NoEquiv (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun D b c hb hc hbc heq hr => D.no_equivocation b hb c hc hbc heq hr

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
      (∀ s A, dq s = Verdict.commit A → A ∈ slotBlocks (S) D s) →
      ∀ r a A, Slots.Elig S r a → dq a = Verdict.commit A →
        A ∈ D.ids ∧ S.slotRound r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have hA := hq a A hcom
    rw [mem_slotBlocks] at hA
    exact ⟨hA.1.1, by rw [hA.1.2]; exact hra⟩
  have hkey := lemma12 ha₁.wf ha₂.wf
    (exclusions_of_views (V := V₁) (V' := V₂) chooseSound_least)
    (fun r a h => by
      by_contra hge
      have := S.mono (Nat.le_of_not_lt hge)
      have : S.slotRound a ≤ S.slotRound r := this
      have h' : S.slotRound r + 3 ≤ S.slotRound a := h
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
    (h : Slots.Elig S r a) : r < a := by
  by_contra hge
  have hm : S.slotRound a ≤ S.slotRound r := S.mono (Nat.le_of_not_lt hge)
  have h' : S.slotRound r + 3 ≤ S.slotRound a := h
  omega

/-- A view is finite, so its blocks stop at a round. -/
theorem view_bounded (D : Dag Validator BlockId Payload) (V : D.View) :
    ∀ b ∈ (V.toRecord).ids,
      ((V.toRecord).block b).round ≤
        D.ids.sup (fun c => (D.block c).round) :=
  fun b hb => Finset.le_sup (f := fun c => (D.block c).round) (V.subset_ids hb)

/-- A view's slot blocks are the universe's. -/
theorem slotBlocks_restrict_subset (S : Slots Validator)
    (D : Dag Validator BlockId Payload) (V : D.View) (r : ℕ) :
    LeanDag.FinWhale.slotBlocks S (V.toRecord) r ⊆
      LeanDag.FinWhale.slotBlocks S D r := by
  intro b hb
  rw [mem_slotBlocks] at hb ⊢
  exact ⟨⟨V.subset_ids hb.1.1, hb.1.2⟩, hb.2⟩

/-- **The pass's horizon**: a slot index above every slot any view of
the DAG can decide. `Slots.slot_lt_of_slotRound_le` is what makes one
exist — the DAG bounds the *rounds*, and a bound on rounds bounds the
slots only because a schedule cannot fit unboundedly many slots into
them.

Read from the universe rather than the view, because a commit names a
block of the universe: the tie-break is a function of the anchor and the
round and reads the whole DAG, so `Assignment.slot` bounds a committed
slot by the DAG's rounds and not the view's. -/
def dagHorizon (D : Dag Validator BlockId Payload) : ℕ :=
  (D.ids.sup (fun b => (D.block b).round) + 1) * Fintype.card Validator

/-- **The pass a view runs**, at the schedule the carrier is given and
the horizon above. Every verdict of this rule is witnessed by some
assignment; this is the one that always exists, and `decided_iff` says
it is the only one that matters. -/
noncomputable def passOf (S : Slots Validator) (D : Dag Validator BlockId Payload)
    (V : D.View) : ℕ → Verdict BlockId :=
  decOf (S) (Slots.Elig S) (V.toRecord)
    (chooseLeast (S) D) (dagHorizon D)

/-- Every slot the pass reaches sits at the schedule's round for it, so
the horizon really is above every slot the pass commits. -/
theorem rle (S : Slots Validator) (D : Dag Validator BlockId Payload) :
    ∀ r, S.slotRound r ≤ D.ids.sup (fun b => (D.block b).round) → r ≤ dagHorizon D :=
  fun _ h => Nat.le_of_lt (LeanDag.Slots.slot_lt_of_slotRound_le (S := S) h)

/-- **And it is an assignment.** Well formed by `wellFormed_decOf`,
committing only blocks of the slot by `mem_slotBlocks_of_decOf`, and
finite because nothing above the horizon is decided. -/
theorem assignment_passOf {D : Dag Validator BlockId Payload} {S : Slots Validator}
    (V : D.View) : Assignment S D V (passOf S D V) where
  wf := wellFormed_decOf (view_bounded D V ) (fun _ _ => lt_of_elig) (rle S D)
    (chooseLeast (S) D)
  slot := fun _ _ h => mem_slotBlocks_of_decOf
    (slotBlocks_restrict_subset (S) D V ) chooseSound_least
    (fun _ _ => lt_of_elig) h
  finite := ⟨dagHorizon D + 1, fun _ hs => decOf_of_gt (by omega)⟩

/-- An assignment commits only below the horizon: a commit names a block
of the slot, so the slot's round is one the view holds. -/
theorem le_dagHorizon {D : Dag Validator BlockId Payload} {S : Slots Validator}
    {V : D.View} {dec : ℕ → Verdict BlockId}
    (ha : Assignment (S) D V  dec) {a : ℕ} {A : BlockId}
    (h : dec a = Verdict.commit A) : a ≤ dagHorizon D := by
  have hA := ha.slot a A h
  rw [mem_slotBlocks] at hA
  refine rle S D a ?_
  rw [← hA.1.2]
  exact Finset.le_sup (f := fun b => (D.block b).round) hA.1.1

/-- **A verdict of this rule is the pass's verdict.** One direction is
the pass being an assignment; the other is `eq_of_wellFormed`, which
says an assignment's decisions are reached by every assignment over the
same rules, the pass included.

This is what makes the remaining properties statable as facts about a
*function*. `Decided` is existential, and an existential over
assignments has no induction on it; through this it has a normal form. -/
theorem decided_iff {D : Dag Validator BlockId Payload} {S : Slots Validator}
    {V : (finWhaleRule (Payload := Payload)).View D} {k : ℕ} {v : Option BlockId} :
    (finWhaleRule (Payload := Payload)).Decided S V k v ↔
      VerdictIs (passOf S D V) k v := by
  refine ⟨?_, fun h => ⟨passOf S D V, assignment_passOf V, h⟩⟩
  rintro ⟨dec, ha, hv⟩
  have hnu : dec k ≠ Verdict.undecided := by
    cases v <;> (rw [show dec k = _ from hv]; simp)
  have := eq_of_wellFormed ha.wf (assignment_passOf V).wf (fun _ _ => lt_of_elig)
    (fun a A h => le_dagHorizon ha h) k hnu
  cases v with
  | none => exact this.trans hv
  | some b => exact this.trans hv

/-- **A direct commit in view is a verdict**, at any schedule and with
no side condition. -/
theorem decided_of_directCommit {D : Dag Validator BlockId Payload} {S : Slots Validator}
    (V : D.View) {k : ℕ} {L : BlockId}
    (hslot : L ∈ LeanDag.FinWhale.slotBlocks (S)
      (V.toRecord) k)
    (hcom : LeanDag.FinWhale.DirectCommit (V.toRecord) L) :
    (finWhaleRule (Payload := Payload)).Decided S (U := D) V k (some L) :=
  decided_iff (V := V) |>.2
    ((assignment_passOf V).wf.direct_commit k L ⟨hslot, hcom⟩)

/-- A decided verdict, as the property layer's option. -/
def optOf (w : Verdict BlockId) : Option BlockId :=
  match w with
  | Verdict.commit b => some b
  | _ => none

/-- And reading it back is the verdict, wherever the slot is decided. -/
theorem verdictIs_optOf {dec : ℕ → Verdict BlockId} {r : ℕ}
    (h : dec r ≠ Verdict.undecided) : VerdictIs dec r (optOf (dec r)) := by
  rcases hw : dec r with b | - | -
  · exact hw
  · exact hw
  · exact absurd hw h

/-- Two assignments agreeing at a slot carry the same verdict there. -/
theorem verdictIs_of_eq {dec dec' : ℕ → Verdict BlockId} {r r' : ℕ} {v : Option BlockId}
    (h : dec' r' = dec r) (hv : VerdictIs dec r v) : VerdictIs dec' r' v := by
  cases v with
  | some b => exact h.trans hv
  | none => exact h.trans hv

/-! ## The band

`Banded` is the property no other rule in this development has to prove
the hard way. Every other one inducts over its decision relation, whose
premises are monotone in the DAG; FinWhale's verdicts are a function
constrained by `WellFormed`, and there is nothing to induct on. What
takes its place is a downward induction on slots — the same shape as
Lemma 12's — with `Band.lean`'s transport at each step.

The one case the transport cannot settle alone is a slot the *larger*
DAG decides directly and the smaller one decided from an anchor. That is
not a band question at all: it is FinWhale's own exclusion between a
direct commit and the tie-break, read inside `D'` alone, which
`exclusions_of_views` supplies. -/

/-- **The top of the band**: two rounds above the highest round the DAG
holds. The two are slack — nothing sits there — and they give the
transport lemmas the room they need above a candidate. -/
def dagTop (D : Dag Validator BlockId Payload) : ℕ :=
  D.ids.sup (fun b => (D.block b).round) + 2

/-- **A decided slot's round is one the DAG reaches.** Every route to a
verdict names a block: a direct commit names the candidate, a direct
skip names the blamers two rounds up, and an indirect verdict names the
anchor's candidate three rounds up. -/
theorem slotRound_le_of_decided {D : Dag Validator BlockId Payload} {S : Slots Validator}
    {V : D.View} {m : ℕ}
    (h : passOf S D V  m ≠ Verdict.undecided) :
    S.slotRound m + 2 ≤ dagTop D := by
  classical
  have ha := assignment_passOf (S := S) V
  have hsup : ∀ b ∈ V.ids, (D.block b).round ≤ D.ids.sup (fun b => (D.block b).round) :=
    fun b hbV => Finset.le_sup (f := fun b => (D.block b).round) (V.subset_ids hbV)
  unfold dagTop
  by_cases hdc : ∃ l, LeanDag.FinWhale.viewCommit (S) D V  m l
  · obtain ⟨l, hslot, -⟩ := hdc
    rw [mem_slotBlocks] at hslot
    have hlr : (D.block l).round = S.slotRound m := hslot.1.2
    have := hsup l hslot.1.1
    omega
  · by_cases hds : LeanDag.FinWhale.viewSkip (S) D V  m
    · obtain ⟨-, nonev, hcard, hnon⟩ := hds
      have hpos : 0 < nonev.card := by
        have := LeanDag.FinWhale.params_arith (Validator := Validator)
        simp only [LeanDag.FinWhale.spQuorum] at hcard; omega
      obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
      obtain ⟨c, hc, -, -⟩ := hnon v₀ hv₀
      simp only [LeanDag.blocksAt, Finset.mem_filter] at hc
      have hcr : (D.block c).round = S.slotRound m + 2 := hc.2
      have := hsup c hc.1
      omega
    · obtain ⟨a, hanc⟩ := ha.wf.has_anchor m hdc hds h
      have hva : passOf S D V  a ≠ Verdict.undecided := fun hu =>
        h (ha.wf.indirect_undecided m a hdc hds hanc hu)
      rcases hq : passOf S D V  a with A | - | -
      · have hA := ha.slot a A hq
        rw [mem_slotBlocks] at hA
        have hle : (D.block A).round ≤ D.ids.sup (fun b => (D.block b).round) :=
          Finset.le_sup (f := fun b => (D.block b).round) hA.1.1
        have hAr : (D.block A).round = S.slotRound a := hA.1.2
        have helig : S.slotRound m + 3 ≤ S.slotRound a := hanc.1
        omega
      · exact absurd hq hanc.2.1
      · exact absurd hq hva

/-- **FinWhale is banded.** The band runs from the slot's own round to
two above the DAG's highest, and the argument is a downward induction on
slots with `Band.lean`'s transport at each step.

Three cases, and the third is the one with content. A slot the smaller
view decided directly stays decided the same way, because a commit and a
skip both survive a band. A slot it decided from an anchor keeps its
anchor — the anchor's commit and the skips below it transport by the
induction hypothesis — and then the tie-break is the same function of
the same anchor. What is left is the larger view deciding *directly* a
slot the smaller one decided from an anchor, and that is settled inside
`D'` alone: a direct commit pins what the tie-break may name, and a
direct skip bars it naming anything. -/
theorem banded : Banded (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) := by
  classical
  intro S D V k v hd
  refine ⟨dagTop D, fun g g' d d' S' D' V' k' hkd hsch hlead hab hVsub => ?_⟩
  have hbU : LeanDag.FinWhale.Band D D' (S.slotRound k + g) (dagTop D + g) g g' :=
    { mem := fun b hbm h1 h2 => hab.mem b hbm h1 h2
      block := fun b hbm h1 h2 => hab.block b hbm (Or.inl ⟨h1, h2⟩)
      block' := fun b hbm hbm' h1 h2 => hab.block b hbm (Or.inr ⟨hbm', h1, h2⟩)
      refs := fun b hbm h1 h2 => hab.refs b hbm h1 h2 }
  have hbV : LeanDag.FinWhale.Band (V.toRecord)
      (V'.toRecord)
      (S.slotRound k + g) (dagTop D + g) g g' :=
    { mem := fun b hbm h1 h2 => by
        simp only [BlockRecord.View.toRecord_block] at h1 h2
        refine hVsub b hbm ?_ ?_
        · change S.slotRound k ≤ (D.block b).round
          omega
        · change (D.block b).round ≤ dagTop D
          omega
      block := fun b hbm h1 h2 => hab.block b (V.subset_ids hbm) (Or.inl ⟨h1, h2⟩)
      block' := fun b hbm hbm' h1 h2 =>
        hab.block b (V.subset_ids hbm) (Or.inr ⟨V'.subset_ids hbm', h1, h2⟩)
      refs := fun b hbm h1 h2 => hab.refs b (V.subset_ids hbm) h1 h2 }
  have ha := assignment_passOf (S := S) (D := D) V
  have wf := ha.wf
  have wf' := (assignment_passOf (S := S') (D := D') V').wf
  have hex := LeanDag.FinWhale.exclusions_of_views (S := S') (D := D')
    (V := V') (V' := V') chooseSound_least
  have key : ∀ n m m', dagHorizon D - m ≤ n → k ≤ m → m + d' = m' + d →
      passOf S D V m ≠ Verdict.undecided →
      passOf S' D' V' m' = passOf S D V m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m m' hn hkm hmm hdec
      have IH : ∀ b b', m < b → b ≤ dagHorizon D → b + d' = b' + d →
          passOf S D V b ≠ Verdict.undecided →
          passOf S' D' V' b' = passOf S D V b := by
        intro b b' hmb hbN hbb hbd
        have hn0 : n ≠ 0 := by rintro rfl; omega
        exact ih (n - 1) (by omega) b b' (by omega) (by omega) hbb hbd
      have hmono : S.slotRound k ≤ S.slotRound m := S.mono hkm
      have hmtop : S.slotRound m + 2 ≤ dagTop D := slotRound_le_of_decided hdec
      have hrmS : S.slotRound m + g = S'.slotRound m' + g' := hsch m m' hmm
      have hlmS : S.leader m = S'.leader m' := hlead m m' hmm (by omega)
      -- the same two facts in the model's vocabulary, where the transport reads them
      have hrm : S.slotRound m + g = S'.slotRound m' + g' := hrmS
      have hlm : S.leader m = S'.leader m' := hlmS
      have hmlo : S.slotRound k + g ≤ S.slotRound m + g := by
        change S.slotRound k + g ≤ S.slotRound m + g
        omega
      have hmhi0 : S.slotRound m + g ≤ dagTop D + g := by
        change S.slotRound m + g ≤ dagTop D + g
        omega
      have hmhi : S.slotRound m + g + 2 ≤ dagTop D + g := by
        change S.slotRound m + g + 2 ≤ dagTop D + g
        omega
      by_cases hdc : ∃ l, LeanDag.FinWhale.viewCommit (S) D V m l
      · obtain ⟨l, hslot, hcom⟩ := hdc
        have hlmem : l ∈ V.ids ∧ (D.block l).round = S.slotRound m := by
          rw [mem_slotBlocks] at hslot; exact ⟨hslot.1.1, hslot.1.2⟩
        have hllo : S.slotRound k + g ≤
            ((V.toRecord).block l).round + g := by
          change S.slotRound k + g ≤ (D.block l).round + g
          omega
        have hlhi : ((V.toRecord).block l).round + g + 2 ≤
            dagTop D + g := by
          change (D.block l).round + g + 2 ≤ dagTop D + g
          omega
        have hslot' := LeanDag.FinWhale.Band.slotBlocks_subset hbV hrm hlm hmlo hmhi0 hslot
        have hcom' := LeanDag.FinWhale.Band.directCommit hbV hlmem.1 hllo hlhi hcom
        rw [wf.direct_commit m l ⟨hslot, hcom⟩, wf'.direct_commit m' l ⟨hslot', hcom'⟩]
      · by_cases hds : LeanDag.FinWhale.viewSkip (S) D V m
        · have hds' := LeanDag.FinWhale.Band.directSkip hbV hrm hlm hmlo hmhi hds
          rw [wf.direct_skip m hds, wf'.direct_skip m' hds']
        · obtain ⟨a, hanc⟩ := wf.has_anchor m hdc hds hdec
          have hva : passOf S D V a ≠ Verdict.undecided := fun hu =>
            hdec (wf.indirect_undecided m a hdc hds hanc hu)
          rcases hq : passOf S D V a with A | - | -
          · have haN : a ≤ dagHorizon D := le_dagHorizon ha hq
            have helig : S.slotRound m + 3 ≤ S.slotRound a := hanc.1
            have hma : m < a := lt_of_elig hanc.1
            obtain ⟨a', haa⟩ : ∃ a', a + d' = a' + d := ⟨a + d' - d, by omega⟩
            have hra : S.slotRound a + g = S'.slotRound a' + g' := hsch a a' haa
            have helig' : S'.slotRound m' + 3 ≤ S'.slotRound a' := by omega
            have hqa' : passOf S' D' V' a' = Verdict.commit A := by
              rw [IH a a' hma haN haa (by rw [hq]; simp), hq]
            have hanc' : LeanDag.FinWhale.Anchor (Slots.Elig S')
                (passOf S' D' V') m' a' := by
              refine ⟨helig', by rw [hqa']; simp, fun b' heb' hlb' => ?_⟩
              have hmb' : m' < b' := lt_of_elig (S := S') heb'
              obtain ⟨b, hbb⟩ : ∃ b, b + d' = b' + d := ⟨b' + d - d', by omega⟩
              have hrb : S.slotRound b + g = S'.slotRound b' + g' := hsch b b' hbb
              have heb : S'.slotRound m' + 3 ≤ S'.slotRound b' := heb'
              have hskip := hanc.2.2 b (show S.slotRound m + 3 ≤ S.slotRound b by omega)
                (by omega)
              rw [IH b b' (by omega) (by omega) hbb (by rw [hskip]; simp), hskip]
            have hA := ha.slot a A hq
            rw [mem_slotBlocks] at hA
            have hAr : (D.block A).round = S.slotRound a := hA.1.2
            have hAtop : S.slotRound a + 2 ≤ dagTop D := slotRound_le_of_decided hva
            have hka : S.slotRound k ≤ S.slotRound a := S.mono (by omega)
            have hAlo : S.slotRound k + g ≤ (D.block A).round + g := by omega
            have hAhi : (D.block A).round + g ≤ dagTop D + g := by omega
            have hAD' : A ∈ D'.ids := hbU.mem A hA.1.1 hAlo hAhi
            have hArd' : (D'.block A).round + g' = (D.block A).round + g :=
              (hbU.block A hA.1.1 hAlo hAhi).1
            have hch : LeanDag.FinWhale.chooseLeast (S') D' A m' =
                LeanDag.FinWhale.chooseLeast (S) D A m :=
              LeanDag.FinWhale.Band.chooseLeast_band hbU hrm hlm hmlo hmhi hA.1.1 hAlo hAhi
            have hval := wf.indirect_commit m a A hdc hds hanc hq
            have habove : A ∈ D'.ids ∧ S'.slotRound m' + 3 ≤ (D'.block A).round :=
              ⟨hAD', by omega⟩
            by_cases hdc' :
                ∃ l, LeanDag.FinWhale.viewCommit (S') D' V' m' l
            · obtain ⟨l', hl'⟩ := hdc'
              obtain ⟨b, hbch⟩ := hex.commit_forces_choose m' l' A habove hl'
              have hbl := hex.commit_pins_choose m' l' A b hl' hbch
              rw [wf'.direct_commit m' l' hl', hval, ← hch, hbch, hbl]
            · by_cases hds' : LeanDag.FinWhale.viewSkip (S') D' V' m'
              · rw [wf'.direct_skip m' hds', hval]
                rcases hcv : LeanDag.FinWhale.chooseLeast (S) D A m with - | b
                · rfl
                · exact absurd (hch.trans hcv) (hex.skip_bars_choose m' A b hds')
              · rw [wf'.indirect_commit m' a' A hdc' hds' hanc' hqa', hval, hch]
          · exact absurd hq hanc.2.1
          · exact absurd hq hva
  have hdk : VerdictIs (passOf S D V) k v := decided_iff.1 hd
  exact decided_iff.2 (verdictIs_of_eq
    (key (dagHorizon D) k k' (by omega) (le_refl k) hkd
      (by cases v <;> (rw [show passOf S D V k = _ from hdk]; simp))) hdk)

/-! ## The liveness property

`LeaderCommits` is `Support.leaderCommits` at `fwSupport` below. What
FinWhale supplies here is the slow-path quorum's place inside the correct
set, and the reading of its certificate condition from coverage. Both are
stated in rounds rather than in slot indices, which is what lets them be
read at a general schedule at all. -/

/-- **The slow-path quorum fits inside the correct set.** `n + 1 = 3f + 2p`
with `p ≥ 1` gives `2f + p ≤ n − f`. -/
theorem spQuorum_le_card_correct :
    LeanDag.FinWhale.spQuorum Validator ≤ (Correct : Finset Validator).card := by
  have hq : quorumCard Validator ≤ (Correct : Finset Validator).card := card_correct
  have hc := P.card_add_one
  have hp := P.p_pos
  have hf := P.p_le_f
  have hqc : quorumCard Validator = Fintype.card Validator - F.f := rfl
  have hsp : LeanDag.FinWhale.spQuorum Validator = 2 * F.f + P.p := rfl
  omega

/-- **Every correct validator certifies a correct leader**, on a
synchronised and populated DAG. The leader's block sits at round `r`;
every correct block at `r + 1` references it, because coverage says a
correct block holds every correct block below it, so every one of them
votes; and a correct block at `r + 2` references all of those, so its
parents voting for the leader are all of `Correct`, which carries the
slow-path quorum. -/
theorem spCommitBy_of_synchronisedOn {D : Dag Validator BlockId Payload} {Rnd r : ℕ}
    (hs : SynchronisedFrom D.block D.ids (Correct : Finset Validator) Rnd)
    (hpop1 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 1))
    (hpop2 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 2))
    (hR : Rnd ≤ r) {L : BlockId} (hL : L ∈ D.ids) (hLr : (D.block L).round = r)
    (hLc : (D.block L).creator ∈ (Correct : Finset Validator)) :
    LeanDag.FinWhale.SPCommitBy D L (Correct : Finset Validator) := by
  refine ⟨(Correct : Finset Validator), Finset.Subset.rfl, spQuorum_le_card_correct, ?_⟩
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop2 v hv
  refine ⟨b, mem_blocksAt.mpr ⟨hb, by rw [hbr, hLr]⟩, hbc, ?_⟩
  refine le_trans spQuorum_le_card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨q, hq, hqc, hqr⟩ := hpop1 w hw
  have hvote : L ∈ (D.block q).refs :=
    hs r hR q hq hqr (by rw [hqc]; exact hw) L hL hLr hLc
  have hpar : q ∈ (D.block b).refs :=
    hs (r + 1) (by omega) b hb hbr (by rw [hbc]; exact hv) q hq hqr (by rw [hqc]; exact hw)
  unfold LeanDag.FinWhale.parentsVoting creatorsOf
  exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hpar, hvote⟩, hqc⟩

/-! ## FinWhale's support shape

`Properties/Support.lean`. The slow path: SP-certificates two rounds
above the candidate, each a block `spQuorum` of whose parents vote. The
fast path is latency and is not a liveness shape. -/

/-- The slow-path quorum fits inside any quorum of the fault model:
`n + 1 = 3f + 2p` with `p ≥ 1` gives `2f + p ≤ n − f`. -/
theorem spQuorum_le_quorumCard :
    LeanDag.FinWhale.spQuorum Validator ≤ quorumCard Validator := by
  have hc := P.card_add_one
  have hp := P.p_pos
  have hf := P.p_le_f
  have hqc : quorumCard Validator = Fintype.card Validator - F.f := rfl
  have hsp : LeanDag.FinWhale.spQuorum Validator = 2 * F.f + P.p := rfl
  omega

/-- **FinWhale's support**: wavelength two, certification the slow path's. -/
def fwSupport : Support (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  wave := 2
  Certifies := fun D c l => LeanDag.FinWhale.SPCertificate D c l

/-- **Law 1.** A certifier two rounds above the settling round keeps its
parents, and each parent keeps its parents and its author, so its
voting parents are the same validators. -/
theorem fwSupport_local :
    Support.Local (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) fwSupport := by
  intro D D' G R₀ h c L hc hcr _ _
  change R₀ + 2 ≤ (BlockRecord.block D c).round at hcr
  have hrefs : (BlockRecord.block D' c).refs = (BlockRecord.block D c).refs :=
    h.refs c hc (by change R₀ < (BlockRecord.block D c).round; omega)
  have hpar : ∀ q ∈ (BlockRecord.block D c).refs,
      (BlockRecord.block D' q).refs = (BlockRecord.block D q).refs ∧
      (BlockRecord.block D' q).creator = (BlockRecord.block D q).creator := by
    intro q hq
    have hqD := BlockRecord.complete D c hc q hq
    have hqr := (BlockRecord.valid D c hc).predecessor q hq
    exact ⟨h.refs q hqD (by change R₀ < (BlockRecord.block D q).round; omega),
      h.creator q hqD (by change R₀ ≤ (BlockRecord.block D q).round; omega)⟩
  change LeanDag.FinWhale.SPCertificate D' c L ↔ LeanDag.FinWhale.SPCertificate D c L
  unfold LeanDag.FinWhale.SPCertificate LeanDag.FinWhale.parentsVoting creatorsOf
  rw [hrefs, Finset.filter_congr (fun q hq => by rw [(hpar q hq).1]),
    Finset.image_congr (fun q hq => (hpar q (Finset.mem_of_mem_filter q hq)).2)]

/-- **Law 2.** Coverage toward the candidate over two layers: every
quorum block one round up votes, every quorum block two rounds up
references each voter, and the quorum carries `spQuorum`. -/
theorem fwSupport_ofCoverage :
    Timed.OfCoverage (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) fwSupport (coreReliability Validator) := by
  intro D T hq r L hpop hct hL hLr hLc c hc hcc hcr
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  change LeanDag.FinWhale.spQuorum Validator ≤ (LeanDag.FinWhale.parentsVoting D c L).card
  refine le_trans (le_trans spQuorum_le_quorumCard hcard) (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨q, hq', hqc, hqr⟩ := hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega) w hw
  have hqT : (finWhaleRule.block D q).creator ∈ T := by rw [hqc]; exact hw
  have hvote : L ∈ (BlockRecord.block D q).refs :=
    hct r le_rfl (by change r < r + 2; omega) q hq' hqT hqr L hL hLc hLr
      Relation.ReflTransGen.refl
  have hpar : q ∈ (BlockRecord.block D c).refs :=
    hct (r + 1) (by omega) (by change r + 1 < r + 2; omega) c hc hcc
      (by change (BlockRecord.block D c).round = r + 1 + 1
          rw [show (BlockRecord.block D c).round = r + 2 from hcr])
      q hq' hqT hqr (Relation.ReflTransGen.single (show RefStepFrom (finWhaleRule.block D) q L from hvote))
  unfold LeanDag.FinWhale.parentsVoting creatorsOf
  exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hpar, hvote⟩, hqc⟩

/-- **Law 3.** A quorum's SP-certificates at the slot's candidate, all
held by a view caught up to the certificate round, are a direct commit
on that view, and the pass commits it. -/
theorem fwSupport_commits :
    Support.Commits (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) fwSupport (coreReliability Validator) := by
  intro S D V T k hq hpop hcert hcov hlead
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hLc' : (BlockRecord.block D L).creator = S.leader k := hLc
  have hLr' : (BlockRecord.block D L).round = S.slotRound k := hLr
  have hlV : L ∈ V.ids := hcov L hLmem
    (by change (BlockRecord.block D L).round ≤ S.slotRound k + 2; omega)
  have hvc : LeanDag.FinWhale.viewCommit (S) D V k L := by
    refine ⟨?_, Or.inr ⟨T, le_trans spQuorum_le_quorumCard hcard, fun v hv => ?_⟩⟩
    · rw [mem_slotBlocks]
      simp only [BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
      exact ⟨⟨hlV, hLr'⟩, hLc'⟩
    · obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 2) (by omega)
        (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega) v hv
      have hbr' : (BlockRecord.block D b).round = S.slotRound k + 2 := hbr
      have hbV : b ∈ V.ids := hcov b hb
        (by change (BlockRecord.block D b).round ≤ S.slotRound k + 2; omega)
      refine ⟨b, ?_, hbc, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hbc hbr⟩
      rw [mem_blocksAt]
      simp only [BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
      exact ⟨hbV, by rw [hbr', hLr']⟩
  refine ⟨L, by omega,
    decided_iff.2 ((assignment_passOf V).wf.direct_commit k L hvc),
    fun S' hround hlead' => ?_⟩
  have hr : S'.slotRound k = S.slotRound k := by
    change S'.slotRound k = S.slotRound k; rw [hround]
  have hvc' := (LeanDag.FinWhale.viewCommit_congr hr (hlead' k (by omega))).2 hvc
  exact decided_iff.2 ((assignment_passOf V).wf.direct_commit k L hvc')

/-! ## FinWhale's fast path

`voteSupport`: `n − p` votes one round up. Its fault model is at most
`p` Byzantine validators, which `Params` bounds by `f` but does not
demand; `fwFastReliability` takes the bound as a hypothesis. -/

/-- **The fast path's fault model**: at most `p` Byzantine validators. -/
def fwFastReliability (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
    (h : F.byzantine.card ≤ P.p) : LeanDag.Reliability Validator where
  correct := (Correct : Finset Validator)
  slack := P.p
  covers := by
    have hc : (Correct : Finset Validator)ᶜ = F.byzantine := by simp [Correct]
    rw [hc]; exact h
  minority := by
    have := P.card_add_one
    have := P.p_pos
    have := P.p_le_f
    omega

/-- **Law 3 of `voteSupport`, for FinWhale's fast path**: `n − p` votes
held by a caught-up view are a fast commit on it, and the pass commits. -/
theorem voteSupport_fast_commits (h : F.byzantine.card ≤ P.p) :
    Support.Commits (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))
      (voteSupport (finWhaleRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)))
      (fwFastReliability Validator h) := by
  intro S D V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.FinWhale.fastCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - P.p ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hLc' : (BlockRecord.block D L).creator = S.leader k := hLc
  have hLr' : (BlockRecord.block D L).round = S.slotRound k := hLr
  have hlV : L ∈ V.ids := hcov L hLmem
    (by change (BlockRecord.block D L).round ≤ S.slotRound k + 1; omega)
  have hvc : LeanDag.FinWhale.viewCommit (S) D V k L := by
    refine ⟨?_, Or.inl ?_⟩
    · rw [mem_slotBlocks]
      simp only [BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
      exact ⟨⟨hlV, hLr'⟩, hLc'⟩
    · change LeanDag.FinWhale.fastCard Validator ≤
        (LeanDag.FinWhale.voters (V.toRecord) L).card
      refine le_trans hcard (Finset.card_le_card ?_)
      intro v hv
      obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) v hv
      have hbr' : (BlockRecord.block D b).round = S.slotRound k + 1 := hbr
      have hbV : b ∈ V.ids := hcov b hb
        (by change (BlockRecord.block D b).round ≤ S.slotRound k + 1; omega)
      unfold LeanDag.FinWhale.voters supporters creatorsOf
      refine Finset.mem_image.mpr ⟨b, ?_, hbc⟩
      rw [Finset.mem_filter, mem_blocksAt]
      simp only [BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
      exact ⟨⟨hbV, by rw [hbr', hLr']⟩, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hbc hbr⟩
  refine ⟨L, by omega,
    decided_iff.2 ((assignment_passOf V).wf.direct_commit k L hvc),
    fun S' hround hlead' => ?_⟩
  have hr : S'.slotRound k = S.slotRound k := by
    change S'.slotRound k = S.slotRound k; rw [hround]
  have hvc' := (LeanDag.FinWhale.viewCommit_congr hr (hlead' k (by omega))).2 hvc
  exact decided_iff.2 ((assignment_passOf V).wf.direct_commit k L hvc')

/-! ## The indirect rule

`Properties.Indirect` asks for a verdict at the slot below a committed
anchor, and asks for it at a **tight bound**: the verdict must survive
any reassignment of leaders away from the slot itself. FinWhale meets
that because every rule it applies at a slot reads the schedule at that
slot alone — `slotBlocks_congr`, `directSkip_congr`,
`indirectCommit_congr`, `chooseLeast_congr` — so the whole of
`pass_indirect` is one case split with a congruence in each branch. -/

/-- **FinWhale's eligibility, off the round structure alone**: an
anchor's candidate sits three rounds above the slot's. It is
`Slots.Elig` with the schedule replaced by its round function, which is
what the property's second quantifier needs — a reassignment of leaders
must not change who may anchor whom. -/
def finWhaleElig (rd : ℕ → ℕ) (i j : ℕ) : Prop := rd i + 3 ≤ rd j

/-- **Two schedules sharing a slot's round and leader decide it alike,
given a common anchor.** Either a direct rule fires — and it is the same
rule, because it reads the slot's round and leader — or the tie-break
does, and it reads the anchor and the same slot. Taking `S' := S` gives
the other half: the slot is decided at all. -/
theorem pass_indirect {D : Dag Validator BlockId Payload} {S S' : Slots Validator}
    {V : D.View} {i j : ℕ} {A : BlockId}
    (hround : S'.slotRound = S.slotRound) (hleader : S'.leader i = S.leader i)
    (hanc : LeanDag.FinWhale.Anchor (Slots.Elig S) (passOf S D V ) i j)
    (hjv : passOf S D V  j = Verdict.commit A)
    (hanc' : LeanDag.FinWhale.Anchor (Slots.Elig S') (passOf S' D V ) i j)
    (hjv' : passOf S' D V  j = Verdict.commit A) :
    passOf S' D V  i = passOf S D V  i ∧ passOf S D V  i ≠ Verdict.undecided := by
  classical
  have hwf := (assignment_passOf (S := S) V).wf
  have hwf' := (assignment_passOf (S := S') V).wf
  have hr : S'.slotRound i = S.slotRound i := by
    change S'.slotRound i = S.slotRound i; rw [hround]
  have hl : S'.leader i = S.leader i := hleader
  by_cases hdc : ∃ l, LeanDag.FinWhale.viewCommit (S) D V  i l
  · obtain ⟨l, hlc⟩ := hdc
    have h1 := hwf.direct_commit i l hlc
    have h2 := hwf'.direct_commit i l ((LeanDag.FinWhale.viewCommit_congr hr hl).2 hlc)
    exact ⟨by rw [h1, h2], by rw [h1]; simp⟩
  · by_cases hds : LeanDag.FinWhale.viewSkip (S) D V  i
    · have h1 := hwf.direct_skip i hds
      have h2 := hwf'.direct_skip i ((LeanDag.FinWhale.viewSkip_congr hr hl).2 hds)
      exact ⟨by rw [h1, h2], by rw [h1]; simp⟩
    · have hdc' : ¬ ∃ l, LeanDag.FinWhale.viewCommit (S') D V  i l := by
        rintro ⟨l, h⟩; exact hdc ⟨l, (LeanDag.FinWhale.viewCommit_congr hr hl).1 h⟩
      have hds' : ¬ LeanDag.FinWhale.viewSkip (S') D V  i := fun h =>
        hds ((LeanDag.FinWhale.viewSkip_congr hr hl).1 h)
      have h1 := hwf.indirect_commit i j A hdc hds hanc hjv
      have h2 := hwf'.indirect_commit i j A hdc' hds' hanc' hjv'
      have hch : LeanDag.FinWhale.chooseLeast (S') D A i =
          LeanDag.FinWhale.chooseLeast (S) D A i :=
        LeanDag.FinWhale.chooseLeast_congr hr hl
      refine ⟨by rw [h1, h2, hch], ?_⟩
      rw [h1]
      cases LeanDag.FinWhale.chooseLeast (S) D A i <;> simp

/-- **The indirect rule, with its bound.** The anchor is the committed
slot `j`; the eligible slots between are skipped, so `j` is the *first*
unskipped one and `Anchor` holds of the pass. `pass_indirect` then says
the verdict at `i` survives every reassignment of leaders away from `i`,
which is the second quantifier. -/
theorem indirect : Indirect
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    finWhaleElig := by
  classical
  intro S D V i j A helig hj hmid
  have hanc : ∀ S₀ : Slots Validator, S₀.slotRound = S.slotRound →
      (finWhaleRule (Payload := Payload)).Decided S₀ V j (some A) →
      (∀ i', i < i' → i' < j → finWhaleElig S.slotRound i i' →
        (finWhaleRule (Payload := Payload)).Decided S₀ V i' none) →
      LeanDag.FinWhale.Anchor ((S₀).Elig) (passOf S₀ D V) i j ∧
        passOf S₀ D V j = Verdict.commit A := by
    intro S₀ hround hjd hmidd
    have hjv : passOf S₀ D V j = Verdict.commit A := decided_iff.1 hjd
    refine ⟨⟨?_, by rw [hjv]; simp, fun a' hea' hlta' => ?_⟩, hjv⟩
    · change S₀.slotRound i + 3 ≤ S₀.slotRound j
      rw [hround]; exact helig
    · have hea : finWhaleElig S.slotRound i a' := by
        have h : S₀.slotRound i + 3 ≤ S₀.slotRound a' := hea'
        rw [hround] at h; exact h
      exact decided_iff.1 (hmidd a' (lt_of_elig (S := S₀) hea') hlta' hea)
  obtain ⟨hancS, hjvS⟩ := hanc S rfl hj hmid
  refine ⟨optOf (passOf S D V i), fun S' hround hleader hjd' hmid' => ?_⟩
  obtain ⟨hancS', hjvS'⟩ := hanc S' hround hjd' hmid'
  obtain ⟨heq, hne⟩ := pass_indirect hround hleader hancS hjvS hancS' hjvS'
  exact decided_iff.2 (verdictIs_of_eq heq (verdictIs_optOf hne))

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
  L ∈ V.ids ∧ LeanDag.FinWhale.DirectCommit (V.toRecord) L

/-- **And a direct commit is a verdict**, at every schedule.
`IsCandidate` places the block at the slot, `DirectCommitIn` puts it in
the view and certifies it, and `decided_of_directCommit` runs the pass
that reads the commit off. -/
theorem commitsDirect : CommitsDirect
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {_} V L r => DirectCommitIn V L r) := by
  rintro S D V k L ⟨-, hround, hcreator⟩ ⟨hmem, hdir⟩
  exact decided_of_directCommit V
    (mem_slotBlocks.2 ⟨⟨hmem, hround⟩, hcreator⟩) hdir

/-! ## The headlines

FinWhale's DAG carries no self-parent clause at the carrier, so it
shows progress and not inclusion. -/

theorem safety : Properties.Safe (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

theorem progress : Properties.Support.Progresses (fwSupport (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload)) (coreReliability Validator) :=
  Properties.Support.progress fwSupport_commits

end FinWhaleProperties

end LeanDag
