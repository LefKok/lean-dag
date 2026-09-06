import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Candidate
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Sustain

/-!
# Chain quality, for any protocol with a quorum law

`docs/target-properties.md` §11.4, the last mechanism whose capstone was
written at one protocol. `chain-quality.md` proved CQ1–CQ7 for the core
over its own `BlockUniverse` and `Decided`; this file is the same arc
over `Properties.DagRule`, and the core's is now an instance of it
(`Quality/`).

**What the arc needs of a rule, in full.** Three things, and only the
last is about verdicts:

* `Causal` — references are present and one round down. Already one of
  the six.
* `Quorate` — a non-genesis block references a quorum of distinct
  authors (`Properties/Optional/Quorate.lean`). This is the carrier law
  §11.4 predicted, arriving as a property.
* `CommitsCandidate` — a committed block is a block of its slot. Already
  one of the six, and the one step the coverage half takes from the
  decision rule.

The inclusion half adds `LeaderCommits` for the committing slot, and
synchrony as a hypothesis, exactly as the core's did.

**What it does not need.** No band, no agreement, no view monotonicity.
Chain quality is a statement about what a *single* commit carries, so
it reads the rule at one verdict and never compares two.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload} {rel : Reliability Validator}
variable {U : R.Universe} {b L : BlockId} {δ : ℕ}

/-! ## Coverage, with no decision rule in sight -/

/-- The reliable validators whose round-`δ` block a cone carries — the
complement, within the reliable set, of `missingAtFrom`. -/
def coveredAt (R : DagRule Validator BlockId Payload) (rel : Reliability Validator)
    (U : R.Universe) (b : BlockId) (δ : ℕ) : Finset Validator :=
  rel.correct.filter fun v =>
    ∃ i ∈ historyFrom (R.block U) b, (R.block U i).creator = v ∧ (R.block U i).round = δ

theorem mem_coveredAt {v : Validator} :
    v ∈ coveredAt R rel U b δ ↔ v ∈ rel.correct ∧
      ∃ i ∈ historyFrom (R.block U) b,
        (R.block U i).creator = v ∧ (R.block U i).round = δ :=
  Finset.mem_filter

theorem coveredAt_subset_correct : coveredAt R rel U b δ ⊆ rel.correct :=
  Finset.filter_subset _ _

/-- Covered and missing partition the reliable validators. -/
theorem coveredAt_eq_sdiff :
    coveredAt R rel U b δ = rel.correct \ missingAtFrom (R.block U) rel b δ := by
  ext v
  rw [mem_coveredAt, Finset.mem_sdiff, mem_missingAtFrom]
  constructor
  · rintro ⟨hv, i, hi, hic, hir⟩
    exact ⟨hv, fun ⟨_, hall⟩ => hall i hi ⟨hic, hir⟩⟩
  · rintro ⟨hv, hmiss⟩
    refine ⟨hv, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hmiss ⟨hv, fun i hi ⟨hic, hir⟩ => hnone i hi hic hir⟩

/-- **CQ1, the count.** A block's cone covers all but at most the slack
of the reliable validators, at every round below it. Purely structural:
density plus the partition. -/
theorem card_coveredAt_ge (hc : Causal R) (hq : Quorate R rel)
    (hb : b ∈ R.ids U) (hδ : δ < (R.block U b).round) :
    rel.correct.card - rel.slack ≤ (coveredAt R rel U b δ).card := by
  have hsub : missingAtFrom (R.block U) rel b δ ⊆ rel.correct := Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_of_subset hsub
  have hmiss := card_missingAtFrom_le (hc U) (hq U) hb hδ
  rw [coveredAt_eq_sdiff, hcard]
  omega

/-- **CQ2 (the half, where the committee gives it).** Every cone
carries, at every round below it, blocks from at least half the reliable
validators.

`hhalf` is the committee condition the packaging needs and `Reliability`
does not carry: the core has it from `n = 3f + 1`, and a model whose
crash bound outruns its slack parameter need not. Stating it as a
hypothesis is what lets the rules that have it quote the half and the
rules that do not still quote `card_coveredAt_ge`. -/
theorem card_correct_le_two_mul_coveredAt (hc : Causal R) (hq : Quorate R rel)
    (hhalf : 2 * rel.slack ≤ rel.correct.card)
    (hb : b ∈ R.ids U) (hδ : δ < (R.block U b).round) :
    rel.correct.card ≤ 2 * (coveredAt R rel U b δ).card := by
  have := card_coveredAt_ge hc hq hb hδ
  omega

/-! ## What a commit carries

One step from the decision rule, and it is `CommitsCandidate`: a
committed block is a block. Everything above then applies to it. -/

section Decided

variable {S : Slots Validator} {V : R.View U} {k : ℕ}

/-- **CQ1.** A committed leader's flush covers all but the slack of the
reliable validators at every round below it — any route, any view, no
synchrony. -/
theorem card_coveredAt_ge_of_decided (hc : Causal R) (hq : Quorate R rel)
    (hcc : CommitsCandidate R) (h : R.Decided S V k (some L))
    (hδ : δ < (R.block U L).round) :
    rel.correct.card - rel.slack ≤ (coveredAt R rel U L δ).card :=
  card_coveredAt_ge hc hq (hcc.mem h) hδ

/-- **CQ2.** -/
theorem card_correct_le_two_mul_coveredAt_of_decided (hc : Causal R) (hq : Quorate R rel)
    (hcc : CommitsCandidate R) (hhalf : 2 * rel.slack ≤ rel.correct.card)
    (h : R.Decided S V k (some L)) (hδ : δ < (R.block U L).round) :
    rel.correct.card ≤ 2 * (coveredAt R rel U L δ).card :=
  card_correct_le_two_mul_coveredAt hc hq hhalf (hcc.mem h) hδ

/-- **The ledger a verdict assignment names**: everything in the causal
history of a committed leader of a slot below `n`. The core's
`ledgerSet` at the carrier. -/
def ledgerSetOf (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ ReachesFrom (R.block U) L b}

/-- A cone block of a committed slot is in the ledger. -/
theorem mem_ledgerSetOf_of_mem_history (hc : Causal R) {g : ℕ → Option BlockId} {n : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ R.ids U)
    (hb : b ∈ historyFrom (R.block U) L) : b ∈ ledgerSetOf R U g n :=
  ⟨k, hk, L, hg, ((hc U).mem_history_iff hL).mp hb⟩

/-- **CQ3 (ledger coverage, cumulative).** For a verdict assignment `g`
with a committed slot `k < n` whose leader sits at round `r`: for every
`δ < r`, at least `|correct| − slack` reliable validators each have a
round-`δ` block in the ledger. The set is exhibited, so no choice and no
decidability of the ledger is needed. -/
theorem ledger_coverage (hc : Causal R) (hq : Quorate R rel) (hcc : CommitsCandidate R)
    {g : ℕ → Option BlockId} {n : ℕ}
    (hdec : R.Decided S V k (some L)) (hg : g k = some L) (hk : k < n)
    (hδ : δ < (R.block U L).round) :
    ∃ W : Finset Validator, W ⊆ rel.correct ∧
      rel.correct.card - rel.slack ≤ W.card ∧
      ∀ v ∈ W, ∃ i ∈ ledgerSetOf R U g n,
        (R.block U i).creator = v ∧ (R.block U i).round = δ := by
  refine ⟨coveredAt R rel U L δ, coveredAt_subset_correct,
    card_coveredAt_ge_of_decided hc hq hcc hdec hδ, ?_⟩
  intro v hv
  obtain ⟨-, i, hi, hic, hir⟩ := mem_coveredAt.mp hv
  exact ⟨i, mem_ledgerSetOf_of_mem_history hc hg hk (hcc.mem hdec) hi, hic, hir⟩

/-! ## Inclusion, at the price of synchrony

The aggregate coverage above upgrades to an *individual* guarantee —
every reliable block enters the ledger — once synchrony has settled, and
only then: the core's witness file carries a model in which commits
recur for ever while the same correct validator is missing from every
flushed layer. The engine is the backbone, which is `LeanDag.Density`'s
and asks nothing of the rule. -/

/-- **CQ5.** Post-`R₀`, every reliable block is in the cone of **every**
committed leader block with a reliable author at a later round — any
commit route, any view. -/
theorem mem_history_of_decided_commit (hc : Causal R) (hq : Quorate R rel)
    (hcc : CommitsCandidate R) {R₀ : ℕ} (hs : SynchronisedOn R U rel.correct R₀)
    (hdec : R.Decided S V k (some L))
    (hLc : (R.block U L).creator ∈ rel.correct)
    (hb : b ∈ R.ids U) (hbc : (R.block U b).creator ∈ rel.correct)
    (hR : R₀ ≤ (R.block U b).round)
    (hlt : (R.block U b).round < (R.block U L).round) :
    b ∈ historyFrom (R.block U) L :=
  mem_historyFrom_of_correct (hc U) (hq U) hs
    ((R.block U L).round - (R.block U b).round - 1)
    L (hcc.mem hdec) b hb hLc hbc hR (by omega)

/-! ## Inclusion liveness

The slot is produced *before* the universe is quantified: the schedule
fixes it, and any execution meeting the rule's own liveness precondition
then commits it. That order is what makes the statement a guarantee
rather than an observation, and it is the core's `IncludesAt` shape with
`Live` where the core wrote its own three conjuncts. -/

/-- **CQ6 (inclusion liveness).** Under a schedule that keeps returning
to reliable leaders and post-`R₀` synchrony, for every round `m ≥ R₀`
there is a slot — above `m`, reliably led — that any execution meeting
the rule's liveness precondition commits, and whose flush contains
**every** reliable round-`m` block; hence every such block is in the
ledger of any verdict assignment covering that slot.

Fairness is taken as a hypothesis rather than through
`LeanDag.FairScheduleOn`, which lives in the core's liveness file: the
property layer names no protocol, and the statement is one line. -/
theorem committed_of_correct_block
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator →
      ℕ → ℕ → Prop}
    (hc : Causal R) (hq : Quorate R rel) (hcc : CommitsCandidate R)
    (hlc : LeaderCommits R Live) (S : Slots Validator) {T : Finset Validator}
    (hT : T ⊆ rel.correct) (fair : ∀ n, ∃ k, n ≤ k ∧ S.leader k ∈ T) (R₀ m : ℕ)
    (hR₀m : R₀ ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R₀ ≤ S.slotRound k' ∧
      ∀ (U : R.Universe) (V : R.View U), Live S V T k' (k' + 1) →
        SynchronisedOn R U rel.correct R₀ →
        ∃ L, R.Decided S V k' (some L) ∧
          ∀ b ∈ R.ids U, (R.block U b).creator ∈ rel.correct →
            (R.block U b).round = m →
            b ∈ historyFrom (R.block U) L ∧
              ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
                b ∈ ledgerSetOf R U g n := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded (m + 1)
  obtain ⟨k₁, hk₁⟩ := S.unbounded R₀
  obtain ⟨k', hk', hlead⟩ := fair (max k₀ k₁)
  have hm : m < S.slotRound k' :=
    lt_of_lt_of_le (by omega) (le_trans hk₀ (S.mono (le_trans (le_max_left _ _) hk')))
  have hR : R₀ ≤ S.slotRound k' :=
    le_trans hk₁ (S.mono (le_trans (le_max_right _ _) hk'))
  refine ⟨k', hm, hR, fun U V hlive hs => ?_⟩
  obtain ⟨L, -, hdec, -⟩ := hlc S V T k' (k' + 1) hlive k' le_rfl (Nat.lt_succ_self k') hlead
  refine ⟨L, hdec, fun b hb hbc hbr => ?_⟩
  obtain ⟨-, hLr, hLc⟩ := hcc S U V k' L hdec
  have hmem : b ∈ historyFrom (R.block U) L :=
    mem_history_of_decided_commit hc hq hcc hs hdec (by rw [hLc]; exact hT hlead) hb hbc
      (by omega) (by omega)
  exact ⟨hmem, fun g n hg hn => mem_ledgerSetOf_of_mem_history hc hg hn (hcc.mem hdec) hmem⟩

/-! ## The capstone -/

/-- **CQ7 (the capstone).** Chain quality in one statement, for any rule
with a quorum law. Unconditionally: every commit's flush covers at least
half the reliable validators at every round below it. Post-`R₀`, under a
schedule that keeps returning to reliable leaders: every reliable block
is in the flush of a slot the schedule fixes in advance. -/
theorem chain_quality
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator →
      ℕ → ℕ → Prop}
    (hc : Causal R) (hq : Quorate R rel) (hcc : CommitsCandidate R)
    (hlc : LeaderCommits R Live) (hhalf : 2 * rel.slack ≤ rel.correct.card)
    (S : Slots Validator) {T : Finset Validator} (hT : T ⊆ rel.correct)
    (fair : ∀ n, ∃ k, n ≤ k ∧ S.leader k ∈ T) (R₀ m : ℕ) (hR₀m : R₀ ≤ m) :
    (∀ (U : R.Universe) (V : R.View U) (k : ℕ) (L : BlockId) (δ : ℕ),
        R.Decided S V k (some L) → δ < (R.block U L).round →
        rel.correct.card ≤ 2 * (coveredAt R rel U L δ).card) ∧
    ∃ k', m < S.slotRound k' ∧ R₀ ≤ S.slotRound k' ∧
      ∀ (U : R.Universe) (V : R.View U), Live S V T k' (k' + 1) →
        SynchronisedOn R U rel.correct R₀ →
        ∃ L, R.Decided S V k' (some L) ∧
          ∀ b ∈ R.ids U, (R.block U b).creator ∈ rel.correct →
            (R.block U b).round = m →
            b ∈ historyFrom (R.block U) L ∧
              ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
                b ∈ ledgerSetOf R U g n :=
  ⟨fun _ _ _ _ _ hdec hδ =>
    card_correct_le_two_mul_coveredAt_of_decided hc hq hcc hhalf hdec hδ,
   committed_of_correct_block hc hq hcc hlc S hT fair R₀ m hR₀m⟩

end Decided

end Arcs

end Properties

end LeanDag
