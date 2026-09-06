import LeanDag.Properties.Commit
import LeanDag.Properties.Sustain
import LeanDag.Properties.Deliver
import LeanDag.Properties.Candidate
import LeanDag.Properties.Live
import LeanDag.Properties.Band
import LeanDag.Density

/-!
# Support: what a rule's commit counts

`docs/target-properties.md` §11.7. Safety is generic because `Banded`
names the one thing every decision relation reads — a bounded window of
references. Liveness was not, because nothing named the one thing every
*commit* counts. `Support` names it: the rule's per-block certification
relation and the wavelength at which its certifiers sit.

It is a **parameter structure**, not a carrier field, for the reason
`Live` and `Elig` are parameters: a rule may have more than one — a
fast-path shape and a slow-path shape — and each earns its own liveness
bound. What stops a parameter from being chosen vacuously is the pair of
laws that consume it. `OfCoverage` is the lower bound: coverage directed
at a candidate certifies it, so a `Certifies` nothing satisfies is
inadmissible. `Commits` is the upper bound: certification by a quorum
produces a verdict, so a `Certifies` everything satisfies is
inadmissible unless the rule commits everything. Between them, the
relation is what the rule counts, whichever end the author chose to put
the work at. `Local` is the third law, and it is `Banded` for the
support relation: certification reads a bounded window above the
candidate, so any `RebasedAbove` above that window preserves it.

**Why `CoversToward` rather than `SynchronisedOn`.** Full coverage says
every reliable block references every reliable block one round below.
A reactive execution does not have it and is not meant to: a reactive
builder omits whatever had not arrived when its exit fired. What it does
have is coverage *toward the candidate* — every reliable block in the
window references every reliable block below it that reaches the
candidate — because that is exactly what its wait clauses guarantee.
`CoversToward` is that restriction; full coverage implies it in one
line; and it is the weakest antecedent under which every rule here
certifies, which is what makes the three theorems at the end generic.

**What becomes generic.** `exists_decided_of_coverage`: a rule with the
laws commits a reliably-led slot on any covered, populated DAG, no
per-rule `LiveReachable` needed. `certifiesAt_of_rebased`: certification
survives every mechanism, once. `Support.leaderCommits`: the rule has
`LeaderCommits` at `Support.live`, so everything downstream of that
property — `decidedBelow_of_run`, chain quality, Barnacle — is reached
with no per-rule liveness precondition at all.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A rule's support shape**: how far above a candidate its certifiers
sit, and what it means for one of them to certify it. -/
structure Support (R : DagRule Validator BlockId Payload) where
  /-- The wavelength: certifiers sit `wave` rounds above the candidate. -/
  wave : ℕ
  /-- `Certifies U c L`: block `c` certifies candidate `L`. -/
  Certifies : R.Universe → BlockId → BlockId → Prop

namespace Support

variable (sp : Support R)

/-- **The reliable set certifies `L` from round `r`**: every `T`-block a
wave above `r` certifies it. -/
def certifiesAt (U : R.Universe) (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c, c ∈ R.ids U → (R.block U c).creator = v →
    (R.block U c).round = r + sp.wave → sp.Certifies U c L

end Support

/-- **Coverage toward a candidate** over a window: every `T`-block at
each level of the window references every `T`-block one level below it
that reaches the candidate. Full coverage restricted to the candidate's
support, and what a reactive wait clause delivers. -/
def CoversToward (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r wave : ℕ) (L : BlockId) : Prop :=
  ∀ n, r ≤ n → n < r + wave →
    ∀ b, b ∈ R.ids U → (R.block U b).creator ∈ T → (R.block U b).round = n + 1 →
    ∀ a, a ∈ R.ids U → (R.block U a).creator ∈ T → (R.block U a).round = n →
      ReachesFrom (R.block U) a L → a ∈ (R.block U b).refs

/-- Full coverage from `Rnd` is coverage toward anything, over any window
at or above `Rnd`. -/
theorem coversToward_of_synchronisedOn {U : R.Universe} {T : Finset Validator}
    {Rnd r wave : ℕ} {L : BlockId} (hs : SynchronisedOn R U T Rnd) (hr : Rnd ≤ r) :
    CoversToward R U T r wave L :=
  fun n hn _ b hb hbc hbr a ha hac har _ => hs n (by omega) b hb hbr hbc a ha har hac

/-- **A `RebasedAbove` is a band from its settling round up to any
ceiling**, at offsets `0` and `G`. What lets a rule discharge `Local`
with the band lemmas it already has for `Banded`. -/
theorem agreeBand_of_rebasedAbove {U U' : R.Universe} {G R₀ : ℕ}
    (h : RebasedAbove R U U' G R₀) (hi lo : ℕ) (hlo : R₀ ≤ lo) :
    AgreeBand R U U' lo hi 0 G where
  mem := fun b hb h1 _ => ((h.mem b).mp ⟨hb, by omega⟩).1
  block := fun b hb hor => by
    have hR : R₀ ≤ (R.block U b).round := by
      rcases hor with ⟨h1, _⟩ | ⟨hb', h1, _⟩
      · omega
      · have := (h.of_mem' hb' (by omega)).2; omega
    exact ⟨by have := h.round b hb hR; omega, h.creator b hb hR⟩
  refs := fun b hb h1 _ => h.refs b hb (by omega)

namespace Support

variable (sp : Support R)

/-! ## The three laws -/

/-- **Law 1 — certification is local.** `Banded` for the support relation:
across any `RebasedAbove`, a certifier whose whole window sits at or
above the settling round certifies the same candidates. -/
def Local : Prop :=
  ∀ {U U' : R.Universe} {G R₀ : ℕ}, RebasedAbove R U U' G R₀ →
    ∀ c L, c ∈ R.ids U → R₀ + sp.wave ≤ (R.block U c).round →
      L ∈ R.ids U → (R.block U L).round + sp.wave = (R.block U c).round →
      (sp.Certifies U' c L ↔ sp.Certifies U c L)

/-- **Law 2 — coverage certifies.** On a window the reliable set has
populated, with coverage toward a reliable candidate at its base, every
reliable block at the top certifies it. The lower bound on `Certifies`. -/
def OfCoverage (rel : Reliability Validator) : Prop :=
  ∀ (U : R.Universe) (T : Finset Validator), rel.IsQuorum T →
    ∀ (r : ℕ) (L : BlockId),
    (∀ n, r ≤ n → n ≤ r + sp.wave → PopulatedOn R U T n) →
    CoversToward R U T r sp.wave L →
    L ∈ R.ids U → (R.block U L).round = r → (R.block U L).creator ∈ T →
    ∀ c, c ∈ R.ids U → (R.block U c).creator ∈ T → (R.block U c).round = r + sp.wave →
      sp.Certifies U c L

/-- **Law 3 — certification commits.** A slot whose every candidate a
reliable quorum certifies, on a populated window a view is caught up
to, is committed within a bound one above it when a quorum member leads
it. `LeaderCommits` with the precondition made explicit; the upper
bound on `Certifies`. -/
def Commits (rel : Reliability Validator) : Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (T : Finset Validator) (k : ℕ),
    rel.IsQuorum T →
    (∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + sp.wave → PopulatedOn R U T n) →
    (∀ L, R.IsCandidate S U k L → sp.certifiesAt U T (S.slotRound k) L) →
    CoversUpto R V (S.slotRound k + sp.wave) →
    S.leader k ∈ T →
    ∃ L, DecidedBelow R S (k + 1) V k (some L)

/-! ## What follows, once -/

/-- **The liveness precondition, in support terms.** A quorum, a horizon
the view is caught up to with the window a wave under it, and at every
quorum-led slot of the window production and certification. The `Live`
every rule with a `Support` has, and the one `LeaderCommits` is proved
against. -/
def live (rel : Reliability Validator) (S : Slots Validator) {U : R.Universe}
    (V : R.View U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  rel.IsQuorum T ∧
    ∃ N, CoversUpto R V N ∧ (∀ k, k < K → S.slotRound k + sp.wave ≤ N) ∧
      ∀ k, lo ≤ k → k < K → S.leader k ∈ T →
        (∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + sp.wave → PopulatedOn R U T n) ∧
        ∀ L, R.IsCandidate S U k L → sp.certifiesAt U T (S.slotRound k) L

/-- **`LeaderCommits`, from Law 3.** -/
theorem leaderCommits {rel : Reliability Validator} (hlc : sp.Commits rel) :
    LeaderCommits R (fun S {U} V T lo K => sp.live rel S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hq, N, hcov, hN, hslot⟩ := hlive
  obtain ⟨hpop, hcert⟩ := hslot k hlo hK hlead
  exact hlc S V T k hq hpop hcert (hcov.mono (hN k hK)) hlead

/-- **The precondition is reachable, from Law 2.** Coverage is coverage
toward every candidate, so every candidate of a reliably-led slot is
certified. No per-rule argument. -/
theorem liveReachable {rel : Reliability Validator} (hcov : sp.OfCoverage rel) :
    LiveReachable R rel sp.wave (fun S {U} V T lo K => sp.live rel S (U := U) V T lo K) := by
  intro U Rnd N hs hpop S V k hV hRnd hN
  refine ⟨rel.isQuorum_correct, N, hV, ?_, ?_⟩
  · intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    omega
  · intro j hlo hj hlead
    have hjk : j = k := by omega
    subst hjk
    refine ⟨fun n h1 h2 => hpop n (by omega) (by omega), ?_⟩
    intro L hL v hv c hc hcc hcr
    exact hcov U rel.correct rel.isQuorum_correct _ L
      (fun n h1 h2 => hpop n (by omega) (by omega))
      (coversToward_of_synchronisedOn hs hRnd) hL.1 hL.2.1 (by rw [hL.2.2]; exact hlead)
      c hc (by rw [hcc]; exact hv) hcr

/-- **A reliably-led slot commits on a covered, populated DAG** — for any
rule with Laws 2 and 3, with no precondition of the rule's own in
sight. -/
theorem exists_decided_of_coverage {rel : Reliability Validator}
    (hcov : sp.OfCoverage rel) (hlc : sp.Commits rel)
    {U : R.Universe} {Rnd N : ℕ} (hs : SynchronisedOn R U rel.correct Rnd)
    (hpop : ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn R U rel.correct r)
    (S : Slots Validator) (V : R.View U) (k : ℕ) (hV : CoversUpto R V N)
    (hRnd : Rnd ≤ S.slotRound k) (hN : S.slotRound k + sp.wave ≤ N)
    (hlead : S.leader k ∈ rel.correct) :
    ∃ L, DecidedBelow R S (k + 1) V k (some L) :=
  exists_decided_of_reachable (sp.leaderCommits hlc) (sp.liveReachable hcov) hs hpop S V k
    hV hRnd hN hlead

/-- **Certification survives every mechanism, from Law 1.** The
certifiers a wave above `r` sit above the settling round with their
whole window, so each still certifies in the transformed universe, at
the rebased round. -/
theorem certifiesAt_of_rebased (hloc : sp.Local) {U U' : R.Universe} {G R₀ : ℕ}
    (h : RebasedAbove R U U' G R₀) {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hL : L ∈ R.ids U) (hLr : (R.block U L).round = r)
    (hc : sp.certifiesAt U T r L) :
    sp.certifiesAt U' T (r - G) L := by
  intro v hv c hc' hcc hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc' (by omega)
  have hcrU : (R.block U c).round = r + sp.wave := by omega
  have hccU : (R.block U c).creator = v := by
    rw [← h.creator c hcU (by omega)]; exact hcc
  exact (hloc h c L hcU (by omega) hL (by omega)).mpr (hc v hv c hcU hccU hcrU)

/-- **A commit survives a sustaining mechanism**, at the same schedule:
the candidates are the same blocks, their certification carries over,
and production carries over, so Law 3 fires in the transformed universe
on any view of it caught up far enough. -/
theorem exists_decided_of_sustains {rel : Reliability Validator}
    (hloc : sp.Local) (hlc : sp.Commits rel)
    {U U' : R.Universe} {R₀ : ℕ} (h : Sustains R U U' 0 R₀)
    (S : Slots Validator) (V' : R.View U') {T : Finset Validator} (k : ℕ) (hq : rel.IsQuorum T)
    (hR₀ : R₀ ≤ S.slotRound k)
    (hpop : ∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + sp.wave → PopulatedOn R U T n)
    (hcert : ∀ L, R.IsCandidate S U k L → sp.certifiesAt U T (S.slotRound k) L)
    (hV' : CoversUpto R V' (S.slotRound k + sp.wave)) (hlead : S.leader k ∈ T) :
    ∃ L, DecidedBelow R S (k + 1) V' k (some L) := by
  refine hlc S V' T k hq ?_ ?_ hV' hlead
  · intro n h1 h2
    have := h.populatedOn_of (T := T) (r := n) (by omega) (Nat.zero_le _) (hpop n h1 h2)
    rwa [Nat.sub_zero] at this
  · rintro L ⟨hL', hLr', hLc'⟩
    obtain ⟨hLU, hround⟩ := h.of_mem' hL' (by omega)
    have hLr : (R.block U L).round = S.slotRound k := by omega
    have hLc : (R.block U L).creator = S.leader k := by
      rw [← h.creator L hLU (by omega)]; exact hLc'
    have := sp.certifiesAt_of_rebased hloc h (T := T) (r := S.slotRound k) hR₀ (Nat.zero_le _)
      hLU hLr (hcert L ⟨hLU, hLr, hLc⟩)
    rwa [Nat.sub_zero] at this

end Support

/-! ## The one-round shape, once

Odontoceti, Nemo and Hybrid commit when a quorum of the round above
references the candidate: certifier and voter are the same block, and
certifying is referencing. Their support is one structure, and two of
its three laws are facts about references alone, so they are proved
here and each rule owes only `Commits`. -/

/-- **Vote support**: wavelength one, certification is reference. -/
def voteSupport (R : DagRule Validator BlockId Payload) : Support R where
  wave := 1
  Certifies := fun U c L => L ∈ (R.block U c).refs

/-- **Law 1 for vote support.** A block strictly above the settling
round keeps its references. -/
theorem voteSupport_local : (voteSupport R).Local := by
  intro U U' G R₀ h c L hc hcr _ _
  change R₀ + 1 ≤ (R.block U c).round at hcr
  change L ∈ (R.block U' c).refs ↔ L ∈ (R.block U c).refs
  rw [h.refs c hc (by omega)]

/-- **Law 2 for vote support.** Coverage toward the candidate at its own
round is the vote. -/
theorem voteSupport_ofCoverage (rel : Reliability Validator) :
    (voteSupport R).OfCoverage rel := by
  intro U T _ r L _ hct hL hLr hLc c hc hcc hcr
  change (R.block U c).round = r + 1 at hcr
  exact hct r le_rfl (by change r < r + 1; omega) c hc hcc hcr L hL hLc hLr
    Relation.ReflTransGen.refl

end Properties

end LeanDag
