import LeanDag.Properties.Bounded
import LeanDag.Properties.Sustain
import LeanDag.Properties.Deliver
import LeanDag.Properties.Candidate
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

**What becomes generic** lives downstream. `Derived/LeaderCommits.lean`:
`LeaderCommits` at `Support.live`, from Law 3, so everything a schedule
mechanism reads — `decidedBelow_of_run`, chain quality, Barnacle — is
reached with no per-rule precondition. `Arcs/Liveness.lean`: liveness
on any covered DAG from Laws 2 and 3, and liveness across every
`Sustains` from Laws 1 and 3.
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
