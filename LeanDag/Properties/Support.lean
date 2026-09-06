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

**Certification, not coverage.** The precondition `Support.live` asks
that every candidate of a reliably-led slot be certified by the reliable
set a wave up, and nothing about how the certifiers came to reference
what they reference. A reactive execution supplies that from its wait
clauses; a timed one supplies it from coverage, through
`Timed.live_of_coverage` (`LeanDag/Timed/Coverage.lean`). No synchrony
predicate is stated under `Properties/`, and `scripts/check-arc-holes.py`
keeps it that way — see that file for why.

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

/-- **Law 2 — certification commits.** A slot whose every candidate a
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

end Properties

end LeanDag
