import LeanDag.Properties.Support
import LeanDag.Properties.Derived.LeaderCommits

/-!
# Liveness, from a support: on a covered DAG, and across a mechanism

`docs/target-properties.md` §11.7. Three theorems, each proved once for
any rule with a `Support` and its laws, none of them per rule and none
per mechanism.

* `exists_decided_of_coverage` — a reliably-led slot commits on any
  DAG the reliable set has covered and populated. Laws 2 and 3
  composed; no precondition of the rule's own appears.
* `certifiesAt_of_rebased` — certification survives every
  `RebasedAbove`, from Law 1.
* `exists_decided_of_sustains` — a commit survives any `Sustains` at the
  same schedule: the candidates are the same blocks, certification and
  production carry over, and Law 3 fires in the transformed universe.
  The liveness half of what `Arcs/GC.lean` and `Arcs/SafeSkip.lean`
  give for safety.
-/

namespace LeanDag

namespace Properties

namespace Support

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable (sp : Support R)

/-- **A reliably-led slot commits on a covered, populated DAG** — for any
rule with Laws 2 and 3. -/
theorem exists_decided_of_coverage {rel : Reliability Validator}
    (hcov : sp.OfCoverage rel) (hlc : sp.Commits rel)
    {U : R.Universe} {Rnd N : ℕ} (hs : SynchronisedOn R U rel.correct Rnd)
    (hpop : ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn R U rel.correct r)
    (S : Slots Validator) (V : R.View U) (k : ℕ) (hV : CoversUpto R V N)
    (hRnd : Rnd ≤ S.slotRound k) (hN : S.slotRound k + sp.wave ≤ N)
    (hlead : S.leader k ∈ rel.correct) :
    ∃ L, DecidedBelow R S (k + 1) V k (some L) := by
  refine hlc S V rel.correct k rel.isQuorum_correct
    (fun n h1 h2 => hpop n (by omega) (by omega)) ?_ (hV.mono hN) hlead
  intro L hL v hv c hc hcc hcr
  exact hcov U rel.correct rel.isQuorum_correct _ L
    (fun n h1 h2 => hpop n (by omega) (by omega))
    (coversToward_of_synchronisedOn hs hRnd) hL.1 hL.2.1 (by rw [hL.2.2]; exact hlead)
    c hc (by rw [hcc]; exact hv) hcr

/-- **Certification survives every mechanism, from Law 1.** -/
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

/-- **A commit survives a sustaining mechanism**, at the same schedule. -/
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

end Properties

end LeanDag
