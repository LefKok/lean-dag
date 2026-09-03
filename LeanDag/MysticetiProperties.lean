import LeanDag.Properties.Sustain
import LeanDag.Liveness

/-!
# The core rule as a carrier, and what it makes of a sustaining mechanism

The core protocol is a single file, `Mysticeti.lean`, rather than a
directory, so its properties-arc material lives here rather than in a
`Mysticeti/Properties/` pair. Two things:

* `mysticetiRule`, the core rule as a `Properties.DagRule` — stated here
  rather than taken from `Barnacle.mysticeti.toDagRule` so that the core's
  conformance depends on no mechanism.

* **What a sustaining mechanism gives the core's liveness.** `Sustains`
  promises that above a settling round old blocks keep their authors,
  references and (shifted) rounds; `certifiesAt_of_sustains` turns that
  into transport of the core's own certificate layer, and
  `directCommit_of_sustains` feeds the result to
  `directCommit_of_certifiesAt` — the lemma the reactive commit runs
  through. So any mechanism that sustains preserves the reactive
  discipline's commit on the transformed DAG, **with no pacing structure
  transported**: what the reactive exit produces is a certificate like
  any other, and certificates are made of references.

This is the consumer test `Sustains` owed. The first statement of that
obligation transported votes by name and could not be fed to this lemma;
the restatement over blocks can.
-/

namespace LeanDag

namespace MysticetiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [Faults Validator]

/-- **The core rule as a carrier.** -/
def mysticetiRule : DagRule Validator BlockId Payload where
  Universe := BlockUniverse Validator BlockId Payload
  View := fun U => View Validator BlockId Payload U
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  Decided := fun S _ V k v => Decided (S := S) _ V k v

variable {U U' : BlockUniverse Validator BlockId Payload} {G R₀ : ℕ}

/-- The carrier's production predicate and the core's are the same
statement with the conjuncts in the other order — the one per-protocol
agreement `Sustains` asks for, here a reordering rather than `rfl`. -/
theorem populatedOn_ofCore {T : Finset Validator} {r : ℕ}
    (h : LeanDag.PopulatedOn U T r) : Properties.PopulatedOn mysticetiRule U T r :=
  fun v hv => let ⟨b, hb, hc, hr⟩ := h v hv; ⟨b, hb, hr, hc⟩

theorem populatedOn_toCore {T : Finset Validator} {r : ℕ}
    (h : Properties.PopulatedOn mysticetiRule U T r) : LeanDag.PopulatedOn U T r :=
  fun v hv => let ⟨b, hb, hr, hc⟩ := h v hv; ⟨b, hb, hc, hr⟩

/-- The votes an old decision-round block counts are the votes it
counted: its references are unchanged, and so are theirs. -/
theorem votesIn_of_sustains (h : Sustains mysticetiRule U U' G R₀) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : R₀ + 1 < (U.block C).round) :
    votesIn U' C L = votesIn U C L := by
  unfold votesIn
  have hrefs : (U'.block C).refs = (U.block C).refs :=
    h.refs C hC (by change R₀ < (U.block C).round; omega)
  rw [hrefs]
  refine Finset.filter_congr fun q hq => ?_
  have hqU : q ∈ U.ids := U.complete C hC q hq
  have hqr := U.round_of_mem_refs hC hq
  have : (U'.block q).refs = (U.block q).refs :=
    h.refs q hqU (by change R₀ < (U.block q).round; omega)
  rw [this]

/-- **The core's certificate predicate transports.** -/
theorem certifies_of_sustains (h : Sustains mysticetiRule U U' G R₀) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : R₀ + 1 < (U.block C).round) :
    Certifies U' C L ↔ Certifies U C L := by
  unfold Certifies
  rw [votesIn_of_sustains h hC hCr]
  have : creatorsOf U'.block (votesIn U C L) = creatorsOf U.block (votesIn U C L) := by
    refine Finset.image_congr fun q hq => ?_
    have hqref := (Finset.mem_filter.mp hq).1
    have hqU : q ∈ U.ids := U.complete C hC q hqref
    have hqr := U.round_of_mem_refs hC hqref
    exact h.creator q hqU (by change R₀ ≤ (U.block q).round; omega)
  rw [this]

/-- **Certification at a slot survives a sustaining mechanism**, above
its settling round. -/
theorem certifiesAt_of_sustains (h : Sustains mysticetiRule U U' G R₀)
    {T : Finset Validator} {r : ℕ} {L : BlockId} (hr : R₀ ≤ r) (hG : G ≤ r)
    (hc : CertifiesAt U T r L) : CertifiesAt U' T (r - G) L := by
  intro v hv c hc' hcc hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc' (by change R₀ ≤ (U'.block c).round + G; omega)
  have hround' : (U'.block c).round + G = (U.block c).round := hround
  have hUr : (U.block c).round = r + 2 := by omega
  have hcreator : (U'.block c).creator = (U.block c).creator :=
    h.creator c hcU (by change R₀ ≤ (U.block c).round; omega)
  have hcc' : (U.block c).creator = v := by rw [← hcreator]; exact hcc
  exact (certifies_of_sustains h hcU (by omega)).mpr (hc v hv c hcU hcc' hUr)

/-- **The reactive commit survives any sustaining mechanism.** The
hypotheses are exactly what `Reactive/Mysticeti.directCommit` establishes
on the original DAG — certification by `cert_or_wait`, and production —
and the conclusion is the commit on the transformed one. -/
theorem directCommit_of_sustains (h : Sustains mysticetiRule U U' G R₀)
    {T : Finset Validator} {r : ℕ} {L : BlockId} (hr : R₀ ≤ r) (hG : G ≤ r)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommit U' L (r - G) :=
  directCommit_of_certifiesAt hcard
    (by
      have := h.populatedOn_of (T := T) (r := r + 2) (by omega) (by omega)
        (populatedOn_ofCore hpop)
      have e : r + 2 - G = r - G + 2 := by omega
      rw [e] at this
      exact populatedOn_toCore this)
    (certifiesAt_of_sustains h hr hG hc)

end MysticetiProperties

end LeanDag
