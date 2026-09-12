import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Helpers.Bounds
import LeanDag.Barnacle.Helpers.Schedule
/-!
# Agreement helpers

Not part of the audit surface. The induction behind BN3, at any
`Boundary` and so for both mechanisms at once: configuration data
agreeing at `k` forces the anchors of `k` to agree — the lesser of two
anchors would be a committed slot past the threshold below the other,
against `anchor_least` — and with them the boundary, the verdicts the
rule is handed, and the next configuration.

The boundary enters in one place. `start_succ_agree` is a `congrArg`: the
next start is the boundary's own function of data the two runs already
agree on. Where a mechanism puts its boundary is therefore irrelevant to
safety, which is the substance of `adaptive-leaders.md` D19.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params} {B : Boundary Validator}
variable {upd : UpdateRule R} {C₀ : Config Validator}
variable {U : R.Universe} {V₁ V₂ : R.View U} {K₁ K₂ : ℕ}

/-- Configuration `k` agrees between two runs. -/
def ConfigAgree (R₁ : Run R P B upd C₀ U V₁ K₁)
    (R₂ : Run R P B upd C₀ U V₂ K₂) (k : ℕ) : Prop :=
  R₁.start k = R₂.start k ∧ R₁.cfg k = R₂.cfg k ∧ R₁.backoff k = R₂.backoff k

/-- Verdicts of a slot both runs have decided agree — the base rule's
agreement law, once the two schedules are seen to be one. The range
hypotheses are per run, since each decides as far as its own anchor. -/
theorem vdct_agree (hR : Properties.Agree R.toDagRule) (R₁ : Run R P B upd C₀ U V₁ K₁)
    (R₂ : Run R P B upd C₀ U V₂ K₂) {k : ℕ} (hc : R₁.cfg k = R₂.cfg k)
    (hk₁ : k < K₁) (hk₂ : k < K₂) {κ : ℕ}
    (h₁ : R₁.start k < (R₁.cfg k).roundOf κ)
    (h₁' : (R₁.cfg k).roundOf κ ≤ (R₁.cfg k).roundOf (R₁.anchor k))
    (h₂ : R₂.start k < (R₂.cfg k).roundOf κ)
    (h₂' : (R₂.cfg k).roundOf κ ≤ (R₂.cfg k).roundOf (R₂.anchor k)) :
    R₁.vdct k κ = R₂.vdct k κ := by
  have d₁ := R₁.closed k hk₁ κ h₁ h₁'
  have d₂ := R₂.closed k hk₂ κ h₂ h₂'
  rw [show (R₁.cfg k).sched = (R₂.cfg k).sched by rw [hc]] at d₁
  exact hR _ _ _ κ _ _ d₁ d₂

/-- The anchors agree: the lesser of two anchors is, in the other run, a
committed slot past the threshold below its anchor. -/
theorem anchor_agree (hR : Properties.Agree R.toDagRule) (R₁ : Run R P B upd C₀ U V₁ K₁)
    (R₂ : Run R P B upd C₀ U V₂ K₂) {k : ℕ} (h : ConfigAgree R₁ R₂ k)
    (hk₁ : k < K₁) (hk₂ : k < K₂) : R₁.anchor k = R₂.anchor k := by
  obtain ⟨hs, hc, _⟩ := h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨⟨A, hA⟩, hround⟩ := R₁.anchor_commits k hk₁
    have hr₂ : R₂.start k + (R₂.cfg k).interval < (R₂.cfg k).roundOf (R₁.anchor k) := by
      rw [← hs, ← hc]; exact hround
    have hnone := R₂.anchor_least k hk₂ (R₁.anchor k) hlt hr₂
    have hv := vdct_agree hR R₁ R₂ hc hk₁ hk₂ (κ := R₁.anchor k)
      (by omega) le_rfl (by omega) ((R₂.cfg k).roundOf_mono hlt.le)
    rw [hA, hnone] at hv
    exact Option.some_ne_none A hv
  · obtain ⟨⟨A, hA⟩, hround⟩ := R₂.anchor_commits k hk₂
    have hr₁ : R₁.start k + (R₁.cfg k).interval < (R₁.cfg k).roundOf (R₂.anchor k) := by
      rw [hs, hc]; exact hround
    have hnone := R₁.anchor_least k hk₁ (R₂.anchor k) hgt hr₁
    have hv := vdct_agree hR R₁ R₂ hc hk₁ hk₂ (κ := R₂.anchor k)
      (by omega) ((R₁.cfg k).roundOf_mono hgt.le) (by omega) le_rfl
    rw [hA, hnone] at hv
    exact Option.some_ne_none A hv.symm

/-- **The boundaries agree**, wherever the mechanism puts them: the next
start is the boundary's function of the configuration, the current start
and the anchor, and the two runs agree on all three. -/
theorem start_succ_agree (hR : Properties.Agree R.toDagRule) (R₁ : Run R P B upd C₀ U V₁ K₁)
    (R₂ : Run R P B upd C₀ U V₂ K₂) {k : ℕ} (h : ConfigAgree R₁ R₂ k)
    (hk₁ : k < K₁) (hk₂ : k < K₂) : R₁.start (k + 1) = R₂.start (k + 1) := by
  have ha := anchor_agree hR R₁ R₂ h hk₁ hk₂
  obtain ⟨hs, hc, _⟩ := h
  rw [R₁.start_succ k hk₁, R₂.start_succ k hk₂, hs, hc, ha]

/-- **The range's verdicts agree as a function.** What the runs hand the
update rule is one object, so a rule reading the committed leaders of the
range it just output reads agreed data and needs no further hypothesis.
Outside the range both are `none` by construction, which is what makes
the equality total: a run constrains its verdicts only inside the span it
decided. -/
theorem spanVdct_agree (hR : Properties.Agree R.toDagRule)
    (R₁ : Run R P B upd C₀ U V₁ K₁) (R₂ : Run R P B upd C₀ U V₂ K₂)
    {k : ℕ} (h : ConfigAgree R₁ R₂ k) (hk₁ : k < K₁) (hk₂ : k < K₂) :
    spanVdct (R₁.cfg k) (R₁.start k) (R₁.start (k + 1)) (R₁.vdct k)
      = spanVdct (R₂.cfg k) (R₂.start k) (R₂.start (k + 1)) (R₂.vdct k) := by
  have ha := anchor_agree hR R₁ R₂ h hk₁ hk₂
  have hs' := start_succ_agree hR R₁ R₂ h hk₁ hk₂
  obtain ⟨hs, hc, _⟩ := h
  funext κ
  simp only [spanVdct, hs, hc, hs']
  split
  · rename_i hk
    have h₂ := boundary_le_anchor R₂ hk₂
    refine vdct_agree hR R₁ R₂ hc hk₁ hk₂ ?_ ?_ hk.1 (by omega)
    · rw [hs, hc]; exact hk.1
    · rw [hc, ha]; omega
  · rfl

/-- Agreement at `k` carries to `k + 1`: the anchors agree, so the anchor
blocks and the range's verdicts agree, so one update of one state yields
one configuration. -/
theorem configAgree_succ (hR : Properties.Agree R.toDagRule) (hanc : Anchored R upd)
    (R₁ : Run R P B upd C₀ U V₁ K₁) (R₂ : Run R P B upd C₀ U V₂ K₂)
    {k : ℕ} (h : ConfigAgree R₁ R₂ k) (hk₁ : k < K₁) (hk₂ : k < K₂) :
    ConfigAgree R₁ R₂ (k + 1) := by
  have ha := anchor_agree hR R₁ R₂ h hk₁ hk₂
  have hs' := start_succ_agree hR R₁ R₂ h hk₁ hk₂
  have hsp := spanVdct_agree hR R₁ R₂ h hk₁ hk₂
  obtain ⟨hs, hc, hb⟩ := h
  obtain ⟨⟨A, hA⟩, hround⟩ := R₁.anchor_commits k hk₁
  have hA₂ : R₂.vdct k (R₂.anchor k) = some A := by
    rw [← ha, ← vdct_agree hR R₁ R₂ hc hk₁ hk₂ (κ := R₁.anchor k)
      (by omega) le_rfl (by rw [← hs, ← hc]; omega) (by rw [← ha, ← hc])]
    exact hA
  have e₁ := R₁.update k hk₁ A hA
  have e₂ := R₂.update k hk₂ A hA₂
  rw [hsp] at e₁
  rw [hc, hb] at e₁
  have e := e₁.trans ((hanc U V₁ V₂ (R₂.cfg k) (R₂.backoff k) _ A).trans e₂.symm)
  exact ⟨hs', (Prod.mk.inj e).1, (Prod.mk.inj e).2⟩

/-- **Configurations agree** up to the lower height, by induction. -/
theorem configAgree (hR : Properties.Agree R.toDagRule) (hanc : Anchored R upd)
    (R₁ : Run R P B upd C₀ U V₁ K₁) (R₂ : Run R P B upd C₀ U V₂ K₂) :
    ∀ k, k ≤ min K₁ K₂ → ConfigAgree R₁ R₂ k
  | 0, _ => ⟨by rw [R₁.init.1, R₂.init.1], by rw [R₁.init.2.1, R₂.init.2.1],
      by rw [R₁.init.2.2, R₂.init.2.2]⟩
  | k + 1, h => configAgree_succ hR hanc R₁ R₂ (configAgree hR hanc R₁ R₂ k (by omega))
      (by omega) (by omega)

end Barnacle

end LeanDag
