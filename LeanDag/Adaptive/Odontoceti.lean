import LeanDag.Adaptive.Mysticeti
import LeanDag.Odontoceti.Liveness
import LeanDag.Odontoceti.Carrier

/-!
# Adaptive leaders under the two-round rule

The Odontoceti mirror of the arc, exhibiting that the adaptive layer is
rule-agnostic: the epoching, the induced instance, the policy and its
clauses are consumed *as found* — `AdaptivePolicy` and `PlacesRuns` are
the very objects of the Mysticeti development, protocol-free — and only
the decision relation is mirrored. `Odontoceti.DecidedWithin` carries
the canonicity clause of the two-round indirect commit through the
bound; its congruence transports the clause in both directions, the
candidate set being schedule-dependent only through `IsLeaderBlock`,
which the two protocols share. Agreement per epoch is
`Properties.Agree` through the embedding, exactly as the three-round
side used the same property; existence consumes O7 and the two-round
descent, with two populated rounds where Mysticeti needs three.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-! The bounded two-round relation is `Odontoceti.DecidedWithin`, the
relation's `AnchoredRule.DecidedWithin` at Odontoceti's data, with its
embedding, bound and congruence proved there. -/

/-- Congruence below the bound, canonicity clause included: the
candidate set reads the schedule only through `IsLeaderBlock`, which
transports in both directions at the decided slot. -/
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : Odontoceti.DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    Odontoceti.DecidedWithin (S := slotsOf hinj a₂) U V B k v :=
  AnchoredRule.decidedWithin_congr_of_slotRound odontocetiLaws trivial (S₁ := slotsOf hinj a₁)
    (S₂ := slotsOf hinj a₂) rfl (fun m hm => by simpa using ha m hm) h

/-- A run closed up to epoch height `E`, two-round rule. -/
structure PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot of a closed epoch is decided inside its window. -/
  closed : ∀ k, epochOf P.W k < E →
    Odontoceti.DecidedWithin (S := slotsOf P.inj assign) U V
      (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, as far as the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U V vdct m

/-- A total run: the adaptive fixpoint, two-round rule. -/
structure AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, Odontoceti.DecidedWithin (S := slotsOf P.inj assign) U V
    (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, everywhere. -/
  coherent : ∀ m, assign m = P.pick U V vdct m

/-- A total run is partial at every height. -/
def AdaptiveRun.toPartial {P : AdaptivePolicy Validator BlockId Payload}
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V) (E : ℕ) :
    PartialRun P U V E where
  assign := R.assign
  vdct := R.vdct
  closed := fun k _ => R.closed k
  coherent := fun m _ => R.coherent m

/-- The master agreement lemma, two-round rule — the Mysticeti induction
verbatim, with O5 where it used M6. -/
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k := by
  suffices main : ∀ e k, epochOf P.W k = e → epochOf P.W k < min E₁ E₂ →
      R₁.vdct k = R₂.vdct k by
    intro k hk; exact main _ k rfl hk
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro k hke hk
    have hassign : ∀ m, m < P.W * (epochOf P.W k + 2) →
        R₁.assign m = R₂.assign m := by
      intro m hm
      have hme : epochOf P.W m < epochOf P.W k + 2 :=
        (epochOf_lt_iff P.W_pos).mpr hm
      rw [R₁.coherent m (by omega), R₂.coherent m (by omega)]
      refine P.adapted U V₁ V₂ R₁.vdct R₂.vdct m (fun j hj => ?_)
      exact ih (epochOf P.W j) (by omega) j rfl (by omega)
    have h₁ := R₁.closed k (by omega)
    have h₂ := R₂.closed k (by omega)
    exact AnchoredRule.DecidedWithin.agree odontocetiLaws trivial (S := slotsOf P.inj R₂.assign)
      (decidedWithin_congr hassign h₁) h₂

/-- **Safety, two-round rule: the adaptive fixpoint is unique** — with
no fairness, synchrony or view hypothesis, exactly as on the
three-round side. -/
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    ∀ k, R₁.vdct k = R₂.vdct k := fun k =>
  partialRun_agree (R₁.toPartial (epochOf P.W k + 1))
    (R₂.toPartial (epochOf P.W k + 1)) k (by omega)

section Existence

variable {P : AdaptivePolicy Validator BlockId Payload}
variable {T : Finset Validator} {c R N : ℕ}

/-! The committed-run descent, bounded, is the relation's
`decidedWithin_below_of_committed_run` at `Odontoceti.exists_least`. -/

/-- One epoch closes, two-round rule, on a view caught up to the
horizon: O7 commits the placed run — two populated rounds where
Mysticeti needs three, its supporters under the horizon so the view
holds them — and the bounded descent clears the epoch below. -/
theorem epoch_closes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N)
    (v : ℕ → Option BlockId) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 2)) + 1 ≤ N) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, Odontoceti.DecidedWithin (S := slotsOf P.inj (fun m => P.pick U V v m)) U
        V (P.W * (E + 2)) k w := by
  obtain ⟨b, hb1, hb2, hbT⟩ := hruns U V v E
  have hWpos := P.W_pos
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B', Odontoceti.DecidedWithin (S := slotsOf P.inj (fun m => P.pick U V v m)) U
        V (b + c - 1 + 1) j (some B') := by
    intro j hj1 hj2
    have hlead : (slotsOf P.inj (fun m => P.pick U V v m)).leader j ∈ T := by
      have := hbT (j - b) (by omega)
      rw [slotsOf_leader]
      have hjb : b + (j - b) = j := by omega
      rwa [hjb] at this
    have hWle : P.W ≤ j := by
      have h1 : P.W * 1 ≤ P.W * (E + 1) := Nat.mul_le_mul_left P.W (by omega)
      omega
    have hRj : R ≤ S.slotRound j := le_trans hRW (S.mono hWle)
    have hround : S.slotRound j + 1 ≤ N := by
      have hj3 : j ≤ P.W * (E + 2) := by omega
      have := S.mono hj3
      omega
    obtain ⟨L, hL, hdc⟩ :=
      directCommit_of_leader_mem (S := slotsOf P.inj (fun m => P.pick U V v m))
        hcard hs hRj
        (hpop _ (by omega) (by omega))
        (hpop _ (by omega) (by omega)) hlead
    exact ⟨L, Odontoceti.DecidedWithin.directCommit
      (S := slotsOf P.inj (fun m => P.pick U V v m)) (by omega) hL
      (directCommitIn_of_coversUpto hdc (hcov.mono hround))⟩
  have hbelow :=
    AnchoredRule.decidedWithin_below_of_committed_run (fun hi h => exists_least hi h) (V := V)
      (S := slotsOf P.inj (fun m => P.pick U V v m))
      (b := b) (n := b + c - 1) (B := b + c - 1 + 1) (by omega) (by omega)
      (fun i hi => hspans b i hi) hrun
  intro k hk
  have hkb : k < b :=
    lt_of_lt_of_le ((epochOf_lt_iff hWpos).mp hk) hb1
  obtain ⟨w, hw⟩ := hbelow k hkb
  exact ⟨w, AnchoredRule.DecidedWithin.mono (S := slotsOf P.inj (fun m => P.pick U V v m))
    hw (by omega)⟩

/-- Partial runs exist at every height, two-round rule, on a view
caught up to the horizon. -/
theorem exists_partialRun (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 1)) + 1 ≤ N) :
    Nonempty (PartialRun P U V E) := by
  classical
  revert hN
  induction E with
  | zero =>
      intro hN
      exact ⟨{ assign := fun m => P.pick U V (fun _ => none) m
               vdct := fun _ => none
               closed := fun k hk => absurd hk (by omega)
               coherent := fun _ _ => rfl }⟩
  | succ E ih =>
      intro hN
      have hNprev : S.slotRound (P.W * (E + 1)) + 1 ≤ N := by
        have hmul : P.W * (E + 1) ≤ P.W * (E + 1 + 1) :=
          Nat.mul_le_mul_left P.W (by omega)
        have := S.mono hmul
        omega
      obtain ⟨R₀⟩ := ih hNprev
      have hclose := epoch_closes hT hcard hc hruns hspans hs hRW hpop
        V hcov R₀.vdct E hN
      set v' : ℕ → Option BlockId := fun k =>
        if h : epochOf P.W k = E then (hclose k (by omega)).choose
        else R₀.vdct k with hv'
      have hagree : ∀ j, epochOf P.W j < E → v' j = R₀.vdct j := by
        intro j hj
        simp only [hv', dif_neg (by omega : ¬ epochOf P.W j = E)]
      have hsched : ∀ m, m < P.W * (E + 2) →
          P.pick U V R₀.vdct m = P.pick U V v' m := by
        intro m hm
        refine P.adapted U V V R₀.vdct v' m (fun j hj => ?_)
        have hjE : epochOf P.W j < E := by
          have := (epochOf_lt_iff P.W_pos).mpr hm
          omega
        exact (hagree j hjE).symm
      refine ⟨{ assign := fun m => P.pick U V v' m
                vdct := v'
                closed := ?_
                coherent := fun _ _ => rfl }⟩
      intro k hk
      by_cases hkE : epochOf P.W k = E
      · have hspec := (hclose k (by omega)).choose_spec
        have : v' k = (hclose k (by omega)).choose := by
          simp only [hv', dif_pos hkE]
        rw [this, hkE]
        exact decidedWithin_congr (fun m hm => hsched m hm) hspec
      · have hkE' : epochOf P.W k < E := by omega
        have hold := R₀.closed k hkE'
        have hsched' : ∀ m, m < P.W * (epochOf P.W k + 2) →
            R₀.assign m = P.pick U V v' m := by
          intro m hm
          have hmE : epochOf P.W m < epochOf P.W k + 2 :=
            (epochOf_lt_iff P.W_pos).mpr hm
          rw [R₀.coherent m (by omega)]
          refine P.adapted U V V R₀.vdct v' m (fun j hj => ?_)
          exact (hagree j (by omega)).symm
        have := decidedWithin_congr hsched' hold
        rw [hagree k hkE']
        exact this

/-- **AL7: adaptive Odontoceti is safe and live.** The fixpoint exists
on every view caught up to every horizon — glued along the diagonal
exactly as on the three-round side — and by
`Odontoceti.adaptiveRun_agree` it is unique. -/
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r)
    (V : View Validator BlockId Payload U) (hcov : ∀ N, V.CoversUpto N) :
    Nonempty (AdaptiveRun P U V) := by
  classical
  have hex : ∀ E, Nonempty (PartialRun P U V E) := fun E =>
    exists_partialRun hT hcard hc hruns hspans hs hRW
      (N := S.slotRound (P.W * (E + 1)) + 1) (fun r _ _ => PopulatedOn.mono hT (hpop r))
      V (hcov _) E (le_refl _)
  set Rs : ∀ E, PartialRun P U V E :=
    fun E => (hex E).some with hRs
  set vd : ℕ → Option BlockId := fun k => (Rs (epochOf P.W k + 1)).vdct k with hvd
  have hdiag : ∀ E j, epochOf P.W j < E → (Rs E).vdct j = vd j := by
    intro E j hj
    exact partialRun_agree (Rs E) (Rs (epochOf P.W j + 1)) j (by omega)
  refine ⟨{ assign := fun m => P.pick U V vd m
            vdct := vd
            closed := ?_
            coherent := fun _ => rfl }⟩
  intro k
  have hclosed := (Rs (epochOf P.W k + 1)).closed k (by omega)
  refine decidedWithin_congr (fun m hm => ?_) hclosed
  have hmE : epochOf P.W m < epochOf P.W k + 2 := (epochOf_lt_iff P.W_pos).mpr hm
  rw [(Rs (epochOf P.W k + 1)).coherent m (by omega)]
  refine P.adapted U V V (Rs (epochOf P.W k + 1)).vdct vd m (fun j hj => ?_)
  exact hdiag _ j (by omega)

end Existence

end Odontoceti

end LeanDag
