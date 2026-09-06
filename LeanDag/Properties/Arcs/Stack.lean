import LeanDag.Properties.Compose
import LeanDag.Properties.Agreement
import LeanDag.Properties.Arcs.Liveness

/-!
# The composition theorem: every stack of mechanisms is one mechanism

`docs/target-properties.md` §11.11, the third part of the goal. Each
DAG-transforming mechanism delivers one relation between the universe
it reads and the one it writes — a rebase of the universe above a
settling round, and a rebase of the schedule. `Rebased` names the pair;
a cut is one at settling round equal to its horizon, a fill or a
re-genesis one at no offset. `Stack` is a finite sequence of them, and
`Stack.rebased` says the sequence is one `Rebased`: offsets add, base
slots add, the settling round is the latest of them read in the first
universe's frame.

`Stack.safe_and_live` is then the claim: for any rule with `Banded`,
`Agree` and a support, and any stack of mechanisms on it, every verdict
above the composite settling round transports to the composite's own
numbering, any view of the composite agrees with the original, and the
liveness precondition carries. Nothing is said about which mechanisms
are in the stack or in what order — a validator that filled a crash
gap, pruned below a horizon, rejoined with a fresh chain and pruned
again is one `Stack`, and the theorem reads it as one rebase.

Two view hypotheses, because they are two different facts. Safety asks
that the two views agree above the settling round, which is what a
validator that keeps its own blocks has. Liveness asks that the
composite's view cover the horizon, which includes blocks the
mechanisms added — a fill's blocks were never in the old view, so no
agreement with it can supply them.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **What one mechanism delivers, universe and schedule together.** -/
structure Rebased (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (S S' : Slots Validator) (G R₀ d : ℕ) : Prop
    extends RebasedAbove R U U' G R₀, Rebases S S' G d

/-- The schedule is a rebase of itself. -/
theorem Rebases.refl {S : Slots Validator} : Rebases S S 0 0 where
  slotRound := fun k => by simp
  leader := fun k => by simp
  base := Nat.zero_le _

namespace Rebased

variable {U U' U'' : R.Universe} {S S' S'' : Slots Validator}

/-- A cut is a rebase at its horizon. -/
theorem of_truncates {G d : ℕ} (h : Truncates R U U' S S' G d) : Rebased R U U' S S' G G d :=
  { h.toRebasedAbove, h.toRebases with }

/-- A fill or a re-genesis is a rebase at no offset, on the same schedule. -/
theorem of_sustains {R₀ : ℕ} (h : Sustains R U U' 0 R₀) : Rebased R U U' S S 0 R₀ 0 :=
  { h, Rebases.refl with }

/-- Doing nothing is a rebase. -/
theorem refl : Rebased R U U S S 0 0 0 := { RebasedAbove.refl, Rebases.refl with }

/-- **Two rebases are one.** -/
theorem trans {G₁ R₁ d₁ G₂ R₂ d₂ : ℕ} (h : Rebased R U U' S S' G₁ R₁ d₁)
    (h' : Rebased R U' U'' S' S'' G₂ R₂ d₂) :
    Rebased R U U'' S S'' (G₁ + G₂) (max R₁ (R₂ + G₁)) (d₁ + d₂) :=
  { h.toRebasedAbove.trans h'.toRebasedAbove, h.toRebases.trans h'.toRebases with }

end Rebased

/-- **A stack of mechanisms**: a finite sequence, each step a `Rebased`.
The indices carry the composite's offset, settling round and base slot,
accumulated as `Rebased.trans` accumulates them. -/
inductive Stack (R : DagRule Validator BlockId Payload) :
    R.Universe → Slots Validator → R.Universe → Slots Validator → ℕ → ℕ → ℕ → Prop
  | nil {U : R.Universe} {S : Slots Validator} : Stack R U S U S 0 0 0
  | step {U U' U'' : R.Universe} {S S' S'' : Slots Validator} {G R₀ d G' R₀' d' : ℕ} :
      Rebased R U U' S S' G R₀ d → Stack R U' S' U'' S'' G' R₀' d' →
      Stack R U S U'' S'' (G + G') (max R₀ (R₀' + G)) (d + d')

/-- **A stack is one mechanism.** -/
theorem Stack.rebased {U U' : R.Universe} {S S' : Slots Validator} {G R₀ d : ℕ} :
    Stack R U S U' S' G R₀ d → Rebased R U U' S S' G R₀ d
  | .nil => Rebased.refl
  | .step h st => h.trans st.rebased

/-! ## Safety across a rebase

`LocalTruncate.of_banded` is this at a cut, where the settling round is
the horizon. A fill settles higher than it shifts, so the general form
carries the settling round separately and asks the slot to sit above it. -/

variable {U U' : R.Universe} {S S' : Slots Validator} {G R₀ d : ℕ}

/-- **A verdict above the settling round transports across any rebase**,
to the rebased numbering, on views that agree above the settling round.
An `↔`, as `LocalTruncate` is. -/
theorem decided_of_rebased (h : Banded R) (hr : Rebased R U U' S S' G R₀ d)
    {V : R.View U} {V' : R.View U'} (hv : ViewAgreeAbove R V V' R₀)
    (k : ℕ) (hk : R₀ ≤ S.slotRound (d + k)) (v : Option BlockId) :
    R.Decided S V (d + k) v ↔ R.Decided S' V' k v := by
  have hsk := hr.slotRound k
  constructor
  · intro hdec
    obtain ⟨top, htop⟩ := h S U V (d + k) v hdec
    refine htop 0 G d 0 S' U' V' k (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m = m' + d := by omega
      subst hmm
      have := hr.slotRound m'
      have hc : d + m' = m' + d := by omega
      rw [hc] at this
      omega
    · intro m m' hm _
      have hmm : m = m' + d := by omega
      subst hmm
      have hc : m' + d = d + m' := by omega
      rw [hc]
      exact (hr.leader m').symm
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact ((hr.mem b).mp ⟨hb, by omega⟩).1
      · intro b hb hband
        have hR : R₀ ≤ (R.block U b).round := by
          rcases hband with ⟨h1, _⟩ | ⟨hm, h1, _⟩
          · omega
          · have := (hr.of_mem' hm (by omega)).2; omega
        exact ⟨by have := hr.round b hb hR; omega, hr.creator b hb hR⟩
      · intro b hb h1 h2
        exact hr.refs b hb (by omega)
    · intro b hbV h1 h2
      exact (hv b (R.viewSound V hbV) (by omega)).mp hbV
  · intro hdec
    obtain ⟨top, htop⟩ := h S' U' V' k v hdec
    refine htop G 0 0 d S U V (d + k) (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m' = m + d := by omega
      subst hmm
      have := hr.slotRound m
      have hc : d + m = m + d := by omega
      rw [hc] at this
      omega
    · intro m m' hm _
      have hmm : m' = m + d := by omega
      subst hmm
      have hc : m + d = d + m := by omega
      rw [hc]
      exact hr.leader m
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact (hr.of_mem' hb (by omega)).1
      · intro b hb hband
        have hR : R₀ ≤ (R.block U' b).round + G := by
          rcases hband with ⟨h1, _⟩ | ⟨hm, h1, _⟩
          · omega
          · have := hr.round b hm (by omega); omega
        obtain ⟨hbU, hround⟩ := hr.of_mem' hb hR
        exact ⟨by omega, (hr.creator b hbU (by omega)).symm⟩
      · intro b hb h1 h2
        obtain ⟨hbU, hround⟩ := hr.of_mem' hb (by omega)
        exact (hr.refs b hbU (by omega)).symm
    · intro b hbV h1 h2
      have hbU' : b ∈ R.ids U' := R.viewSound V' hbV
      obtain ⟨hbU, hround⟩ := hr.of_mem' hbU' (by omega)
      exact (hv b hbU (by omega)).mpr hbV

/-- **Cross-rebase agreement**, from any view of the rebased universe. -/
theorem decided_agree_rebased (ha : Agree R) (hb : Banded R)
    (hr : Rebased R U U' S S' G R₀ d) {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' R₀) {W : R.View U'} {k : ℕ} (hk : R₀ ≤ S.slotRound (d + k))
    {w v : Option BlockId} (hW : R.Decided S' W k w) (hV : R.Decided S V (d + k) v) : w = v :=
  ha S' W V' k w v hW ((decided_of_rebased hb hr hv k hk v).mp hV)

/-! ## Liveness across a rebase -/

namespace Support

variable (sp : Support R)

/-- **`live` survives any rebase**, at the rebased numbering, for a
window above the settling round. `live_of_truncates` at a cut,
`live_of_sustains` at a fill; here the two are one statement. -/
theorem live_of_rebased {rel : Reliability Validator} (hloc : sp.Local)
    (hr : Rebased R U U' S S' G R₀ d) {V : R.View U} {V' : R.View U'}
    {T : Finset Validator} {lo K : ℕ}
    (hlive : sp.live rel S V T lo K) (hR₀ : R₀ ≤ S.slotRound lo) (hlo : d ≤ lo) (hK : lo < K)
    (hV' : ∀ N, G ≤ N → CoversUpto R V N → CoversUpto R V' (N - G)) :
    sp.live rel S' V' T (lo - d) (K - d) := by
  obtain ⟨hq, N, hcov, hN, hslot⟩ := hlive
  have hGN : G ≤ N := by
    have := hN lo hK
    have := hr.base
    have := S.mono hlo
    omega
  refine ⟨hq, N - G, hV' N hGN hcov, ?_, ?_⟩
  · intro k' hk'
    have hs := hr.slotRound k'
    have := hN (d + k') (by omega)
    omega
  · intro k' hlo' hK' hlead'
    have hs := hr.slotRound k'
    have hl := hr.leader k'
    have hlead : S.leader (d + k') ∈ T := by rw [← hl]; exact hlead'
    obtain ⟨hpop, hcert⟩ := hslot (d + k') (by omega) (by omega) hlead
    have hGk : G ≤ S.slotRound (d + k') := le_trans hr.base (S.mono (Nat.le_add_right d k'))
    have hRk : R₀ ≤ S.slotRound (d + k') := le_trans hR₀ (S.mono (by omega))
    refine ⟨?_, ?_⟩
    · intro n' h1 h2
      have := hr.toRebasedAbove.populatedOn_of (T := T) (r := n' + G) (by omega) (by omega)
        (hpop (n' + G) (by omega) (by omega))
      rwa [Nat.add_sub_cancel] at this
    · rintro L ⟨hL', hLr', hLc'⟩
      obtain ⟨hLU, hround⟩ := hr.toRebasedAbove.of_mem' hL' (by omega)
      have hLr : (R.block U L).round = S.slotRound (d + k') := by omega
      have hLc : (R.block U L).creator = S.leader (d + k') := by
        rw [← hr.creator L hLU (by omega), hLc']; exact hl
      have := sp.certifiesAt_of_rebased hloc hr.toRebasedAbove (T := T)
        (r := S.slotRound (d + k')) hRk hGk hLU hLr (hcert L ⟨hLU, hLr, hLc⟩)
      have e : S.slotRound (d + k') - G = S'.slotRound k' := by omega
      rwa [e] at this

end Support

/-! ## The composition theorem -/

/-- **Every stack of mechanisms keeps safety and liveness**, for any rule
with `Banded`, `Agree` and a support. Above the composite settling
round: verdicts transport to the composite's numbering, any view of
the composite agrees with the original, and the liveness precondition
carries. Nothing is assumed about which mechanisms are stacked or in
what order. -/
theorem Stack.safe_and_live (hb : Banded R) (ha : Agree R) (sp : Support R) (hloc : sp.Local)
    (st : Stack R U S U' S' G R₀ d) {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' R₀) :
    (∀ (k : ℕ) (v : Option BlockId), R₀ ≤ S.slotRound (d + k) →
        (R.Decided S V (d + k) v ↔ R.Decided S' V' k v)) ∧
    (∀ (W : R.View U') (k : ℕ) (w v : Option BlockId), R₀ ≤ S.slotRound (d + k) →
        R.Decided S' W k w → R.Decided S V (d + k) v → w = v) ∧
    (∀ {rel : Reliability Validator} {T : Finset Validator} {lo K : ℕ},
        sp.live rel S V T lo K → R₀ ≤ S.slotRound lo → d ≤ lo → lo < K →
        (∀ N, G ≤ N → CoversUpto R V N → CoversUpto R V' (N - G)) →
        sp.live rel S' V' T (lo - d) (K - d)) :=
  ⟨fun k v hk => decided_of_rebased hb st.rebased hv k hk v,
   fun _ k _ _ hk hW hV => decided_agree_rebased ha hb st.rebased hv hk hW hV,
   fun hlive hR₀ hlo hK hV' => sp.live_of_rebased hloc st.rebased hlive hR₀ hlo hK hV'⟩

end Properties

end LeanDag
