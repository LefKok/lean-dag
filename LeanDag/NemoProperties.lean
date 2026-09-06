import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import LeanDag.Nemo.Carrier
import LeanDag.Nemo.Liveness
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Derived.Bounded
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support

import LeanDag.Properties.Arcs.Liveness

/-!
# Nemo conforms to the target properties

`docs/porting-plan.md` step 1, and the first rule ported after the
audit that closed the mechanism side. `Nemo/Carrier.lean` has the
carrier and the three properties that are one Nemo theorem apiece; here
is `Banded`, the one induction the rule owes, and the liveness pair on
top of it.

**Nemo is the cheapest of the four**, and deliberately so: three
constructors, no direct skip, a wave of two, and rules that read one
round above the slot. The band helpers it needs are the generic ones
now in `Properties/Band.lean`, which is what porting Nemo was meant to
establish.
-/

namespace LeanDag

namespace NemoProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Band

variable {U U' : Nemo.Universe Validator BlockId Payload} {lo hi g g' : ℕ}

/-! The three field projections, restated in Nemo's own vocabulary. The
generic forms in `Properties/Band.lean` speak of `R.block U`, which is
`U.block` by definition but a distinct atom to `omega`; saying it once
here keeps every proof below in one vocabulary. -/

theorem memB (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {b : BlockId} (hb : b ∈ U.ids) (h1 : lo ≤ (U.block b).round + g)
    (h2 : (U.block b).round + g ≤ hi) : b ∈ U'.ids :=
  AgreeBand.mem_band h hb h1 h2

theorem blockB (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {b : BlockId} (hb : b ∈ U.ids) (h1 : lo ≤ (U.block b).round + g)
    (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).creator = (U.block b).creator :=
  AgreeBand.block_band h hb h1 h2

theorem blockB' (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {b : BlockId} (hb : b ∈ U.ids) (hb' : b ∈ U'.ids)
    (h1 : lo ≤ (U'.block b).round + g') (h2 : (U'.block b).round + g' ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).creator = (U.block b).creator :=
  AgreeBand.block_band' h hb hb' h1 h2

theorem refsB (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {b : BlockId} (hb : b ∈ U.ids) (h1 : lo < (U.block b).round + g)
    (h2 : (U.block b).round + g ≤ hi) : (U'.block b).refs = (U.block b).refs :=
  AgreeBand.refs_band h hb h1 h2

/-- A candidate of a slot is a candidate of the slot the shift names. -/
theorem isLeaderBlock_band (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {S S' : Slots Validator} {k k' : ℕ} {L : BlockId}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlk : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi)
    (hL : Nemo.IsLeaderBlock (S := S) U k L) :
    Nemo.IsLeaderBlock (S := S') U' k' L := by
  obtain ⟨hm, hr, hc⟩ := hL
  have hb := blockB h hm (by omega) (by omega)
  exact ⟨memB h hm (by omega) (by omega), by omega, by rw [hb.2, hc, hlk]⟩

/-- **The supporters a view holds transport.** A voting-round block the
view held is a block of the shifted universe at the shifted round, and
it references the candidate still. -/
theorem supportersIn_band (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {V : Nemo.View Validator BlockId Payload U} {V' : Nemo.View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} :
    Nemo.supportersIn U V L r ⊆ Nemo.supportersIn U' V' L r' := by
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqL⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.ids := (Nemo.mem_blocksAt.mp hqA).1
  have hqr : (U.block q).round = r + 1 := (Nemo.mem_blocksAt.mp hqA).2
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · exact Nemo.mem_blocksAt.mpr
      ⟨memB h hqU (by omega) (by omega),
       by have := blockB h hqU (by omega) (by omega); omega⟩
  · rw [refsB h hqU (by omega) (by omega)]; exact hqL
  · rw [(blockB h hqU (by omega) (by omega)).2]; exact hvq

/-- **And so does the direct commit.** -/
theorem directCommitIn_band (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {V : Nemo.View Validator BlockId Payload U} {V' : Nemo.View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hc : Nemo.DirectCommitIn U V L r) :
    Nemo.DirectCommitIn U' V' L r' :=
  le_trans hc (Finset.card_le_card (supportersIn_band h hrr hr hhi hV))

/-- **The anchor certifies what it certified.** Both directions: a
certificate inside an old anchor's history is old, by `reaches_old`, and
an old one stays inside it, by `reaches_of`. -/
theorem certifiedIn_band (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Nemo.CertifiedIn U' A L r' ↔ Nemo.CertifiedIn U A L r := by
  have hA' : A ∈ U'.ids := memB h hA hAlo hAhi
  constructor
  · rintro ⟨p, hp, hpr, hpL⟩
    have hpre : ReachesFrom U'.block A p := (Nemo.mem_history_iff hA').mp hp
    obtain ⟨hpU, hpreU, hpeq⟩ :=
      AgreeBand.reaches_old h hA hAlo hAhi hpre (by
        show lo ≤ (U'.block p).round + g'; omega)
    have hpeq' : (U.block p).round + g = (U'.block p).round + g' := hpeq
    refine ⟨p, (Nemo.mem_history_iff hA).mpr hpreU, by omega, ?_⟩
    rwa [refsB h hpU (by omega) (by omega)] at hpL
  · rintro ⟨p, hp, hpr, hpL⟩
    have hpre : ReachesFrom U.block A p := (Nemo.mem_history_iff hA).mp hp
    have hpU : p ∈ U.ids := U.causal.mem_ids_of_reaches hA hpre
    have hb := blockB h hpU (by omega) (by omega)
    refine ⟨p, (Nemo.mem_history_iff hA').mpr
      (AgreeBand.reaches_of h hA hAhi hpre (by
        show lo ≤ (U.block p).round + g; omega)), by omega, ?_⟩
    rw [refsB h hpU (by omega) (by omega)]; exact hpL

/-- **A candidate the band did not carry is certified from no old
anchor.** Its certificate would have to lie in the anchor's history,
which is old, and an old block references only old blocks. This is the
premise `indirectSkip` needs. -/
theorem not_certifiedIn_band_novel
    (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hL : L ∉ U.ids) : ¬ Nemo.CertifiedIn U' A L r' := by
  intro hc
  rw [certifiedIn_band h hA hAlo hAhi hrr hr hhi] at hc
  obtain ⟨p, hp, -, hpL⟩ := hc
  have hpre : ReachesFrom U.block A p := (Nemo.mem_history_iff hA).mp hp
  exact hL (U.complete p (U.causal.mem_ids_of_reaches hA hpre) L hpL)

end Band

/-- **Every verdict of Nemo reads a band of rounds.** One induction,
three cases. The direct case reads one round above the slot and stops —
Nemo's wavelength. The indirect pair reads the anchor's derivation and
the intermediates', and the top is the largest of those.

Nothing here supposes the larger universe adds no candidates. Where one
appears the anchor cannot certify it (`not_certifiedIn_band_novel`),
which is exactly what `indirectSkip`'s negative premise needs. -/
theorem banded_aux [S : Slots Validator] {U : Nemo.Universe Validator BlockId Payload}
    {V : Nemo.View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (hd : Nemo.Decided U V k v) :
    ∃ top, S.slotRound k + 1 ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : Slots Validator)
        (U' : Nemo.Universe Validator BlockId Payload)
        (V' : Nemo.View Validator BlockId Payload U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand (nemoRule (Payload := Payload)) U U' (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        Nemo.Decided (S := S') U' V' k' v := by
  classical
  induction hd with
  | @directCommit k L hL hc =>
      refine ⟨S.slotRound k + 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine Nemo.Decided.directCommit (S := S')
        (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL) ?_
      exact directCommitIn_band hab hkk (by omega) (by omega)
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hc
  | @indirectCommit k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Nemo.Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hAL : Nemo.IsLeaderBlock U j A := Nemo.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Nemo.Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold Nemo.Eligible Nemo.decisionRound at helig'
      have htopk : S.slotRound k + 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Nemo.Decided.indirectCommit (S := S') (by omega) (by
          unfold Nemo.Eligible Nemo.decisionRound; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_
        (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL) ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Nemo.Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold Nemo.Eligible Nemo.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · exact (certifiedIn_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mpr hcert
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Nemo.Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hAL : Nemo.IsLeaderBlock U j A := Nemo.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Nemo.Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold Nemo.Eligible Nemo.decisionRound at helig'
      have htopk : S.slotRound k + 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Nemo.Decided.indirectSkip (S := S') (by omega) (by
          unfold Nemo.Eligible Nemo.decisionRound; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Nemo.Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold Nemo.Eligible Nemo.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · intro L' hL'
        by_cases hLo : L' ∈ U.ids
        · have hLS : Nemo.IsLeaderBlock (S := S) U k L' := by
            obtain ⟨hm, hr, hc⟩ := hL'
            have hb := blockB' hab hLo hm (by omega) (by omega)
            exact ⟨hLo, by omega, by rw [← hb.2, hc]; exact hlk.symm⟩
          intro hct
          exact hnone L' hLS
            ((certifiedIn_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mp hct)
        · exact not_certifiedIn_band_novel hab hAL.1 hAlo hAhi hkk (by omega) (by omega) hLo

/-- **Nemo is banded.** -/
theorem banded : Banded (nemoRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := S) hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' U' V' k' hkd hsch hlead hab hV⟩

/-! ## The liveness properties

`LeaderCommits` is `Support.leaderCommits` at `voteSupport`, and `Descends` is not among them: it follows from `Indirect` by the generic
induction in `Properties/Derived/Descent.lean` (§11.2b), and what Nemo
supplies for it is the round-structure hypothesis. -/

/-- **Law 3 of `voteSupport`, for Nemo** (`Properties/Support.lean`): a
majority referencing the candidate one round up is its direct commit.
Laws 1 and 2 are the generic ones for the one-round shape. -/
theorem voteSupport_commits (hn : 0 < Fintype.card Validator) :
    (voteSupport (nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))).Commits (nemoReliability Validator hn) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : Nemo.majority Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - (Fintype.card Validator - Nemo.majority Validator)
      ≤ T.card at h2
    have : Nemo.majority Validator ≤ Fintype.card Validator := by unfold Nemo.majority; omega
    omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hdc : Nemo.DirectCommit U L (S.slotRound k) := by
    refine le_trans hcard (Finset.card_le_card ?_)
    intro w hw
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
      (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) w hw
    exact Nemo.mem_supporters.mpr ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ w hw b hb hbc hbr, hbc⟩
  have hin : Nemo.DirectCommitIn U V L (S.slotRound k) := Nemo.directCommitIn_of_coversUpto hdc hcov
  refine ⟨L, by omega, Nemo.Decided.directCommit ⟨hLmem, hLr, hLc⟩ hin, ?_⟩
  intro S' hround hlead'
  refine Nemo.Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-- **A3 as a property.** The two indirect constructors, by cases on a
certified candidate at the slot — which is the whole proof, and is why
the verdict survives a reassignment of leaders elsewhere: the case split
reads slot `i`'s candidate and the anchor's history, and neither moves. -/
theorem indirect :
    Indirect (nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun sr i j => sr i + 2 ≤ sr j) := by
  classical
  intro S U V i j A helig hj hmid
  letI := S
  have he : Nemo.Eligible Validator i j := Nemo.eligible_iff.mpr helig
  have hlt : i < j := by
    by_contra hge
    have := S.mono (Nat.le_of_not_lt hge)
    unfold Nemo.Eligible Nemo.decisionRound at he; omega
  have heq : ∀ (S' : Slots Validator), S'.slotRound = S.slotRound → ∀ x y,
      Nemo.Eligible Validator (S := S') x y ↔ Nemo.Eligible Validator (S := S) x y := by
    intro S' hround x y
    simp only [Nemo.Eligible, Nemo.decisionRound, hround]
  by_cases hc : ∃ L, Nemo.IsLeaderBlock (S := S) U i L ∧
      Nemo.CertifiedIn U A L (S.slotRound i)
  · obtain ⟨L, hL, hcert⟩ := hc
    refine ⟨some L, fun S' hround hlead hj' hmid' => ?_⟩
    refine Nemo.Decided.indirectCommit (S := S') hlt ((heq S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2
        (Nemo.eligible_iff (S := S) |>.mp ((heq S' hround i i').mp h3))) ?_ ?_
    · obtain ⟨hm, hr, hcr⟩ := hL
      exact ⟨hm, by rw [hround]; exact hr, by rw [hlead]; exact hcr⟩
    · rw [hround]; exact hcert
  · push Not at hc
    refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
    refine Nemo.Decided.indirectSkip (S := S') hlt ((heq S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2
        (Nemo.eligible_iff (S := S) |>.mp ((heq S' hround i i').mp h3))) ?_
    intro L hL'
    have hLS : Nemo.IsLeaderBlock (S := S) U i L := by
      obtain ⟨hm, hr, hcr⟩ := hL'
      exact ⟨hm, by rw [← hround]; exact hr, by rw [← hlead]; exact hcr⟩
    have hnt := hc L hLS
    show ¬ Nemo.CertifiedIn U A L (S'.slotRound i)
    rw [hround]; exact hnt

/-- **And a committed run decides everything below it**, from `Indirect`
with no induction of its own. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : Nemo.SpansEligible (Validator := Validator) (S := S) c) :
    Descends (nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c :=
  Descends.of_indirect indirect hc
    (fun b i hi => Nemo.eligible_iff.mp (hspans b i hi))

end NemoProperties

namespace Nemo

/-! ## Liveness, composed

`Support.decidedBelow_of_fairRun` at Nemo's vote support, under the
majority fault model `nemoReliability`. The direct proof this replaced
committed each slot of the run and ran the crash descent; both are the
generic theorems now. -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [C : CrashFaults Validator] [S : Slots Validator] {T : Finset Validator}

/-- **Liveness.** Under post-`R` coverage, growth to the horizon, and a
recurring run of `c` reliable-led slots, every slot below the run is
decided — the run placed past both the target and `R` by fairness.

The quantifier order is the content: the slot `b` is fixed by the *schedule*
alone, before any universe is named, so "eventually" means "any DAG grown
past this schedule-fixed slot". Crashed-leader slots are settled here and
only here: they descend onto the run via `indirectSkip`. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ Live Validator)
    (hcard : majority Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v := by
  have hTn := Finset.card_le_univ T
  have hn : 0 < Fintype.card Validator := by unfold majority at hcard; omega
  obtain ⟨b, hb, hRb, h⟩ :=
    (Properties.voteSupport (NemoProperties.nemoRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload))).decidedBelow_of_fairRun
      (Properties.voteSupport_ofCoverage _) (NemoProperties.voteSupport_commits hn) hc
      (NemoProperties.descends hc hspan) (T := T)
      ⟨Finset.subset_univ _, by
        change Fintype.card Validator - (Fintype.card Validator - majority Validator) ≤ T.card
        omega⟩ fair R s
  refine ⟨b, hb, hRb, fun U N V hpop hs hN hcov i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs (fun r _ h2 => PopulatedOn.mono hT (hpop r h2)) hcov hN i hi
  exact ⟨v, hv.2.1⟩

/-- **Liveness at `T := Live`** — the whole live class, which the tight
committee `n = 2f + 1` requires exactly. -/
theorem all_decided_below_of_fairRun_live {c : ℕ} (hc : 0 < c)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn (Live Validator) c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r ≤ N, Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl majority_le_card_live hspan fair R s

end Nemo


end LeanDag
