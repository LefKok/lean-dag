import LeanDag.Odontoceti.Carrier
import LeanDag.MysticetiProperties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Derived.Bounded
import LeanDag.Adaptive.Odontoceti

import LeanDag.Properties.Arcs.Liveness

import LeanDag.Timed.Coverage

import LeanDag.Properties.Arcs.Headline

/-!
# Odontoceti conforms to the target properties

`docs/target-properties.md` §11.2. The third rule to be put through the
properties at its own carrier, and the first not written for them.

**Why this rule and not another.** Odontoceti mirrors the core
constructor for constructor at a shorter wavelength —
`decisionRound k = slotRound k + 1`, no certificate round — so if the
six obligations are the right six, the differences it does have should
be the only work. That is what a third instance is for.

**All six, and the fifth found a defect on the way.**

`Decided.directSkip` used to quantify over the candidates the universe
holds, so a slot with no candidate was skipped *vacuously*.
`AgreeBand`'s membership clause runs one way — a block of `U` in the
band is a block of `U'` — because a band must admit universes that hold
*more*. A candidate present in `U'` and absent from `U` was therefore
beyond reach, and the goal `L ∈ U.ids` could not be closed.

That was the core's own defect, before its repair
(`docs/target-properties.md` §3.2), and the repair transferred without
change: Odontoceti's `DirectSkipIn` and the core's are the same
predicate, so `Decided.directSkip` now takes `DirectSkipSlotIn`.

What is Odontoceti's own, and what this file has to supply, is the
shorter wavelength — the direct rule counts supporters at
`slotRound k + 1` where the core counts certificates two rounds up —
and `ThickLink`, the indirect test, which counts supporters inside the
anchor's cone. Both needed their own band transport. The minimality
premise on `indirectCommit`, which the core has no analogue of, needed
`not_thickLink_band_novel`: a fresh candidate is thick-linked from no
old anchor, so it cannot undercut the least one.
-/

namespace LeanDag

namespace OdontocetiProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## What this file adds to `Odontoceti/Carrier.lean`

The carrier, `Causal`, `Agree`, `CommitsCandidate` and `CommitsDirect`
are there, upstream of every mechanism. Here is the band and everything
the band gives, plus the two liveness properties, which need the bounded
relation and so the adaptive arc.

## The band, across a shifted universe

Odontoceti shares the core's block vocabulary — `IsLeaderBlock`,
`blocksAt`, `slotBlamers` — so the core's band lemmas apply once the
carriers are identified, which `toCore` does by the three fields. What
is Odontoceti's own is the direct rule, which counts *supporters* at
`slotRound k + 1` rather than certificates two rounds up, and the
indirect test `ThickLink`, which counts supporters inside the anchor's
cone. Those need their own transport, and they are what follows. -/

section Band

variable {U U' : BlockUniverse Validator BlockId Payload} {lo hi g g' : ℕ}

/-- The two carriers project identically, so a band for one is a band
for the other. -/
theorem toCore (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g') :
    AgreeBand (MysticetiProperties.mysticetiRule (Payload := Payload)) U U' lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **Supporters survive the band.** A block one round above the slot
that referenced the candidate references it still, and it is a block of
the shifted universe at the shifted round. -/
theorem supportersIn_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} :
    supportersIn U V L (r + 1) ⊆ supportersIn U' V' L (r' + 1) := by
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqL⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.block q).round = r + 1 := (mem_blocksAt.mp hqA).2
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · exact MysticetiProperties.blocksAt_band (toCore h) (by omega) (by omega) (by omega) hqA
  · rw [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)]; exact hqL
  · rw [(MysticetiProperties.band_block (toCore h) hqU (by omega) (by omega)).2]; exact hvq

/-- **And so does the direct commit.** -/
theorem directCommitIn_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hc : Odontoceti.DirectCommitIn U V L r) :
    Odontoceti.DirectCommitIn U' V' L r' :=
  le_trans hc (Finset.card_le_card (supportersIn_band h hrr hr hhi hV))

/-- **The anchor's cone of supporters is the cone it was.** Both
inclusions at once: a supporter inside an old anchor's history is old,
by `reaches_old`, and an old one stays inside it, by `reaches_of`. -/
theorem coneSupports_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Odontoceti.coneSupports U' A L r' = Odontoceti.coneSupports U A L r := by
  have hset : (blocksAt U' (r' + 1)).filter
        (fun q => L ∈ (U'.block q).refs ∧ q ∈ history U' A)
      = (blocksAt U (r + 1)).filter (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A) := by
    have hA' : A ∈ U'.ids := MysticetiProperties.band_mem (toCore h) hA hAlo hAhi
    ext q
    simp only [Finset.mem_filter, mem_blocksAt]
    constructor
    · rintro ⟨⟨hqU', hqr'⟩, hqL, hqh⟩
      have hqre : ReachesFrom U'.block A q := (mem_history_iff (U := U') hA').mp hqh
      have hqrR : (MysticetiProperties.mysticetiRule.block U' q).round = r' + 1 := hqr'
      obtain ⟨hqU, hqreU, hqeq⟩ :=
        AgreeBand.reaches_old (toCore h) hA hAlo hAhi hqre (by omega)
      have hqeq' : (U.block q).round + g = (U'.block q).round + g' := hqeq
      refine ⟨⟨hqU, by omega⟩, ?_, (mem_history_iff (U := U) hA).mpr hqreU⟩
      rwa [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)] at hqL
    · rintro ⟨⟨hqU, hqr⟩, hqL, hqh⟩
      have hqre : ReachesFrom U.block A q := (mem_history_iff (U := U) hA).mp hqh
      have hlink : (MysticetiProperties.mysticetiRule.block U q).round
          = (U.block q).round := rfl
      refine ⟨?_, ?_, ?_⟩
      · exact mem_blocksAt.mp (MysticetiProperties.blocksAt_band (toCore h)
          (by omega) (by omega) (by omega) (mem_blocksAt.mpr ⟨hqU, hqr⟩))
      · rw [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)]; exact hqL
      · exact (mem_history_iff (U := U') hA').mpr
          (AgreeBand.reaches_of (toCore h) hA hAhi hqre (by omega))
  unfold Odontoceti.coneSupports
  rw [hset]
  refine MysticetiProperties.creatorsOf_band (toCore h) ?_
  intro b hb
  obtain ⟨hbA, -⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.ids := (mem_blocksAt.mp hbA).1
  have hbr : (U.block b).round = r + 1 := (mem_blocksAt.mp hbA).2
  exact ⟨hbU, by omega, by omega⟩

/-- **So the indirect test reads the same.** -/
theorem thickLink_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Odontoceti.ThickLink U' A L r' ↔ Odontoceti.ThickLink U A L r := by
  unfold Odontoceti.ThickLink
  rw [coneSupports_band h hA hAlo hAhi hrr hr hhi]

/-- **A candidate the band did not carry is thick-linked from no old
anchor.** Its supporters would have to sit in the anchor's cone, which
is old, and an old block references only old blocks — so the cone
supports nothing, and the threshold is positive.

This is the premise `indirectSkip` needs and the one `indirectCommit`'s
minimality clause needs: a fresh candidate cannot undercut the least
one, because it passes no test at all. -/
theorem not_thickLink_band_novel
    (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hL : L ∉ U.ids) (hpos : 0 < Fintype.card Validator - 3 * F.f) :
    ¬ Odontoceti.ThickLink U' A L r' := by
  intro ht
  rw [thickLink_band h hA hAlo hAhi hrr hr hhi] at ht
  unfold Odontoceti.ThickLink Odontoceti.coneSupports at ht
  have hempty : (blocksAt U (r + 1)).filter
      (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqA, hqL, -⟩ := Finset.mem_filter.mp hq
    exact hL (U.complete q (mem_blocksAt.mp hqA).1 L hqL)
  rw [hempty] at ht
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty, Nat.le_zero] at ht
  omega

end Band

/-- The thick-link threshold is positive: `Faults5` asks for `5f + 1`
validators, so `card − 3f ≥ 2f + 1`. -/
theorem thickLink_threshold_pos : 0 < Fintype.card Validator - 3 * F.f := by
  have := F.card_validators5
  omega

/-- **Every verdict of Odontoceti reads a band of rounds.** One
induction, four cases. The direct cases read one round above the slot
and stop — Odontoceti's wavelength, where the core reads two. The
indirect cases read their anchor's derivation and the intermediates',
and the top is the largest of those.

Nothing here supposes the larger universe adds no candidates. Where one
appears the anchor cannot see it (`not_thickLink_band_novel`), which is
what the minimality premise needs as much as the skip does, and the
slot-level skip does not look for it at all. -/
theorem banded_aux [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (hd : Odontoceti.Decided U V k v) :
    ∃ top, S.slotRound k + 1 ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : Slots Validator)
        (U' : BlockUniverse Validator BlockId Payload)
        (V' : View Validator BlockId Payload U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand (odontocetiRule (Payload := Payload)) U U'
          (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        Odontoceti.Decided (S := S') U' V' k' v := by
  classical
  induction hd with
  | @directCommit k L hL hc =>
      refine ⟨S.slotRound k + 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine Odontoceti.Decided.directCommit (S := S')
        (MysticetiProperties.isLeaderBlock_band (toCore hab) hkk hlk (by omega) (by omega) hL) ?_
      exact directCommitIn_band hab hkk (by omega) (by omega)
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hc
  | @directSkip k hs =>
      refine ⟨S.slotRound k + 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact Odontoceti.Decided.directSkip (S := S')
        (MysticetiProperties.directSkipSlotIn_band (toCore hab) hkk hlk rfl (by omega)
          (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hs)
  | @indirectCommit k j A L hkj helig hanchor hmid hL ht hmin ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Odontoceti.Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U j A := Odontoceti.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Odontoceti.Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold Odontoceti.Eligible Odontoceti.decisionRound at helig'
      have htopk : S.slotRound k + 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Odontoceti.Decided.indirectCommit (S := S') (by omega) (by
          unfold Odontoceti.Eligible Odontoceti.decisionRound; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_
        (MysticetiProperties.isLeaderBlock_band (toCore hab) hkk hlk (by omega) (by omega) hL)
        ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Odontoceti.Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold Odontoceti.Eligible Odontoceti.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · exact (thickLink_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mpr ht
      · intro L' hL' ht'
        by_cases hLo : L' ∈ U.ids
        · exact hmin L' (MysticetiProperties.isLeaderBlock_band_old (toCore hab) hkk hlk
            (by omega) (by omega) hLo hL')
            ((thickLink_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mp ht')
        · exact absurd ht' (not_thickLink_band_novel hab hAL.1 hAlo hAhi hkk
            (by omega) (by omega) hLo thickLink_threshold_pos)
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Odontoceti.Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U j A := Odontoceti.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Odontoceti.Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold Odontoceti.Eligible Odontoceti.decisionRound at helig'
      have htopk : S.slotRound k + 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Odontoceti.Decided.indirectSkip (S := S') (by omega) (by
          unfold Odontoceti.Eligible Odontoceti.decisionRound; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Odontoceti.Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold Odontoceti.Eligible Odontoceti.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · intro L hL' ht'
        by_cases hLo : L ∈ U.ids
        · exact hnone L (MysticetiProperties.isLeaderBlock_band_old (toCore hab) hkk hlk
            (by omega) (by omega) hLo hL')
            ((thickLink_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mp ht')
        · exact not_thickLink_band_novel hab hAL.1 hAlo hAhi hkk
            (by omega) (by omega) hLo thickLink_threshold_pos ht'

/-- **Odontoceti reads a band.** -/
theorem banded : Banded
    (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := S) hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' U' V' k' hkd hsch hlead hab hV⟩

/-- **Odontoceti skips an unsupported slot from a correct quorum.**

The liveness half of the repair. Making the skip a count of blockers
rather than a vacuous quantification made it strictly harder to satisfy,
and a rule no quorum can ever trigger would be sound and useless. This
says the repaired rule is still reachable: a correct quorum whose
voting-round blocks reference no candidate skips the slot, without
waiting for an anchor.

The count is the core's, so the argument is too — `subset_blamers`
applies unchanged, the two carriers projecting identically. -/
theorem skipsUnsupported :
    SkipsUnsupported (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun T => quorumCard Validator ≤ T.card) :=
  fun S U V T k hq hpres huns =>
    Odontoceti.Decided.directSkip (S := S)
      (le_trans hq (Finset.card_le_card
        (MysticetiProperties.subset_blamers (S := S) hpres huns)))

/-! ## The bounded relation, and the two liveness properties

`Adaptive/Odontoceti.DecidedWithin` already names the slots a derivation
mentions, which is the tight information `LeaderCommits` and `Descends`
need. What is added here is the bridge to `DecidedBelow`, and then the
two properties are Odontoceti's own liveness results wearing them. -/

section Bounded

/-- **Odontoceti's bounded relation lands in the derived one.** -/
theorem decidedBelow_of_decidedWithin [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {B k : ℕ} {v : Option BlockId} (h : Odontoceti.DecidedWithin (S := S) U V B k v) :
    DecidedBelow (odontocetiRule (Payload := Payload)) S B V k v :=
  ⟨h.lt_bound, h.toDecided, fun S' hround hlead =>
    (Odontoceti.decidedWithin_congr_of_slotRound (S₁ := S) (S₂ := S') hround.symm
      (fun m hm => (hlead m hm).symm) h).toDecided⟩

/-- **Law 3 of `voteSupport`, for Odontoceti** (`Properties/Support.lean`):
a quorum referencing the candidate one round up is its direct commit,
which is `directCommit_of_votesAt`. -/
theorem voteSupport_commits :
    (voteSupport (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))).Commits (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hdc : Odontoceti.DirectCommit U L (S.slotRound k) :=
    Odontoceti.directCommit_of_votesAt hcard
      (hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega))
      (hcert L ⟨hLmem, hLr, hLc⟩)
  have hin : Odontoceti.DirectCommitIn U V L (S.slotRound k) :=
    Odontoceti.directCommitIn_of_coversUpto hdc hcov
  refine ⟨L, by omega, Odontoceti.Decided.directCommit ⟨hLmem, hLr, hLc⟩ hin, ?_⟩
  intro S' hround hlead'
  refine Odontoceti.Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-- **O-A3 as a property.** The two indirect constructors, by cases on a
thick-linked candidate at the slot, committing the least one. The whole
proof is that case split, which is why the verdict survives a
reassignment of leaders elsewhere: it reads slot `i`'s candidates and
the anchor's history, and a schedule naming the same leader at `i` and
the same rounds changes neither. The minimality clause transports for
the same reason.

This is `odontoceti_descent.indirect` and the case split that stood
inside the committed-run descent, stated once. -/
theorem indirect :
    Indirect (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun sr i j => sr i + 2 ≤ sr j) := by
  classical
  intro S U V i j A helig hj hmid
  letI := S
  have he : Odontoceti.Eligible Validator i j := Odontoceti.eligible_iff.mpr helig
  have hlt : i < j := Odontoceti.lt_of_eligible he
  have heligS : ∀ (S' : Slots Validator), S'.slotRound = S.slotRound →
      ∀ x y, Odontoceti.Eligible Validator (S := S') x y ↔
        Odontoceti.Eligible Validator (S := S) x y := by
    intro S' hround x y
    simp only [Odontoceti.Eligible, Odontoceti.decisionRound, hround]
  by_cases hc : ∃ L, IsLeaderBlock U i L ∧ Odontoceti.ThickLink U A L (S.slotRound i)
  · have hCne : (U.ids.filter fun L => IsLeaderBlock U i L ∧
        Odontoceti.ThickLink U A L (S.slotRound i)).Nonempty := by
      obtain ⟨L, hL, ht⟩ := hc
      exact ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩
    set Lm := (U.ids.filter fun L => IsLeaderBlock U i L ∧
      Odontoceti.ThickLink U A L (S.slotRound i)).min' hCne with hLm
    have hmem := Finset.min'_mem _ hCne
    rw [Finset.mem_filter] at hmem
    have hminS : ∀ L', IsLeaderBlock U i L' →
        Odontoceti.ThickLink U A L' (S.slotRound i) → ¬ L' < Lm := by
      intro L' hL' ht' hlt'
      exact absurd hlt' (not_lt.mpr (Finset.min'_le _ L'
        (Finset.mem_filter.mpr ⟨hL'.1, hL', ht'⟩)))
    refine ⟨some Lm, fun S' hround hlead hj' hmid' => ?_⟩
    have hLm' : IsLeaderBlock (S := S') U i Lm := by
      obtain ⟨hm, hr, hcr⟩ := hmem.2.1
      exact ⟨hm, by rw [hround]; exact hr, by rw [hlead]; exact hcr⟩
    refine Odontoceti.Decided.indirectCommit (S := S') hlt
      ((heligS S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2
        (Odontoceti.eligible_iff (S := S) |>.mp ((heligS S' hround i i').mp h3)))
      hLm' (by rw [hround]; exact hmem.2.2) ?_
    intro L' hL' ht'
    refine hminS L' ?_ (by rw [← hround]; exact ht')
    obtain ⟨hm, hr, hcr⟩ := hL'
    exact ⟨hm, by rw [← hround]; exact hr, by rw [← hlead]; exact hcr⟩
  · push Not at hc
    refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
    refine Odontoceti.Decided.indirectSkip (S := S') hlt
      ((heligS S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2
        (Odontoceti.eligible_iff (S := S) |>.mp ((heligS S' hround i i').mp h3))) ?_
    intro L hL'
    obtain ⟨hm, hr, hcr⟩ := hL'
    have hLS : IsLeaderBlock (S := S) U i L :=
      ⟨hm, by rw [← hround]; exact hr, by rw [← hlead]; exact hcr⟩
    have hnt := hc L hLS
    show ¬ Odontoceti.ThickLink U A L (S'.slotRound i)
    rw [hround]
    exact hnt

/-- **And a committed run decides everything below it.** Was a downward
induction carrying the bound by hand; it is now `Descends.of_indirect`,
with `Eligible` read as the round inequality. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : Odontoceti.SpansEligible (Validator := Validator) (S := S) c) :
    Descends (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c :=
  Descends.of_indirect indirect hc
    (fun b i hi => Odontoceti.eligible_iff.mp (hspans b i hi))

end Bounded

end OdontocetiProperties

namespace Odontoceti

/-! ## O10 — liveness, composed

`Timed.decidedBelow_of_fairRun` at Odontoceti's vote support: the run
commits by `voteSupport_commits`, and `descends` clears what is under
it. The direct proof this replaced ran O7 at each slot of the run and
then O9. -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator] {T : Finset Validator}

/-- **O10 (thesis Theorem 12).** Under production and post-`R`
synchrony, a recurring run of `c` correct-led slots decides
every slot below it, on any view caught up to the horizon — with the
run placed past both the target and `R` by fairness. Note the horizon:
the run's last slot needs rounds up to its `slotRound + 1` only. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v := by
  obtain ⟨b, hb, hRb, h⟩ :=
    Timed.decidedBelow_of_fairRun (Properties.voteSupport (OdontocetiProperties.odontocetiRule
      (Validator := Validator) (BlockId := BlockId) (Payload := Payload)))
      (Timed.voteSupport_ofCoverage _) OdontocetiProperties.voteSupport_commits
      (OdontocetiProperties.descends hc hspan) (T := T)
      ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩ fair R k
  refine ⟨b, hb, hRb, fun U N V hpop hs hN hcov i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hcov hN i hi
  exact ⟨v, hv.2.1⟩

/-- **O10 at `T := Correct`.** -/
theorem all_decided_below_of_fairRun_correct {c : ℕ} (hc : 0 < c)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn (Correct : Finset Validator) c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r, R ≤ r → r ≤ N → Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl card_correct hspan fair R k

end Odontoceti


namespace OdontocetiProperties

/-! ## The headlines -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

theorem safety : Properties.Safe (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

theorem liveness : Properties.Support.Lives (Properties.voteSupport (odontocetiRule
    (Validator := Validator) (BlockId := BlockId) (Payload := Payload)))
    (coreReliability Validator) :=
  Properties.Support.liveness voteSupport_commits commitsCandidate selfParent noEquiv

end OdontocetiProperties

end LeanDag
