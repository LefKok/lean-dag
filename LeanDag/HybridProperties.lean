import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import LeanDag.Hybrid.Carrier
import LeanDag.Hybrid.Liveness
import LeanDag.MysticetiProperties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Derived.Bounded

/-!
# Hybrid conforms to the target properties

`docs/porting-plan.md` step 2. `Hybrid/Carrier.lean` has the carrier at
each threshold and the three properties that are one Hybrid theorem
apiece; here is `Banded` and the liveness pair.

**The band forced a repair before it could be proved.** Hybrid's skip
quantified over the candidates a slot happens to have, which a mechanism
adding one defeats; `DirectSkipSlotIn` replaced it, as it replaced the
core's and Odontoceti's. That is recorded where it happened, in
`Hybrid/Decision.lean`.

**The universe is the core's**, so the band helpers are the core's too,
reached through `toCore` — the carrier's universe is a subtype of the
core's, and `AgreeBand` at the subtype is `AgreeBand` at the underlying
universe by its three fields.
-/

namespace LeanDag

namespace HybridProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

section Band

variable {k : ℕ}
variable {U U' : {U : BlockUniverse Validator BlockId Payload // HonestNoEquiv U}}
variable {lo hi g g' : ℕ}

/-- The band at Hybrid's carrier is the band at the core's, the universe
being the core's under a predicate. -/
theorem toCore (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g') :
    AgreeBand (MysticetiProperties.mysticetiRule (Payload := Payload))
      U.val U'.val lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **Supporters survive the band.** -/
theorem supportersIn_band (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g')
    {V : View Validator BlockId Payload U.val} {V' : View Validator BlockId Payload U'.val}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.val.block b).round + g →
      (U.val.block b).round + g ≤ hi → b ∈ V'.ids)
    {L : BlockId} :
    Hybrid.supportersIn U.val V L r ⊆ Hybrid.supportersIn U'.val V' L r' := by
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqL⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.val.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.val.block q).round = r + 1 := (mem_blocksAt.mp hqA).2
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · exact MysticetiProperties.blocksAt_band (toCore h) (by omega) (by omega) (by omega) hqA
  · rw [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)]; exact hqL
  · rw [(MysticetiProperties.band_block (toCore h) hqU (by omega) (by omega)).2]; exact hvq

/-- **And so does the direct commit.** -/
theorem directCommitIn_band (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g')
    {V : View Validator BlockId Payload U.val} {V' : View Validator BlockId Payload U'.val}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.val.block b).round + g →
      (U.val.block b).round + g ≤ hi → b ∈ V'.ids)
    {L : BlockId} (hc : Hybrid.DirectCommitIn U.val V L r) :
    Hybrid.DirectCommitIn U'.val V' L r' :=
  le_trans hc (Finset.card_le_card (supportersIn_band h hrr hr hhi hV))

/-- **The anchor's cone of supporters is the cone it was.** -/
theorem coneSupports_band (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.val.ids)
    (hAlo : lo ≤ (U.val.block A).round + g) (hAhi : (U.val.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Hybrid.coneSupports U'.val A L r' = Hybrid.coneSupports U.val A L r := by
  have hset : (blocksAt U'.val (r' + 1)).filter
        (fun q => L ∈ (U'.val.block q).refs ∧ q ∈ history U'.val A)
      = (blocksAt U.val (r + 1)).filter
        (fun q => L ∈ (U.val.block q).refs ∧ q ∈ history U.val A) := by
    have hA' : A ∈ U'.val.ids := MysticetiProperties.band_mem (toCore h) hA hAlo hAhi
    ext q
    simp only [Finset.mem_filter, mem_blocksAt]
    constructor
    · rintro ⟨⟨hqU', hqr'⟩, hqL, hqh⟩
      have hqre : ReachesFrom U'.val.block A q := (mem_history_iff (U := U'.val) hA').mp hqh
      obtain ⟨hqU, hqreU, hqeq⟩ :=
        AgreeBand.reaches_old MysticetiProperties.causal (toCore h) hA hAlo hAhi hqre
          (by show lo ≤ (U'.val.block q).round + g'; omega)
      have hqeq' : (U.val.block q).round + g = (U'.val.block q).round + g' := hqeq
      refine ⟨⟨hqU, by omega⟩, ?_, (mem_history_iff (U := U.val) hA).mpr hqreU⟩
      rwa [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)] at hqL
    · rintro ⟨⟨hqU, hqr⟩, hqL, hqh⟩
      have hqre : ReachesFrom U.val.block A q := (mem_history_iff (U := U.val) hA).mp hqh
      refine ⟨?_, ?_, ?_⟩
      · exact mem_blocksAt.mp (MysticetiProperties.blocksAt_band (toCore h)
          (by omega) (by omega) (by omega) (mem_blocksAt.mpr ⟨hqU, hqr⟩))
      · rw [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)]; exact hqL
      · exact (mem_history_iff (U := U'.val) hA').mpr
          (AgreeBand.reaches_of MysticetiProperties.causal (toCore h) hA hAhi hqre
            (by show lo < (U.val.block q).round + g; omega))
  unfold Hybrid.coneSupports
  rw [hset]
  refine MysticetiProperties.creatorsOf_band (toCore h) ?_
  intro b hb
  obtain ⟨hbA, -⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.val.ids := (mem_blocksAt.mp hbA).1
  have hbr : (U.val.block b).round = r + 1 := (mem_blocksAt.mp hbA).2
  exact ⟨hbU, by omega, by omega⟩

/-- **So the indirect test reads the same.** -/
theorem thickLink_band (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.val.ids)
    (hAlo : lo ≤ (U.val.block A).round + g) (hAhi : (U.val.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Hybrid.ThickLink k U'.val A L r' ↔ Hybrid.ThickLink k U.val A L r := by
  unfold Hybrid.ThickLink
  rw [coneSupports_band h hA hAlo hAhi hrr hr hhi]

/-- **A candidate the band did not carry passes the indirect test from
no old anchor.** Its supporters would sit in the anchor's cone, which is
old, and an old block references only old blocks — so the cone supports
nothing, and an admissible threshold is positive. -/
theorem not_thickLink_band_novel
    (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.val.ids)
    (hAlo : lo ≤ (U.val.block A).round + g) (hAhi : (U.val.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hL : L ∉ U.val.ids) (hpos : 0 < k) : ¬ Hybrid.ThickLink k U'.val A L r' := by
  intro ht
  rw [thickLink_band h hA hAlo hAhi hrr hr hhi] at ht
  unfold Hybrid.ThickLink Hybrid.coneSupports at ht
  have hempty : (blocksAt U.val (r + 1)).filter
      (fun q => L ∈ (U.val.block q).refs ∧ q ∈ history U.val A) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqA, hqL, -⟩ := Finset.mem_filter.mp hq
    exact hL (U.val.complete q (mem_blocksAt.mp hqA).1 L hqL)
  rw [hempty] at ht
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty, Nat.le_zero] at ht
  omega

/-- **And the slot-level skip transports**, which is what the repair was
for. Blockers stay blockers: a voting-round block referencing no
candidate of the old slot references none of the new one either, since a
candidate the band already had is a candidate at either end and a
candidate it did not have is referenced by no old block. -/
theorem directSkipSlotIn_band (h : AgreeBand (hybridRule (Payload := Payload) k) U U' lo hi g g')
    {S S' : Slots Validator}
    {V : View Validator BlockId Payload U.val} {V' : View Validator BlockId Payload U'.val}
    {s s' : ℕ} (hkk : S.slotRound s + g = S'.slotRound s' + g')
    (hlead : S.leader s = S'.leader s') (hlo : lo = S.slotRound s + g)
    (hhi : S.slotRound s + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.val.block b).round + g →
      (U.val.block b).round + g ≤ hi → b ∈ V'.ids)
    (hs : Hybrid.DirectSkipSlotIn (S := S) U.val V s) :
    Hybrid.DirectSkipSlotIn (S := S') U'.val V' s' := by
  unfold Hybrid.DirectSkipSlotIn at hs ⊢
  refine le_trans hs (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  simp only [Hybrid.slotBlamers, Finset.mem_filter] at hqf
  obtain ⟨hqA, hqn⟩ := hqf
  have hqU : q ∈ U.val.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.val.block q).round = S.slotRound s + 1 := (mem_blocksAt.mp hqA).2
  refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
  · simp only [Finset.mem_inter, Hybrid.slotBlamers, Finset.mem_filter]
    refine ⟨⟨MysticetiProperties.blocksAt_band (toCore h) (by omega) (by omega) (by omega) hqA,
      ?_⟩, hV q hqV (by omega) (by omega)⟩
    rw [MysticetiProperties.band_refs (toCore h) hqU (by omega) (by omega)]
    intro j hj hjL
    have hjU : j ∈ U.val.ids := U.val.complete q hqU j hj
    exact hqn j hj (MysticetiProperties.isLeaderBlock_band_old (toCore h) hkk hlead
      (by omega) (by omega) hjU hjL)
  · rw [(MysticetiProperties.band_block (toCore h) hqU (by omega) (by omega)).2]; exact hvq

end Band

theorem banded_aux [S : Slots Validator] {kt : ℕ}
    {U : {U : BlockUniverse Validator BlockId Payload // HonestNoEquiv U}}
    {V : View Validator BlockId Payload U.val} {k : ℕ} {v : Option BlockId}
    (hpos : 0 < kt) (hd : Hybrid.Decided kt U.val V k v) :
    ∃ top, S.slotRound k + 1 ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : Slots Validator)
        (U' : {U : BlockUniverse Validator BlockId Payload // HonestNoEquiv U})
        (V' : View Validator BlockId Payload U'.val) (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand (hybridRule (Payload := Payload) kt) U U'
          (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.val.block b).round →
          (U.val.block b).round ≤ top → b ∈ V'.ids) →
        Hybrid.Decided (S := S') kt U'.val V' k' v := by
  classical
  induction hd with
  | @directCommit k L hL hc =>
      refine ⟨S.slotRound k + 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine Hybrid.Decided.directCommit (S := S')
        (MysticetiProperties.isLeaderBlock_band (toCore hab) hkk hlk (by omega) (by omega) hL) ?_
      exact directCommitIn_band hab hkk (by omega) (by omega)
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hc
  | @directSkip k hs =>
      refine ⟨S.slotRound k + 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact Hybrid.Decided.directSkip (S := S')
        (directSkipSlotIn_band hab hkk hlk rfl (by omega)
          (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hs)
  | @indirectCommit k j A L hkj helig hanchor hmid hL ht hmin ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Hybrid.Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U.val j A := Hybrid.isLeaderBlock_of_decided (k := kt) hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Hybrid.Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold Hybrid.Eligible Hybrid.decisionRound at helig'
      have htopk : S.slotRound k + 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.val.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.val.block A).round + g := by rw [hAL.2.1]; omega
      refine Hybrid.Decided.indirectCommit (S := S') (by omega) (by
          unfold Hybrid.Eligible Hybrid.decisionRound; omega)
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
        have helg : Hybrid.Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold Hybrid.Eligible Hybrid.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · exact (thickLink_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mpr ht
      · intro L' hL' ht'
        by_cases hLo : L' ∈ U.val.ids
        · exact hmin L' (MysticetiProperties.isLeaderBlock_band_old (toCore hab) hkk hlk
            (by omega) (by omega) hLo hL')
            ((thickLink_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mp ht')
        · exact absurd ht' (not_thickLink_band_novel hab hAL.1 hAlo hAhi hkk
            (by omega) (by omega) hLo hpos)
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ Hybrid.Eligible Validator k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U.val j A := Hybrid.isLeaderBlock_of_decided (k := kt) hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : Hybrid.Eligible Validator k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold Hybrid.Eligible Hybrid.decisionRound at helig'
      have htopk : S.slotRound k + 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.val.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.val.block A).round + g := by rw [hAL.2.1]; omega
      refine Hybrid.Decided.indirectSkip (S := S') (by omega) (by
          unfold Hybrid.Eligible Hybrid.decisionRound; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : Hybrid.Eligible Validator (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold Hybrid.Eligible Hybrid.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · intro L hL' ht'
        by_cases hLo : L ∈ U.val.ids
        · exact hnone L (MysticetiProperties.isLeaderBlock_band_old (toCore hab) hkk hlk
            (by omega) (by omega) hLo hL')
            ((thickLink_band hab hAL.1 hAlo hAhi hkk (by omega) (by omega)).mp ht')
        · exact not_thickLink_band_novel hab hAL.1 hAlo hAhi hkk
            (by omega) (by omega) hLo hpos ht'

/-- **Hybrid reads a band**, at every threshold the committee admits. -/
theorem banded {kt : ℕ} (hpos : 0 < kt) :
    Banded (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := S) hpos hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' U' V' k' hkd hsch hlead hab hV⟩



/-! ## The two liveness properties, and the skip -/

/-- **Hybrid skips an unsupported slot from a hybrid quorum.**

The liveness half of the repair, and the reason to believe it was a
repair rather than a tightening: making the skip a count of blockers
made it strictly harder to satisfy, and a rule no quorum can trigger
would be sound and useless. This says the repaired rule is still
reachable — a set meeting the hybrid quorum whose voting-round blocks
reference no candidate skips the slot, with no anchor and no synchrony.

The blamer set is the core's shape, so the containment argument is the
core's; only the threshold differs. -/
theorem skipsUnsupported (kt : ℕ) :
    SkipsUnsupported (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) (fun T => Hybrid.q Validator ≤ T.card) := by
  intro S U V T k hq hpres huns
  refine Hybrid.Decided.directSkip (S := S) (le_trans hq (Finset.card_le_card ?_))
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
  have hcU : c ∈ U.val.ids := V.subset_ids hcV
  refine Finset.mem_image.mpr ⟨c, ?_, hcc⟩
  rw [Finset.mem_inter, Hybrid.slotBlamers, Finset.mem_filter]
  exact ⟨⟨mem_blocksAt.mpr ⟨hcU, hcr⟩,
    fun j hj hjL => huns c hcV (by rw [hcc]; exact hv) hcr j hjL hj⟩, hcV⟩


/-- **Hybrid's liveness precondition**, over a slot window, at the
hybrid quorum `q = n − fb − fc` and a wavelength of two. -/
def hybridLive (S : Slots Validator)
    {U : {U : BlockUniverse Validator BlockId Payload // HonestNoEquiv U}}
    (V : View Validator BlockId Payload U.val) (T : Finset Validator) (lo K : ℕ) : Prop :=
  Hybrid.q Validator ≤ T.card ∧
    ∃ R₀ N, SynchronisedOn U.val T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U.val T r) ∧ V.CoversUpto N ∧
      ∀ k, k < K → S.slotRound k + 1 ≤ N

/-- **A reliably-led slot commits**, at a bound one above the slot. -/
theorem leaderCommits (kt : ℕ) :
    LeaderCommits (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) (fun S {U} V T lo K => hybridLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := hlive
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk := hN k hK
  obtain ⟨L, hL, hdc⟩ := Hybrid.directCommit_of_leader_mem (S := S) (U := U.val) hcard hs hRk
    (hpop _ hRk (by omega)) (hpop _ (by omega) (by omega)) hlead
  have hin : Hybrid.DirectCommitIn U.val V L (S.slotRound k) :=
    Hybrid.directCommitIn_of_coversUpto hdc (hcov.mono hNk)
  refine ⟨L, by omega, Hybrid.Decided.directCommit hL hin, ?_⟩
  intro S' hround hlead'
  obtain ⟨hm, hr, hcr⟩ := hL
  refine Hybrid.Decided.directCommit (S := S') ⟨hm, by rw [hround]; exact hr,
    by rw [hlead' k (by omega)]; exact hcr⟩ ?_
  rw [hround]; exact hin

/-- **H-A3 as a property.** The two indirect constructors, by cases on a
thick-linked candidate at the slot, committing the least one. -/
theorem indirect (kt : ℕ) :
    Indirect (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) (fun sr i j => sr i + 2 ≤ sr j) := by
  classical
  intro S U V i j A helig hj hmid
  letI := S
  have he : Hybrid.Eligible Validator i j := Hybrid.eligible_iff.mpr helig
  have hlt : i < j := Hybrid.lt_of_eligible he
  have heligS : ∀ (S' : Slots Validator), S'.slotRound = S.slotRound →
      ∀ x y, Hybrid.Eligible Validator (S := S') x y ↔
        Hybrid.Eligible Validator (S := S) x y := by
    intro S' hround x y
    simp only [Hybrid.Eligible, Hybrid.decisionRound, hround]
  by_cases hc : ∃ L, IsLeaderBlock U.val i L ∧
      Hybrid.ThickLink kt U.val A L (S.slotRound i)
  · have hCne : (U.val.ids.filter fun L => IsLeaderBlock U.val i L ∧
        Hybrid.ThickLink kt U.val A L (S.slotRound i)).Nonempty := by
      obtain ⟨L, hL, ht⟩ := hc
      exact ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩
    set Lm := (U.val.ids.filter fun L => IsLeaderBlock U.val i L ∧
      Hybrid.ThickLink kt U.val A L (S.slotRound i)).min' hCne with hLm
    have hmem := Finset.min'_mem _ hCne
    rw [Finset.mem_filter] at hmem
    have hminS : ∀ L', IsLeaderBlock U.val i L' →
        Hybrid.ThickLink kt U.val A L' (S.slotRound i) → ¬ L' < Lm := by
      intro L' hL' ht' hlt'
      exact absurd hlt' (not_lt.mpr (Finset.min'_le _ L'
        (Finset.mem_filter.mpr ⟨hL'.1, hL', ht'⟩)))
    refine ⟨some Lm, fun S' hround hlead hj' hmid' => ?_⟩
    have hLm' : IsLeaderBlock (S := S') U.val i Lm := by
      obtain ⟨hm, hr, hcr⟩ := hmem.2.1
      exact ⟨hm, by rw [hround]; exact hr, by rw [hlead]; exact hcr⟩
    refine Hybrid.Decided.indirectCommit (S := S') hlt
      ((heligS S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2
        (Hybrid.eligible_iff (S := S) |>.mp ((heligS S' hround i i').mp h3)))
      hLm' (by rw [hround]; exact hmem.2.2) ?_
    intro L' hL' ht'
    refine hminS L' ?_ (by rw [← hround]; exact ht')
    obtain ⟨hm, hr, hcr⟩ := hL'
    exact ⟨hm, by rw [← hround]; exact hr, by rw [← hlead]; exact hcr⟩
  · push Not at hc
    refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
    refine Hybrid.Decided.indirectSkip (S := S') hlt
      ((heligS S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2
        (Hybrid.eligible_iff (S := S) |>.mp ((heligS S' hround i i').mp h3))) ?_
    intro L hL'
    obtain ⟨hm, hr, hcr⟩ := hL'
    have hLS : IsLeaderBlock (S := S) U.val i L :=
      ⟨hm, by rw [← hround]; exact hr, by rw [← hlead]; exact hcr⟩
    have hnt := hc L hLS
    show ¬ Hybrid.ThickLink kt U.val A L (S'.slotRound i)
    rw [hround]; exact hnt

/-- **And a committed run decides everything below it.** -/
theorem descends {kt : ℕ} {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : Hybrid.SpansEligible (Validator := Validator) (S := S) c) :
    Descends (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) S c :=
  Descends.of_indirect (indirect kt) hc
    (fun b i hi => Hybrid.eligible_iff.mp (hspans b i hi))

end HybridProperties

end LeanDag
