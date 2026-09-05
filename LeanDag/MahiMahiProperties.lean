import LeanDag.MahiMahi.Carrier
import LeanDag.MysticetiProperties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.FromBand
import LeanDag.Properties.Commit
import LeanDag.MahiMahi.Helpers.Liveness
import LeanDag.MahiMahi.Helpers.Synchrony
import LeanDag.Properties.Live

/-!
# Mahi-Mahi's band, and the two liveness properties

`docs/target-properties.md` §3.4c said this band was *reachable* under
`2 ≤ w` and nobody had reached it. What was in the way was a note —
"needs a carrier per width" — that Hybrid had already answered and
nobody re-read (`MahiMahi/Carrier.lean`).

**Mahi-Mahi shares the core's block vocabulary**, so the core's band
lemmas apply once the carriers are identified, which `toCore` does by
the three fields. What is Mahi-Mahi's own is that every rule reads a
*cone*: a vote is the least block of its author and round in the voting
block's causal history, and a blame is the absence of any such block.
`MahiMahi.candidatesAt` is where that lands, and it is the one transport this
file has to prove; everything above it follows.

**The wave rounds truncate, and `2 ≤ w` is what repairs them.**
`votingRound w r = r + w - 2` and `decisionRoundAt w r = r + w - 1` are
`ℕ` subtractions, so `(r + g) + w - 2 = (r + w - 2) + g` needs
`2 ≤ r + w`. Every hypothesis below carries `2 ≤ w`, and every
Mahi-Mahi theorem already carries `3 ≤ w` or more, so it costs no
consumer anything.
-/

namespace LeanDag

namespace MahiMahiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U U' : BlockUniverse Validator BlockId Payload} {lo hi g g' w : ℕ}

/-! ## The band, across a shifted universe -/

/-- The two carriers project identically, so a band for one is a band
for the other. -/
theorem toCore (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g') :
    AgreeBand (MysticetiProperties.mysticetiRule (Payload := Payload)) U U' lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **The candidates a block's cone holds at a round are the ones it
held.** Both inclusions: a block inside an old cone at a band round is
old, by `reaches_old`, and an old one stays inside it, by `reaches_of`.
This is the transport every Mahi-Mahi rule rests on — votes, blames,
certificates and the indirect test all read this set. -/
theorem candidatesAt_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    {q : BlockId} (hq : q ∈ U.ids) (hqlo : lo ≤ (U.block q).round + g)
    (hqhi : (U.block q).round + g ≤ hi) {a : Validator} {r r' : ℕ}
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + g ≤ hi) :
    MahiMahi.candidatesAt U' q a r' = MahiMahi.candidatesAt U q a r := by
  have hq' : q ∈ U'.ids := MysticetiProperties.band_mem (toCore h) hq hqlo hqhi
  ext b
  simp only [MahiMahi.candidatesAt, Finset.mem_filter, mem_blocksAt]
  constructor
  · rintro ⟨⟨hbU', hbr'⟩, hba, hbh⟩
    have hbre : ReachesFrom U'.block q b := (mem_history_iff (U := U') hq').mp hbh
    obtain ⟨hbU, hbreU, hbeq⟩ :=
      AgreeBand.reaches_old MysticetiProperties.causal (toCore h) hq hqlo hqhi hbre
        (by show lo ≤ (U'.block b).round + g'; omega)
    have hbeq' : (U.block b).round + g = (U'.block b).round + g' := hbeq
    have hbb := MysticetiProperties.band_block (toCore h) hbU (by omega) (by omega)
    exact ⟨⟨hbU, by omega⟩, by rw [← hbb.2]; exact hba,
      (mem_history_iff (U := U) hq).mpr hbreU⟩
  · rintro ⟨⟨hbU, hbr⟩, hba, hbh⟩
    have hbre : ReachesFrom U.block q b := (mem_history_iff (U := U) hq).mp hbh
    have hbb := MysticetiProperties.band_block (toCore h) hbU (by omega) (by omega)
    refine ⟨⟨MysticetiProperties.band_mem (toCore h) hbU (by omega) (by omega), by omega⟩,
      by rw [hbb.2]; exact hba, ?_⟩
    exact (mem_history_iff (U := U') hq').mpr
      (AgreeBand.reaches_of MysticetiProperties.causal (toCore h) hq hqhi hbre
        (by show lo ≤ (U.block b).round + g; omega))

/-- **A vote is the vote it was.** Both clauses read the same cone, and
`candidatesAt_band` settles it as an equality rather than a
containment. -/
theorem votes_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    {q : BlockId} (hq : q ∈ U.ids) (hqlo : lo ≤ (U.block q).round + g)
    (hqhi : (U.block q).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g)
    (hLhi : (U.block L).round + g ≤ hi) :
    MahiMahi.Votes U' q L ↔ MahiMahi.Votes U q L := by
  have hLb := MysticetiProperties.band_block (toCore h) hL hLlo hLhi
  have hset : MahiMahi.candidatesAt U' q (U'.block L).creator (U'.block L).round
      = MahiMahi.candidatesAt U q (U.block L).creator (U.block L).round := by
    rw [hLb.2]
    exact candidatesAt_band h hq hqlo hqhi (by omega) hLlo hLhi
  unfold MahiMahi.Votes
  rw [hset]

/-- **And a blame is the blame it was.** The skip rule reads a *cone*
rather than the universe's candidates, and a cone is settled by the band
in both directions — so the shape `docs/target-properties.md` §3.2
recorded as a defect, a negative clause a larger DAG can falsify, does
not arise here at all. A candidate the band added is in no old block's
history. -/
theorem blames_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    {q : BlockId} (hq : q ∈ U.ids) (hqlo : lo ≤ (U.block q).round + g)
    (hqhi : (U.block q).round + g ≤ hi) {a : Validator} {r r' : ℕ}
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + g ≤ hi) :
    MahiMahi.Blames U' q a r' ↔ MahiMahi.Blames U q a r := by
  unfold MahiMahi.Blames
  rw [candidatesAt_band h hq hqlo hqhi hrr hr hhi]

/-- **A certificate certifies what it certified.** Its votes are cast by
its own references, one round below it, and each of those reads a cone
the band settles. -/
theorem certifies_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    {C : BlockId} (hC : C ∈ U.ids) (hClo : lo < (U.block C).round + g)
    (hChi : (U.block C).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g)
    (hLhi : (U.block L).round + g ≤ hi) :
    MahiMahi.Certifies U' C L ↔ MahiMahi.Certifies U C L := by
  have hq : ∀ q ∈ (U.block C).refs, q ∈ U.ids ∧ (U.block q).round + 1 = (U.block C).round :=
    fun q hqm => ⟨U.complete C hC q hqm, U.round_of_mem_refs hC hqm⟩
  have hset : MahiMahi.votesIn U' C L = MahiMahi.votesIn U C L := by
    unfold MahiMahi.votesIn
    rw [MysticetiProperties.band_refs (toCore h) hC hClo hChi]
    refine Finset.filter_congr fun q hqm => ?_
    exact votes_band h (hq q hqm).1 (by have := (hq q hqm).2; omega)
      (by have := (hq q hqm).2; omega) hL hLlo hLhi
  unfold MahiMahi.Certifies
  rw [hset, MysticetiProperties.creatorsOf_band (toCore h)]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  exact ⟨(hq b hbp).1, by have := (hq b hbp).2; omega, by have := (hq b hbp).2; omega⟩

/-! ## The direct rules

Forward only, as everywhere: a band may add blocks, and a quorum that
was met is met still. The skip needs no separate argument for a
candidate the band added, `blames_band` being an equivalence. -/

/-- Certificates survive the band. -/
theorem certificates_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    (hw : 2 ≤ w) {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ}
    (hLr : (U.block L).round = r) (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + w - 1 + g ≤ hi) :
    MahiMahi.certificates U w L r ⊆ MahiMahi.certificates U' w L r' := by
  intro C hC
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCU : C ∈ U.ids := (mem_blocksAt.mp hCA).1
  have hCr : (U.block C).round = MahiMahi.decisionRoundAt w r := (mem_blocksAt.mp hCA).2
  have hdr : MahiMahi.decisionRoundAt w r = r + w - 1 := rfl
  have hdr' : MahiMahi.decisionRoundAt w r' = r' + w - 1 := rfl
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact MysticetiProperties.blocksAt_band (toCore h) (by omega) (by omega) (by omega) hCA
  · exact (certifies_band h hCU (by omega) (by omega) hL (by omega) (by omega)).mpr hCc

/-- **And so does the direct commit.** -/
theorem directCommitIn_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    (hw : 2 ≤ w) {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ}
    (hLr : (U.block L).round = r) (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + w - 1 + g ≤ hi) (hc : MahiMahi.DirectCommitIn U V w L r) :
    MahiMahi.DirectCommitIn U' V' w L r' := by
  refine le_trans hc (Finset.card_le_card ?_)
  intro a ha
  obtain ⟨C, hC, hCa⟩ := Finset.mem_image.mp ha
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCU : C ∈ U.ids := (mem_blocksAt.mp (Finset.mem_filter.mp hCc).1).1
  have hCr : (U.block C).round = MahiMahi.decisionRoundAt w r :=
    (mem_blocksAt.mp (Finset.mem_filter.mp hCc).1).2
  have hdr : MahiMahi.decisionRoundAt w r = r + w - 1 := rfl
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨certificates_band h hw hL hLr hrr hr hhi hCc, hV C hCV (by omega) (by omega)⟩, ?_⟩
  rw [(MysticetiProperties.band_block (toCore h) hCU (by omega) (by omega)).2]; exact hCa

/-- **And the direct skip.** A blamer stays a blamer, and a candidate
the band added changes nothing: the blame reads the blamer's cone, which
the band settles both ways. -/
theorem directSkipIn_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    (hw : 2 ≤ w) {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {a : Validator} {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + w - 2 + g ≤ hi) (hs : MahiMahi.DirectSkipIn U V w a r) :
    MahiMahi.DirectSkipIn U' V' w a r' := by
  refine le_trans hs (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqb⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.block q).round = MahiMahi.votingRound w r := (mem_blocksAt.mp hqA).2
  have hvr : MahiMahi.votingRound w r = r + w - 2 := rfl
  have hvr' : MahiMahi.votingRound w r' = r' + w - 2 := rfl
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨MysticetiProperties.blocksAt_band (toCore h) (by omega) (by omega) (by omega) hqA, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · exact (blames_band h hqU (by omega) (by omega) hrr hr (by omega)).mpr hqb
  · rw [(MysticetiProperties.band_block (toCore h) hqU (by omega) (by omega)).2]; exact hqv

/-! ## The anchored test

Both directions, and the clause a one-directional band forces: a
candidate the band did not carry is certified from no old anchor,
because the certificate would have to lie in the anchor's cone and an
old cone holds only old blocks. -/

theorem certifiedIn_band (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    (hw : 2 ≤ w) {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ} (hLr : (U.block L).round = r)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + w - 1 + g ≤ hi) :
    MahiMahi.CertifiedIn U' w A L r' ↔ MahiMahi.CertifiedIn U w A L r := by
  have hA' : A ∈ U'.ids := MysticetiProperties.band_mem (toCore h) hA hAlo hAhi
  have hdr : MahiMahi.decisionRoundAt w r = r + w - 1 := rfl
  have hdr' : MahiMahi.decisionRoundAt w r' = r' + w - 1 := rfl
  constructor
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
    have hCr' : (U'.block C).round = r' + w - 1 := by
      have := (mem_blocksAt.mp hCA).2; omega
    obtain ⟨hCU, hreU, hCeq⟩ :=
      AgreeBand.reaches_old MysticetiProperties.causal (toCore h) hA hAlo hAhi hre
        (by show lo ≤ (U'.block C).round + g'; omega)
    have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
    exact ⟨C, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hCU, by omega⟩,
      (certifies_band h hCU (by omega) (by omega) hL (by omega) (by omega)).mp hCc⟩, hreU⟩
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
    have hCU : C ∈ U.ids := (mem_blocksAt.mp hCA).1
    have hCr : (U.block C).round = r + w - 1 := by have := (mem_blocksAt.mp hCA).2; omega
    exact ⟨C, certificates_band h hw hL hLr hrr hr hhi hC,
      AgreeBand.reaches_of MysticetiProperties.causal (toCore h) hA hAhi hre
        (by show lo ≤ (U.block C).round + g; omega)⟩

theorem not_certifiedIn_band_novel
    (h : AgreeBand (mahiMahiRule (Payload := Payload) w) U U' lo hi g g')
    (hw : 2 ≤ w) {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    {L : BlockId} (hLo : L ∉ U.ids) {r r' : ℕ} (hLr : (U'.block L).round = r')
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + w - 1 + g ≤ hi) :
    ¬ MahiMahi.CertifiedIn U' w A L r' := by
  rintro ⟨C, hC, hre⟩
  have hdr' : MahiMahi.decisionRoundAt w r' = r' + w - 1 := rfl
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCr' : (U'.block C).round = r' + w - 1 := by have := (mem_blocksAt.mp hCA).2; omega
  obtain ⟨hCU, -, hCeq⟩ :=
    AgreeBand.reaches_old MysticetiProperties.causal (toCore h) hA hAlo hAhi hre
      (by show lo ≤ (U'.block C).round + g'; omega)
  have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
  have hCround : (U.block C).round = r + w - 1 := by omega
  -- the quorum is positive, so some old reference of `C` votes for `L`
  have hpos : 0 < (MahiMahi.votesIn U' C L).card := by
    have hq := MysticetiProperties.quorumCard_pos (Validator := Validator)
    have hcard : (creatorsOf U'.block (MahiMahi.votesIn U' C L)).card
        ≤ (MahiMahi.votesIn U' C L).card := Finset.card_image_le
    have hcc := hCc
    unfold MahiMahi.Certifies at hcc
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
  obtain ⟨hqm, hqv⟩ := Finset.mem_filter.mp hq
  rw [MysticetiProperties.band_refs (toCore h) hCU
    (by show lo < (U.block C).round + g; omega)
    (by show (U.block C).round + g ≤ hi; omega)] at hqm
  have hqU : q ∈ U.ids := U.complete C hCU q hqm
  have hqr : (U.block q).round + 1 = (U.block C).round := U.round_of_mem_refs hCU hqm
  have hq' : q ∈ U'.ids := MysticetiProperties.band_mem (toCore h) hqU
    (by show lo ≤ (U.block q).round + g; omega)
    (by show (U.block q).round + g ≤ hi; omega)
  -- `L` is in an old block's cone, so `L` is old
  have hLh : L ∈ history U' q := (Finset.mem_filter.mp hqv.1).2.2
  obtain ⟨hLU, -, -⟩ :=
    AgreeBand.reaches_old MysticetiProperties.causal (toCore h) hqU
      (by show lo ≤ (U.block q).round + g; omega)
      (by show (U.block q).round + g ≤ hi; omega)
      ((mem_history_iff (U := U') hq').mp hLh) (by show lo ≤ (U'.block L).round + g'; omega)
  exact hLo hLU

/-! ## The band a verdict reads

One induction, four cases. The direct cases read to the decision round
`slotRound k + w − 1` and stop; the indirect cases read their anchor's
derivation and the intermediates', and the top is the largest of those.

`2 ≤ w` is the whole of what `docs/target-properties.md` §3.4c said
this band needed, and it enters
exactly where the truncated wave rounds do. Nothing here supposes the
larger universe adds no candidates: where one appears the anchor cannot
see it (`not_certifiedIn_band_novel`), and the slot-level skip does not
look for it at all — it reads the blamers' cones, which the band settles
both ways. -/
theorem banded_aux [S : Slots Validator] (hw : 2 ≤ w)
    {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (hd : MahiMahi.Decided w U V k v) :
    ∃ top, S.slotRound k + w - 1 ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : Slots Validator)
        (U' : BlockUniverse Validator BlockId Payload)
        (V' : View Validator BlockId Payload U') (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand (mahiMahiRule (Payload := Payload) w) U U'
          (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        MahiMahi.Decided (S := S') w U' V' k' v := by
  classical
  induction hd with
  | @directCommit k L hL hc =>
      refine ⟨S.slotRound k + w - 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine MahiMahi.Decided.directCommit (S := S')
        (MysticetiProperties.isLeaderBlock_band (toCore hab) hkk hlk (by omega) (by omega) hL) ?_
      exact directCommitIn_band hab hw
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hL.1 hL.2.1 hkk (by omega) (by omega) hc
  | @directSkip k hs =>
      refine ⟨S.slotRound k + w - 1, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      refine MahiMahi.Decided.directSkip (S := S') ?_
      rw [← hlk]
      exact directSkipIn_band hab hw (fun b hb h1 h2 => hV b hb (by omega) (by omega))
        hkk (by omega) (by omega) hs
  | @indirectCommit k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ MahiMahi.Eligible Validator w k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U j A := MahiMahi.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : MahiMahi.Eligible Validator w k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold MahiMahi.Eligible MahiMahi.decisionRound at helig'
      have htopk : S.slotRound k + w - 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      have hanch := hjt g g' d d' S' U' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          MahiMahi.Eligible Validator w (S := S') k' i' →
          MahiMahi.Decided (S := S') w U' V' i' none := by
        intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : MahiMahi.Eligible Validator w (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold MahiMahi.Eligible MahiMahi.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have helig'' : MahiMahi.Eligible Validator w (S := S') k' (j - k + k') := by
        unfold MahiMahi.Eligible MahiMahi.decisionRound; omega
      exact MahiMahi.Decided.indirectCommit (S := S') (by omega) helig'' hanch hmid'
        (MysticetiProperties.isLeaderBlock_band (toCore hab) hkk hlk (by omega) (by omega) hL)
        ((certifiedIn_band hab hw hAL.1 hAlo hAhi hL.1 hL.2.1 hkk (by omega) (by omega)).mpr hcert)
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun i =>
        if hh : k < i ∧ i < j ∧ MahiMahi.Eligible Validator w k i then
          (ihmid i hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hkj' : S.slotRound k ≤ S.slotRound j := S.mono (le_of_lt hkj)
      have hAL : IsLeaderBlock U j A := MahiMahi.isLeaderBlock_of_decided hanchor
      have hkey : ∀ i (h1 : k < i) (h2 : i < j) (h3 : MahiMahi.Eligible Validator w k i),
          (ihmid i h1 h2 h3).choose ≤ top := by
        intro i h1 h2 h3
        have heqf : f i = (ihmid i h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := helig
      unfold MahiMahi.Eligible MahiMahi.decisionRound at helig'
      have htopk : S.slotRound k + w - 1 ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' := hsch j _ hjd
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      have hanch := hjt g g' d d' S' U' V' (j - k + k') hjd hsch
        (fun m m' hm hb => hlead m m' hm (by omega))
        (hab.mono (by omega) (by omega))
        (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      have hmid' : ∀ i', k' < i' → i' < j - k + k' →
          MahiMahi.Eligible Validator w (S := S') k' i' →
          MahiMahi.Decided (S := S') w U' V' i' none := by
        intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : MahiMahi.Eligible Validator w (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
          have := h3
          unfold MahiMahi.Eligible MahiMahi.decisionRound at this ⊢; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd hsch
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      have helig'' : MahiMahi.Eligible Validator w (S := S') k' (j - k + k') := by
        unfold MahiMahi.Eligible MahiMahi.decisionRound; omega
      refine MahiMahi.Decided.indirectSkip (S := S') (by omega) helig'' hanch hmid' ?_
      intro L' hL' hc'
      by_cases hLo : L' ∈ U.ids
      · exact hnone L' (MysticetiProperties.isLeaderBlock_band_old (toCore hab) hkk hlk
          (by omega) (by omega) hLo hL')
          ((certifiedIn_band hab hw hAL.1 hAlo hAhi hLo
            (by
              have := MysticetiProperties.isLeaderBlock_band_old (toCore hab) hkk hlk
                (by omega) (by omega) hLo hL'
              exact this.2.1)
            hkk (by omega) (by omega)).mp hc')
      · exact absurd hc' (not_certifiedIn_band_novel hab hw hAL.1 hAlo hAhi hLo hL'.2.1
          hkk (by omega) (by omega))


/-- **Mahi-Mahi reads a band**, at every width its rules are stated
for. -/
theorem banded (hw : 2 ≤ w) :
    Banded (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux (S := S) hw hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' U' V' k' hkd hsch hlead hab hV⟩

/-! ## The two liveness properties

`Descends` is not among them: it follows from `Indirect` by the generic
induction of `Properties/Derived/Descent.lean`.

**What Mahi-Mahi's precondition is, and why it is not the conclusion.**
Every other rule here takes synchrony and population and *derives* a
direct commit; Mahi-Mahi's liveness arc takes the direct commit as given
— `MM3a` is "if the slot's leader is in `good`, it commits" — and gets
its unpredictability results from there. `good U w k` is a fact about
the DAG, a quorum of certificates at the decision round, and says
nothing about verdicts. What `LeaderCommits` adds to it is the **bound**:
the verdict survives any reassignment of the leaders of other slots,
which is what a schedule mechanism reads and what MM3a does not
state. -/

/-- A view caught up to the decision round holds every certificate,
so it commits what the DAG commits. -/
theorem directCommitIn_of_coversUpto {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {w : ℕ} {L : BlockId} {r : ℕ}
    (h : MahiMahi.DirectCommit U w L r) (hV : V.CoversUpto (MahiMahi.decisionRoundAt w r)) :
    MahiMahi.DirectCommitIn U V w L r := by
  refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
  intro C hC
  obtain ⟨hCU, hCr, -⟩ := MahiMahi.mem_certificates.mp hC
  exact Finset.mem_inter.mpr ⟨hC, hV C hCU (by omega)⟩

/-- **Mahi-Mahi's liveness precondition**, over a slot window: the view
is caught up to a horizon the window's decision rounds sit under, and
every `T`-led slot of the window has a good leader. -/
def mahiLive (w : ℕ) (S : Slots Validator)
    {U : BlockUniverse Validator BlockId Payload} (V : View Validator BlockId Payload U)
    (T : Finset Validator) (lo K : ℕ) : Prop :=
  ∃ N, (∀ k, k < K → MahiMahi.decisionRound Validator w k ≤ N) ∧ V.CoversUpto N ∧
    ∀ k, lo ≤ k → k < K → S.leader k ∈ T → S.leader k ∈ MahiMahi.good (S := S) U w k

/-- **Mahi-Mahi's precondition is reachable** (`Properties/Live.lean`),
and here the guard is not a formality. `mahiLive` asks that the slot's
leader be **good** — that its block already carries a direct commit —
which is close to the conclusion `LeaderCommits` draws, so the property
alone says little until this is proved. `MM5a`
(`good_of_synchronisedOn`) is what proves it: a reliable leader on a
synchronised, populated DAG is good, and the counting is the wave's.

The wavelength is `w − 1`, which is `decisionRound` measured from the
slot's round. -/
theorem liveReachable {w : ℕ} (hw : 4 ≤ w) :
    LiveReachable (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (coreReliability Validator) (w - 1)
      (fun S {U} V T lo K => mahiLive w S (U := U) V T lo K) := by
  intro U Rnd N hs hpop S V k hcov hRnd hN
  letI : Slots Validator := S
  have hdr : MahiMahi.decisionRound Validator w k = S.slotRound k + w - 1 := rfl
  have hdN : MahiMahi.decisionRound Validator w k ≤ N := by rw [hdr]; omega
  refine ⟨N, ?_, hcov, ?_⟩
  · intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    show S.slotRound j + w - 1 ≤ N
    omega
  · intro j hlo hj hlead
    have hjk : j = k := by omega
    subst hjk
    exact MahiMahi.good_of_synchronisedOn hw Finset.Subset.rfl card_correct hs hRnd
      (hpop _ hRnd (by omega)) (hpop _ (by omega) (by omega))
      (hpop _ (by rw [hdr]; omega) hdN) hlead

/-- **A good leader's slot commits**, at a bound one above the slot:
the commit reads that slot's round and leader and no others. -/
theorem leaderCommits (w : ℕ) :
    LeaderCommits (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
      (fun S {U} V T lo K => mahiLive w S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨N, hN, hcov, hgood⟩ := hlive
  have hg := hgood k hlo hK hlead
  unfold MahiMahi.good at hg
  rw [MahiMahi.mem_goodAt] at hg
  obtain ⟨L, hLU, hLr, hLc, hcommit⟩ := hg
  have hdr : MahiMahi.decisionRound Validator w k
      = MahiMahi.decisionRoundAt w (S.slotRound k) := rfl
  have hin : MahiMahi.DirectCommitIn U V w L (S.slotRound k) :=
    directCommitIn_of_coversUpto hcommit (hcov.mono (by rw [← hdr]; exact hN k hK))
  refine ⟨L, by omega, MahiMahi.Decided.directCommit ⟨hLU, hLr, hLc⟩ hin, ?_⟩
  intro S' hround hlead'
  refine MahiMahi.Decided.directCommit (S := S') ⟨hLU, ?_, ?_⟩ ?_
  · rw [hround]; exact hLr
  · rw [hlead' k (by omega)]; exact hLc
  · show MahiMahi.DirectCommitIn U V w L (S'.slotRound k)
    rw [hround]; exact hin

open Classical in
/-- **The indirect rule, with its bound.** The anchor is the committed
slot `j`; the eligible slots between are skipped, so `j` is the nearest.
The case split reads slot `i`'s candidates and the anchor's cone, and a
schedule naming the same leader at `i` and the same rounds changes
neither — which is the second quantifier.

Shorter than Odontoceti's by a clause: the indirect test is "a
certificate in the anchor's cone", and two certificates at one slot name
the same candidate, so there is no tie-break to preserve. -/
theorem indirect {w : ℕ} (hw : 1 ≤ w) :
    Indirect (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (fun sr i j => sr i + w ≤ sr j) := by
  classical
  intro S U V i j A helig hj hmid
  letI := S
  have he : MahiMahi.Eligible Validator w i j := by
    unfold MahiMahi.Eligible MahiMahi.decisionRound; omega
  have hlt : i < j := MahiMahi.lt_of_eligible hw he
  have heligS : ∀ (S' : Slots Validator), S'.slotRound = S.slotRound →
      ∀ x y, MahiMahi.Eligible Validator w (S := S') x y ↔
        MahiMahi.Eligible Validator w (S := S) x y := by
    intro S' hround x y
    simp only [MahiMahi.Eligible, MahiMahi.decisionRound, hround]
  have hback : ∀ x y, MahiMahi.Eligible Validator w (S := S) x y →
      S.slotRound x + w ≤ S.slotRound y := by
    intro x y hxy
    unfold MahiMahi.Eligible MahiMahi.decisionRound at hxy
    have := S.mono (le_of_lt (MahiMahi.lt_of_eligible hw hxy))
    omega
  by_cases hc : ∃ L, IsLeaderBlock U i L ∧ MahiMahi.CertifiedIn U w A L (S.slotRound i)
  · obtain ⟨L, hL, hcert⟩ := hc
    refine ⟨some L, fun S' hround hlead hj' hmid' => ?_⟩
    refine MahiMahi.Decided.indirectCommit (S := S') hlt ((heligS S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2 (hback i i' ((heligS S' hround i i').mp h3)))
      ?_ ?_
    · obtain ⟨hm, hr, hcr⟩ := hL
      exact ⟨hm, by rw [hround]; exact hr, by rw [hlead]; exact hcr⟩
    · show MahiMahi.CertifiedIn U w A L (S'.slotRound i)
      rw [hround]; exact hcert
  · push Not at hc
    refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
    refine MahiMahi.Decided.indirectSkip (S := S') hlt ((heligS S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2 (hback i i' ((heligS S' hround i i').mp h3))) ?_
    intro L hL'
    obtain ⟨hm, hr, hcr⟩ := hL'
    have hLS : IsLeaderBlock (S := S) U i L :=
      ⟨hm, by rw [← hround]; exact hr, by rw [← hlead]; exact hcr⟩
    show ¬ MahiMahi.CertifiedIn U w A L (S'.slotRound i)
    rw [hround]
    exact hc L hLS

end MahiMahiProperties

end LeanDag
