import LeanDag.SafeSkip.Basic
import LeanDag.Liveness

/-!
# Verdict invariance across the fill

The `decided_chop` analogue for extension rather than truncation: every
verdict a view reached before a Safe Skip fill re-derives, for the same
view, in the extension — and therefore agrees, by M6 in the extension,
with every verdict any view reaches after it (`decided_fill_agree`).

The proof rests on the fill's conservativity, sharpened to the rule
layer. Every set the four rules count — votes, certificates, blames —
is drawn from a view's blocks, all of them old, whose references the
fill preserves; and a *fresh* id can appear in none of those references,
so even for a fresh candidate the vote and certificate sets are empty on
**both** sides. The `*In` predicates are therefore equal across the
fill for every candidate (`certificatesIn_fill`, `blameSetIn_fill`), and
reachability from an old block never leaves the old ids
(`reaches_fill_old`).

One obligation is genuinely new. `Decided.directSkip` quantifies over
the universe's leader blocks, and the fill may create a candidate where
there was none: a filled block landing on a slot of the recovering
validator. The old verdict skipped that slot *vacuously*; the new
derivation must skip it by counting, and the count is supplied by the
one hypothesis of the theorem — the view holds a quorum of authors at
the round above each gap round (`hq`). This is not an artefact: a view
too sparse to blame the filled candidate genuinely cannot re-derive the
skip, and the hypothesis is exactly `directSkip_fresh`'s, relativised to
the view.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

namespace SkipMsg

variable (sk : SkipMsg U)

/-- A view of `U` is a view of the extension, unchanged: its blocks are
old, and old references are preserved. -/
def liftView (V : View Validator BlockId Payload U) :
    View Validator BlockId Payload sk.skipFill where
  ids := V.ids
  subset_ids := V.subset_ids.trans sk.ids_subset_skipFill
  complete := by
    intro i hi j hj
    rw [sk.skipFill_block_old (V.subset_ids hi)] at hj
    exact V.complete i hi j hj

@[simp] theorem liftView_ids (V : View Validator BlockId Payload U) :
    (sk.liftView V).ids = V.ids := rfl

/-- Creators read identically on old blocks. -/
theorem creatorsOf_fill {s : Finset BlockId} (hs : s ⊆ U.ids) :
    creatorsOf sk.skipFill.block s = creatorsOf U.block s := by
  unfold creatorsOf
  refine Finset.image_congr ?_
  intro b hb
  simp only
  rw [sk.skipFill_block_old (hs (Finset.mem_coe.mp hb))]

theorem votesIn_subset_ids {C L : BlockId} (hC : C ∈ U.ids) :
    votesIn U C L ⊆ U.ids := by
  intro q hq
  unfold votesIn at hq
  exact U.complete _ hC _ (Finset.mem_filter.mp hq).1

theorem certificatesIn_subset_ids (V : View Validator BlockId Payload U)
    {L : BlockId} {r : ℕ} : certificatesIn U V L r ⊆ U.ids := by
  intro C hC
  unfold certificatesIn at hC
  exact V.subset_ids (Finset.mem_inter.mp hC).2

theorem inter_view_subset_ids (V : View Validator BlockId Payload U)
    (s : Finset BlockId) : s ∩ V.ids ⊆ U.ids :=
  fun q hq => V.subset_ids (Finset.mem_inter.mp hq).2

/-- Votes read identically on old certificates — for *every* candidate:
an old block's references are preserved, and a fresh candidate lies in
none of them on either side. -/
theorem votesIn_fill {C L : BlockId} (hC : C ∈ U.ids) :
    votesIn sk.skipFill C L = votesIn U C L := by
  unfold votesIn
  rw [sk.skipFill_block_old hC]
  refine Finset.filter_congr ?_
  intro q hq
  rw [sk.skipFill_block_old (U.complete _ hC _ hq)]

theorem certifies_fill {C L : BlockId} (hC : C ∈ U.ids) :
    Certifies sk.skipFill C L ↔ Certifies U C L := by
  unfold Certifies
  rw [sk.votesIn_fill hC, sk.creatorsOf_fill (votesIn_subset_ids hC)]

/-- Certificates a view holds read identically — again for every
candidate. -/
theorem certificatesIn_fill (V : View Validator BlockId Payload U)
    {L : BlockId} {r : ℕ} :
    certificatesIn sk.skipFill (sk.liftView V) L r = certificatesIn U V L r := by
  unfold certificatesIn certificates
  ext C
  simp only [Finset.mem_inter, Finset.mem_filter, liftView_ids]
  constructor
  · rintro ⟨⟨hb, hc⟩, hV⟩
    have hCo := V.subset_ids hV
    rw [mem_blocksAt] at hb
    refine ⟨⟨mem_blocksAt.mpr ⟨hCo, ?_⟩, (sk.certifies_fill hCo).mp hc⟩, hV⟩
    rw [← sk.skipFill_block_old hCo]
    exact hb.2
  · rintro ⟨⟨hb, hc⟩, hV⟩
    have hCo := V.subset_ids hV
    rw [mem_blocksAt] at hb
    refine ⟨⟨mem_blocksAt.mpr ⟨sk.ids_subset_skipFill hCo, ?_⟩,
      (sk.certifies_fill hCo).mpr hc⟩, hV⟩
    rw [sk.skipFill_block_old hCo]
    exact hb.2

/-- The blocks a view holds that blame a candidate read identically —
for every candidate, a fresh id lying in no old reference set. -/
theorem blameSetIn_fill (V : View Validator BlockId Payload U)
    {L : BlockId} {r : ℕ} :
    ((blocksAt sk.skipFill (r + 1)).filter
        (fun q => L ∉ (sk.skipFill.block q).refs)) ∩ (sk.liftView V).ids =
      ((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids := by
  ext q
  simp only [Finset.mem_inter, Finset.mem_filter, liftView_ids]
  constructor
  · rintro ⟨⟨hb, hn⟩, hV⟩
    have hqo := V.subset_ids hV
    rw [mem_blocksAt] at hb
    rw [sk.skipFill_block_old hqo] at hb hn
    exact ⟨⟨mem_blocksAt.mpr ⟨hqo, hb.2⟩, hn⟩, hV⟩
  · rintro ⟨⟨hb, hn⟩, hV⟩
    have hqo := V.subset_ids hV
    rw [mem_blocksAt] at hb
    have hround' : (sk.skipFill.block q).round = r + 1 := by
      rw [sk.skipFill_block_old hqo]; exact hb.2
    have hn' : L ∉ (sk.skipFill.block q).refs := by
      rw [sk.skipFill_block_old hqo]; exact hn
    exact ⟨⟨mem_blocksAt.mpr ⟨sk.ids_subset_skipFill hqo, hround'⟩, hn'⟩, hV⟩

/-- Reachability from an old block never leaves the old ids, in either
universe, and coincides between them. -/
theorem reaches_fill_old {a b : BlockId} (ha : a ∈ U.ids) :
    Reaches sk.skipFill a b ↔ b ∈ U.ids ∧ Reaches U a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | tail _ hstep ih =>
        obtain ⟨hbo, hr⟩ := ih
        unfold RefStepFrom at hstep
        rw [sk.skipFill_block_old hbo] at hstep
        exact ⟨U.complete _ hbo _ hstep, hr.tail hstep⟩
  · rintro ⟨_, h⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hr hstep ih =>
        have hbo : b ∈ U.ids := by
          clear ih hstep
          induction hr with
          | refl => exact ha
          | @tail x y _ hstep' ih' => exact U.complete _ ih' _ hstep'
        refine (ih hbo).tail ?_
        unfold RefStepFrom
        rw [sk.skipFill_block_old hbo]
        exact hstep

/-- Certification transports both ways for an old anchor: any witness
certificate reached from it is itself old, and votes read identically. -/
theorem certifiedIn_fill {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) :
    CertifiedIn sk.skipFill A L r ↔ CertifiedIn U A L r := by
  unfold CertifiedIn certificates
  constructor
  · rintro ⟨C, hC, hreach⟩
    obtain ⟨hCo, hreach'⟩ := (sk.reaches_fill_old hA).mp hreach
    simp only [Finset.mem_filter] at hC
    rw [mem_blocksAt] at hC
    refine ⟨C, ?_, hreach'⟩
    simp only [Finset.mem_filter]
    rw [mem_blocksAt]
    rw [sk.skipFill_block_old hCo] at hC
    exact ⟨⟨hCo, hC.1.2⟩, (sk.certifies_fill hCo).mp hC.2⟩
  · rintro ⟨C, hC, hreach⟩
    simp only [Finset.mem_filter] at hC
    rw [mem_blocksAt] at hC
    have hCo := hC.1.1
    refine ⟨C, ?_, (sk.reaches_fill_old hA).mpr ⟨hCo, hreach⟩⟩
    simp only [Finset.mem_filter]
    rw [mem_blocksAt]
    refine ⟨⟨sk.ids_subset_skipFill hCo, ?_⟩, (sk.certifies_fill hCo).mpr hC.2⟩
    rw [sk.skipFill_block_old hCo]
    exact hC.1.2

/-- No old anchor certifies a fresh candidate: everything it reaches is
old, and no old reference contains a fresh id. -/
theorem not_certifiedIn_fresh {A : BlockId} {k r : ℕ} (hA : A ∈ U.ids) :
    ¬ CertifiedIn sk.skipFill A (sk.fresh k) r := by
  rintro ⟨C, hC, hreach⟩
  obtain ⟨hCo, -⟩ := (sk.reaches_fill_old hA).mp hreach
  simp only [certificates, Finset.mem_filter] at hC
  have hcert := hC.2
  unfold Certifies at hcert
  have hempty : votesIn sk.skipFill C (sk.fresh k) = ∅ := by
    rw [sk.votesIn_fill hCo]
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro q hq
    intro hmem
    exact sk.hfresh_new k (U.complete _ (U.complete _ hCo _ hq) _ hmem)
  rw [hempty] at hcert
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at hcert
  have := F.card_validators
  have := F.card_byzantine
  omega

section Slots

variable [S : Slots Validator]

/-- A leader block of `U` remains one of the extension. -/
theorem isLeaderBlock_fill {k : ℕ} {L : BlockId}
    (h : IsLeaderBlock U k L) : IsLeaderBlock sk.skipFill k L :=
  ⟨sk.ids_subset_skipFill h.1,
    by rw [sk.skipFill_block_old h.1]; exact h.2.1,
    by rw [sk.skipFill_block_old h.1]; exact h.2.2⟩

/-- A leader block of the extension is an old one, or a filled block on
a slot of the recovering validator. -/
theorem isLeaderBlock_fill_cases {k : ℕ} {L : BlockId}
    (h : IsLeaderBlock sk.skipFill k L) :
    IsLeaderBlock U k L ∨
      ∃ k', sk.r0 < k' ∧ k' ≤ sk.r ∧ L = sk.fresh k' ∧
        k' = S.slotRound k ∧ sk.v1 = S.leader k := by
  obtain ⟨hmem, hround, hcreator⟩ := h
  rcases Finset.mem_union.mp hmem with ho | hf
  · rw [sk.skipFill_block_old ho] at hround hcreator
    exact Or.inl ⟨ho, hround, hcreator⟩
  · obtain ⟨k', hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    rw [sk.skipFill_block_fresh] at hround hcreator
    exact Or.inr ⟨k', hk1, hk2, rfl, hround, hcreator⟩

/-- **The blockers of a slot read identically across the fill.** An old
block's references are old, and a filled candidate is fresh, so a block
that referenced no candidate before the fill references none after it.
This is the clause that used to need counting: the fill cannot turn a
blocker into a supporter, because it adds nothing an old block points
at. -/
theorem slotBlamersIn_fill (V : View Validator BlockId Payload U) {k : ℕ} :
    slotBlamers sk.skipFill k ∩ (sk.liftView V).ids = slotBlamers U k ∩ V.ids := by
  ext q
  simp only [Finset.mem_inter, slotBlamers, Finset.mem_filter, mem_blocksAt, liftView_ids]
  constructor
  · rintro ⟨⟨hb, hn⟩, hV⟩
    have hqo := V.subset_ids hV
    rw [sk.skipFill_block_old hqo] at hb hn
    exact ⟨⟨⟨hqo, hb.2⟩, fun j hj hjL => hn j hj (sk.isLeaderBlock_fill hjL)⟩, hV⟩
  · rintro ⟨⟨hb, hn⟩, hV⟩
    have hqo := V.subset_ids hV
    refine ⟨⟨⟨sk.ids_subset_skipFill hb.1, ?_⟩, ?_⟩, hV⟩
    · rw [sk.skipFill_block_old hqo]; exact hb.2
    · rw [sk.skipFill_block_old hqo]
      intro j hj hjL
      rcases sk.isLeaderBlock_fill_cases hjL with hold | ⟨k', _, _, rfl, _, _⟩
      · exact hn j hj hold
      · exact sk.hfresh_new k' (U.complete q hqo _ hj)

/-! ## Where the transport used to be

The two verdict transports stood here: a four-constructor
induction over the core's decision relation carrying SS4 across this one
transformer, and agreement composed onto it.

They are gone. What survives above is the statement of what the fill
preserves — the four rule transfers, each an equality across the fill,
and the two negative clauses saying a fresh candidate is certified by
nothing an old anchor can see. `Properties/Arcs/SafeSkip.lean` reads
them: two fields make the fill a `Properties.Extends`, and
`decided_fill_of_persist` and `decided_fill_agree_of_properties` follow
from `Persist` — proved once for the protocol, for every extension — and
`Agree`.

The hypothesis that went missing along the way is worth keeping in
view. The bespoke transport carried `QuorateOverGap` until the skip
rule became a count of blockers; the properties version never had it.
`QuorateOverGap` stays below, because it is still the condition under
which a pre-crash view could have skipped a gap slot at all. -/


/-- **The view is quorate over the gap**: at every gap round it holds blocks
from a quorum of distinct authors at the round above.

No longer consumed by the verdict transport, which needs no condition
once a skip is a count of blockers. Kept because it is the condition under
which a *pre-crash* view could have skipped a gap slot at all, and so
the honest precondition for a recovering validator having decided
anything there. -/
def QuorateOverGap (V : View Validator BlockId Payload U) : Prop :=
  ∀ n, sk.r0 < n → n ≤ sk.r →
    quorumCard Validator ≤
      (creatorsOf U.block ((blocksAt U (n + 1)) ∩ V.ids)).card

end Slots

end SkipMsg

end LeanDag
