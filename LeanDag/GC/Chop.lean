import LeanDag.Mysticeti
import LeanDag.Record.Chop
import LeanDag.DoS.Exposure

/-!
# The horizon: truncation as rebasing

`garbage.md` §2, §4 — the operator and the safety half: **G1** (truncation
is a universe, with the one-way `DoSValid` transfer) and **G2** (verdict
invariance): `supporters`, `blames`, `certificates`, `DirectCommit`,
`DirectSkip` and the indirect test `CertifiedIn` computed in `chop U G`
agree with `U` for slots at or above the cut.

The design (`garbage.md` §2): `chop U G` keeps the blocks of rounds `≥ G`,
rebases rounds by `−G`, and empties the reference sets of the new base
layer — the round-`G` blocks become the new geneses. Every validity clause
then holds of the truncation exactly as it held of the original, so
`chop U G` is a bona-fide `BlockUniverse` and every existing theorem
applies to it verbatim. Verdict invariance is pure window-locality: each
rule reads rounds strictly above the base layer, where `chop` changes
nothing but the round label.

The one-way `DoSValid` transfer (`dosValid_chop`) is where the *statute of
limitations* lives: cones shrink under truncation, so exposure shrinks, so
the condition weakens per block. The converse fails by design — an
equivocation whose witnessing pair falls strictly below the cut is
forgiven — and the witness file makes that visible on data.
-/

namespace LeanDag

/-! The block-level operator `chopBlk` is `BlockRecord.lean`'s. -/

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ} {b i j : BlockId}

/-! ## The core's universe -/

/-- The core's truncation of a block is that, at the core's universe. -/
def chopBlock (U : BlockUniverse Validator BlockId Payload) (G : ℕ)
    (i : BlockId) : Block Validator BlockId Payload :=
  chopBlk U.block G i

/-- Truncation leaves authorship unchanged. -/
@[simp]
theorem chopBlock_creator :
    (chopBlock U G i).creator = (U.block i).creator := by
  unfold chopBlock chopBlk; split <;> rfl

/-- Truncation rebases rounds by the cut. -/
@[simp]
theorem chopBlock_round :
    (chopBlock U G i).round = (U.block i).round - G := by
  unfold chopBlock chopBlk; split <;> rfl

/-- Truncation leaves payloads unchanged. -/
@[simp]
theorem chopBlock_payload :
    (chopBlock U G i).payload = (U.block i).payload := by
  unfold chopBlock chopBlk; split <;> rfl

/-- At or below the cut a block becomes a genesis: its references are dropped. -/
theorem chopBlock_refs_of_le (h : (U.block i).round ≤ G) :
    (chopBlock U G i).refs = ∅ := chopBlk_refs_of_le h

/-- Above the cut references are untouched. -/
theorem chopBlock_refs_of_lt (h : G < (U.block i).round) :
    (chopBlock U G i).refs = (U.block i).refs := chopBlk_refs_of_lt h

/-- The truncation's references never exceed the original's. -/
theorem chopBlock_refs_subset :
    (chopBlock U G i).refs ⊆ (U.block i).refs := by
  rcases Nat.lt_or_ge G (U.block i).round with h | h
  · rw [chopBlock_refs_of_lt h]
  · rw [chopBlock_refs_of_le h]; exact Finset.empty_subset _

/-- Creators are untouched, so creator sets are, pointwise. -/
theorem creatorsOf_chopBlock (s : Finset BlockId) :
    creatorsOf (chopBlock U G) s = creatorsOf U.block s :=
  creatorsOf_chopBlk s

/-- **The cut**: the block record's, at the core. -/
def chop (U : BlockUniverse Validator BlockId Payload) (G : ℕ) :
    BlockUniverse Validator BlockId Payload :=
  BlockRecord.chop U G

theorem mem_chop_ids :
    i ∈ (chop U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  BlockRecord.mem_chop_ids

theorem chop_block_eq : (chop U G).block = chopBlock U G := rfl

/-! ## Transfer lemmas: rounds, layers, reachability, cones -/

/-- A step in the truncation is a step in the original. -/
theorem reaches_of_reaches_chop (h : Reaches (chop U G) b i) :
    Reaches U b i := by
  induction h with
  | refl => exact Reaches.refl
  | tail _ hstep ih =>
      exact ih.trans (Reaches.single (chopBlock_refs_subset hstep))

/-- A path of the original whose endpoint stays at or above the cut never
dips below it, so it survives truncation whole. -/
theorem reaches_chop_of_reaches (hb : b ∈ U.ids) (h : Reaches U b i)
    (hi : G ≤ (U.block i).round) : Reaches (chop U G) b i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Reaches.refl
  | head hstep hrest ih =>
      rename_i x y
      have hy_ids : y ∈ U.ids := U.complete x hb y hstep
      have hy_round := U.round_of_mem_refs hb hstep
      have hi_le := round_le_of_reaches hy_ids hrest
      refine Relation.ReflTransGen.head ?_ (ih hy_ids)
      show y ∈ (chopBlock U G x).refs
      rw [chopBlock_refs_of_lt (by omega)]
      exact hstep

theorem reaches_chop_iff (hb : b ∈ (chop U G).ids) :
    Reaches (chop U G) b i ↔ Reaches U b i ∧ G ≤ (U.block i).round := by
  rw [mem_chop_ids] at hb
  constructor
  · intro h
    have hi_ids := mem_ids_of_reaches (mem_chop_ids.mpr hb) h
    rw [mem_chop_ids] at hi_ids
    exact ⟨reaches_of_reaches_chop h, hi_ids.2⟩
  · rintro ⟨h, hi⟩
    exact reaches_chop_of_reaches hb.1 h hi

/-- **The cone above the cut**: truncation intersects every cone with the
window. This is the lemma the windowed budget (`garbage.md` G13) and the
statute of limitations both run on. -/
theorem history_chop (hb : b ∈ (chop U G).ids) :
    history (chop U G) b =
      (history U b).filter fun i => G ≤ (U.block i).round := by
  have hbU : b ∈ U.ids := (mem_chop_ids.mp hb).1
  ext i
  rw [mem_history_iff hb, reaches_chop_iff hb, Finset.mem_filter,
    mem_history_iff hbU]

/-! ## The statute of limitations, and its one-way door -/

/-- Exposure in the truncation is exposure in the original: the witnessing
pair survives un-rebasing. -/
theorem exposedIn_of_exposedIn_chop {X : Validator}
    (hb : b ∈ (chop U G).ids) (h : ExposedIn (chop U G) b X) :
    ExposedIn U b X := by
  obtain ⟨x, hx, y, hy, hpair⟩ := h
  rw [history_chop hb, Finset.mem_filter] at hx hy
  have hbU := (mem_chop_ids.mp hb).1
  refine ⟨x, hx.1, y, hy.1, ?_⟩
  obtain ⟨hne, hxc, hyc, hround⟩ := hpair
  refine ⟨hne, ?_, ?_, ?_⟩
  · rw [← chopBlock_creator (U := U) (G := G)]; exact hxc
  · rw [← chopBlock_creator (U := U) (G := G)]; exact hyc
  · have hxG := hx.2
    have hyG := hy.2
    have hr := hround
    rw [chop_block_eq, chopBlock_round, chopBlock_round] at hr
    omega

/-- **G1, DoS half — the one-way door.** The condition survives
truncation; the converse fails by design (the statute of limitations,
witnessed in `LeanDagTest/GC/Chop.lean`). -/
theorem dosValid_chop (hdos : DoSValid U) : DoSValid (chop U G) := by
  intro b hb i hi
  intro hexp
  have hbU := (mem_chop_ids.mp hb).1
  have hiU : i ∈ (U.block b).refs := chopBlock_refs_subset hi
  have := hdos b hbU i hiU
  rw [← chopBlock_creator (U := U) (G := G)] at this
  exact this (exposedIn_of_exposedIn_chop hb hexp)

end LeanDag
