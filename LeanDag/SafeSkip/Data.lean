import LeanDag.BlockRecord

/-!
# Safe Skip: the data of a fill

A validator that crashes and recovers faces a gap: liveness rests on
correct validators building in every round (P8), skipping rounds is
known to break it, and producing the missing blocks one by one costs a
round trip per round of downtime. **Safe Skip** closes the gap with a
single message. The recovering validator `v1` names a block `B2` at
round `r` on another validator `v2`'s history line, and its own last
block `B1`; the message *denotes* one block per gap round, deterministic
given the DAG.

`SkipData` is that message, stated over an id set and a block map
rather than over a universe because the *data* of a fill is the same
for every rule and only the invariants a universe carries differ. Two
readings of the filled block are supplied: `fillBlock` adds a self
reference to `v1`'s block of the round below, which the core's
self-parent clause demands; `copyBlock` carries the donor's references
verbatim, which every rule without that clause takes. `Blocks` is what
a reading owes the record for the fill to close (`Record/Fill.lean`).
-/

namespace LeanDag

variable {Validator : Type*}
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- The denotation of a Safe Skip message, together with the freshness
data an implementation supplies (new ids for the filled blocks and their
decoder).

`line` is `v2`'s history line: one block per round from `r0 := round B1`
up to `r`, each referencing the one below — the chain the message's `B2`
pins by following self-parents. `hgap` is the crash itself: `v1`
authored nothing strictly between `B1` and `r`. -/
structure SkipData (ids : Finset BlockId)
    (blk : BlockId → Block Validator BlockId Payload) where
  /-- The recovering validator. -/
  v1 : Validator
  /-- Its last block before the crash. -/
  B1 : BlockId
  /-- The donor of the reference structure. -/
  v2 : Validator
  /-- The target round — the round of the pinned block `B2 = line r`. -/
  r : ℕ
  /-- `v2`'s history line, meaningful on rounds `[round B1, r]`. -/
  line : ℕ → BlockId
  /-- Fresh ids for the filled blocks, and their decoder. -/
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  /-- `B1` is `v1`'s only block at its round — the whole of what the
  boundary argument needs. Stated directly rather than as `v1 ∈ Correct`
  because the two are not interchangeable in every fault model:
  non-equivocation gives it for a correct `v1` (`hB1uniq_of_correct`),
  and the hybrid model of report §14 gives it for a *crash-prone* one,
  which is the case Safe Skip exists to serve. -/
  hB1uniq : ∀ j ∈ ids, (blk j).creator = v1 →
    (blk j).round = (blk B1).round → j = B1
  hv12 : v1 ≠ v2
  hB1 : B1 ∈ ids
  hB1c : (blk B1).creator = v1
  hline_mem : ∀ k, (blk B1).round ≤ k → k ≤ r → line k ∈ ids
  hline_creator : ∀ k, (blk B1).round ≤ k → k ≤ r →
    (blk (line k)).creator = v2
  hline_round : ∀ k, (blk B1).round ≤ k → k ≤ r →
    (blk (line k)).round = k
  hline_chain : ∀ k, (blk B1).round < k → k ≤ r →
    line (k - 1) ∈ (blk (line k)).refs
  hfresh_new : ∀ k, fresh k ∉ ids
  hidx : ∀ k, idx (fresh k) = k
  /-- The crash: `v1` authored nothing in the gap. -/
  hgap : ∀ b ∈ ids, (blk b).creator = v1 →
    (blk B1).round < (blk b).round → (blk b).round ≤ r → False

namespace SkipData

variable {ids : Finset BlockId} {blk : BlockId → Block Validator BlockId Payload}
variable (sk : SkipData ids blk)

/-- The round of the anchor block — the bottom of the gap. -/
def r0 : ℕ := (blk sk.B1).round

/-- The self reference of the filled block at round `k`: the anchor at
the boundary, the previous filled block above it. -/
def prev (k : ℕ) : BlockId :=
  if k = sk.r0 + 1 then sk.B1 else sk.fresh (k - 1)

/-- The filled block at gap round `k`: `v2`'s references at that round,
plus the added self reference. -/
def fillBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := insert (sk.prev k) (blk (sk.line k)).refs
  payload := (blk (sk.line k)).payload

/-- The filled block **without the self reference**: `v2`'s references
at that round, re-authored.

The self reference exists to satisfy the core's `ValidWrt.self_parent`,
and it is the one thing about the fill a validity rule can object to: it
grafts the anchor's reference set onto the donor's, and a rule that
constrains what a *pair* of references may see together — FinWhale's
`ValidHere.leader_clause` — is not preserved by that graft. A rule with
no self-parent clause takes this block instead, and then validity is the
donor's verbatim. -/
def copyBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := (blk (sk.line k)).refs
  payload := (blk (sk.line k)).payload

/-- The gap rounds, as a `Finset`. -/
def gap : Finset ℕ := (Finset.range (sk.r + 1)).filter (fun k => sk.r0 < k)

/-- The ids of the filled blocks. -/
def freshIds : Finset BlockId := sk.gap.image sk.fresh

theorem mem_freshIds {b : BlockId} :
    b ∈ sk.freshIds ↔ ∃ k, sk.r0 < k ∧ k ≤ sk.r ∧ b = sk.fresh k := by
  simp only [freshIds, gap, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨h2, h1⟩, h3⟩; exact ⟨k, h1, by omega, h3.symm⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨by omega, h1⟩, h3.symm⟩

theorem r0_le_of_lt {k : ℕ} (h : sk.r0 < k) : (blk sk.B1).round ≤ k := le_of_lt h

/-- **What a reading of the filled blocks owes the record**: one block
per gap round, at that round, by the recovering validator, referencing
only old ids and filled ids. -/
structure Blocks where
  /-- The filled block at gap round `k`. -/
  blk : ℕ → Block Validator BlockId Payload
  round : ∀ k, (blk k).round = k
  creator : ∀ k, (blk k).creator = sk.v1
  refs_mem : ∀ k, sk.r0 < k → k ≤ sk.r → ∀ j ∈ (blk k).refs, j ∈ ids ∪ sk.freshIds

/-- The block map of the fill: old ids as before, filled ids decoded. -/
def fillMap (B : sk.Blocks) (b : BlockId) : Block Validator BlockId Payload :=
  if b ∈ ids then blk b else B.blk (sk.idx b)

variable {sk}

@[simp] theorem fillMap_old {B : sk.Blocks} {b : BlockId} (hb : b ∈ ids) :
    sk.fillMap B b = blk b := if_pos hb

@[simp] theorem fillMap_fresh {B : sk.Blocks} {k : ℕ} :
    sk.fillMap B (sk.fresh k) = B.blk k := by
  simp only [fillMap, if_neg (sk.hfresh_new k), sk.hidx]

variable (sk)

/-- The copy reading: the donor's references verbatim. Needs only that
the old universe is closed under references. -/
def copyBlocks (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) : sk.Blocks where
  blk := sk.copyBlock
  round := fun _ => rfl
  creator := fun _ => rfl
  refs_mem := fun k hk1 hk2 j hj =>
    Finset.mem_union_left _ (hc _ (sk.hline_mem k (sk.r0_le_of_lt hk1) hk2) j hj)

/-- The self-referencing reading: the donor's references plus `v1`'s
block of the round below. -/
def selfBlocks (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) : sk.Blocks where
  blk := sk.fillBlock
  round := fun _ => rfl
  creator := fun _ => rfl
  refs_mem := fun k hk1 hk2 j hj => by
    simp only [fillBlock, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · by_cases hb : k = sk.r0 + 1
      · simp only [prev, if_pos hb]
        exact Finset.mem_union_left _ sk.hB1
      · simp only [prev, if_neg hb]
        exact Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k - 1, by omega, by omega, rfl⟩)
    · exact Finset.mem_union_left _ (hc _ (sk.hline_mem k (sk.r0_le_of_lt hk1) hk2) j hj)

@[simp] theorem copyBlocks_blk (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) :
    (sk.copyBlocks hc).blk = sk.copyBlock := rfl

@[simp] theorem selfBlocks_blk (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) :
    (sk.selfBlocks hc).blk = sk.fillBlock := rfl

end SkipData

end LeanDag
