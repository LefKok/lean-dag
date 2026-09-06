import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.Integration.HydrozoanMechanisms

/-!
# Garbage collection, crash recovery and re-genesis for Optimal-Hydrozoan

Optimal-Hydrozoan's universes are Hydrozoan's under leader exclusion.
`Excluded` is that invariant on the record, and it is mechanised: it
survives the cut because a block two rounds above the horizon keeps its
refs and its refs keep theirs; the copy fill because a filled
block's refs are the donor's and old blocks vote only for old
blocks; and re-genesis because the new block is bound by no exclusion
and is its creator's only block. The carrier then reads as records under
`Excluded`, through Hydrozoan's adapter, and every mechanism cell is
`Arcs/Record.lean` at that instance.

The fill cell is the one the skip-fill refutation had put out of
scope. That was a fact about the core's `skipFill`, whose self
reference grafts the anchor's refs onto the donor's; the copy fill
adds no edge, and the objection does not apply.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs
open LeanDag.Barnacle.OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable {S : Slots Replica} {G d : ℕ}

section HZ

variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- **Leader exclusion survives the cut.** A block bound by exclusion
sits two rounds above the horizon, so it keeps its refs, its refs
keep theirs and their creators, and its candidates are old blocks at a
rebased round. -/
theorem leaderExcludedAll_chopHZ (hU : LeaderExcludedAll U) :
    LeaderExcludedAll (chopHZ U G) := by
  intro b hb v h2 hwit j hj
  rw [mem_chopHZ_ids] at hb
  have h2' := h2
  rw [chopHZ_round] at h2'
  have hjb := hj
  rw [chopHZ_refs_of_lt (by omega)] at hjb
  have hjU := U.complete b hb.1 j hjb
  rw [chopHZ_creator]
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  have hpar : ∀ j', j' ∈ ((chopHZ U G).block b).refs → j' ∈ (U.block b).refs := by
    intro j' hj'
    rwa [chopHZ_refs_of_lt (by omega)] at hj'
  have hcand : ∀ L j', j' ∈ (U.block b).refs →
      LeanDag.Hydrozoan.IsVote (chopHZ U G) j' L →
      IsCandidateAt (chopHZ U G) (((chopHZ U G).block b).round - 2) v L →
      IsCandidateAt U ((U.block b).round - 2) v L ∧ LeanDag.Hydrozoan.IsVote U j' L := by
    intro L j' hj' hv hc
    have hj'U := U.complete b hb.1 j' hj'
    have hj'r := (U.valid b hb.1).predecessor j' hj'
    unfold LeanDag.Hydrozoan.IsVote at hv ⊢
    rw [chopHZ_refs_of_lt (by omega)] at hv
    obtain ⟨hLm, hLr, hLa⟩ := hc
    rw [mem_chopHZ_ids] at hLm
    rw [chopHZ_round, chopHZ_round] at hLr
    rw [chopHZ_creator] at hLa
    exact ⟨⟨hLm.1, by omega, hLa⟩, hv⟩
  obtain ⟨hc₁, hv₁'⟩ := hcand L₁ j₁ (hpar j₁ hj₁) hv₁ hL₁
  obtain ⟨hc₂, hv₂'⟩ := hcand L₂ j₂ (hpar j₂ hj₂) hv₂ hL₂
  exact hU b hb.1 v (by omega) ⟨L₁, L₂, hc₁, hc₂, hne, ⟨j₁, hpar j₁ hj₁, hv₁'⟩,
    ⟨j₂, hpar j₂ hj₂, hv₂'⟩⟩ j hjb

variable {sk : SkipData U.ids U.block}

/-- A candidate voted for by an old block is old, and a candidate in the
old universe. -/
theorem isCandidateAt_of_old {r : ℕ} {v : Replica} {j L : BlockId} (hj : j ∈ U.ids)
    (hv : LeanDag.Hydrozoan.IsVote (copyFillHZ U sk) j L)
    (hc : IsCandidateAt (copyFillHZ U sk) r v L) : IsCandidateAt U r v L := by
  unfold LeanDag.Hydrozoan.IsVote at hv
  rw [copyFillHZ_block_old hj] at hv
  have hLU := U.complete j hj L hv
  obtain ⟨-, hLr, hLa⟩ := hc
  rw [copyFillHZ_block_old hLU] at hLr hLa
  exact ⟨hLU, hLr, hLa⟩

/-- **Leader exclusion survives the copy fill.** A filled block's refs
are the donor's; old blocks vote only for old blocks; so whatever a
block of the fill witnesses, a block of the old universe with the same
refs witnessed, and its refs were already excluded. -/
theorem leaderExcludedAll_copyFillHZ (hU : LeaderExcludedAll U) :
    LeaderExcludedAll (copyFillHZ U sk) := by
  intro b hb v h2 hwit j hj
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  rcases mem_copyFillHZ_ids.mp hb with ho | hf
  · -- an old block: refs, round and witnesses are the old universe's
    rw [copyFillHZ_block_old ho] at h2 hj hj₁ hj₂
    have hj₁U := U.complete b ho j₁ hj₁
    have hj₂U := U.complete b ho j₂ hj₂
    have hjU := U.complete b ho j hj
    rw [copyFillHZ_block_old hjU]
    refine hU b ho v h2 ⟨L₁, L₂, isCandidateAt_of_old hj₁U hv₁ ?_,
      isCandidateAt_of_old hj₂U hv₂ ?_, hne, ⟨j₁, hj₁, ?_⟩, ⟨j₂, hj₂, ?_⟩⟩ j hj
    · rw [copyFillHZ_block_old ho] at hL₁; exact hL₁
    · rw [copyFillHZ_block_old ho] at hL₂; exact hL₂
    · unfold LeanDag.Hydrozoan.IsVote at hv₁ ⊢
      rw [copyFillHZ_block_old hj₁U] at hv₁; exact hv₁
    · unfold LeanDag.Hydrozoan.IsVote at hv₂ ⊢
      rw [copyFillHZ_block_old hj₂U] at hv₂; exact hv₂
  · -- a filled block: everything is the donor's
    obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    have hlm := sk.hline_mem k (by omega) hk2
    have hlr : (U.block (sk.line k)).round = k := sk.hline_round k (by omega) hk2
    rw [copyFillHZ_block_fresh] at h2 hj hj₁ hj₂ hL₁ hL₂
    simp only [SkipData.copyBlock] at h2 hj hj₁ hj₂ hL₁ hL₂
    have hj₁U := U.complete _ hlm j₁ hj₁
    have hj₂U := U.complete _ hlm j₂ hj₂
    have hjU := U.complete _ hlm j hj
    rw [copyFillHZ_block_old hjU]
    have h2' : 2 ≤ (U.block (sk.line k)).round := by omega
    have hr : k - 2 = (U.block (sk.line k)).round - 2 := by omega
    rw [hr] at hL₁ hL₂
    exact hU _ hlm v h2' ⟨L₁, L₂, isCandidateAt_of_old hj₁U hv₁ hL₁,
      isCandidateAt_of_old hj₂U hv₂ hL₂, hne,
      ⟨j₁, hj₁, by unfold LeanDag.Hydrozoan.IsVote at hv₁ ⊢
                   rw [copyFillHZ_block_old hj₁U] at hv₁; exact hv₁⟩,
      ⟨j₂, hj₂, by unfold LeanDag.Hydrozoan.IsVote at hv₂ ⊢
                   rw [copyFillHZ_block_old hj₂U] at hv₂; exact hv₂⟩⟩ j hj

/-- **Leader exclusion survives re-genesis.** The new block sits at round
zero, so it is bound by no exclusion; and it is its creator's only
block, so it can be no second candidate of a witnessed equivocation and
no parent of anything old. Every old block's witnesses and refs are
unchanged. -/
theorem leaderExcludedAll_addGenesisHZ {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (hU : LeaderExcludedAll U) {v : Replica} {g : BlockId} {hg : g ∉ U.ids}
    {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v} :
    LeaderExcludedAll (addGenesisHZ U v g hg hsev) := by
  intro b hb u h2 hwit j hj
  rcases mem_addGenesisHZ_ids.mp hb with rfl | hbU
  · rw [addGenesisHZ_block_new] at h2
    simp at h2
  · rw [addGenesisHZ_block_old hbU] at h2 hwit hj
    have hjU := U.complete b hbU j hj
    rw [addGenesisHZ_block_old hjU]
    obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
    have hj₁' : j₁ ∈ (U.block b).refs := by rwa [addGenesisHZ_block_old hbU] at hj₁
    have hj₂' : j₂ ∈ (U.block b).refs := by rwa [addGenesisHZ_block_old hbU] at hj₂
    by_cases huv : u = v
    · subst huv
      have hc : ∀ L, IsCandidateAt (addGenesisHZ U u g hg hsev) ((U.block b).round - 2) u L →
          L = g := by
        rintro L ⟨hLm, -, hLa⟩
        rcases mem_addGenesisHZ_ids.mp hLm with rfl | hLU
        · rfl
        · rw [addGenesisHZ_block_old hLU] at hLa
          exact absurd hLa (hsev L hLU)
      exact absurd ((hc L₁ hL₁).trans (hc L₂ hL₂).symm) hne
    · have hcand : ∀ L, IsCandidateAt (addGenesisHZ U v g hg hsev) ((U.block b).round - 2) u L →
          IsCandidateAt U ((U.block b).round - 2) u L := by
        rintro L ⟨hLm, hLr, hLa⟩
        rcases mem_addGenesisHZ_ids.mp hLm with rfl | hLU
        · rw [addGenesisHZ_block_new] at hLa
          exact absurd hLa.symm huv
        · rw [addGenesisHZ_block_old hLU] at hLr hLa
          exact ⟨hLU, hLr, hLa⟩
      have hvote : ∀ j ∈ (U.block b).refs, ∀ L,
          LeanDag.Hydrozoan.IsVote (addGenesisHZ U v g hg hsev) j L →
          LeanDag.Hydrozoan.IsVote U j L := by
        intro j hj L hv
        have hjU := U.complete b hbU j hj
        unfold LeanDag.Hydrozoan.IsVote at hv ⊢
        rw [addGenesisHZ_block_old hjU] at hv
        exact hv
      exact hU b hbU u h2 ⟨L₁, L₂, hcand L₁ hL₁, hcand L₂ hL₂, hne,
        ⟨j₁, hj₁', hvote j₁ hj₁' L₁ hv₁⟩, ⟨j₂, hj₂', hvote j₂ hj₂' L₂ hv₂⟩⟩ j hj

/-- **Leader exclusion, as an invariant on the record.** -/
def Excluded (W : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  LeaderExcludedAll W

/-- **And it is mechanised**: the three facts above, read at the record. -/
instance Excluded.mechanised :
    BlockRecord.Invariant.Mechanised (Excluded (Replica := Replica) (BlockId := BlockId)) where
  chop := fun G h => leaderExcludedAll_chopHZ (G := G) h
  copyFill := fun sk h => leaderExcludedAll_copyFillHZ (sk := sk) h
  addGenesis := fun v g _ hg hsev h =>
    leaderExcludedAll_addGenesisHZ (v := v) (g := g) (hg := hg) (hsev := hsev) h

end HZ

section Opt

variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan's carrier, on the record**: Hydrozoan's adapter,
under `Excluded`. -/
def optOnRecord :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).OnRecord LeanDag.Hydrozoan.ValidWrt
      (LeanDag.Hydrozoan.NonByzantine : Finset Replica) Excluded where
  toRec := fun W => W.val
  inv := fun W => W.property
  ofRec := fun W h => ⟨W, h⟩
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  ofView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

variable {W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
  (BlockId := BlockId)).Universe}

/-- **The cut, at Optimal-Hydrozoan's carrier**: the record's. -/
def chopOpt (W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
    (BlockId := BlockId)).Universe) (G : ℕ) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Universe :=
  optOnRecord.chop W G

/-- **The fill, at Optimal-Hydrozoan's carrier**: the record's copy fill. -/
def copyFillOpt (W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
    (BlockId := BlockId)).Universe) (sk : SkipData W.val.ids W.val.block) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Universe :=
  optOnRecord.copyFill W sk

/-- **Re-genesis, at Optimal-Hydrozoan's carrier**: the record's. -/
def addGenesisOpt (W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
    (BlockId := BlockId)).Universe) (v : Replica) (g : BlockId)
    (hg : g ∉ W.val.ids) (hsev : ∀ b ∈ W.val.ids, (W.val.block b).creator ≠ v) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Universe :=
  optOnRecord.addGenesis W v g () hg hsev

end Opt

end Integration

end LeanDag
