import LeanDag.Integration.Preservation
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.GC
import LeanDag.Timed.Extension
/-!
# I4 — the fill does not restore coverage, and why that is correct

Coverage under the Safe Skip fill, at the core: every statement here is
`Timed/Extension.lean`'s generic one at the fill's `Extends` witness, or
`Timed.synchronisedOn_of_rebased` at its `Sustains` witness.

**Coverage fails at every gap round of every fill**, for a reliable set
that counts the recovering validator, on no hypotheses beyond the ones
that make the fill worth doing (`not_synchronisedOn_skipFill`). The
reason is the fact that makes Safe Skip **safe**: no old block
references a fresh identifier, so a filled block landing on a leader
slot is always directly skipped and the fill cannot conjure a commit.
Coverage asks for the opposite, that every reliable block at round
`n+1` reference every reliable block at round `n`, and at a gap round
the fill supplies a reliable block that the round above does not
reference. One fact, two consequences.

This is not a defect. Safe Skip's claim is that it restores
*production* (`PopulatedOn`, SS2), the hypothesis liveness consumes,
and it makes no claim about coverage. Coverage is untouched for any
set excluding the recovering validator, and it returns for every set
strictly above the fill, once the recovered validator is building
again (`synchronisedOn_skipFill_above`).
-/

namespace LeanDag

namespace Integration

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The fill is an extension of the core's carrier. -/
theorem extends_skipFill (sk : SkipMsg U) :
    Properties.Extends (MysticetiProperties.mysticetiRule (Payload := Payload)) U sk.skipFill :=
  Properties.Arcs.extends_of_skipFill _ sk rfl rfl rfl rfl

/-- **I4, refuted.** The fill does not restore coverage. If the
recovering validator is counted reliable — which is exactly what SS2
does — then at any gap round `k` above the coverage round, an old
reliable block at `k+1` fails to reference the filled block at `k`.

The hypotheses are the situation SS2 creates: `hv1` puts `v1` in the
reliable set, `hk` places the gap round in the covered range, and `hb`
asks only that some reliable validator built at the round above, which
`PopulatedOn` supplies. -/
theorem not_synchronisedOn_skipFill (sk : SkipMsg U) {T : Finset Validator}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ SynchronisedOn sk.skipFill T R :=
  Timed.not_synchronisedOn_of_extends (extends_skipFill sk) hk
    (f := sk.fresh k)
    ⟨Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩), sk.hfresh_new k⟩
    (by change (sk.skipFill.block (sk.fresh k)).round = k; rw [sk.skipFill_block_fresh]; rfl)
    (by change (sk.skipFill.block (sk.fresh k)).creator ∈ T; rw [sk.skipFill_block_fresh]; exact hv1)
    hb hbround hbc

/-- **The refutation is narrow: it is about counting the recovering
validator reliable during the gap it slept through.** Exclude it from
the reliable set and coverage is untouched: the fill's blocks are its
alone, so the clause never quantifies over them. -/
theorem synchronisedOn_skipFill_of_notMem (sk : SkipMsg U) {T : Finset Validator}
    {R : ℕ} (hs : SynchronisedOn U T R) (hv1 : sk.v1 ∉ T) :
    SynchronisedOn sk.skipFill T R :=
  Timed.synchronisedOn_of_extends (extends_skipFill sk) hs fun b hn => by
    rcases Finset.mem_union.mp hn.1 with ho | hf
    · exact absurd ho hn.2
    · obtain ⟨k, _, _, rfl⟩ := sk.mem_freshIds.mp hf
      change (sk.skipFill.block (sk.fresh k)).creator ∉ T
      rw [sk.skipFill_block_fresh]; exact hv1

/-- **I4, positively.** Coverage holds *strictly* above the fill: past
the target round every block is old, references are preserved, and the
original condition applies unchanged. This is the form a liveness
argument after recovery consumes.

The strictness is not slack. At `n = sk.r` the lower block may still
be the last filled one, and `not_synchronisedOn_skipFill` refutes
coverage there; `sk.r < R'` is exactly the first round at which every
block in play is old. -/
theorem synchronisedOn_skipFill_above (sk : SkipMsg U) {T : Finset Validator}
    {R R' : ℕ} (hs : SynchronisedOn U T R) (hR : R ≤ R') (hR' : sk.r < R') :
    SynchronisedOn sk.skipFill T R' := by
  have h := Timed.synchronisedOn_of_rebased
    (R := MysticetiProperties.mysticetiRule) (Properties.Arcs.sustains_skipFill sk)
    (T := T) (r := R') (Nat.succ_le_of_lt hR') (Nat.zero_le _)
    (Timed.SynchronisedOn.mono (MysticetiProperties.synchronisedOn_eq.mpr hs) hR)
  exact MysticetiProperties.synchronisedOn_eq.mp (by simpa using h)

/-- **Synchrony survives the cut, from the rebase** (I2). `Sustains`
applied, as votes and production already were. -/
theorem synchronisedOn_chop {T : Finset Validator} {Rs R' : ℕ}
    (hs : LeanDag.SynchronisedOn U T Rs) (hGR : Rs ≤ G + R') :
    LeanDag.SynchronisedOn (chop U G) T R' := by
  have h := Timed.synchronisedOn_of_rebased (R := MysticetiProperties.mysticetiRule)
    (Properties.Arcs.sustains_chop (U := U) (G := G)) (T := T) (r := G + R') (by omega) (by omega)
    (Timed.SynchronisedOn.mono ((MysticetiProperties.synchronisedOn_eq).mpr hs) hGR)
  exact MysticetiProperties.synchronisedOn_eq.mp (by simpa using h)

end Integration

end LeanDag
