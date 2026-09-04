import LeanDag.Properties.Witness

/-!
# What follows from the band

`docs/target-properties.md` §3.8 and §4. Nothing here is an obligation.
Every theorem below discharges one property from another, once and
generically, so that a protocol proving `Banded` need not prove any of
them and a protocol that would rather prove them directly still may —
Hydrozoan proves `Persist` and `Local` on its own, having no `Banded`.

The split this file marks is the one worth keeping in view. A protocol
or a mechanism must *show*: `Causal`, `Agree`, `Banded`, `ViewSound`,
`LocalTruncate`, `LeaderCommits`, `Descends`, and, on the mechanism
side, `Sustains`. Everything else in `Properties/` is vocabulary the
obligations are stated in, a consequence, or optional; the consequences
live here and `Optional/` holds the rest.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Persistence falls out.** An extension carries every band and adds
only blocks; a larger view holds everything the band names. -/
theorem Persist.of_banded (h : Banded R) : Persist.Unconditional R := by
  intro S U U' he V V' _ hV k v hd
  obtain ⟨top, htop⟩ := h S U V k v hd
  exact htop S U' V' rfl (fun _ _ => rfl) (AgreeBand.of_extends he _ _)
    (fun b hb _ _ => hV hb)

/-- **And monotonicity in the view.** Fix the universe and the band
carries itself; a larger view holds everything the band names. The
core's L2 is a four-case induction, and this is the same statement with
none. -/
theorem decided_mono_of_banded (h : Banded R) {S : Slots Validator} {U : R.Universe}
    {V V' : R.View U} (hsub : R.viewIds V ⊆ R.viewIds V') {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V k v) : R.Decided S V' k v := by
  obtain ⟨top, htop⟩ := h S U V k v hd
  exact htop S U V' rfl (fun _ _ => rfl) AgreeBand.refl (fun b hb _ _ => hsub hb)

/-- **And locality.** Two DAGs agreeing above a round at or below the
slot's agree on the band, and views agreeing there hold the same blocks
of it. -/
theorem Local.of_banded (hvs : ViewSound R) (h : Banded R) : Local R := by
  intro S U U' r hag V V' hvag k hk v hd
  obtain ⟨top, htop⟩ := h S U V k v hd
  refine htop S U' V' rfl (fun _ _ => rfl) (AgreeBand.of_agreeAbove hag hk)
    (fun b hb hlo _ => ?_)
  exact (hvag b (hvs V hb) (by omega)).mp hb

/-- **A bound falls out of the band.** The slots sitting at or below a
round are finitely many, since the round structure is monotone and
unbounded, so the band's top names a slot bound and the verdict is
unchanged by reassignment above it.

The bound is not tight: it is every slot the band's rounds can hold,
where a derivation may have named fewer. A mechanism wanting a tight
bound asks the protocol for one (`Commit.lean`); this is what a rule
gets for nothing. -/
theorem exists_decidedBelow (h : Banded R) {S : Slots Validator} {U : R.Universe}
    {V : R.View U} {k : ℕ} {v : Option BlockId} (hd : R.Decided S V k v) :
    ∃ B, DecidedBelow R S B V k v := by
  obtain ⟨top, ht⟩ := h S U V k v hd
  obtain ⟨B₀, hB₀⟩ := S.unbounded (top + 1)
  refine ⟨max (k + 1) B₀, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _), hd, ?_⟩
  intro S' hround hlead
  refine ht S' U V hround (fun m hm => hlead m ?_) AgreeBand.refl (fun b hb _ _ => hb)
  by_contra hge
  push_neg at hge
  have hB : B₀ ≤ m := le_trans (le_max_right _ _) hge
  have := S.mono hB
  omega

end Properties

end LeanDag
