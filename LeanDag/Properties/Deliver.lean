import LeanDag.Properties.Band
/-!
# What a view-level mechanism owes

`docs/target-properties.md` §11.5. `Sustains` is what a mechanism that
transforms the **DAG** owes a protocol. Rate limiting and the joiner
transform a **view**: `LeanDag/DoS/` builds no universe at all — its one
constructor is `View.ofAccepted` — and a rate-limited validator differs
from an unlimited one only in what it holds.

**Safety needs nothing.** A verdict reached on a smaller view is reached
on a larger one (`decided_mono_of_banded`), so a rate limiter cannot
make a validator decide wrongly. That is the whole safety story for this
class of mechanism, and it was already derived.

**Liveness had nothing at all.** Nothing said a rate limiter eventually
delivers enough for a slot to decide, and a mechanism that deferred a
block forever would have satisfied every obligation in this development.
`DeliversOn` is that statement.

**The protocol side is derived, not owed.** `exists_coversUpto_decides`
below: every verdict has a round it is settled by, and any view covering
to that round reaches it. So a protocol proves nothing new here — the
band already said which rounds a verdict reads, and covering them is
what a view has to do. The obligation falls entirely on the mechanism,
which is the same asymmetry §3.6 records for `Sustains`.

**On what a rate limiter can honestly promise.** `Delivers` asks for
coverage of *everything* the universe holds up to a round. A limiter
that permanently drops Byzantine spam does not satisfy it, and should
not have to: the verdict is reached because a quorum of correct blocks
suffices, not because every block arrives. A weaker obligation naming
only the correct blocks would serve those mechanisms, and stating it
needs a consumer that asks for it — which is why it is not stated here.
`DoS/Novelty.lean` bounds the *size* of a rate-limited view and says
nothing yet about its coverage, so this obligation has no witness in
this development.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A view is caught up to round `N`**: it holds every block the
universe has at or below that round.

The record states it once as `View.CoversUpto` (`BlockRecord.lean`);
this is the same three lines at a carrier. -/
def CoversUpto (R : DagRule Validator BlockId Payload) {U : R.Universe}
    (V : R.View U) (N : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → (R.block U b).round ≤ N → b ∈ R.viewIds V

/-- Covering a round covers every earlier one. -/
theorem CoversUpto.mono {U : R.Universe} {V : R.View U} {M N : ℕ}
    (h : CoversUpto R V N) (hMN : M ≤ N) : CoversUpto R V M :=
  fun b hb hr => h b hb (le_trans hr hMN)

/-- **A verdict is reached by every view caught up far enough.** The
round is the band's ceiling: the verdict reads nothing above it, so a
view holding everything up to it holds everything the verdict reads.

This is the protocol's whole contribution to view-level liveness, and it
is `Banded` applied. -/
theorem exists_coversUpto_decides (h : Banded R) {S : Slots Validator}
    {U : R.Universe} {W : R.View U} {k : ℕ} {v : Option BlockId}
    (hW : R.Decided S W k v) :
    ∃ N, ∀ V : R.View U, CoversUpto R V N → R.Decided S V k v := by
  obtain ⟨top, htop⟩ := h S U W k v hW
  refine ⟨top, fun V hcov => ?_⟩
  exact htop 0 0 0 0 S U V k (by omega) (fun m m' hm => by
      have : m = m' := by omega
      subst this; rfl)
    (fun m m' hm _ => by have : m = m' := by omega
                         subst this; rfl)
    AgreeBand.refl (fun b hb _ h2 => hcov b (R.viewSound W hb) h2)

/-- **A view holds the reliable set's blocks over a window.** Weaker
than `CoversUpto` in the way a rate limiter needs: it says nothing about
what an equivocator or a withholder produced, because a verdict is
reached from a quorum of correct evidence and not from every block. -/
def CoversOn (R : DagRule Validator BlockId Payload) {U : R.Universe}
    (V : R.View U) (T : Finset Validator) (lo hi : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → (R.block U b).creator ∈ T →
    lo ≤ (R.block U b).round → (R.block U b).round ≤ hi → b ∈ R.viewIds V

/-- Full coverage over a window is coverage of any set over it. -/
theorem CoversUpto.coversOn {U : R.Universe} {V : R.View U} {N : ℕ}
    (h : CoversUpto R V N) (T : Finset Validator) (lo : ℕ) :
    CoversOn R V T lo N :=
  fun b hb _ _ hhi => h b hb hhi

/-- **A view-level mechanism delivers the reliable set.** For every
round, one of the views it produces holds every `T`-block from `lo` up to
it. What a rate limiter can promise, and what `DoS/Delivers.lean`
proves of the novelty budget. -/
def DeliversOn (R : DagRule Validator BlockId Payload) {U : R.Universe}
    (view : ℕ → R.View U) (T : Finset Validator) (lo : ℕ) : Prop :=
  ∀ hi, ∃ t, CoversOn R (view t) T lo hi

end Properties

end LeanDag
