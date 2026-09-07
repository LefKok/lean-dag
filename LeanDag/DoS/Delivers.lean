import LeanDag.DoS.Novelty
import LeanDag.GC.Bootstrap
import LeanDag.Mysticeti.Properties
/-!
# The novelty budget delivers

`Properties/Deliver.lean` states what a **view-level** mechanism owes,
and this is the witness. A rate limiter is the case that obligation
exists for: `DoS/` builds no universe, only views, and until the
obligation was written a limiter that deferred a block forever satisfied
everything in this development.

**The strong form is not what a limiter can promise, and the attempt is
what shows it.** `Properties.Delivers` asks the view to hold *every*
block of the universe up to a round. Nothing here forces that:
`Delivery.accepts_correct` constrains acceptance for correct blocks
alone, and a block a Byzantine author withholds from everyone is a block
of `U` in nobody's view. Worse, `Delivery.accepted_inj` *requires* a
validator to drop one of an equivocating pair, so at a round where an
equivocator published twice no admissible delivery covers the layer. The
strong obligation's only model is `View.full`, which is the mechanism
that does nothing.

**The weak form is the right one, and it holds.** `Properties.CoversOn`
asks for the blocks of a reliable set over a window, and that is exactly
what `accepts_correct` and `EventuallyDelivers` supply: after the
settling round a correct validator holds every correct block, accepts
every one it holds, and its retained store keeps whole causal cones. The
budget never enters the argument — a rate limit that defers a *correct*
block would have to violate `accepts_correct`, so the novelty budget's
own theorems, which bound the *size* of `viewUpto`, are not needed and
not used.

**And it commits.** `directCommitIn_of_certifiesAt` counts a reliable
quorum's certificates inside a view rather than in the universe, so the
coverage proved here is enough for a rate-limited validator to reach the
verdict. That is the consumer the obligation was stated for.
-/

namespace LeanDag

namespace DoS

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {v : Validator} {n : ℕ}

/-- **A retained store is a view.** It holds only real blocks
(`viewUpto_subset_ids`) and is closed under references
(`mem_viewUpto_of_mem_refs`), which are the two things a view is. -/
def View.ofViewUpto (D : Delivery U) (v : Validator) (n : ℕ) :
    View Validator BlockId Payload U where
  ids := viewUpto D v n
  subset_ids := viewUpto_subset_ids
  complete := fun _ hi _ hj => mem_viewUpto_of_mem_refs hi hj

@[simp] theorem View.ofViewUpto_ids : (View.ofViewUpto D v n).ids = viewUpto D v n := rfl

/-- **What a rate-limited store holds.** After the settling round a
correct validator's store contains every correct block up to its own
round — the store is built from what it accepted, it accepted every
correct block it held, and eventual delivery gave it all of them. -/
theorem correct_mem_viewUpto {R : ℕ} (hED : EventuallyDelivers D R)
    (hv : v ∈ (Correct : Finset Validator)) {a : BlockId} (ha : a ∈ U.ids)
    (hac : (U.block a).creator ∈ (Correct : Finset Validator))
    (hlo : R ≤ (U.block a).round) (hhi : (U.block a).round ≤ n) :
    a ∈ viewUpto D v n := by
  have hheld : a ∈ D.held v (U.block a).round :=
    hED (U.block a).round hlo v hv a ha rfl hac
  have hacc : a ∈ D.accepted v (U.block a).round :=
    D.accepts_correct v hv (U.block a).round a hheld hac
  exact history_subset_viewUpto hhi hacc ((mem_history_iff ha).mpr Relation.ReflTransGen.refl)

/-- **The witness.** The novelty budget's stores cover the correct
validators from the settling round on, so a rate limiter delivers in the
sense `Properties.DeliversOn` names. -/
theorem deliversOn_viewUpto {R : ℕ} (hED : EventuallyDelivers D R)
    (hv : v ∈ (Correct : Finset Validator)) :
    Properties.DeliversOn (MysticetiProperties.mysticetiRule (Payload := Payload))
      (fun t => View.ofViewUpto D v t) (Correct : Finset Validator) R :=
  fun hi => ⟨hi, fun a ha hac hlo hhi => correct_mem_viewUpto hED hv ha hac hlo hhi⟩

/-- **A rate-limited validator commits.** Given a reliable quorum whose
decision-round blocks certify `L`, a store that has settled reaches the
direct commit — no appeal to the budget, and no coverage of anything an
equivocator produced. -/
theorem directCommitIn_viewUpto [S : Slots Validator] {R r : ℕ} {L : BlockId}
    {T : Finset Validator} (hED : EventuallyDelivers D R)
    (hv : v ∈ (Correct : Finset Validator)) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hR : R ≤ r + 2) (hn : r + 2 ≤ n)
    (hpop2 : PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommitIn U (View.ofViewUpto D v n) L r :=
  directCommitIn_of_certifiesAt hcard hpop2
    (fun b hb hbc hbr => correct_mem_viewUpto hED hv hb (hT hbc) (by omega) (by omega)) hc

end DoS

end LeanDag
