import LeanDag.Properties.Local
import LeanDag.Properties.Reindex

/-!
# Garbage collection, for any protocol with `Local` and `Reindex`

`docs/target-properties.md` G2, the garbage-collection half. A replica
that has pruned below a horizon reaches the verdicts it would have
reached with its whole history, at its own numbering.

**A truncation is two steps, and they are two properties.** It drops
what lies below the horizon — locality — and renumbers what remains so
the retained layer sits at round zero — re-indexing. `decided_truncate`
below is their composition, and it is three lines because both halves
have been stated where they belong.

**The step between them has to be supplied.** The composition passes
through the universe that has been restricted and *not yet* renumbered,
and neither this file nor `Properties/` can construct it: `DagRule.Universe`
is abstract by design, which is what lets one schema serve carriers as
different as Hydrozoan's and Nemo's. So it is a parameter, and a
protocol exhibits it.

**No arc currently defines one.** `GC.chop` restricts and renumbers in a
single step — `chop`'s `ids` filters on the round while `chopBlock`
lowers it — so a protocol reaching for this theorem must first define
the intermediate and relate it to `chop` on both sides. That is the
concrete residue of the risk §3.4 recorded, and it is a definition and
two agreements rather than an induction: the inductions are `Local` and
`Reindex`, each paid once per protocol.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Verdicts survive a truncation**, for any protocol that is local
and re-indexes.

`Umid` is `U` with everything below the horizon dropped and the rounds
left alone; `U'` is `Umid` renumbered. The base-slot premise
`G ≤ S.slotRound d` is the only arithmetic condition, and it is the one
the concrete developments already thread. -/
theorem decided_truncate (hl : Local R) (hr : Reindex R)
    {S S' : Slots Validator} {U Umid U' : R.Universe} {G d : ℕ}
    (hres : AgreeAbove R U Umid G) (hsh : Shifted R Umid U' S S' G d)
    {V : R.View U} {Vmid : R.View Umid} {V' : R.View U'}
    (hvres : ViewAgreeAbove R V Vmid G) (hvsh : R.viewIds Vmid = R.viewIds V')
    (hd : G ≤ S.slotRound d) {k : ℕ} {v : Option BlockId}
    (h : R.Decided S V (d + k) v) :
    R.Decided S' V' k v := by
  have hk : G ≤ S.slotRound (d + k) := le_trans hd (S.mono (Nat.le_add_right d k))
  exact hr S S' Umid U' G d hsh Vmid V' hvsh k v
    (hl S U Umid G hres V Vmid hvres (d + k) hk v h)

end Arcs

end Properties

end LeanDag
