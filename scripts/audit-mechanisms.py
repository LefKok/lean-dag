#!/usr/bin/env python3
"""Which mechanisms have been instantiated for which protocols.

`docs/target-properties.md` part 2 claims that a rule showing the
properties composes with *each mechanism* with no further proof.
`audit-conformance.py` says which rules show which properties;
`audit-bespoke.py` says that no mechanism theorem reaches a protocol
outside them. Neither says whether a mechanism has ever been *applied*
to a rule — and it cannot, because a cell nobody wrote leaves no code
behind. Both audits check what exists; this one checks what does not.

A cell is:

* `yes`  — some declaration applies one of the mechanism's generic
           theorems and names one of the rule's carriers;
* `open` — the rule shows everything the mechanism asks for and no such
           declaration exists. That is the gap this audit is for: not a
           defect, but work the properties have already paid for and
           nobody has collected;
* `--`   — the rule does not show what the mechanism asks for, which is
           `audit-conformance.py`'s business and not repeated here.

Reads `docs/depgraph/deps.tsv` and `docs/decls.json`; regenerate both
before trusting a run. Reports only — an uncollected cell is work
outstanding rather than a defect.
"""

import collections
import importlib.util
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

_spec = importlib.util.spec_from_file_location(
    "conformance", ROOT / "scripts" / "audit-conformance.py")
conformance = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(conformance)

# The generic theorems a protocol instance of each mechanism applies,
# and the properties the mechanism asks of a rule. An entry point is a
# theorem stated over `Properties.DagRule`; applying one at a carrier is
# what "this rule has this mechanism" means.
# The third field names rules the mechanism does not apply to at all,
# with the reason: out of scope is not the same as owed. Barnacle's
# liveness runs on `LiveRule`, so a rule with no `BaseRule` instance is
# not a candidate for it however many properties it shows.
MECHANISMS = [
    ("garbage collection", {},
     ["LeanDag.Properties.LocalTruncate.of_banded",
      "LeanDag.Properties.Arcs.decided_of_truncate",
      "LeanDag.Properties.Arcs.decided_of_truncated",
      "LeanDag.Properties.Arcs.decided_agree_truncate",
      "LeanDag.Properties.Arcs.decided_agree_horizons"],
     ["Banded", "Agree"]),
    ("extension",
     {"Optimal-Hydrozoan":
      "`skipFill` breaks leader exclusion — `not_leaderExcludedAll_Ufill`"},
     ["LeanDag.Properties.Persist.of_banded",
      "LeanDag.Properties.Arcs.decided_skipFill",
      "LeanDag.Properties.Arcs.decided_agree_extends",
      "LeanDag.Properties.Arcs.decided_fill_of_persist",
      "LeanDag.Properties.Arcs.decided_fill_agree_of_properties"],
     ["Banded", "Agree"]),
    ("re-genesis", {},
     ["LeanDag.Integration.addGenesis", "LeanDag.Integration.addGenesisNemo",
      "LeanDag.Integration.addGenesisFinWhale", "LeanDag.Integration.addGenesisHZ",
      "LeanDag.Integration.addGenesisHybrid", "LeanDag.Integration.addGenesisOpt"],
     ["Banded", "Agree"]),
    ("adaptive leaders",
     {"FinWhale": "no `BaseRule` instance",
      "Mahi-Mahi": "no `BaseRule` instance"},
     ["LeanDag.Barnacle.descent_of_support"],
     ["Support", "Indirect"]),
    ("chain quality", {},
     ["LeanDag.Properties.Arcs.card_coveredAt_ge_of_decided",
      "LeanDag.Properties.Arcs.card_correct_le_two_mul_coveredAt_of_decided",
      "LeanDag.Properties.Arcs.ledger_coverage",
      "LeanDag.Properties.Arcs.mem_history_of_decided_commit",
      "LeanDag.Properties.Arcs.committed_of_correct_block",
      "LeanDag.Properties.Arcs.chain_quality"],
     ["Causal", "Quorate", "CommitsCandidate"]),
]


# Barnacle reaches a rule through its `LiveRule`, which extends the
# carrier: a descent theorem names `mysticetiLive`, not `mysticetiRule`.
# For the leaders column those names count as the rule's.
LIVE_RULES = {
    "core Mysticeti": ["Barnacle.mysticetiLive"],
    "reactive Mysticeti": ["Barnacle.mysticetiLive"],
    "Hydrozoan": ["Barnacle.hydrozoanLive"],
    "Optimal-Hydrozoan": ["Barnacle.optimalHydrozoanLive"],
    "Odontoceti": ["Barnacle.odontocetiLive"],
    "Nemo": ["Barnacle.nemoLive"],
    "Hybrid / Orcaella": ["Barnacle.orcaellaLive"],
}


def graph():
    """Declaration -> what it uses, from the dependency graph."""
    uses = collections.defaultdict(set)
    for line in (ROOT / "docs" / "depgraph" / "deps.tsv").read_text().splitlines():
        parts = line.split("\t")
        if parts[0] == "EDGE":
            uses[parts[1]].add(parts[2])
    return uses


def main():
    import json
    path = ROOT / "docs" / "decls.json"
    if not path.exists():
        print("docs/decls.json missing; run scripts/extract-decls.py", file=sys.stderr)
        return 1
    shown = conformance.conclusions(json.loads(path.read_text()))
    uses = graph()

    # A carrier is "reached with" an entry point when one declaration
    # names both: the entry point is the mechanism, the carrier is the
    # rule it was applied at.
    applied = collections.defaultdict(set)
    for name, _, entries, _ in MECHANISMS:
        for d, used in uses.items():
            if not any(e in used for e in entries):
                continue
            for carrier in {c for _, cs, _ in conformance.RULES for c in cs}:
                if "LeanDag." + carrier in used:
                    applied[name].add(carrier)
            for rule, lives in LIVE_RULES.items():
                for lv in lives:
                    if "LeanDag." + lv in used:
                        applied[name].update(
                            cs for r, cs, _ in conformance.RULES if r == rule)

    width = max(len(name) for name, _, _ in conformance.RULES) + 1
    cols = [name for name, _, _, _ in MECHANISMS]
    head = {"garbage collection": "cut", "extension": "extend", "re-genesis": "regen",
            "adaptive leaders": "leaders", "chain quality": "quality"}
    # Liveness across the DAG-transforming mechanisms is one generic theorem
    # per shape (`Support.live_of_sustains`, `Support.live_of_truncates`), fed
    # by the witness the mechanism already has. A rule with a support and a
    # witness therefore has it with nothing written per cell, which the
    # column scores as `der`; `yes` records an instance somebody did write.
    LIVE_ENTRIES = ["LeanDag.Properties.Support.live_of_sustains",
                    "LeanDag.Properties.Support.live_of_truncates",
                    "LeanDag.Properties.Support.decidedBelow_of_run_sustains",
                    "LeanDag.Properties.Support.decidedBelow_of_run_truncates"]
    live_applied = set()
    for d, used in uses.items():
        if not any(e in used for e in LIVE_ENTRIES):
            continue
        for carrier in {c for _, cs, _ in conformance.RULES for c in cs}:
            if "LeanDag." + carrier in used:
                live_applied.add(carrier)
    print("mechanisms applied, by rule (`open` = the properties are there "
          "and nobody collected)\n")
    print(" " * width + "  ".join(head[c].ljust(8) for c in cols) + "  live    ")
    gaps = []
    for rule, carriers, _ in conformance.RULES:
        cells = []
        transformed = False
        for name, skip, _, needs in MECHANISMS:
            if not carriers or rule in skip:
                cells.append("--      ")
                continue
            has = all(any(c in shown.get(p, ()) for c in carriers) for p in needs)
            got = any(c in applied[name] for c in carriers)
            if got:
                cells.append("yes     ")
                if name in ("garbage collection", "extension", "re-genesis"):
                    transformed = True
            elif has:
                cells.append("open    ")
                gaps.append((rule, name, needs))
            else:
                cells.append("--      ")
        has_supp = any(c in shown.get("Support", ()) for c in carriers)
        if any(c in live_applied for c in carriers):
            cells.append("yes     ")
        elif has_supp and transformed:
            cells.append("der     ")
        else:
            cells.append("--      ")
        print(rule.ljust(width) + "  ".join(cells))

    print()
    total = sum(1 for _ in gaps)
    if gaps:
        print(f"{total} cells are open — the rule shows what the mechanism asks "
              f"and no instance exists:")
        for rule, name, needs in gaps:
            print(f"  {rule:20s} {name:20s} (has {', '.join(needs)})")
    else:
        print("no open cells.")
    print("`live`: liveness across every DAG-transforming mechanism the rule has a witness\n"
          "  for — `der` from the rule's support and the witness alone (`Arcs/Liveness.lean`),\n"
          "  `yes` where an instance is written.")
    print("\n`--`: the rule has no carrier, does not show what the mechanism asks "
          "(which is\n`audit-conformance.py`'s business), or is out of scope for it:")
    for name, skip, _, _ in MECHANISMS:
        for rule, why in sorted(skip.items()):
            print(f"  {rule:20s} {name:20s} {why}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
