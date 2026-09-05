#!/usr/bin/env python3
"""Which protocols have shown which properties.

`docs/target-properties.md` §11.2. Part 1 of the goal claims a set of
properties every DAG consensus rule must show; part 2 claims that showing
them buys every mechanism. Neither claim is worth much against one
protocol, so the count that matters is how many rules have instances —
and this recomputes it rather than trusting the table.

A rule is "conforming" for a property when some theorem's conclusion is
that property applied to the rule's carrier. Carriers are found by
scanning for `DagRule`-valued definitions, so a new one is picked up
without editing this script; a rule with no carrier cannot show anything
and its reason is recorded below.

Reads `docs/decls.json`; regenerate with `scripts/extract-decls.py`.
Reports only — it never fails a build, since a missing instance is work
outstanding rather than a defect.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The decision rules of this repository. `carrier` is the `DagRule` a
# rule's conformance is stated against, or None with the reason it has
# none.
# A rule may have more than one carrier: the core and Hydrozoan have
# their own, and Barnacle's interface supplies a second for the rules it
# instantiates. A property counts as shown at any of them.
RULES = [
    ("core Mysticeti",     ["MysticetiProperties.mysticetiRule",
                            "Barnacle.mysticetiRule"], "two carriers"),
    ("reactive Mysticeti", ["MysticetiProperties.mysticetiRule"],
                           "shares the core's rule"),
    ("Hydrozoan",          ["Hydrozoan.rule"],                   None),
    ("Optimal-Hydrozoan",  ["Barnacle.optimalHydrozoanRule"],    "carrier via Barnacle"),
    ("Odontoceti",         ["OdontocetiProperties.odontocetiRule",
                            "Barnacle.odontocetiRule"], "two carriers"),
    ("Nemo",               ["Barnacle.nemoRule"],                "carrier via Barnacle"),
    ("Mahi-Mahi",          [], "no carrier; band conditional on `2 <= w` (3.4c)"),
    ("Hybrid / Orcaella",  ["Barnacle.orcaellaRule"],
                           "carrier via Barnacle, one per threshold"),
    ("FinWhale",           [], "no carrier; no `Slots` layer at all (3.4c)"),
    ("Black Marlin",       [], "no carrier; commits by round, no slot-indexed relation"),
]

# The obligations, in the order 11.1 lists them.
# The six every rule owes, then the two in `Properties/Optional/`, owed
# only when a mechanism asks: `CommitsDirect` by a rule whose direct
# predicate a window count reads, `SkipsUnsupported` by one that skips
# without waiting for an anchor.
OBLIGATIONS = ["Causal", "Banded", "Agree", "CommitsCandidate",
               "LeaderCommits", "Indirect", "CommitsDirect", "SkipsUnsupported"]
REQUIRED = 6
DERIVED = ["Persist", "LocalTruncate", "Descends"]
# What each derived property follows from. `Descends` used to be an
# obligation and is now the indirect rule with a downward induction on
# top (`Properties/Derived/Descent.lean`).
DERIVED_FROM = {"Persist": "Banded", "LocalTruncate": "Banded",
                "Descends": "Indirect"}

# Files that state the generic theory rather than an instance of it.
GENERIC = re.compile(r"^LeanDag\.Properties\b")


def owner(carrier):
    """The module prefix a carrier belongs to.

    Needed because two carriers can share a short name: the core's
    `MysticetiProperties.mysticetiRule` and Barnacle's
    `Barnacle.mysticetiRule` both print as `mysticetiRule` inside their
    own namespaces, and matching on the suffix alone credits one with
    the other's instances.
    """
    return "LeanDag." + carrier.split(".")[0]


def conclusions(decls):
    """Map property name -> set of carriers it is shown for.

    Two ways of showing one: a theorem whose conclusion is the property
    at that carrier, or a conformance `Statement` that lists it — both
    count, since a protocol may discharge a conjunct inline rather than
    naming it."""
    out = {}
    for d in decls:
        if GENERIC.match(d["module"]):
            continue
        flat = " ".join(d["statement"].split())
        is_stmt = d["kind"] == "def" and d["name"] in ("Statement", "holds")
        if d["kind"] != "theorem" and not is_stmt:
            continue
        for prop in OBLIGATIONS + DERIVED:
            hit = (re.search(r":\s*(LeanDag\.)?(Properties\.)?" + prop + r"\b", flat)
                   or (is_stmt and re.search(r"Properties\." + prop + r"\b", flat)))
            if not hit:
                continue
            owners = {owner(c) for _, cs, _ in RULES for c in cs}
            for carrier in {c for _, cs, _ in RULES for c in cs}:
                if not re.search(r"\b" + re.escape(carrier.split(".")[-1]) + r"\b", flat):
                    continue
                mine = owner(carrier)
                # A statement in another carrier's namespace names that
                # carrier, not this one.
                if d["module"].startswith(mine) or not any(
                        d["module"].startswith(o) for o in owners if o != mine):
                    out.setdefault(prop, set()).add(carrier)
    return out


def main():
    path = ROOT / "docs/decls.json"
    if not path.exists():
        print("docs/decls.json missing; run scripts/extract-decls.py", file=sys.stderr)
        return 1
    shown = conclusions(json.loads(path.read_text()))

    cols = OBLIGATIONS + ["|"] + DERIVED
    short = {"Causal": "caus", "Banded": "band", "Agree": "agre",
             "CommitsCandidate": "cand", "LeaderCommits": "lead",
             "Indirect": "indr", "CommitsDirect": "drct*",
             "Descends": "desc",
             "SkipsUnsupported": "skip*",
             "Persist": "pers", "LocalTruncate": "trnc",
             "|": "|"}
    width = max(len(name) for name, _, _ in RULES) + 1
    print("obligations, then what follows from them "
          "(der = free; desc = free, given indr)\n")
    print(" " * width + "  ".join(short[c].ljust(4) for c in cols))
    conforming = 0
    for name, carriers, note in RULES:
        cells = []
        has = lambda prop: any(c in shown.get(prop, ()) for c in carriers)
        for c in cols:
            if c == "|":
                cells.append("|   ")
            elif carriers and has(c):
                cells.append("yes ")
            elif c in DERIVED and carriers and has(DERIVED_FROM[c]):
                # a consequence of the band: nothing to show per protocol
                cells.append("der ")
            else:
                cells.append("--  ")
        print(name.ljust(width) + "  ".join(cells) + ("   " + note if note else ""))
        if carriers and all(has(c) for c in OBLIGATIONS[:REQUIRED]):
            conforming += 1

    allcarriers = {c for _, cs, _ in RULES for c in cs}
    without = [n for n, cs, _ in RULES if not cs]
    partial_ = [n for n, cs, _ in RULES
                if cs and not all(any(c in shown.get(o, ()) for c in cs)
                                  for o in OBLIGATIONS[:REQUIRED])]
    print(f"\n{len(allcarriers)} carriers over {len(RULES)} rules; "
          f"{conforming} show all six required properties.")
    if partial_:
        print("Carrier but not the six: " + ", ".join(partial_) + ".")
        print("  `Agree` and `CommitsCandidate` are `Barnacle.Laws` renamed;")
        print("  `Causal` needs the universe-level facts `Laws` states only for views,")
        print("  and `Banded` is the induction each rule owes. Those four are per-rule.")
    if without:
        print(f"{len(without)} with no carrier: " + ", ".join(without) + ".")
    print("* CommitsDirect and SkipsUnsupported are optional "
          "(`Properties/Optional/`): owed\n  only when a mechanism reads the "
          "rule's direct predicate, or the rule skips\n  without waiting for an "
          "anchor.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
