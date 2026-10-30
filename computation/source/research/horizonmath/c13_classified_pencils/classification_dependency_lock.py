#!/usr/bin/env python3
"""Focused fail-closed audit of the external classification boundary for C(13,7,4).

This does not reprove Gordon--Patashnik--Petro--Taylor.  It checks the finite
objects used after that theorem is invoked:

* all 28^3 literal Figure-1 completions are regenerated from source data;
* the 576 construction-group permutations partition them into 67 classes;
* the exceptional Figure-6 cover is added separately;
* the resulting 68 literal links agree with the frozen proof catalog;
* every regenerated link is a 15-block (12,6,3) cover; and
* both pointed-star mapping routines are exhaustively checked against brute
  force on every simple graph on four vertices under every relabeling.

The point of this checker is to make a referee-sensitive dependency boundary
small and executable without modifying the frozen theorem replay.
"""
from __future__ import annotations

import json
from itertools import combinations, permutations, product
from pathlib import Path

import independent_source as IS
import verify_pencils as V

HERE = Path(__file__).resolve().parent
P = tuple(range(12))
LABELS = "0123456789AB"
CORE_WORDS = (
    "014589", "0167AB", "2345AB", "236789",
    "02468A", "02579B", "13469B", "13578A",
    "03478B", "03569A", "12479A", "12568B",
)
FIG6_LABELS = "0123456789TE"
FIG6_WORDS = (
    "012345", "012678", "0129TE", "0378TE", "0456TE",
    "045789", "034569", "13689E", "14579E", "14568T",
    "13457T", "23679T", "24589T", "24567E", "23458E",
)


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def literal_sources():
    core = tuple(
        frozenset(LABELS.index(ch) for ch in word) for word in CORE_WORDS
    )
    short = tuple(frozenset(range(4 * g, 4 * g + 4)) for g in range(3))
    choices = tuple(
        tuple(q | frozenset(extra) for extra in combinations(sorted(set(P) - q), 2))
        for q in short
    )
    f6 = tuple(
        frozenset(FIG6_LABELS.index(ch) for ch in word) for word in FIG6_WORDS
    )
    need(len(core) == 12 and len(set(core)) == 12, "Figure-1 core malformed")
    need(len(f6) == 15 and len(set(f6)) == 15, "Figure-6 source malformed")
    need(tuple(len(c) for c in choices) == (28, 28, 28), "completion choices")
    return core, short, choices, f6


def construction_group(core, short):
    target_core = set(core)
    target_short = set(short)
    p4 = tuple(permutations(range(4)))
    group = []
    for gp in permutations(range(3)):
        for within in product(p4, repeat=3):
            perm = tuple(
                4 * gp[i // 4] + within[i // 4][i % 4] for i in P
            )
            if {frozenset(perm[x] for x in b) for b in core} != target_core:
                continue
            if {frozenset(perm[x] for x in b) for b in short} != target_short:
                continue
            group.append(perm)
    need(len(group) == len(set(group)) == 576, "construction group order")
    return tuple(group)


def completion_key(blocks):
    return tuple(sorted(tuple(sorted(b)) for b in blocks))


def quotient_raw_completions(core, choices, group):
    unseen = {
        completion_key(extras)
        for extras in product(*choices)
    }
    need(len(unseen) == 28 ** 3 == 21952, "raw Figure-1 completion count")
    reps = []
    orbit_sizes = []
    while unseen:
        rep = min(unseen)
        orbit = {
            completion_key(frozenset(g[x] for x in b) for b in rep)
            for g in group
        }
        need(orbit <= unseen, "construction-group orbit overlap")
        unseen -= orbit
        reps.append(rep)
        orbit_sizes.append(len(orbit))
    need(len(reps) == 67, "Figure-1 quotient class count")
    need(sum(orbit_sizes) == 21952, "Figure-1 orbit partition total")
    links = tuple(
        core + tuple(frozenset(b) for b in rep)
        for rep in reps
    )
    return links, tuple(orbit_sizes)


def covers_all_triples(link):
    return all(any(set(t) <= b for b in link) for t in combinations(P, 3))


def check_catalog(figure1, f6):
    data = json.loads((HERE / "minimum_link_catalog.json").read_text())
    need(data.get("schema") == "c13-minimum-link-catalog-v1", "catalog schema")
    classes = data.get("classes", [])
    need(len(classes) == 68, "catalog class count")
    rebuilt = figure1 + (f6,)
    for cid, (link, row) in enumerate(zip(rebuilt, classes), 1):
        need(row.get("class_id") == cid, f"catalog class id {cid}")
        need(
            {tuple(sorted(b)) for b in link}
            == {tuple(block) for block in row.get("blocks", [])},
            f"literal catalog mismatch at class {cid}",
        )
        need(len(link) == len(set(link)) == 15, f"distinct blocks class {cid}")
        need(all(len(b) == 6 for b in link), f"block size class {cid}")
        need(covers_all_triples(link), f"triple coverage class {cid}")
    return len(classes)


def brute_maps(source, sp, target, tp):
    target_set = set(target)
    out = set()
    for image in permutations(tp):
        mapping = dict(zip(sp, image))
        if {frozenset(mapping[x] for x in b) for b in source} == target_set:
            out.add(tuple(mapping[x] for x in sp))
    return out


def audit_star_mappers():
    """Compare both project mappers with brute force on every graph/relabeling."""
    sp = (0, 1, 2, 3)
    tp = (4, 5, 6, 7)
    edges = tuple(frozenset(e) for e in combinations(sp, 2))
    cases = 0
    maps_checked = 0
    for mask in range(1 << len(edges)):
        source = tuple(edges[i] for i in range(len(edges)) if mask & (1 << i))
        for image in permutations(tp):
            renaming = dict(zip(sp, image))
            target = tuple(
                frozenset(renaming[x] for x in edge) for edge in source
            )
            expected = brute_maps(source, sp, target, tp)
            got_primary = {
                tuple(g[x] for x in sp)
                for g in V.star_maps(source, sp, target, tp)
            }
            got_independent = {
                tuple(g[x] for x in sp)
                for g in IS.maps_by_partitions(source, sp, target, tp)
            }
            need(got_primary == expected, "primary star mapper omitted/added map")
            need(got_independent == expected, "independent star mapper omitted/added map")
            cases += 1
            maps_checked += len(expected)
    need(cases == 64 * 24 == 1536, "star-mapper audit case count")
    return cases, maps_checked


def verify():
    core, short, choices, f6 = literal_sources()
    group = construction_group(core, short)
    figure1, orbit_sizes = quotient_raw_completions(core, choices, group)
    catalog_classes = check_catalog(figure1, f6)

    # Cross-check literal source constants against the separately authored route.
    need(set(core) == set(IS.core), "independent source core disagreement")
    need(set(f6) == set(IS.F6), "independent source Figure-6 disagreement")
    need(IS.raw == 21952, "independent source raw count disagreement")

    mapper_cases, mapper_isomorphisms = audit_star_mappers()
    return {
        "status": "PASS_C13_CLASSIFICATION_DEPENDENCY_LOCK",
        "figure1_raw_completions": 21952,
        "figure1_construction_group_order": len(group),
        "figure1_quotient_classes": len(figure1),
        "figure1_orbit_total": sum(orbit_sizes),
        "exceptional_figure6_included": True,
        "frozen_catalog_classes": catalog_classes,
        "all_rebuilt_links_are_15_block_123_covers": True,
        "star_mapper_bruteforce_cases": mapper_cases,
        "star_mapper_bruteforce_isomorphisms": mapper_isomorphisms,
        "claim_boundary": (
            "This checker validates the literal finite source objects and the "
            "pointed-star mapping implementations used after the published "
            "minimum-(12,6,3) classification is invoked. It does not reprove "
            "that published classification, establish priority, or authorize release."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
