#!/usr/bin/env python3
"""Fail-closed one-command release gate for the internal C(13,7,4)=30 packet.

The gate does not prove the published minimum-(12,6,3) classification. It
verifies the repository-controlled finite computation and its frozen evidence:
all manifest hashes, two independently structured full replays in normal and
optimized Python, a strict-warning native C++ replay plus UBSan-equivalent build,
hostile/positive tests in both modes, and the headline census.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "verification_manifest.json"
PRIMARY = ROOT / "primary_replay.json"
INDEPENDENT = ROOT / "independent_replay.json"
NATIVE = ROOT / "native_review"
NATIVE_OUTPUT_SHA256 = "b06bc67b873b1969da5b0219af89fa9a7c955573084af0855333285e43b368ff"
DOMAIN_DIGEST = "425ec3b48e8eecdcc3eb5ac1dbe2555b28420967ea7db00cb690c1e44ddbcb5e"


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_json(script: str, optimized: bool) -> dict:
    cmd = [sys.executable]
    if optimized:
        cmd.append("-O")
    cmd.append(script)
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    need(
        proc.returncode == 0,
        f"{script} {'-O' if optimized else 'normal'} failed: {proc.stderr[-4000:]}",
    )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            f"{script} {'-O' if optimized else 'normal'} emitted non-JSON stdout"
        ) from exc


def run_tests(optimized: bool) -> None:
    cmd = [sys.executable]
    if optimized:
        cmd.append("-O")
    cmd += ["-m", "unittest", "test_classified_pencils", "-v"]
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    need(
        proc.returncode == 0,
        "test_classified_pencils "
        + ("-O " if optimized else "")
        + f"failed: {(proc.stdout + proc.stderr)[-6000:]}",
    )


def check_manifest() -> dict:
    manifest = json.loads(MANIFEST.read_text())
    need(manifest.get("schema") == "c13-classified-pencil-verification-v1", "manifest schema")
    files = manifest.get("files")
    need(isinstance(files, dict) and files, "manifest file map")
    checked = {}
    for name, expected in sorted(files.items()):
        path = ROOT / name
        need(path.is_file(), f"missing manifest file: {name}")
        got = sha256(path)
        need(got == expected, f"hash mismatch: {name}: {got} != {expected}")
        checked[name] = got
    return manifest


def check_headline(primary: dict, independent: dict) -> None:
    need(primary.get("status") == "PASS_EXACT_ALL68_CLASSIFIED_PENCIL_OBSTRUCTION", "primary status")
    need(primary.get("root_link_classes") == 68, "primary root-class count")
    need(primary.get("figure1_classes") == 67, "primary Figure-1 class count")
    need(primary.get("exceptional_figure6_included") is True, "primary Figure-6 inclusion")
    need(primary.get("minimum_point_quadruples") == 33660, "primary quadruple count")
    need(primary.get("pair_closed") == 31263, "primary pair-closed count")
    need(primary.get("arc_closed") == 2355, "primary arc-closed count")
    need(primary.get("union_search_closed") == 42, "primary joined-case count")
    need(primary.get("remaining_14_block_pencil_assignments") == 0, "primary surviving 14-block assignment")
    need(primary["pair_closed"] + primary["arc_closed"] + primary["union_search_closed"] == 33660,
         "primary partition does not sum")

    control = primary.get("positive_control", {})
    need(control.get("cover_blocks") == 30, "primary 30-cover block count")
    need(control.get("covered_quadruples") == 715, "primary 30-cover coverage")
    need(control.get("outside_blocks") == 15, "primary positive-control outside count")
    need(control.get("retained_actual_pencils") == 3, "primary positive-control pencil count")

    need(independent.get("status") == "PASS_INDEPENDENT_GLOBAL29_PENCIL_EXCLUSION", "independent status")
    need(independent.get("root_classes") == 68, "independent root-class count")
    need(independent.get("figure1_root_classes") == 67, "independent Figure-1 count")
    need(independent.get("exceptional_figure6") is True, "independent Figure-6 inclusion")
    need(independent.get("source_raw_completions") == 21952, "independent raw completion count")
    need(independent.get("source_core_group") == 576, "independent source group")
    need(independent.get("source_star_types") == 62, "independent star-type count")
    need(independent.get("point_quadruples") == 33660, "independent quadruple count")
    need(independent.get("pair_closed") == 31263, "independent pair-closed count")
    need(independent.get("arc_closed") == 2355, "independent arc-closed count")
    need(independent.get("joined_cases") == 42, "independent joined-case count")
    need(independent.get("compatible_tuples") == 280152, "independent compatible tuple count")
    need(independent.get("minimum_joined_union") == 15, "independent minimum union")
    need(independent.get("positive30_quadruples") == 715, "independent positive-control coverage")
    need(independent["pair_closed"] + independent["arc_closed"] + independent["joined_cases"] == 33660,
         "independent partition does not sum")

    need(primary.get("domain_digest") == DOMAIN_DIGEST, "primary domain digest")
    need(independent.get("domain_digest") == DOMAIN_DIGEST, "independent domain digest")



def run_checked(cmd: list[str], cwd: Path, label: str) -> subprocess.CompletedProcess:
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        text=True,
        capture_output=True,
        check=False,
    )
    need(
        proc.returncode == 0,
        f"{label} failed: {(proc.stdout + proc.stderr)[-6000:]}",
    )
    return proc


def check_native_manifest() -> dict:
    path = NATIVE / "verification_manifest.json"
    need(path.is_file(), "missing native verification manifest")
    manifest = json.loads(path.read_text())
    need(manifest.get("schema") == "c13-native-rigidity-v1", "native manifest schema")
    files = manifest.get("files")
    need(isinstance(files, list) and files, "native manifest file list")
    for entry in files:
        need(isinstance(entry, dict), "native manifest entry")
        name = entry.get("path")
        expected = entry.get("sha256")
        expected_bytes = entry.get("bytes")
        need(isinstance(name, str) and isinstance(expected, str), "native manifest fields")
        target = NATIVE / name
        need(target.is_file(), f"missing native manifest file: {name}")
        need(target.stat().st_size == expected_bytes, f"native byte-count mismatch: {name}")
        got = sha256(target)
        need(got == expected, f"native hash mismatch: {name}: {got} != {expected}")
    return manifest


def run_native() -> dict:
    native_manifest = check_native_manifest()
    run_checked(
        [sys.executable, "prepare_catalog.py", "--proof-dir", "..", "--check"],
        NATIVE,
        "native catalog preparation check",
    )

    with tempfile.TemporaryDirectory(prefix="c13-global30-native-") as td:
        td = Path(td)
        optimized_bin = td / "c13-native"
        ubsan_bin = td / "c13-native-ubsan"
        optimized_out = td / "c13-native.jsonl"
        ubsan_out = td / "c13-native-ubsan.jsonl"

        run_checked(
            [
                "g++", "-O2", "-std=c++17", "-Wall", "-Wextra", "-Werror", "-pedantic",
                "check_pencils.cpp", "-lcrypto", "-o", str(optimized_bin),
            ],
            NATIVE,
            "native strict-warning compile",
        )
        primary = run_checked([str(optimized_bin)], NATIVE, "native optimized replay")
        optimized_out.write_text(primary.stdout)
        need(
            hashlib.sha256(primary.stdout.encode()).hexdigest() == NATIVE_OUTPUT_SHA256,
            "native optimized output hash",
        )
        need(
            primary.stdout == (NATIVE / "compiled-output.jsonl").read_text(),
            "native optimized output differs from frozen output",
        )
        run_checked(
            [
                sys.executable, "validate_compiled.py", str(optimized_out),
                "--proof-dir", "..",
            ],
            NATIVE,
            "native optimized receipt validation",
        )

        run_checked(
            [
                "g++", "-O1", "-g", "-std=c++17", "-Wall", "-Wextra", "-Werror", "-pedantic",
                "-fsanitize=undefined", "-fno-sanitize-recover=all", "-D_GLIBCXX_ASSERTIONS",
                "check_pencils.cpp", "-lcrypto", "-o", str(ubsan_bin),
            ],
            NATIVE,
            "native UBSan compile",
        )
        ubsan = run_checked([str(ubsan_bin)], NATIVE, "native UBSan replay")
        ubsan_out.write_text(ubsan.stdout)
        need(not ubsan.stderr.strip(), f"native UBSan diagnostics: {ubsan.stderr[-4000:]}")
        need(primary.stdout == ubsan.stdout, "native optimized/UBSan output divergence")
        run_checked(
            [
                sys.executable, "validate_compiled.py", str(ubsan_out),
                "--proof-dir", "..",
            ],
            NATIVE,
            "native UBSan receipt validation",
        )

    compiler = run_checked(["g++", "--version"], NATIVE, "g++ version").stdout.splitlines()[0]
    return {
        "native_status": "PASS_COMPILED_DOMAIN_AND_GLOBAL_CENSUS_CROSSCHECK",
        "native_manifest_files_verified": len(native_manifest["files"]),
        "native_output_sha256": NATIVE_OUTPUT_SHA256,
        "native_optimized_ubsan_equivalence": True,
        "native_compiler": compiler,
    }

def verify() -> dict:
    manifest = check_manifest()

    frozen_primary = json.loads(PRIMARY.read_text())
    frozen_independent = json.loads(INDEPENDENT.read_text())

    primary_normal = run_json("verify_pencils.py", optimized=False)
    primary_optimized = run_json("verify_pencils.py", optimized=True)
    need(primary_normal == primary_optimized, "primary normal/-O replay divergence")
    need(primary_normal == frozen_primary, "primary replay differs from frozen receipt")

    independent_normal = run_json("independent_raw_replay.py", optimized=False)
    independent_optimized = run_json("independent_raw_replay.py", optimized=True)
    need(independent_normal == independent_optimized, "independent normal/-O replay divergence")
    need(independent_normal == frozen_independent, "independent replay differs from frozen receipt")

    check_headline(primary_normal, independent_normal)

    run_tests(optimized=False)
    run_tests(optimized=True)
    native = run_native()

    return {
        "status": "PASS_C13_GLOBAL30_RELEASE_GATE",
        "theorem": "C(13,7,4)=30",
        "assurance_boundary": (
            "Repository-controlled exact finite proof and independent replay pass; "
            "published minimum-(12,6,3) classification remains an external theorem "
            "dependency. No novelty, external-referee, or proof-assistant claim."
        ),
        "manifest_files_verified": len(manifest["files"]),
        "primary_status": primary_normal["status"],
        "independent_status": independent_normal["status"],
        "root_classes": 68,
        "minimum_point_quadruples": 33660,
        "pair_closed": 31263,
        "arc_closed": 2355,
        "joined_cases": 42,
        "compatible_tuples": 280152,
        "minimum_joined_union": 15,
        "positive_control_quadruples": 715,
        "domain_digest": DOMAIN_DIGEST,
        "normal_optimized_equivalence": True,
        "hostile_positive_tests_normal_and_optimized": True,
        **native,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--receipt", type=Path)
    args = ap.parse_args()
    out = verify()
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    if args.receipt is not None:
        args.receipt.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
