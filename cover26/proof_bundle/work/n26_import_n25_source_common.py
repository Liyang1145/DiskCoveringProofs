"""Explicit qualified prior-SOURCE theorem scope and full dependency collection."""

from collections import Counter
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import sys


ROOT = Path("C:/热爱单机但萌新/_incoming-local-math-20261004/recovered-20261004/workspace/"
            "research-2026/n21-25-synthesis/round4-solo-20261004")
SOURCE = ROOT/"n25-global-final5/ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json"
BINDING = ROOT/"n25-all-final-prerequisites-byte-binding-v4/VERIFIED.json"
LEDGER = ROOT/"n25-all-final-prerequisites-byte-binding-v4/CURRENT-INPUTS.jsonl"
FROZEN_LEDGER = SOURCE.parent/"FROZEN-INPUTS.jsonl"
EXPECTED = {
    "accepted": "30389bfa3132d08954281e743db670fbb3874785e0d90c9876d4f5ddeec31dd1",
    "binding": "76939a3cebda597280e67d8ba95319458eb3654a65898e0fd27724e8cfedf33b",
    "ledger": "69be5a2ca453e1581792db62c5300470fef7df2055ca61c630ed50790aa6b058",
}
U = F(234701, 1000000)
TOTALS = {14: 172092, 15: 139315, 16: 120782, 17: 289140}


def local_path(value):
    text = str(value).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper()+":"+text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/"+text[0].lower()+text[2:])
    return Path(text)


def normalized(value):
    # The fixed accepted ledger already stores absolute canonical names.
    # Normalize lexical aliases without opening every file a second time.
    text = os.path.normpath(os.path.abspath(str(local_path(value))))
    return text.casefold() if sys.platform == "win32" else text


def sha(path):
    digest = hashlib.sha256()
    with local_path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024*1024), b""):
            digest.update(block)
    return digest.hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON object key: "+str(key))
        result[key] = value
    return result


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"), object_pairs_hook=unique_object)


def scope_gate(accepted, binding):
    if (
        accepted["schema"] != "N25-arbitrary-unit-closed-disk-cover-global-computer-assisted-source-proof-v1"
        or accepted["verified"] is not True or accepted["N"] != 25
        or accepted["theorem"] != "r_D(25)=1/(sqrt(6)+sqrt(3))"
        or accepted["exact_radius"] != "1/(sqrt(6)+sqrt(3))"
        or accepted["exact_radius_squared_Qsqrt2"] != ["1", "-2/3"]
        or accepted["global_source_proof_closed"] is not True
        or accepted["global_optimality_proved"] is not True
        or accepted["all_pending_families"] != 0
        or accepted["required_boundary_families"] != [14, 15, 16, 17]
        or accepted["complete_necessary_residual_weak_graph_counts"] != list(TOTALS.values())
        or accepted["complete_necessary_residual_weak_graphs"] != 721329
        or accepted["arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed"] is not True
        or accepted["not_Lean_Coq_formalization_not_third_party_peer_review_not_all_attaining_configurations_classified"] is not True
        or accepted["all_old_exact_mathematics_honestly_reused_not_new_full_all_old_tree_replays"] is not True
        or accepted["written_math_not_claimed_machine_proved_by_content_check"] is not True
        or accepted["current_files_and_whole_archives_independently_rechecked"] != 555483
        or accepted["binding_report_independently_verified_by_full_current_content_audit"] is not True
        or accepted["all_prerequisites_binding_sha256"] != EXPECTED["binding"]
        or accepted["frozen_input_ledger_sha256"] != EXPECTED["ledger"]
        or binding["schema"] != "N25-four-whole-source-family-same-radical-root-current-premise-byte-closure-v1"
        or binding["verified"] is not True or binding["N"] != 25
        or binding["global_optimality_proved"] is not False
        or binding["all_required_families"] != [14, 15, 16, 17]
        or binding["complete_necessary_residual_weak_graphs"] != 721329
        or binding["current_files_and_whole_archives_checked"] != 555483
        or binding["current_input_ledger_sha256"] != EXPECTED["ledger"]
        or binding["mismatches"] != []
        or accepted["family_partitions"] != binding["family_partitions"]
        or any(binding[field] is not True for field in (
            "all_four_actual_full_payment_ledgers_independently_sequentially_scanned",
            "all_parent_final_lower_chains_zero",
            "all_current_content_bindings_checked",
            "old_mathematics_honestly_reused_not_new_all_old_tree_replays",
            "written_math_not_claimed_machine_proved_by_content_checks",
            "correct_original_B17_222283_plus66857_equals289140_not_manuscript_typo"))
    ):
        raise ValueError("import lost the exact arbitrary-cover qualified completed N25 SOURCE theorem")
    if (
        accepted["original_B17_final_terminal_observed"] is not True
        or accepted["binding_creator_terminal_observed"] is not False
        or accepted["source_document_sha256"] != binding["global_source_manuscript_sha256"]
        or accepted["source_B17_count_erratum_sha256"] != binding["global_source_B17_count_erratum_sha256"]
    ):
        raise ValueError("N25 source history, manuscript or original missing-terminal qualification changed")
    for row, b in zip(binding["family_partitions"], range(14, 18), strict=True):
        if row["B"] != b or row["complete_necessary_parents"] != TOTALS[b] or row["pending"] != 0:
            raise ValueError("N25 imported source has a missing or unfinished whole family")
    threshold = F(3, 2)*(1-U*U)
    if threshold <= 0 or threshold**2 <= 2:
        raise ValueError("N26 screen is not below the exact N25 radical lower bound")
    return {
        "exact_N26_radius_screen": str(U),
        "exact_positive_threshold_above_sqrt2": str(threshold),
        "exact_threshold_square_margin_above_two": str(threshold**2-2),
        "imported_n25_lower_bound_STRICTLY_above_N26_screen": True,
        "every_at_most26_cover_in_scope_has_EXACTLY26_original_distinct_necessary_disks": True,
        "no_corner_shadow_padding_needed_after_slack_generic_perturbation_below_screen": True,
        "import_scope": "qualified completed computer-assisted SOURCE theorem; not Lean/Coq or peer review",
    }


def collect_prior_inventory(accepted, extra_files):
    if sha(LEDGER) != EXPECTED["ledger"] or sha(FROZEN_LEDGER) != EXPECTED["ledger"]:
        raise ValueError("N25 accepted frozen/current prerequisite ledger changed")
    inventory, aliases = {}, {}
    # The historical C: incoming directory is now a junction to its F:
    # archive. Preserve the accepted ledger's original C: path identities,
    # while permitting the exact resolved archive root, not arbitrary drives.
    incoming_literal = Path(os.path.normpath(os.path.abspath(str(ROOT.parents[4]))))
    dependencies_literal = incoming_literal.parent/"dependencies"
    allowed = (
        incoming_literal, incoming_literal.resolve(),
        dependencies_literal, dependencies_literal.resolve(),
    )
    previous, count = None, 0
    with LEDGER.open(encoding="ascii") as stream:
        for count, line in enumerate(stream, 1):
            row = json.loads(line, object_pairs_hook=unique_object)
            if set(row) != {"path", "sha256"}:
                raise ValueError("invalid old N25 prerequisite row")
            path = Path(os.path.normpath(os.path.abspath(str(local_path(row["path"])))))
            digest = row["sha256"]
            key = normalized(path)
            if (
                not path.is_absolute() or not any(path.is_relative_to(root) for root in allowed)
                or key in aliases or not isinstance(digest, str) or len(digest) != 64
                or any(c not in "0123456789abcdef" for c in digest)
                or (previous is not None and previous >= row["path"])
            ):
                raise ValueError(json.dumps({
                    "invalid_N25_prerequisite_row": count, "path": str(path),
                    "absolute": path.is_absolute(),
                    "within_original_allowed_roots": any(path.is_relative_to(root) for root in allowed),
                    "normalized_duplicate": key in aliases,
                    "valid_digest": isinstance(digest, str) and len(digest) == 64
                        and all(c in "0123456789abcdef" for c in digest),
                    "strict_original_ledger_order": previous is None or previous < row["path"],
                    "original_allowed_roots": list(map(str, allowed)),
                }))
            inventory[str(path)] = digest
            aliases[key] = str(path)
            previous = row["path"]
            if count % 100000 == 0:
                print(json.dumps({"prior_N25_fixed_prerequisite_rows_collected": count,
                                  "NOT_yet_content_rehashed": True}), flush=True)
    if count != 555483:
        raise ValueError("imported N25 prerequisite closure is truncated or enlarged")
    old_count = count
    entries = {
        **accepted["new_global_entry_frozen_files"],
        str(SOURCE): EXPECTED["accepted"], str(BINDING): EXPECTED["binding"],
        str(LEDGER): EXPECTED["ledger"], str(FROZEN_LEDGER): EXPECTED["ledger"],
        **{str(path.resolve()): sha(path) for path in extra_files},
    }
    for text, digest in entries.items():
        path = Path(os.path.normpath(os.path.abspath(str(local_path(text)))))
        key = normalized(path)
        if key in aliases:
            if inventory[aliases[key]] != digest:
                raise ValueError("old proof and newly imported global-entry bindings disagree")
        else:
            inventory[str(path)] = digest
            aliases[key] = str(path)
    return inventory, old_count


def family_ledger_gate(accepted):
    results = []
    for part in accepted["family_partitions"]:
        b = part["B"]
        for field, digest_field in (
            ("final_path", "final_sha256"), ("payment_ledger_path", "payment_ledger_sha256"),
            ("pending_ledger_path", "pending_ledger_sha256"),
        ):
            if sha(part[field]) != part[digest_field]:
                raise ValueError("N25 actual family ledger/final bytes changed")
        final = read(part["final_path"])
        if final["verified"] is not True or (final["N"], final["B"]) != (25, b):
            raise ValueError("wrong imported N25 family final")
        counter = Counter()
        index = -1
        with local_path(part["payment_ledger_path"]).open(encoding="ascii") as stream:
            for index, line in enumerate(stream):
                row = json.loads(line, object_pairs_hook=unique_object)
                if row["parent_group" if b == 14 else "parent_index"] != index:
                    raise ValueError("missing, duplicated or reordered N25 parent payment")
                status = row["kind" if b == 14 else "status"]
                counter[status] += 1
                if status == "nonstrict-same-root-complete-family" and (
                    b != 16 or index != 115569
                    or row["strict_completion_types"] != 90 or row["same_root_core_completion_types"] != 1
                    or row["core_lower_radius"] != "1/(sqrt(6)+sqrt(3))"
                    or row["not_a_strict_upper_radius_weak_graph_exclusion"] is not True
                    or row["transport_sha256"] != sha(ROOT/"n25-B16-p115569-nonstrict1/VERIFIED.json")
                ):
                    raise ValueError("N25 attaining parent was mis-scoped as a strict upper-radius exclusion")
        if index+1 != TOTALS[b] or dict(counter) != part["actual_payment_kinds"]:
            raise ValueError("N25 whole-family payment partition disagrees")
        residual = local_path(part["pending_ledger_path"])
        if b == 14:
            with residual.open(encoding="ascii") as stream:
                header = json.loads(next(stream), object_pairs_hook=unique_object)
                if header["schema"] != "independent-all-parent-B14-chain-residual-v1" or (
                    header["N"], header["B"]) != (25, 14) or stream.read().strip():
                    raise ValueError("N25 B14 has an unpaid residual")
        elif residual.stat().st_size != 0:
            raise ValueError("N25 imported family has an unpaid residual")
        results.append({"B": b, "whole_parent_rows_freshly_checked": index+1,
                        "actual_payment_kinds": dict(counter), "pending": 0})
        print(json.dumps({"imported_N25_full_parent_ledger_checked": b,
                          "parents": index+1, "old_mathematical_trees_NOT_replayed": True}), flush=True)
    return results
