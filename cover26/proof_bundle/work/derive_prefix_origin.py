"""Reproducible mechanical derivation; the bound original source is untouched."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import publish, sha


WORK = Path(__file__).resolve().parent
EXPECTED_BASE = "4b172c9236ba49880115dec51f6d3fe401bc495d9497e5e9d9b96e4d1edad724"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    base = WORK / "peel_synthesis_n26_cap8_prefix.cpp"
    if sha(base) != EXPECTED_BASE:
        raise ValueError("frozen prefix source changed")
    source = base.read_text(encoding="utf-8")
    changes = [
        (
            "bool screen=true,audit_order=false;",
            "bool screen=true,audit_order=false;\n"
            "bool origin_screen=false;\nuint64_t origin_prunes=0;",
        ),
        (
            "bool possible(State const&s){\n if(!screen)return true;",
            "bool possible(State const&s){\n"
            " // Necessary for an actual cover with rho < U < 1/4, not for\n"
            " // arbitrary weak graph realizability. Already-added edges persist.\n"
            " if(origin_screen){\n"
            "  uint32_t exposed=(uint32_t(1)<<b)-1;\n"
            "  for(int i=0;i<b;i++)exposed|=s.adjacency[i];\n"
            "  if(exposed==(uint32_t(1)<<n)-1){origin_prunes++;return false;}\n"
            " }\n if(!screen)return true;",
        ),
        ("if(argc!=14)", "if(argc!=15)"),
        (
            "prefix(-|i,j,...) frontier-depth\");",
            "prefix(-|i,j,...) frontier-depth origin-screen(0|1)\");",
        ),
        (
            "auto prefix=parse_prefix(argv[12]);int depth=(int)integer(argv[13]);",
            "auto prefix=parse_prefix(argv[12]);int depth=(int)integer(argv[13]);\n"
            " long long origin_flag=integer(argv[14]);\n"
            " if(origin_flag!=0&&origin_flag!=1)throw runtime_error(\"invalid origin flag\");\n"
            " origin_screen=origin_flag;",
        ),
        (
            "calls=0;prunes=0;started=chrono::steady_clock::now();",
            "calls=0;prunes=0;origin_prunes=0;started=chrono::steady_clock::now();",
        ),
        (
            'f<<",\\"frontier_depth\\":"<<depth<<",\\"scale\\":"<<scale<<",\\"caps\\":[";',
            'f<<",\\"origin_screen\\":"<<(origin_screen?"true":"false")'
            '<<",\\"origin_prunes\\":"<<origin_prunes'
            '<<",\\"frontier_depth\\":"<<depth<<",\\"scale\\":"<<scale<<",\\"caps\\":[";',
        ),
        (
            'catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\\n";return 1;}',
            'catch(exception const&e){cerr<<"REJECTED "<<e.what()'
            '<<" calls="<<calls<<" origin_prunes="<<origin_prunes'
            '<<" survivors="<<survivors.size()<<"\\n";return 1;}',
        ),
    ]
    records = []
    for before, after in changes:
        if source.count(before) != 1:
            raise ValueError("mechanical derivation anchor missing or ambiguous: " + before)
        source = source.replace(before, after)
        records.append({"before": before, "after": after})
    args.output.mkdir(parents=True)
    target = args.output / "peel_prefix_origin.cpp"
    target.write_text(source, encoding="utf-8")
    publish(args.output / "DERIVATION.json", {
        "schema": "N26-prefix-origin-mechanical-derivation-v1",
        "base_path": str(base), "base_sha256": sha(base),
        "source_path": str(target), "source_sha256": sha(target),
        "derivation_script_sha256": sha(__file__),
        "changes": records, "global_optimality_proved": False,
    })
    print(json.dumps({"source": str(target), "source_sha256": sha(target),
                      "base_unchanged": sha(base) == EXPECTED_BASE}), flush=True)


if __name__ == "__main__":
    main()
