#!/usr/bin/env python3
"""Lane C / part 300: exact per-index leaf-assignment plan for the C01-C04
census membership proofs.

Diagnosis (part 299, from the real CI job log of run 41769569707):
`mem_iff_id_KKKK` is proved by one `decide +kernel +revert` on
`(data KKKK).terminal = true / KKKK ∉ sharpIDs / KKKK ∉ paidIDs`.
`Finset.union`'s value is `s - t + t` (Mathlib/Data/Multiset/UnionInter.lean:45),
so reducing the ~1997-literal nested `paidIDs` value costs ~10^6 comparisons
and whnf hits the 200000 heartbeat cap.  Fix = never let `decide` see a union:
use `Finset.mem_union` structurally down to the *literal* leaves and decide only
on literals (≤ ~210 elements each).

This script reads the actual Lean literals and computes, for every source index,
which literal leaf would contain it, plus the size of the resulting proof, so the
emitter can be generated with exact arithmetic and a self-check.
"""
import re, os, json, glob

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'lean', 'N11Formalization'))


def lit_ids(fn):
    t = open(fn, encoding='utf-8', errors='replace').read()
    d = {}
    for m in re.finditer(r'^def (\w+) : Finset \(Fin 5011\) :=\s*\{([^}]*)\}', t, re.M):
        d[m.group(1)] = [int(x) for x in re.findall(r'\d+', m.group(2))]
    return d


def terminal_flags():
    t = open(os.path.join(LEAN, 'DBMSourceTreeData.lean'), encoding='utf-8', errors='replace').read()
    out = []
    for b in t.split('def node')[1:]:
        m = re.search(r'terminal := (true|false)', b)
        out.append(m.group(1) == 'true')
    return out


def windows(ids):
    """collapse a literal id set to its [lo,hi] window (ids in a block are
    contiguous-ish; return exact min/max)."""
    return (min(ids), max(ids))


def main():
    term = terminal_flags()
    census = json.load(open(os.path.join(HERE, 'residual389-census.json')))
    residual = set(census['residual_ids'])

    n505 = lit_ids(os.path.join(LEAN, 'Paid16GeneralNext505.lean'))
    w505 = {k: windows(v) for k, v in sorted(n505.items())}
    ids505 = set(i for v in n505.values() for i in v)

    n1182 = {}
    w1182 = {}
    for k in range(1, 9):
        d = lit_ids(os.path.join(LEAN, 'Paid16GeneralNext1182S%02d.lean' % k))
        for name, v in d.items():
            n1182['S%02d.%s' % (k, name)] = v
            w1182['S%02d.%s' % (k, name)] = windows(v)
    ids1182 = set(i for v in n1182.values() for i in v)

    # window tiling check: Next1182 sub-blocks must tile [2565, max] with no gap
    wins = sorted(w1182.values())
    tiles = all(wins[i + 1][0] == wins[i][1] + 1 for i in range(len(wins) - 1))
    overlap = all(wins[i][1] < wins[i + 1][0] for i in range(len(wins) - 1))

    # per-index leaf assignment
    leaf1182 = {}
    for name, v in n1182.items():
        for i in v:
            leaf1182[i] = name
    leaf505 = {}
    for name, v in n505.items():
        for i in v:
            leaf505[i] = name

    report = {
        'source_sha256': census.get('source_sha256'),
        'next505': {'parts': len(n505), 'ids': len(ids505), 'range': windows(ids505),
                    'windows': w505},
        'next1182': {'parts': len(n1182), 'ids': len(ids1182), 'range': windows(ids1182),
                     'tiles_contiguous': tiles, 'pairwise_disjoint': overlap,
                     'windows': w1182},
        'terminal_total': sum(term),
        'terminal_by_range': {
            '<1160': sum(1 for i in range(5011) if term[i] and i < 1160),
            '1160..2564': sum(1 for i in range(5011) if term[i] and 1160 <= i < 2565),
            '2565..5010': sum(1 for i in range(5011) if term[i] and i >= 2565),
        },
        'terminal_paid_leaf_required': sum(
            1 for i in range(5011) if term[i] and i >= 2565),
        'decides_if_interval_strategy': {
            'per_high_index_leaf_decide': 1,
            'per_high_index_omega_conjuncts': 63,
            'per_mid_index_omega_conjuncts': 24,
        },
    }
    # sanity: the two paid ranges must be disjoint (Next505 < 2565 <= Next1182)
    report['next505_below_next1182'] = max(ids505) < min(ids1182)
    report['leaf1182_coverage'] = len(leaf1182)
    report['leaf505_coverage'] = len(leaf505)

    out = os.path.join(HERE, 'census-c01-c04-plan.json')
    json.dump(report, open(out, 'w'), indent=1, sort_keys=True)
    print('wrote', out)
    print('Next505 : parts=%d ids=%d range=%s' % (len(n505), len(ids505), windows(ids505)))
    print('Next1182: parts=%d ids=%d range=%s tiles=%s disjoint=%s'
          % (len(n1182), len(ids1182), windows(ids1182), tiles, overlap))
    print('Next505 entirely below Next1182:', report['next505_below_next1182'])
    print('terminal by range:', report['terminal_by_range'])


if __name__ == '__main__':
    main()
