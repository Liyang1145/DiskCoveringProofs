from pathlib import Path

p = Path(__file__).with_name('joint_oracle_attack_new4.py')
s = p.read_text(encoding='utf-8')
bad = """           'pilot_node_read': {k: (None if v is None else [float(x) for x in np.asarray(v)[:8]])
                               for k, v in cand.items()},"""
good = """           'pilot_node_read': {str(k): (None if not hasattr(v, '__len__')
                                        else [float(x) for x in np.asarray(v).reshape(-1)[:8]])
                               for k, v in cand.items()},"""
assert bad in s, 'pilot_node_read block not found'
s = s.replace(bad, good, 1)
p.write_text(s, encoding='utf-8')
print('pilot_node_read guarded')
