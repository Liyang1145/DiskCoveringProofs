"""Read-only compact inspection of publication inputs; not proof acceptance."""
import argparse
import json
from pathlib import Path


def compact(value, depth=0):
    if isinstance(value, dict):
        if depth >= 2:
            return {"object_keys": list(value)[:35], "key_count": len(value)}
        return {key: compact(item, depth + 1) for key, item in value.items()}
    if isinstance(value, list):
        if len(value) <= 12:
            return [compact(item, depth + 1) for item in value]
        return {"items": len(value), "first": compact(value[0], depth + 1)}
    if isinstance(value, str) and len(value) > 700:
        return value[:700] + "...[truncated]"
    return value


parser = argparse.ArgumentParser()
parser.add_argument("paths", nargs="+")
args = parser.parse_args()
for raw_path in args.paths:
    path = Path(raw_path)
    try:
        data = json.loads(path.read_text(encoding="utf-8-sig"))
    except Exception as exc:
        print(json.dumps({"path": str(path), "error": type(exc).__name__}))
        continue
    print(json.dumps({"path": str(path), "data": compact(data)}, ensure_ascii=False, indent=2))
