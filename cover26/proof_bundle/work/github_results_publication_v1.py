"""Publish only explicitly selected research files. Never persist credentials."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from urllib.parse import quote

CURL = r"C:\Windows\System32\curl.exe"
GIT = r"C:\热爱单机但萌新\dependencies\Git\cmd\git.exe"
TOKEN_ENV = "CODEX_RESULTS_PUBLICATION_TOKEN"


def api(method, route, payload=None, upload=None, timeout=60):
    token = os.environ.get(TOKEN_ENV, "")
    if not token:
        raise RuntimeError(f"Set {TOKEN_ENV} for this process only.")
    if any(char in token for char in '\r\n"'):
        raise RuntimeError("Invalid credential characters.")
    hostname = "uploads.github.com" if upload else "api.github.com"
    ip = args.upload_ip if upload else args.api_ip
    url = route if route.startswith("https://") else f"https://{hostname}{route}"
    if not url.startswith(f"https://{hostname}/"):
        raise RuntimeError("Refusing to send credentials to another host.")
    config = [
        "url = " + json.dumps(url),
        "request = " + json.dumps(method),
        'header = "Authorization: Bearer ' + token + '"',
        'header = "Accept: application/vnd.github+json"',
        'header = "X-GitHub-Api-Version: 2022-11-28"',
        'header = "User-Agent: Codex-results-publication"',
    ]
    command = [
        CURL, "--config", "-", "--silent", "--show-error",
        "--connect-timeout", "15", "--max-time", str(timeout),
        "--resolve", f"{hostname}:443:{ip}", "--write-out", "\n%{http_code}",
    ]
    if upload:
        config.append('header = "Content-Type: application/octet-stream"')
        command.extend(["--data-binary", "@" + str(upload)])
    elif payload is not None:
        config.append('header = "Content-Type: application/json"')
        config.append("data = " + json.dumps(json.dumps(payload, ensure_ascii=True)))
    response = subprocess.run(
        command, input="\n".join(config) + "\n", encoding="utf-8",
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if response.returncode:
        raise RuntimeError("GitHub transport failed: " + response.stderr.replace(token, "[redacted]"))
    raw, status = response.stdout.rsplit("\n", 1)
    data = json.loads(raw) if raw.strip() else {}
    if int(status) >= 400:
        raise RuntimeError(f"GitHub HTTP {status}: {data.get('message', 'request failed')}")
    return data


def run_git(arguments, cwd, authenticated=False):
    env = os.environ.copy()
    env["GIT_TERMINAL_PROMPT"] = "0"
    config = ["-c", "core.longpaths=true", "-c", "core.autocrlf=false"]
    if authenticated:
        token = os.environ[TOKEN_ENV]
        basic = base64.b64encode(("x-access-token:" + token).encode()).decode()
        env.update({
            "GIT_CONFIG_COUNT": "2",
            "GIT_CONFIG_KEY_0": "http.https://github.com/.extraHeader",
            "GIT_CONFIG_VALUE_0": "Authorization: Basic " + basic,
            "GIT_CONFIG_KEY_1": "http.curloptResolve",
            "GIT_CONFIG_VALUE_1": f"github.com:443:{args.git_ip}",
        })
        config.extend(["-c", "credential.helper="])
    result = subprocess.run(
        [GIT, *config, *arguments], cwd=cwd, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding="utf-8",
        errors="replace", check=False,
    )
    output = result.stdout
    if authenticated:
        output = output.replace(token, "[redacted]").replace(basic, "[redacted]")
    print(output, end="", flush=True)
    if result.returncode:
        raise RuntimeError(f"Git command failed with status {result.returncode}.")
    return output.strip()


def inspect():
    user = api("GET", "/user")
    repos = api("GET", "/user/repos?per_page=100&sort=updated&affiliation=owner")
    print(json.dumps({
        "login": user["login"], "id": user["id"],
        "repositories": [
            {k: repo.get(k) for k in ("full_name", "private", "description", "html_url")}
            for repo in repos
        ],
    }, ensure_ascii=False, indent=2))


def create():
    user = api("GET", "/user")
    if user["login"] != args.owner:
        raise RuntimeError("Authenticated account does not match the selected owner.")
    repos = api("GET", "/user/repos?per_page=100&affiliation=owner")
    matches = [repo for repo in repos if repo["name"].lower() == args.name.lower()]
    if matches:
        raise RuntimeError("Repository already exists; refusing to overwrite or reuse silently.")
    result = api("POST", "/user/repos", {
        "name": args.name,
        "description": "Local disk-covering proof packages: n=11,12,14,21–25; ongoing n=26 research with explicit proof status.",
        "private": True, "auto_init": False, "has_wiki": False,
    })
    print(json.dumps({k: result[k] for k in ("full_name", "private", "html_url", "clone_url")}, indent=2))


def push():
    root = Path(args.root).resolve()
    expected_url = f"https://github.com/{args.owner}/{args.name}.git"
    if not (root / "README.md").is_file():
        raise RuntimeError("Prepared README missing.")
    if not (root / ".git").exists():
        run_git(["init", "-b", "main"], root)
        run_git(["config", "user.name", args.owner], root)
        run_git(["config", "user.email", f"{args.user_id}+{args.owner}@users.noreply.github.com"], root)
        run_git(["remote", "add", "origin", expected_url], root)
    else:
        current_remote = run_git(["remote", "get-url", "origin"], root)
        if current_remote != expected_url:
            raise RuntimeError("Remote mismatch.")
    run_git(["add", "--all"], root)
    result = subprocess.run([GIT, "diff", "--cached", "--quiet"], cwd=root, check=False)
    if result.returncode == 1:
        run_git(["commit", "--quiet", "-m", args.message], root)
    elif result.returncode != 0:
        raise RuntimeError("Unable to inspect staged changes.")
    run_git(["push", "-u", "origin", "main"], root, authenticated=True)
    head = run_git(["rev-parse", "HEAD"], root)
    remote = api("GET", f"/repos/{args.owner}/{args.name}/git/ref/heads/main")
    if remote["object"]["sha"] != head:
        raise RuntimeError("Remote commit does not match local HEAD.")
    print(json.dumps({"remote_verified": True, "commit": head, "repository": expected_url}, indent=2))


def remote_read():
    data = api("GET", args.route)
    if args.output:
        Path(args.output).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"Saved non-secret GitHub response: {args.output}")
    elif isinstance(data, list):
        print(json.dumps([
            {k: item.get(k) for k in ("name", "path", "type", "sha", "size", "html_url")}
            for item in data
        ], ensure_ascii=False, indent=2))
    else:
        print(json.dumps(data, ensure_ascii=False, indent=2))


parser = argparse.ArgumentParser()
parser.add_argument("--api-ip", default="20.205.243.168")
parser.add_argument("--git-ip", default="20.205.243.166")
parser.add_argument("--upload-ip", default="20.205.243.168")
sub = parser.add_subparsers(dest="action", required=True)
sub.add_parser("inspect")
create_parser = sub.add_parser("create")
create_parser.add_argument("--owner", required=True)
create_parser.add_argument("--name", required=True)
push_parser = sub.add_parser("push")
push_parser.add_argument("--root", required=True)
push_parser.add_argument("--owner", required=True)
push_parser.add_argument("--name", required=True)
push_parser.add_argument("--user-id", required=True)
push_parser.add_argument("--message", required=True)
read_parser = sub.add_parser("read")
read_parser.add_argument("--route", required=True)
read_parser.add_argument("--output")
args = parser.parse_args()
try:
    {"inspect": inspect, "create": create, "push": push, "read": remote_read}[args.action]()
except Exception as error:
    print(f"Publication stopped safely: {error}", file=sys.stderr)
    sys.exit(1)
