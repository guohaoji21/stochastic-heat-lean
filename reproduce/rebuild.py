import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
LOCAL = ROOT / "lean"
UPSTREAM = ROOT / "dependencies"
RESULT = json.loads((ROOT / "reproduce/baseline-lock.json").read_text(encoding="utf-8"))
ORDER = json.loads((ROOT / "reproduce/baseline-build-order.json").read_text(encoding="utf-8"))
IMPORT = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([\w.]+)",
    re.M,
)
COMMENT_TOKEN = re.compile(r'/-|-/|--[^\n]*|"(?:[^"\\]|\\.)*"')
AXIOM_COMMAND = re.compile(r"^#print axioms ([\w.]+)\s*$", re.M)
AXIOM_RESULT = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPILED_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig",
                     ".dll", ".so", ".dylib")
TARGET_AUDIT_COMMAND = '''
open Lean Elab Command
set_option maxHeartbeats 0 in
elab "#audit_target " target:ident : command => do
  let env ← getEnv
  let mod := target.getId
  let some idx := env.getModuleIdx? mod | throwError "Missing target module {mod}"
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    if env.getModuleIdxFor? name == some idx then acc.push name else acc
  if names.isEmpty then
    throwError "No declarations found in target module {mod}"
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    logInfo m!"'{name}' depends on axioms: {axioms.qsort Name.lt |>.toList}"
    for dependency in axioms do
      unless dependency == ``propext || dependency == ``Classical.choice || dependency == ``Quot.sound do
        throwError "Unexpected axiom {dependency} in {name}"
'''


def module_path(module, extension):
    return Path(*module.split(".")).with_suffix(extension)


def hash_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def artifact_digest(paths, root):
    digest = hashlib.sha256()
    for path in sorted(paths):
        if path.is_file():
            digest.update(path.relative_to(root).as_posix().encode("utf-8"))
            digest.update(b"\0")
            digest.update(hash_file(path).encode("ascii"))
    return digest.hexdigest()


def compiled_environment_digest(roots, version, manifest):
    digest = hashlib.sha256(b"stochastic-heat-cache-v2\0")
    digest.update(version.encode("utf-8"))
    digest.update(manifest.read_bytes())
    for root in roots:
        digest.update(str(root.resolve()).encode("utf-8"))
        files = (path for path in root.rglob("*") if path.name.endswith(COMPILED_SUFFIXES))
        digest.update(artifact_digest(files, root).encode("ascii"))
    return digest.hexdigest()


def module_artifacts_digest(objects, module):
    main_object = objects / module_path(module, ".olean")
    return artifact_digest(
        (main_object.with_name(main_object.stem + suffix) for suffix in COMPILED_SUFFIXES), objects
    )


def source_modules(directory):
    return {
        ".".join(path.relative_to(directory).with_suffix("").parts): (directory, path)
        for path in directory.rglob("*.lean")
    }


def source_imports(path):
    source = path.read_text(encoding="utf-8-sig")
    parts = []
    depth = 0
    start = end = 0
    for token in COMMENT_TOKEN.finditer(source):
        value = token.group()
        if value == "/-":
            if not depth:
                parts.append(source[end:token.start()])
                start = token.start()
            depth += 1
        elif value == "-/" and depth:
            depth -= 1
            if not depth:
                parts.append("\n" * source.count("\n", start, token.end()))
                end = token.end()
        elif not depth and value.startswith("--"):
            parts.append(source[end:token.start()])
            end = token.end()
    parts.append(source[end:])
    code = "".join(parts)
    return IMPORT.findall(code)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("packages", type=Path)
    parser.add_argument("run", type=Path)
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--target", action="append")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    packages = args.packages.resolve()
    run = args.run.resolve()
    run.mkdir(parents=True, exist_ok=True)
    objects = run / "objects"
    logs = run / "logs"
    logs.mkdir(exist_ok=True)

    manifest_path = UPSTREAM / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    package_libs = []
    for package in manifest["packages"]:
        checkout = packages / package["name"]
        git = checkout / ".git"
        revision = (git / "HEAD").read_text().strip()
        if revision.startswith("ref: "):
            revision = (git / revision.removeprefix("ref: ")).read_text().strip()
        if revision != package["rev"]:
            sys.exit(f"Package revision mismatch for {package['name']}: {revision}")
        package_libs.append(checkout / ".lake/build/lib/lean")
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, [objects, *package_libs]))}
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    print(version, flush=True)
    print(f"Pinned package revisions matched: {len(package_libs)}", flush=True)

    local = source_modules(LOCAL)
    sources = {**source_modules(UPSTREAM), **source_modules(UPSTREAM / "EllipticPDE"), **local}
    audited = set(ORDER)
    if audited != set(RESULT["module_sha256"]) or not audited <= set(local):
        sys.exit("The original audit inventory is inconsistent with the supplied sources")
    for module in ORDER:
        path = local[module][1]
        if hashlib.sha256(path.read_bytes()).hexdigest() != RESULT["module_sha256"][module]:
            sys.exit(f"Source hash mismatch for {module}")
    targets = args.target or [*ORDER, *sorted(set(local) - audited)]
    invalid = set(targets) - set(local)
    if invalid:
        sys.exit(f"Unknown paper modules: {', '.join(sorted(invalid))}")

    graph = {}
    external = set()
    core = {"Init", "Lean", "Std", "Lake"}

    def collect(module):
        if module in graph or module in external:
            return
        if module not in sources:
            external.add(module)
            return
        _, path = sources[module]
        names = source_imports(path)
        graph[module] = {name for name in names if name in sources}
        for name in names:
            collect(name)

    if not args.target:
        collect("HeatPaperMain")
    for module in targets:
        collect(module)
    missing = [
        module for module in sorted(external)
        if module.split(".")[0] not in core
        and not any((lib / module_path(module, ".olean")).is_file() for lib in package_libs)
    ]
    paper_count = len(set(local) & graph.keys())
    print(
        f"Building {paper_count} paper modules and {len(graph) - paper_count} "
        "vendored modules from source.",
        flush=True,
    )
    if missing:
        sys.exit("Direct external imports without an object file:\n" + "\n".join(missing))
    for directory in sorted({(objects / module_path(module, ".olean")).parent for module in graph}):
        directory.mkdir(parents=True, exist_ok=True)

    def log_path(module):
        return logs / (module + ".log")

    lean_prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    print("Checking compiled toolchain and dependency fingerprints.", flush=True)
    environment_digest = compiled_environment_digest(
        [lean_prefix / "lib" / "lean", *package_libs], version, manifest_path
    )
    source_digests = {}

    def source_digest(module):
        if module not in source_digests:
            digest = hashlib.sha256(environment_digest.encode("ascii"))
            digest.update(module.encode("utf-8"))
            digest.update(sources[module][1].read_bytes())
            for dependency in sorted(graph[module]):
                digest.update(source_digest(dependency).encode("ascii"))
            source_digests[module] = digest.hexdigest()
        return source_digests[module]

    for module in graph:
        source_digest(module)

    def compile_module(module):
        base, source = sources[module]
        output = objects / module_path(module, ".olean")
        stamp = output.with_suffix(".ok")
        stamp.unlink(missing_ok=True)
        with log_path(module).open("wb") as log:
            result = subprocess.run(
                ["lean", "-j", "1", "--root", str(base), "-o", str(output), str(source)],
                cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
            )
        if result.returncode == 0 and output.is_file():
            stamp.write_text(f"{source_digest(module)}\n{module_artifacts_digest(objects, module)}\n", encoding="ascii")
        return result.returncode

    def cached(module):
        stamp = objects / module_path(module, ".ok")
        if not stamp.is_file() or not (objects / module_path(module, ".olean")).is_file():
            return False
        fields = stamp.read_text(encoding="ascii", errors="replace").splitlines()
        return (len(fields) == 2 and fields[0] == source_digest(module)
                and fields[1] == module_artifacts_digest(objects, module))

    reusable = {}

    def reusable_with_imports(module):
        if module not in reusable:
            reusable[module] = cached(module) and all(
                reusable_with_imports(dependency) for dependency in graph[module]
            )
        return reusable[module]

    complete = {module for module in graph if reusable_with_imports(module)}
    if complete:
        print(f"Resuming this run with {len(complete)} previously compiled modules.", flush=True)
    remaining = set(graph) - complete
    active = {}
    deferred = []
    parallelism = args.jobs
    priority = {module: index for index, module in enumerate(graph)}
    started = time.monotonic()

    def report_progress(name):
        if len(complete) % 25 == 0 or name in RESULT["selected_modules"]:
            elapsed = round(time.monotonic() - started)
            print(f"{len(complete)}/{len(graph)} ({elapsed}s): {name}", flush=True)

    def failure(name):
        return log_path(name).read_text(encoding="utf-8", errors="replace")

    def report_failure(name):
        print(f"FAILED {name}. See {log_path(name)}", flush=True)
        detail = failure(name)[-5000:]
        print(detail.encode(sys.stdout.encoding, errors="backslashreplace").decode(sys.stdout.encoding), flush=True)

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while remaining or active or deferred:
            if deferred and not active:
                if len(deferred) > 1 and parallelism > 1:
                    parallelism -= 1
                    print(f"Reducing parallel builds to {parallelism} after file read errors.", flush=True)
                name = deferred.pop(0)
                print(f"Retrying {name} with no other compiler process active.", flush=True)
                if compile_module(name):
                    report_failure(name)
                    return 1
                complete.add(name)
                report_progress(name)
                continue
            if not deferred:
                ready = sorted(
                    (name for name in remaining if graph[name] <= complete), key=priority.__getitem__
                )
                for name in ready[:max(0, parallelism - len(active))]:
                    remaining.remove(name)
                    active[pool.submit(compile_module, name)] = name
            if not active:
                sys.exit(f"Unresolved import cycle: {sorted(remaining)}")
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for job in finished:
                name = active.pop(job)
                if job.result():
                    if "failed to read file" in failure(name):
                        print(f"File read error in {name}; queued for an exclusive retry.", flush=True)
                        deferred.append(name)
                        continue
                    report_failure(name)
                    return 1
                complete.add(name)
                report_progress(name)

    extensions = sorted(set(local) - audited)
    extension_declarations = [
        declaration
        for module in extensions
        for declaration in AXIOM_COMMAND.findall(local[module][1].read_text(encoding="utf-8-sig"))
    ]
    if args.target:
        audit_declarations = []
        audit_lines = ["import Lean", *(f"import {name}" for name in dict.fromkeys(targets)),
                       TARGET_AUDIT_COMMAND, *(f"#audit_target {name}" for name in dict.fromkeys(targets))]
    else:
        audit_declarations = [*RESULT["declarations"], *extension_declarations]
        audit_lines = [f"import {name}" for name in [*RESULT["selected_modules"], *extensions]]
        audit_lines += [f"#print axioms {name}" for name in audit_declarations]
    audit = run / "Audit.lean"
    audit.write_text("\n".join(audit_lines) + "\n", encoding="utf-8")
    with (run / "axioms.log").open("wb") as log:
        audit_result = subprocess.run(
            ["lean", "-j", "1", str(audit)], cwd=ROOT, env=env,
            stdout=log, stderr=subprocess.STDOUT,
        )
    if audit_result.returncode:
        print(f"Axiom audit failed. See {run / 'axioms.log'}", flush=True)
        return audit_result.returncode
    actual = {
        declaration: {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
        for declaration, axioms in AXIOM_RESULT.findall((run / "axioms.log").read_text(encoding="utf-8"))
    }
    missing_audits = set(audit_declarations) - actual.keys()
    unexpected = {name: axioms - STANDARD_AXIOMS for name, axioms in actual.items() if axioms - STANDARD_AXIOMS}
    if missing_audits or unexpected:
        print(f"Incomplete audits: {sorted(missing_audits)}. Unexpected axioms: {unexpected}.", flush=True)
        return 1
    if args.target and not actual:
        print("The target axiom audit did not produce any declaration results.", flush=True)
        return 1
    print(f"Compiled {len(complete)} modules. Axiom audit passed for {len(actual)} declarations.", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
