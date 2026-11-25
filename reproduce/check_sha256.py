"""Verify the UTF-8 SHA256SUMS shipped in the paper archive."""

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="?", type=Path, default=Path("SHA256SUMS"))
    args = parser.parse_args()
    root = args.manifest.resolve().parent
    seen = set()
    failed = []
    for line in args.manifest.read_text(encoding="utf-8-sig").splitlines():
        match = re.fullmatch(r"([0-9a-fA-F]{64})  (.+)", line)
        if not match:
            parser.error(f"invalid checksum entry: {line!r}")
        expected, name = match.groups()
        relative = PurePosixPath(name)
        path = root.joinpath(*relative.parts).resolve()
        if (relative.is_absolute() or ".." in relative.parts or "\\" in name
                or not path.is_relative_to(root) or path in seen):
            parser.error(f"invalid or duplicate package path: {name!r}")
        seen.add(path)
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected.lower():
            failed.append(name)
    if not seen:
        parser.error("the checksum list is empty")
    for name in failed:
        print(f"FAILED {name}")
    if failed:
        return 1
    print(f"SHA-256 matches for {len(seen)} files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
