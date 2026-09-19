#!/usr/bin/env python3
"""Create a deterministic, allowlisted source export in a fresh directory."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import shutil
import sys


MANIFEST_NAME = "SOURCE-MANIFEST.sha256"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def read_allowlist(path: Path) -> list[str]:
    entries = [line.strip() for line in path.read_text(encoding="utf-8").splitlines()]
    entries = [entry for entry in entries if entry and not entry.startswith("#")]
    if entries != sorted(entries):
        raise ValueError("allowlist entries must be sorted")
    if len(entries) != len(set(entries)):
        raise ValueError("allowlist contains duplicate entries")
    for entry in entries:
        posix = PurePosixPath(entry)
        if posix.is_absolute() or ".." in posix.parts or "." in posix.parts:
            raise ValueError(f"invalid allowlist path: {entry}")
        if "\\" in entry or entry == MANIFEST_NAME:
            raise ValueError(f"invalid or reserved allowlist path: {entry}")
    return entries


def export(source_root: Path, allowlist: Path, destination: Path, workspace_root: Path) -> None:
    source_root = source_root.resolve(strict=True)
    allowlist = allowlist.resolve(strict=True)
    workspace_root = workspace_root.resolve(strict=True)
    destination = destination.resolve(strict=False)

    if not inside(source_root, workspace_root):
        raise ValueError("source root must be inside the declared workspace root")
    if not inside(destination, workspace_root):
        raise ValueError("destination must be inside the declared workspace root")
    if inside(destination, source_root) or inside(source_root, destination):
        raise ValueError("destination and source trees must not contain one another")
    if destination.exists():
        raise FileExistsError("destination must be fresh")

    entries = read_allowlist(allowlist)
    resolved: list[tuple[str, Path]] = []
    for entry in entries:
        candidate = source_root.joinpath(*PurePosixPath(entry).parts)
        if not candidate.is_file():
            raise FileNotFoundError(f"missing allowlisted file: {entry}")
        target = candidate.resolve(strict=True)
        if not inside(target, source_root):
            raise ValueError(f"allowlisted file escapes source root: {entry}")
        resolved.append((entry, target))

    destination.mkdir(parents=True, exist_ok=False)
    manifest_lines: list[str] = []
    for entry, source in resolved:
        output = destination.joinpath(*PurePosixPath(entry).parts)
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, output)
        copied_hash = sha256(output)
        if copied_hash != sha256(source):
            raise OSError(f"copy verification failed: {entry}")
        manifest_lines.append(f"{copied_hash}  {entry}")
    (destination / MANIFEST_NAME).write_text(
        "\n".join(manifest_lines) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"exported {len(entries)} files to {destination}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--source-root", type=Path, default=Path.cwd())
    parser.add_argument("--allowlist", type=Path, default=Path("distribution-files.txt"))
    parser.add_argument("--workspace-root", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    source_root = args.source_root
    workspace_root = args.workspace_root or source_root.resolve().parent
    try:
        export(source_root, args.allowlist, args.destination, workspace_root)
    except (OSError, ValueError) as error:
        print(f"export error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
