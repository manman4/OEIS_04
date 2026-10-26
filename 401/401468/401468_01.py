"""Write A401468 for n=1..N to b401468.txt (default N=1000).

a(n) = sum(A046801(k) for k in range(1, n+1)).
A046801(k) is the number of positive divisors of 2**k - 1.

This program sums published A046801 data; it does not factor Mersenne
numbers independently. The bundled b046801.txt is reused. If absent,
one download is attempted, without automatic retries. Only the Python
standard library and exact integer arithmetic are used.

Usage: python3 401468_01.py [N]
The default source and output are beside this script.
"""

import argparse
from datetime import datetime, timezone
import hashlib
from itertools import accumulate
import json
from pathlib import Path
import sys
from tempfile import NamedTemporaryFile
from urllib.error import URLError
from urllib.request import urlopen


N = 1000
DIRECTORY = Path(__file__).resolve().parent
SOURCE = DIRECTORY / "b046801.txt"
OUTPUT = DIRECTORY / "b401468.txt"
SOURCE_URL = "https://oeis.org/A046801/b046801.txt"


def parse_source(text: str) -> list[int]:
    """Read positive terms with consecutive indices starting at 1."""
    counts = []
    for line_number, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"Source line {line_number}: expected two integers")
        index, value = map(int, fields)
        if index != len(counts) + 1 or value < 1:
            raise ValueError(
                f"Source line {line_number}: invalid index or divisor count"
            )
        counts.append(value)
    if not counts or counts[0] != 1:
        raise ValueError("Source must begin with A046801(1) = 1")
    return counts


def atomic_write(path: Path, text: str) -> None:
    """Replace the destination only after writing a complete temporary file."""
    temporary = None
    try:
        with NamedTemporaryFile(
            mode="w", encoding="utf-8", newline="\n",
            dir=path.parent, prefix=f".{path.name}.", delete=False,
        ) as stream:
            temporary = Path(stream.name)
            stream.write(text)
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def load_counts(source: Path = SOURCE) -> list[int]:
    if source.exists():
        return parse_source(source.read_text(encoding="utf-8"))

    print(f"Downloading {SOURCE_URL} once; no automatic retries.", file=sys.stderr)
    with urlopen(SOURCE_URL, timeout=60) as response:
        raw = response.read()
    text = raw.decode("utf-8")
    counts = parse_source(text)
    atomic_write(source, text)
    metadata = {
        "url": SOURCE_URL,
        "retrieved_at_utc": datetime.now(timezone.utc).isoformat(),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "first_index": 1,
        "last_index": len(counts),
    }
    atomic_write(
        source.with_suffix(".source.json"),
        json.dumps(metadata, ensure_ascii=False, indent=2) + "\n",
    )
    return counts


def write_bfile(limit: int, source: Path = SOURCE, output: Path = OUTPUT) -> int:
    """Write the inclusive range 1..limit using the published source terms."""
    if limit < 1:
        raise ValueError("N must be at least 1")
    if output.resolve() in {source.resolve(), Path(__file__).resolve()}:
        raise ValueError("Output must differ from the source and script")
    counts = load_counts(source)
    if len(counts) < limit:
        raise ValueError(
            f"Source ends at n={len(counts)}; n={limit} is unavailable. "
            "The cached source was not downloaded again."
        )
    rows = (
        f"{index} {value}\n"
        for index, value in enumerate(accumulate(counts[:limit]), 1)
    )
    atomic_write(output, "".join(rows))
    return limit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=N,
                        help=f"last index, inclusive (default: {N})")
    parser.add_argument("--source", type=Path, default=SOURCE,
                        help="local A046801 b-file (downloaded once if absent)")
    parser.add_argument("--output", type=Path, default=OUTPUT,
                        help="output b-file")
    args = parser.parse_args()
    try:
        count = write_bfile(args.N, args.source, args.output)
    except (OSError, URLError, ValueError) as error:
        parser.exit(1, f"Error: {error}\n")
    print(f"Saved {count} terms (n=1..{args.N}) to {args.output}")


if __name__ == "__main__":
    main()
