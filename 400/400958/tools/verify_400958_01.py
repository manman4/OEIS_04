#!/usr/bin/env python3
"""Test A400958 values and the actual checkpoint I/O, without using saved b-files."""
import argparse
import fcntl
from pathlib import Path
import signal
import subprocess
import tempfile


def trial_mu(n):
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def main():
    a = argparse.ArgumentParser()
    a.add_argument("binary", nargs="?", default="./400958_01")
    a.add_argument("--quick", action="store_true")
    args = a.parse_args()
    binary = str(Path(args.binary).resolve())
    calls = 0
    with tempfile.TemporaryDirectory(prefix="a400958-01-test-") as d:
        root = Path(d)

        def run(*options, good=True):
            nonlocal calls
            p = subprocess.run([binary, *map(str, options)], cwd=d, text=True,
                               capture_output=True, timeout=120)
            calls += 1
            if good:
                assert p.returncode == 0, p.stderr
            else:
                assert p.returncode != 0, options
                assert not p.stdout, (options, p.stdout)
                return p
            rows = [tuple(map(int, line.split())) for line in p.stdout.splitlines()]
            assert [n for n, _ in rows] == list(range(len(rows)))
            assert "\r" not in p.stderr
            return rows

        # Definition oracle: factor each integer separately, with no shared sieve.
        mu = [trial_mu(n) for n in range(1, 100002)]
        total = 0
        expected = []
        for i in range(1, 100001):
            total += mu[i - 1] * mu[i]
            if i == 10**len(expected):
                expected.append((len(expected), total))
        for segment, threads in [(1, 1), (97, 1), (113, 4), (138600, 4)]:
            n = 3 if segment == 1 else 5
            assert run("--max-n", n, "--segment", segment, "--threads", threads,
                       "--no-checkpoint") == expected[:n + 1]
        assert not list(root.iterdir()), "no-checkpoint mode created files"

        # Resume partway through a decade, then switch threads and segment size.
        partial = run("--max-n", 5, "--segment", 17, "--threads", 1,
                      "--stop-after-blocks", 4)
        assert partial == expected[:2]
        state = root / "400958_01.checkpoint"
        assert state.read_text().splitlines()[1].split()[0] == "45"
        assert run("--max-n", 5, "--segment", 1009, "--threads", 4) == expected
        saved = state.read_bytes()
        assert run("--max-n", 5) == expected
        assert state.read_bytes() == saved
        run("--max-n", 4, good=False)

        # A torn temporary checkpoint is ignored; the previous atomic file wins.
        (root / "400958_01.checkpoint.tmp.123456").write_text("partial write")
        assert run("--max-n", 5) == expected
        damaged = bytearray(saved)
        damaged[damaged.index(b"100001")] = ord("2")
        state.write_bytes(damaged)
        run("--max-n", 5, good=False)
        assert state.read_bytes() == damaged
        state.write_bytes(saved)

        # Lock contention cannot modify an existing checkpoint.
        with open(str(state) + ".lock", "a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            p = run("--max-n", 5, good=False)
            assert "locked" in p.stderr and state.read_bytes() == saved

        # Extension computes the next decade, instead of treating old rows as final.
        known = [-1, -3, 3, -11, 12, -187, 409, 1683, -2631, -3009, -39942]
        assert run("--max-n", 6) == list(enumerate(known[:7]))

        # SIGINT saves at a completed block boundary and can be resumed.
        interrupted = root / "interrupt.checkpoint"
        p = subprocess.Popen([binary, "--max-n", "13", "--segment", "1000000",
                              "--checkpoint", str(interrupted)], cwd=d, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        lines = []
        while len(lines) < 4:
            line = p.stdout.readline()
            assert line, "interruption test exited before producing rows"
            lines.append(line)
        p.send_signal(signal.SIGINT)
        rest, diagnostics = p.communicate(timeout=20)
        assert p.returncode == 130, diagnostics
        assert "Stopped:" in diagnostics
        assert run("--max-n", 9, "--checkpoint", str(interrupted)) == list(enumerate(known[:10]))

        # Full prefix crosses 32-bit boundaries in the actual accumulation loop.
        n = 7 if args.quick else 10
        assert run("--max-n", n, "--no-checkpoint") == list(enumerate(known[:n + 1]))

        # Default target is 13, without starting a complete long-running job.
        one = run("--checkpoint", root / "default.checkpoint", "--stop-after-blocks", 1)
        assert one == [(0, -1)]
        for bad in [("--max-n", 17), ("--max-n", -1), ("--threads", 0),
                    ("--segment", 0), ("--segment", 2000000001),
                    ("--max-n",), ("--unknown", 1),
                    ("--checkpoint", root / "missing" / "x")]:
            run(*bad, good=False)
    print(f"PASS: {calls} invocations plus SIGINT; definition oracle through n=5, "
          f"checkpoint/resume/extension/checksum/lock tests; full prefix through n={n}")


if __name__ == "__main__":
    main()
