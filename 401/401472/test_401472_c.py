"""Small, isolated correctness and persistence checks for the C implementation."""

from contextlib import contextmanager
import fcntl
from itertools import combinations
from math import prod
import os
from pathlib import Path
import resource
import shlex
import signal
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).with_name('401472_01.c')
RESULT = 'b401472_01.txt'


class ProgramChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.build = tempfile.TemporaryDirectory(prefix='a401472-c-build-')
        cls.build_path = Path(cls.build.name)
        cls.compiler = shlex.split(os.environ.get('CC', 'cc'))
        cls.flags = ['-std=c17', '-O1', '-Wall', '-Wextra', '-Wpedantic', '-Werror']
        cls.flags += shlex.split(os.environ.get('CFLAGS', ''))
        cls.binary = cls.compile('program')
        cls.low_memory = cls.compile('limited', ['-DMAXHB=10'])
        for call in ('fsync', 'rename'):
            harness = cls.build_path / (call + '.c')
            if call == 'fsync':
                body = 'int failed_fsync(int fd) { (void)fd; errno=EIO; return -1; }'
                prototype = 'int failed_fsync(int);'
            else:
                body = 'int failed_rename(const char *a, const char *b) { (void)a; (void)b; errno=EACCES; return -1; }'
                prototype = 'int failed_rename(const char *, const char *);'
            harness.write_text(prototype + '\n#define ' + call + ' failed_' + call +
                               '\n#include "401472_01.c"\n' + body + '\n')
            setattr(cls, 'failed_' + call, cls.compile(call, source=harness))

    @classmethod
    def tearDownClass(cls):
        cls.build.cleanup()

    @classmethod
    def compile(cls, name, extra=(), source=SOURCE):
        binary = cls.build_path / name
        subprocess.run(cls.compiler + cls.flags + list(extra) + ['-I', str(SOURCE.parent),
                       str(source), '-o', str(binary)], check=True, capture_output=True,
                       text=True, timeout=25)
        return binary

    @contextmanager
    def folder(self, seed=None):
        with tempfile.TemporaryDirectory(prefix='a401472-c-results-') as name:
            folder = Path(name)
            if seed is not None:
                (folder / RESULT).write_bytes(seed)
            yield folder

    def run_program(self, folder, *args, binary=None, preexec=None):
        return subprocess.run([str(binary or self.binary), *map(str, args)], cwd=folder,
                              capture_output=True, text=True, timeout=8, preexec_fn=preexec)

    def test_definition_oracle_through_12(self):
        # Enumerate the actual products of all subsets, without prime vectors,
        # precomputed optima, or the C program's bounds/free-prime reductions.
        maxima = [0] * 13
        for mask in range(1 << 11):
            chosen = [j + 2 for j in range(11) if mask >> j & 1]
            products = [prod(part) for size in range(len(chosen) + 1)
                        for part in combinations(chosen, size)]
            if len(products) == len(set(products)):
                n = max(chosen, default=1)
                maxima[n] = max(maxima[n], len(chosen))
        for n in range(1, 13):
            maxima[n] = max(maxima[n], maxima[n - 1])
        expected = ''.join(f'{n} {v}\n' for n, v in enumerate(maxima[1:], 1))
        with self.folder() as folder:
            result = self.run_program(folder, 12)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((folder / RESULT).read_text(), expected)
            self.assertEqual(result.stdout, expected)

    def test_resume_and_smaller_limit(self):
        with self.folder() as folder:
            self.assertEqual(self.run_program(folder, 6).returncode, 0)
            self.assertEqual(self.run_program(folder, 12).returncode, 0)
            before = (folder / RESULT).read_bytes()
            result = self.run_program(folder, 3)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((folder / RESULT).read_bytes(), before)
            self.assertIn('n=1..3 verified', result.stderr)
            self.assertEqual(result.stdout, '')

    def test_bad_saved_data_preserved(self):
        seeds = [b'1 -1\n', b'1 2147483647\n', b'1 999999999999999999999999\n',
                 b'1 0\n2 0\n', b'1 0\n3 1\n', b'1 0\n2 1',
                 b'1 0 junk\n', b'1 0\ninvalid\n', b'1 0\x00\n']
        for seed in seeds:
            with self.subTest(seed=seed), self.folder(seed) as folder:
                result = self.run_program(folder, 3)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual((folder / RESULT).read_bytes(), seed)
                self.assertEqual(result.stdout, '')

    def test_cli_rejection_and_help(self):
        for args in (['0'], ['-1'], ['65'], ['4junk'], ['4.5'], ['4294967300'],
                     ['9999999999999999999999999999'], ['4', 'ignored'], [''], ['+4']):
            with self.subTest(args=args), self.folder() as folder:
                result = self.run_program(folder, *args)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse((folder / RESULT).exists())
        with self.folder() as folder:
            self.assertEqual(self.run_program(folder, '--help').returncode, 0)
            self.assertFalse((folder / RESULT).exists())
        with self.folder() as folder:
            self.assertEqual(self.run_program(folder, 1).returncode, 0)
            self.assertEqual((folder / RESULT).read_text(), '1 0\n')

    def test_live_and_stale_locks(self):
        with self.folder() as folder:
            with (folder / (RESULT + '.lock')).open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                self.assertNotEqual(self.run_program(folder, 3).returncode, 0)
                self.assertFalse((folder / RESULT).exists())
            self.assertEqual(self.run_program(folder, 3).returncode, 0)

    def test_output_aliases_rejected(self):
        for hardlink in (False, True):
            with self.subTest(hardlink=hardlink), self.folder() as folder:
                other = folder / 'other.txt'
                other.write_bytes(b'1 0\n')
                if hardlink:
                    os.link(other, folder / RESULT)
                else:
                    (folder / RESULT).symlink_to(other.name)
                self.assertNotEqual(self.run_program(folder, 3).returncode, 0)
                self.assertEqual(other.read_bytes(), b'1 0\n')

    def test_legacy_temporary_alias_untouched(self):
        with self.folder(b'1 0\n') as folder:
            other = folder / 'other.txt'
            other.write_bytes(b'KEEP\n')
            (folder / (RESULT + '.tmp')).symlink_to(other.name)
            result = self.run_program(folder, 3)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(other.read_bytes(), b'KEEP\n')
            self.assertFalse(list(folder.glob('.b401472_01.txt.tmp.*')))

    def test_write_sync_and_rename_failures_preserve_prefix(self):
        def forbid_growth():
            signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
            resource.setrlimit(resource.RLIMIT_FSIZE, (0, 0))
        cases = [(self.binary, forbid_growth), (self.failed_fsync, None),
                 (self.failed_rename, None)]
        for binary, preexec in cases:
            with self.subTest(binary=binary.name), self.folder(b'1 0\n') as folder:
                result = self.run_program(folder, 2, binary=binary, preexec=preexec)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual((folder / RESULT).read_bytes(), b'1 0\n')
                self.assertEqual(result.stdout, '')
                self.assertFalse(list(folder.glob('.b401472_01.txt.tmp.*')))

    def test_memory_cap_preserves_proved_prefix(self):
        for limit in (14, 64):
            with self.subTest(limit=limit), self.folder() as folder:
                result = self.run_program(folder, limit, binary=self.low_memory)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('MAXHB=10', result.stderr)
                self.assertEqual((folder / RESULT).read_text().splitlines()[-1], '13 8')

    def test_saved_row_count_boundaries(self):
        seed = ''.join(f'{n} 0\n' for n in range(1, 65)).encode()
        with self.folder(seed) as folder:
            result = self.run_program(folder, 1)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((folder / RESULT).read_bytes(), seed)
        seed += b'65 0\n'
        with self.folder(seed) as folder:
            self.assertNotEqual(self.run_program(folder, 1).returncode, 0)
            self.assertEqual((folder / RESULT).read_bytes(), seed)

    def test_compile_time_memory_boundaries(self):
        for value in (9, 31):
            result = subprocess.run(self.compiler + self.flags + [f'-DMAXHB={value}',
                                    '-fsyntax-only', str(SOURCE)], capture_output=True,
                                    text=True, timeout=8)
            self.assertNotEqual(result.returncode, 0)
        self.compile('maxhb28', ['-DMAXHB=28'])

    def test_all_layout_boundaries_without_searching_64(self):
        harness = self.build_path / 'layout.c'
        harness.write_text('#define main saved_main\n#include "401472_01.c"\n#undef main\n'
                           'int main(void) {\n'
                           'for (int n=1;n<=64;n++) { if(!initialize_vectors(n)) return 1; '
                           'if(np>18 || vector_bits>42) return 2; '
                           'for(int m=2;m<=n;m++) if(npf[m]>3) return 3; }\n'
                           'return np==18 && vector_bits==42 ? 0 : 4; }\n')
        binary = self.compile('layout', source=harness)
        with self.folder() as folder:
            self.assertEqual(self.run_program(folder, binary=binary).returncode, 0)
            self.assertFalse((folder / RESULT).exists())


if __name__ == '__main__':
    unittest.main()
