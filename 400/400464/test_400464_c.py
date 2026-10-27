"""Small, isolated checks for A400464's C implementation and saved results."""

from contextlib import contextmanager
import fcntl
from itertools import combinations
import os
from pathlib import Path
import resource
import shlex
import signal
import stat
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).with_name('400464_01.c')
RESULT = 'b400464_01.txt'


class ProgramChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.build = tempfile.TemporaryDirectory(prefix='a400464-c-build-')
        cls.build_path = Path(cls.build.name)
        cls.compiler = shlex.split(os.environ.get('CC', 'cc'))
        cls.flags = ['-std=c17', '-O1', '-Wall', '-Wextra', '-Wpedantic', '-Werror']
        cls.flags += shlex.split(os.environ.get('CFLAGS', ''))
        cls.binary = cls.compile('program')
        bodies = {
            'fsync': 'int failed_fsync(int fd) { (void)fd; errno=EIO; return -1; }',
            'rename': 'int failed_rename(const char *a, const char *b) { (void)a; (void)b; errno=EACCES; return -1; }',
            'calloc': 'void *failed_calloc(size_t n, size_t s) { (void)n; (void)s; errno=ENOMEM; return NULL; }',
        }
        for call, body in bodies.items():
            harness = cls.build_path / (call + '.c')
            # The macro also renames the prototype in the system header.
            harness.write_text('#define ' + call + ' failed_' + call +
                               '\n#include "400464_01.c"\n' + body + '\n')
            setattr(cls, 'failed_' + call, cls.compile(call, source=harness))
        harness = cls.build_path / 'interrupted.c'
        harness.write_text('#define rename interrupted_rename\n'
                           '#include "400464_01.c"\n#include <signal.h>\n'
                           'int interrupted_rename(const char *a, const char *b) { '
                           '(void)a; (void)b; raise(SIGTERM); errno=EINTR; return -1; }\n')
        cls.interrupted = cls.compile('interrupted', source=harness)

    @classmethod
    def tearDownClass(cls):
        cls.build.cleanup()

    @classmethod
    def compile(cls, name, extra=(), source=SOURCE):
        binary = cls.build_path / name
        result = subprocess.run(cls.compiler + cls.flags + list(extra) + ['-I', str(SOURCE.parent),
                                str(source), '-o', str(binary)], capture_output=True,
                                text=True, timeout=20)
        if result.returncode:
            raise RuntimeError(result.stderr)
        return binary

    @contextmanager
    def folder(self, seed=None):
        with tempfile.TemporaryDirectory(prefix='a400464-c-results-') as name:
            folder = Path(name)
            if seed is not None:
                (folder / RESULT).write_bytes(seed)
            yield folder

    def run_program(self, folder, *args, binary=None, preexec=None):
        return subprocess.run([str(binary or self.binary), *map(str, args)], cwd=folder,
                              capture_output=True, text=True, timeout=8, preexec_fn=preexec)

    def test_definition_oracle_through_12(self):
        # Enumerate sets containing 1 as well as those omitting it. Only products
        # of TWO DISTINCT elements are compared: squares are not included.
        maxima = [0] * 13
        for mask in range(1 << 12):
            chosen = [j + 1 for j in range(12) if mask >> j & 1]
            products = [a*b for a, b in combinations(chosen, 2)]
            if len(products) == len(set(products)):
                n = max(chosen, default=0)
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
        seeds = [b'1 -1\n', b'1 0\n', b'1 2147483647\n',
                 b'1 999999999999999999999999999\n', b'1 1\n2 1\n',
                 b'1 1\n3 3\n', b'1 1\n2 2', b'1 1 junk\n',
                 b'1 1\ninvalid\n', b'1 1\x00\n', b'1 1\n\x00junk\n',
                 b'99999999999999999999 1\n', b'1 1\n2 3\n']
        for seed in seeds:
            with self.subTest(seed=seed), self.folder(seed) as folder:
                result = self.run_program(folder, 3)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual((folder / RESULT).read_bytes(), seed)
                self.assertEqual(result.stdout, '')

    def test_cli_rejection_and_help(self):
        for args in (['0'], ['-1'], ['1001'], ['4junk'], ['4.5'], ['4294967300'],
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
            self.assertEqual((folder / RESULT).read_text(), '1 1\n')

    def test_live_and_stale_locks(self):
        with self.folder() as folder:
            with (folder / (RESULT + '.lock')).open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                self.assertNotEqual(self.run_program(folder, 3).returncode, 0)
                self.assertFalse((folder / RESULT).exists())
            self.assertEqual(self.run_program(folder, 3).returncode, 0)
            self.assertTrue((folder / (RESULT + '.lock')).is_file())

    def test_output_and_lock_aliases_rejected(self):
        for suffix in ('', '.lock'):
            for hardlink in (False, True):
                with self.subTest(suffix=suffix, hardlink=hardlink), self.folder() as folder:
                    other = folder / 'other.txt'
                    other.write_bytes(b'1 1\n')
                    if hardlink:
                        os.link(other, folder / (RESULT + suffix))
                    else:
                        (folder / (RESULT + suffix)).symlink_to(other.name)
                    self.assertNotEqual(self.run_program(folder, 3).returncode, 0)
                    self.assertEqual(other.read_bytes(), b'1 1\n')

    def test_legacy_temporary_alias_untouched(self):
        with self.folder(b'1 1\n') as folder:
            other = folder / 'other.txt'
            other.write_bytes(b'KEEP\n')
            (folder / (RESULT + '.tmp')).symlink_to(other.name)
            result = self.run_program(folder, 3)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(other.read_bytes(), b'KEEP\n')
            self.assertFalse(list(folder.glob('.b400464_01.txt.tmp.*')))

    def test_write_sync_and_rename_failures_preserve_prefix(self):
        def forbid_growth():
            signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
            resource.setrlimit(resource.RLIMIT_FSIZE, (0, 0))
        cases = [(self.binary, forbid_growth), (self.failed_fsync, None),
                 (self.failed_rename, None)]
        for binary, preexec in cases:
            with self.subTest(binary=binary.name), self.folder(b'1 1\n') as folder:
                result = self.run_program(folder, 2, binary=binary, preexec=preexec)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual((folder / RESULT).read_bytes(), b'1 1\n')
                self.assertEqual(result.stdout, '')
                self.assertFalse(list(folder.glob('.b400464_01.txt.tmp.*')))

    def test_interruption_before_replace_preserves_prefix(self):
        with self.folder(b'1 1\n') as folder:
            result = self.run_program(folder, 2, binary=self.interrupted)
            self.assertEqual(result.returncode, -signal.SIGTERM)
            self.assertEqual((folder / RESULT).read_bytes(), b'1 1\n')
            self.assertEqual(result.stdout, '')

    def test_allocation_failure_preserves_results(self):
        with self.folder(b'1 1\n') as folder:
            result = self.run_program(folder, 2, binary=self.failed_calloc)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual((folder / RESULT).read_bytes(), b'1 1\n')
            self.assertEqual(result.stdout, '')

    def test_saved_row_count_boundaries(self):
        # These rows are only syntactically plausible. N=1 must retain all
        # rows, while proving only F(1), without trusting later saved values.
        seed = ''.join(f'{n} {n}\n' for n in range(1, 1001)).encode()
        with self.folder(seed) as folder:
            self.assertEqual(self.run_program(folder, 1).returncode, 0)
            self.assertEqual((folder / RESULT).read_bytes(), seed)
        seed += b'1001 1001\n'
        with self.folder(seed) as folder:
            self.assertNotEqual(self.run_program(folder, 1).returncode, 0)
            self.assertEqual((folder / RESULT).read_bytes(), seed)

    def test_maximum_model_without_large_search(self):
        harness = self.build_path / 'boundary.c'
        harness.write_text('#define main saved_main\n#include "400464_01.c"\n#undef main\n'
                           'int main(void) {\n'
                           'if(!initialize_search(MAXN)) return 1;\n'
                           'if(used_bytes!=1002001 || spf[997]!=997 || spf[1000]!=2) return 2;\n'
                           'used[1000*999]=1; A[0]=1000; k=1; count_factors(1000,1);\n'
                           'if(cntp[2]!=1 || cntp[5]!=1) return 3;\n'
                           'count_factors(1000,-1); free(used); return 0; }\n')
        binary = self.compile('boundary', source=harness)
        with self.folder() as folder:
            self.assertEqual(self.run_program(folder, binary=binary).returncode, 0)
        # Accept N=1000, but stop at the deliberately wrong saved value F(2).
        # This exercises maximum-N setup without calculating F(1000).
        with self.folder(b'1 1\n2 1\n') as folder:
            result = self.run_program(folder, 1000)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('n=2 is incorrect', result.stderr)
            self.assertEqual((folder / RESULT).read_bytes(), b'1 1\n2 1\n')

    def test_fifo_and_unreadable_results_rejected(self):
        for suffix in ('', '.lock'):
            with self.subTest(suffix=suffix), self.folder() as folder:
                path = folder / (RESULT + suffix)
                os.mkfifo(path)
                self.assertNotEqual(self.run_program(folder, 3).returncode, 0)
                self.assertTrue(stat.S_ISFIFO(path.lstat().st_mode))
        if os.geteuid() != 0:
            with self.folder(b'1 1\n') as folder:
                path = folder / RESULT
                path.chmod(0o200)
                try:
                    result = self.run_program(folder, 3)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, '')
                finally:
                    path.chmod(0o600)
                self.assertEqual(path.read_bytes(), b'1 1\n')


if __name__ == '__main__':
    unittest.main()
