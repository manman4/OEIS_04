"""Independent small enumeration, exact prefix checks, and checkpoint I/O tests."""
from contextlib import redirect_stderr, redirect_stdout
import importlib.util
import io
from itertools import combinations
import json
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("problem425", Path(__file__).with_name("400464_01.py"))
program = importlib.util.module_from_spec(spec)
spec.loader.exec_module(program)


class GeneratorChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.checkpoint = self.root/"checkpoint.json"
        self.bfile = self.root/"b.txt"
        self.output = self.root/"terms.txt"

    def compute(self, n, verify_only=False):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            return program.compute(n, self.checkpoint, self.output, self.bfile,
                                   verify_only=verify_only)

    def test_all_small_subsets_and_maxima(self):
        # No SAT model, pruning, prior maxima or sequence values in this oracle.
        by_maximum = program.collision_edges(12)
        edges = [set(edge) for group in by_maximum.values() for edge in group]
        direct = []
        for n in range(1, 13):
            maximum = 0
            for mask in range(1 << n):
                subset = [a for a in range(1, n+1) if mask >> (a-1) & 1]
                products = [a*b for a, b in combinations(subset, 2)]
                valid = len(set(products)) == len(products)
                self.assertEqual(valid, not any(edge <= set(subset) for edge in edges))
                if valid:
                    maximum = max(maximum, len(subset))
            direct.append(maximum)
        self.assertEqual(self.compute(12), direct)

    def test_first30_and_resume_and_smaller_request(self):
        first = self.compute(18)
        values = self.compute(30)
        self.assertEqual(values[:18], first)
        # Previously computed values are used only for this after-the-fact check.
        self.assertEqual(values, [1,2,3,4,5,5,6,6,7,7,8,9,10,10,10,11,12,12,
                                  13,13,13,14,15,15,16,16,16,16,17,17])
        lines = self.bfile.read_text().splitlines()
        self.assertEqual(lines, [f"{n} {v}" for n,v in enumerate(values,1)])
        before = {p:p.read_bytes() for p in (self.checkpoint,self.bfile,self.output)}
        self.compute(30, verify_only=True)
        self.assertEqual(before, {p:p.read_bytes() for p in before})
        self.assertEqual(self.compute(12), values[:12])
        self.assertEqual(self.bfile.read_text().splitlines(), lines)

    def test_wrong_maximum_and_wrong_witness_rejected(self):
        self.compute(5)
        state = json.loads(self.checkpoint.read_text())
        state['values'][4] = 4
        state['witnesses'][4] = [1,2,3,4]
        self.checkpoint.write_text(json.dumps(state))
        with self.assertRaisesRegex(ValueError, 'not maximal at n=5'):
            self.compute(5, verify_only=True)
        state['limit_completed'] = 6
        state['values'] = [1,2,3,4,5,5]
        state['witnesses'] = [[1],[1,2],[1,2,3],[1,2,3,4],[1,2,3,4,5],[1,2,3,4,6]]
        state['statistics'].append({})
        self.checkpoint.write_text(json.dumps(state))
        with self.assertRaisesRegex(ValueError, 'Colliding pair products at n=6'):
            self.compute(6, verify_only=True)

    def test_interrupt_or_unknown_preserves_proved_prefix(self):
        original = program.UpperModel.probe
        for exception in (KeyboardInterrupt, program.IncompleteCheck):
            with self.subTest(exception=exception.__name__):
                for path in (self.checkpoint,self.bfile,self.output):
                    path.unlink(missing_ok=True)
                def interrupted(model, n, target):
                    if n == 6:
                        raise exception('simulated')
                    return original(model,n,target)
                with patch.object(program.UpperModel,'probe',interrupted):
                    with self.assertRaises(exception):
                        self.compute(8)
                self.assertEqual(json.loads(self.checkpoint.read_text())['limit_completed'],5)
                self.assertEqual(len(self.bfile.read_text().splitlines()),5)
                self.assertFalse(self.output.exists())
                self.assertEqual(self.compute(8),[1,2,3,4,5,5,6,6])

    def test_missing_checkpoint_preserves_nonempty_bfile(self):
        self.bfile.write_text('1 1\n2 2\n3 3\n')
        self.output.write_text('existing one-line output\n')
        before={path:path.read_bytes() for path in (self.bfile,self.output)}
        for verify_only in (False,True):
            with self.assertRaisesRegex(ValueError,'nonempty b-file'):
                self.compute(3,verify_only=verify_only)
            self.assertFalse(self.checkpoint.exists())
            self.assertEqual(before,{path:path.read_bytes() for path in before})

    def test_empty_checkpoint_preserves_nonempty_bfile(self):
        state=program.load_state(self.checkpoint)
        self.checkpoint.write_text(json.dumps(state))
        self.bfile.write_text('1 1\n2 2\n3 3\n')
        before={path:path.read_bytes() for path in (self.checkpoint,self.bfile)}
        with self.assertRaisesRegex(ValueError,'nonempty b-file'):
            self.compute(3)
        self.assertEqual(before,{path:path.read_bytes() for path in before})
        self.assertFalse(self.output.exists())

    def test_empty_bfile_allows_first_term_timeout_and_restart(self):
        self.bfile.write_text('')
        with patch.object(program.UpperModel,'probe',side_effect=program.IncompleteCheck('simulated')):
            with self.assertRaises(program.IncompleteCheck):
                self.compute(3)
        self.assertEqual(json.loads(self.checkpoint.read_text())['limit_completed'],0)
        self.assertEqual(self.bfile.read_text(),'')
        self.assertEqual(self.compute(3),[1,2,3])

    def test_cli_missing_checkpoint_preserves_bfile_and_output(self):
        self.bfile.write_text('1 1\n2 2\n3 3\n')
        self.output.write_text('existing output\n')
        before={path:path.read_bytes() for path in (self.bfile,self.output)}
        result=subprocess.run([sys.executable,'-S','-B',program.__file__,'3',
                               '--checkpoint',str(self.checkpoint),'--bfile',str(self.bfile),
                               '--output',str(self.output)],capture_output=True,text=True)
        self.assertEqual(result.returncode,1)
        self.assertIn('nonempty b-file',result.stderr)
        self.assertEqual(result.stdout,'')
        self.assertFalse(self.checkpoint.exists())
        self.assertEqual(before,{path:path.read_bytes() for path in before})

    def test_failed_bfile_write_recovers_from_checkpoint(self):
        original = program.atomic_write
        def fail_at_six(path,text):
            if path == self.bfile and len(text.splitlines()) == 6:
                raise OSError('simulated b-file write failure')
            return original(path,text)
        with patch.object(program,'atomic_write',fail_at_six):
            with self.assertRaises(OSError):
                self.compute(8)
        self.assertEqual(json.loads(self.checkpoint.read_text())['limit_completed'],6)
        self.assertEqual(len(self.bfile.read_text().splitlines()),5)
        self.compute(8)
        self.assertEqual(self.bfile.read_text().splitlines(),
                         ['1 1','2 2','3 3','4 4','5 5','6 5','7 6','8 6'])

    def test_atomic_replace_failure_preserves_old_file(self):
        self.bfile.write_text('old complete contents\n')
        with patch.object(Path,'replace',side_effect=OSError('simulated')):
            with self.assertRaises(OSError):
                program.atomic_write(self.bfile,'new contents\n')
        self.assertEqual(self.bfile.read_text(),'old complete contents\n')
        self.assertEqual(list(self.root.glob('.*.tmp')),[])

    def test_matches_optional_z3_reference_through30(self):
        from importlib.util import find_spec
        if find_spec('z3') is None:
            self.skipTest('optional z3 reference not installed')
        fast = self.compute(30)
        other = self.root/'reference'
        other.mkdir()
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            reference = program.compute(30,other/'state.json',other/'terms.txt',
                                        other/'b.txt',engine='z3')
        self.assertEqual(fast,reference)

    def test_root_symmetry_reduction_against_all_small_subsets(self):
        previous = 0
        for n in range(1,15):
            edges = program.collision_edges(n)
            zero_edges = [tuple(v-1 for v in e) for group in edges.values() for e in group]
            search = program.SidonSearch(n,[0],zero_edges,0)
            required = search.free | search.forced | (1 << (n-1))
            maximum = canonical = 0
            for mask in range(1 << n):
                subset = [i+1 for i in range(n) if mask >> i & 1]
                products = [a*b for a,b in combinations(subset,2)]
                if len(set(products)) != len(products):
                    continue
                maximum = max(maximum,len(subset))
                if mask & required == required and not mask & search.forbidden:
                    canonical = max(canonical,len(subset))
            if maximum > previous:
                self.assertEqual(canonical,maximum,(n,canonical,maximum))
            previous = maximum

    def test_coloring_bounds_every_prefix(self):
        import random
        rng=random.Random(425)
        n=7
        for _ in range(20):
            adjacency=[0]*n
            for a,b in combinations(range(n),2):
                if rng.randrange(2):
                    adjacency[a]|=1<<b;adjacency[b]|=1<<a
            order,bounds=program.SidonSearch.color_order((1<<n)-1,adjacency)
            for end in range(1,n+1):
                vertices=order[:end]
                maximum=0
                for mask in range(1<<end):
                    chosen=[vertices[i] for i in range(end) if mask>>i&1]
                    if all(adjacency[a]>>b&1 for a,b in combinations(chosen,2)):
                        maximum=max(maximum,len(chosen))
                self.assertLessEqual(maximum,bounds[end-1])

    def test_default_works_without_site_packages(self):
        command=[sys.executable,'-S','-B',program.__file__,'12',
                 '--checkpoint',str(self.checkpoint),'--bfile',str(self.bfile),
                 '--output',str(self.output)]
        result=subprocess.run(command,capture_output=True,text=True,check=True)
        self.assertEqual(result.stdout.strip(),'1, 2, 3, 4, 5, 5, 6, 6, 7, 7, 8, 9')

    def test_cli_stdout_stderr_and_combined_output(self):
        command = [sys.executable, '-B', program.__file__, '8',
                   '--checkpoint', str(self.checkpoint), '--bfile', str(self.bfile),
                   '--output', str(self.output)]
        expected = '1, 2, 3, 4, 5, 5, 6, 6'
        separate = subprocess.run(command, capture_output=True, text=True, check=True)
        self.assertEqual(separate.stdout.strip(), expected)
        self.assertIn('n=8: 6 (optimal)\n', separate.stderr)
        stdout_only = subprocess.run(command, stdout=subprocess.PIPE,
                                     stderr=subprocess.DEVNULL, text=True, check=True)
        self.assertEqual(stdout_only.stdout.strip(), expected)
        stderr_only = subprocess.run(command, stdout=subprocess.DEVNULL,
                                     stderr=subprocess.PIPE, text=True, check=True)
        self.assertIn('Saved proved prefix n=1..8', stderr_only.stderr)
        combined = subprocess.run(command, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, text=True, check=True)
        self.assertEqual(combined.stdout.splitlines().count(expected), 1)
        self.assertNotIn('\r', combined.stdout)

    def test_output_lock_and_path_aliases(self):
        with program.output_locks([self.checkpoint,self.bfile]):
            with self.assertRaises(program.OutputLocked):
                with program.output_locks([self.bfile]):
                    self.fail('concurrent writer accepted')
        with self.assertRaises(ValueError):
            program.validate_paths([Path(program.__file__),self.checkpoint,self.bfile,self.bfile])
        with self.assertRaises(ValueError):
            program.validate_paths([Path(program.__file__),self.checkpoint,self.bfile,
                                    Path(str(self.bfile)+'.lock')])


if __name__ == '__main__':
    unittest.main()
