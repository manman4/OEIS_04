"""Short independent mathematical checks and data-safety regressions."""
from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import importlib.util
import inspect
import io
from itertools import combinations
import json
from math import prod
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("problem795", Path(__file__).with_name("401472_01.py"))
program = importlib.util.module_from_spec(spec)
spec.loader.exec_module(program)


def distinct_products(items):
    products = [1]
    for item in items:
        products.extend([value*item for value in products])
    return len(products) == len(set(products))


class SafetyChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.checkpoint = self.root/"state.json"
        self.output = self.root/"terms.txt"
        self.bfile = self.root/"b.txt"

    def compute(self, n, verify_only=False):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            program.compute(n, self.checkpoint, self.output, verify_only=verify_only,
                            bfile=self.bfile)

    def cli(self, n, optimized=False):
        return [sys.executable]+(['-O'] if optimized else [])+[
            '-B',program.__file__,str(n),'--checkpoint',str(self.checkpoint),
            '--output',str(self.output),'--bfile',str(self.bfile)]

    def test_independent_maxima_and_relations(self):
        oracle=[]
        for n in range(1,13):
            best=0
            for mask in range(1 << (n-1)):
                items=[i+2 for i in range(n-1) if mask>>i&1]
                if distinct_products(items):
                    best=max(best,len(items))
            oracle.append(best)
        self.compute(12)
        self.assertEqual(json.loads(self.checkpoint.read_text())['values'],oracle)
        fs={n:program.factors(n) for n in range(2,31)}
        for mask in range(1<<8):
            items=[i+2 for i in range(8) if mask>>i&1]
            relation=program.find_relation(items,fs)
            self.assertEqual(relation is None,distinct_products(items),items)
            if relation is not None:
                self.assertEqual(prod(relation['left']),prod(relation['right']))
        relation=program.find_relation([2,3,5,30],fs)
        self.assertIsNotNone(relation)
        self.assertEqual(prod(relation['left']),prod(relation['right']))

    def test_missing_or_empty_checkpoint_preserves_bfile(self):
        self.bfile.write_text('1 0\n2 1\n3 2\n')
        self.output.write_text('existing output\n')
        before={p:p.read_bytes() for p in (self.bfile,self.output)}
        for empty_checkpoint in (False,True):
            if empty_checkpoint:
                self.checkpoint.write_text(json.dumps(program.load_state(self.checkpoint)))
            for verify_only in (False,True):
                with self.assertRaisesRegex(ValueError,'nonempty b-file'):
                    self.compute(3,verify_only)
                self.assertEqual(before,{p:p.read_bytes() for p in before})
        result=subprocess.run(self.cli(3),capture_output=True,text=True)
        self.assertEqual(result.returncode,1)
        self.assertIn('nonempty b-file',result.stderr)
        self.assertEqual(before,{p:p.read_bytes() for p in before})

    def test_smaller_request_keeps_full_bfile_without_universe_metadata(self):
        self.compute(7)
        state=json.loads(self.checkpoint.read_text())
        state.pop('universe_limit')
        self.checkpoint.write_text(json.dumps(state))
        original=self.bfile.read_bytes()
        self.compute(3)
        self.assertEqual(self.bfile.read_bytes(),original)
        self.assertEqual(program.load_state(self.checkpoint)['limit_completed'],7)
        self.assertEqual(self.output.read_text().strip(),'0, 1, 2')

    def test_interruption_inside_term_construction_preserves_last_commit(self):
        self.compute(2)
        lines,start=inspect.getsourcelines(program.completed_state)
        target=start+next(i for i,line in enumerate(lines) if '"witnesses":' in line)
        triggered=[False]
        def trace(frame,event,arg):
            if (event=='line' and frame.f_code is program.completed_state.__code__ and
                    frame.f_lineno==target and frame.f_locals.get('n')==3 and not triggered[0]):
                triggered[0]=True
                raise KeyboardInterrupt
            return trace
        try:
            sys.settrace(trace)
            with self.assertRaises(KeyboardInterrupt):
                self.compute(3)
        finally:
            sys.settrace(None)
        self.assertTrue(triggered[0])
        state=program.load_state(self.checkpoint)
        self.assertEqual(state['limit_completed'],2)
        self.assertEqual([len(state[name]) for name in ('values','witnesses','statistics')],[2,2,2])
        self.compute(3)
        self.assertEqual(program.load_state(self.checkpoint)['limit_completed'],3)

    def test_interruption_after_term_commit_and_failed_bfile_write(self):
        self.compute(2)
        original=program.atomic_write
        triggered=[False]
        def interrupt(path,text):
            if path==self.checkpoint and json.loads(text)['limit_completed']==3 and not triggered[0]:
                triggered[0]=True
                raise KeyboardInterrupt
            return original(path,text)
        with patch.object(program,'atomic_write',interrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.compute(3)
        self.assertEqual(program.load_state(self.checkpoint)['limit_completed'],3)
        self.assertEqual(len(self.bfile.read_text().splitlines()),3)
        def fail_bfile(path,values):
            if len(values)==4:
                raise OSError('simulated b-file failure')
            return original(path,''.join(f'{i} {v}\n' for i,v in enumerate(values,1)))
        with patch.object(program,'write_bfile',fail_bfile):
            with self.assertRaises(OSError):
                self.compute(4)
        self.assertEqual(program.load_state(self.checkpoint)['limit_completed'],4)
        self.assertEqual(len(self.bfile.read_text().splitlines()),3)
        self.compute(4)
        self.assertEqual(len(self.bfile.read_text().splitlines()),4)

    def test_unknown_result_keeps_proved_prefix_and_resumes(self):
        self.compute(5)
        with patch.object(program,'upper_probe',side_effect=program.IncompleteCheck('simulated')):
            with self.assertRaises(program.IncompleteCheck):
                self.compute(6)
        state=program.load_state(self.checkpoint)
        self.assertEqual(state['limit_completed'],5)
        self.assertEqual(len(self.bfile.read_text().splitlines()),5)
        self.compute(6)
        self.assertEqual(program.load_state(self.checkpoint)['limit_completed'],6)

    def test_invalid_checkpoint_metadata_is_rejected(self):
        self.compute(3)
        base=json.loads(self.checkpoint.read_text())
        cases=[]
        for key,values in [('limit_completed',[True,-1,101]),
                           ('universe_limit',[True,2.0,0,101,10**9]),
                           ('target_limit',[False,0,101]),
                           ('elapsed_seconds',[True,-1,float('nan'),float('inf')])]:
            for value in values:
                changed=deepcopy(base);changed[key]=value;cases.append(changed)
        changed=deepcopy(base);changed['values'][1]=True;cases.append(changed)
        changed=deepcopy(base);changed['witnesses'][1]=[2.0];cases.append(changed)
        changed=deepcopy(base);changed['statistics']=[];cases.append(changed)
        changed=deepcopy(base);changed['cuts']=[{'left':[2,2],'right':[4]}];cases.append(changed)
        changed=deepcopy(base);changed['pending']={'n':101,'lower_bound':0,'witness':[]};cases.append(changed)
        for changed in cases:
            self.checkpoint.write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                program.load_state(self.checkpoint)

    def test_checkpoint_lock_and_shared_bfile_lock_across_processes(self):
        self.bfile.write_text('existing data\n')
        for shared in (self.checkpoint,self.bfile):
            with program.output_locks([shared]):
                result=subprocess.run(self.cli(1),capture_output=True,text=True)
                self.assertEqual(result.returncode,1)
                self.assertIn('Another process is using',result.stderr)
            self.assertEqual(self.bfile.read_text(),'existing data\n')
            self.assertFalse(self.checkpoint.exists())

    def test_optimized_python_and_required_solver_check(self):
        code=("import importlib.util,json; "
              f"s=importlib.util.spec_from_file_location('p',{program.__file__!r}); "
              "p=importlib.util.module_from_spec(s);s.loader.exec_module(p); "
              "print(json.dumps(p.find_relation([2,3,6],{n:p.factors(n) for n in [2,3,6]})))")
        result=subprocess.run([sys.executable,'-O','-B','-c',code],capture_output=True,text=True,check=True)
        relation=json.loads(result.stdout)
        self.assertTrue(relation['left'] and relation['right'])
        self.assertEqual(prod(relation['left']),prod(relation['right']))
        result=subprocess.run(self.cli(12,optimized=True),capture_output=True,text=True,check=True)
        self.assertEqual(program.load_state(self.checkpoint)['values'],[0,1,2,3,4,4,5,5,6,6,7,7])

    def test_atomic_replace_failure_and_output_aliases(self):
        self.bfile.write_text('old data\n')
        with patch.object(Path,'replace',side_effect=OSError('simulated')):
            with self.assertRaises(OSError):
                program.atomic_write(self.bfile,'new data\n')
        self.assertEqual(self.bfile.read_text(),'old data\n')
        self.assertEqual(list(self.root.glob('.*.tmp')),[])
        with self.assertRaises(ValueError):
            program.compute(1,self.checkpoint,self.bfile,bfile=self.bfile)
        with self.assertRaises(ValueError):
            program.compute(1,self.checkpoint,Path(str(self.bfile)+'.lock'),bfile=self.bfile)

    def test_empty_prefix_after_first_term_interrupt_can_resume(self):
        with patch.object(program,'pure_prime_construction',side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.compute(1)
        self.assertEqual(program.load_state(self.checkpoint)['limit_completed'],0)
        self.assertEqual(self.bfile.read_text(),'')
        self.compute(2)
        self.assertEqual(program.load_state(self.checkpoint)['values'],[0,1])

    def test_cli_boundaries(self):
        for value in ['0','101','-1','not-a-number']:
            result=subprocess.run(self.cli(value),capture_output=True,text=True)
            self.assertEqual(result.returncode,2)
            self.assertFalse(self.checkpoint.exists())
        for timeout in ['-1',str(1<<32)]:
            result=subprocess.run(self.cli(1)+['--timeout-ms',timeout],capture_output=True,text=True)
            self.assertEqual(result.returncode,2)
            self.assertFalse(self.checkpoint.exists())
        # Upper boundary allocation only; no long search.
        solver,variables=program.build_solver(100,[],1)
        self.assertEqual(len(variables),99)
        self.assertEqual(max(variables),100)


if __name__=='__main__':
    unittest.main()
