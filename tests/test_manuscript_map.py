"""Protect the distinction between renumbering, statement edits and proof edits."""
import importlib.util
import unittest
from pathlib import Path

path = Path(__file__).resolve().parents[1]/'tools/check_manuscript_map.py'
spec = importlib.util.spec_from_file_location('check_manuscript_map', path)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

TEX = r'''
\begin{theorem}\label{thm:stable}
For $x>0$, $f(x)>0$.
\end{theorem}
\begin{proof}Apply positivity.\end{proof}
'''

class StatementTracking(unittest.TestCase):
    def setUp(self):
        self.mapping = {'manuscript': {'sha256': mod.digest(TEX)},
                        'entries': [{'paper_label': 'thm:stable',
                                     'baseline': mod.extract(TEX)['thm:stable']}]}

    def test_intro_or_numbering_change(self):
        changed = r'\setcounter{theorem}{18}' + '\nNew introduction.\n' + TEX
        self.assertEqual(mod.compare(changed,self.mapping)['changes'], [])

    def test_math_change_requires_review(self):
        report = mod.compare(TEX.replace('f(x)>0','f(x)\\ge0'),self.mapping)
        self.assertEqual(report['changes'][0]['status'], 'statement_changed')

    def test_proof_change_is_distinct(self):
        report = mod.compare(TEX.replace('Apply positivity.','Apply convexity.'),self.mapping)
        self.assertEqual(report['changes'][0]['status'], 'proof_changed')

    def test_renamed_label_requires_review(self):
        report = mod.compare(TEX.replace('thm:stable','thm:new'),self.mapping)
        self.assertEqual(report['changes'][0]['status'], 'missing_or_renamed')

    def test_comments_are_ignored(self):
        report = mod.compare(TEX.replace('For $x>0$', '% comment\nFor $x>0$'),self.mapping)
        self.assertEqual(report['changes'], [])

    def test_duplicate_label_fails(self):
        with self.assertRaises(ValueError):
            mod.extract(TEX+TEX)

if __name__ == '__main__':
    unittest.main()
