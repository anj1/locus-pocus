"""Exercise certificate generation, replay, and rejection through the public CLI."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CertificateTests(unittest.TestCase):
    def certificate(self, data, *options, script='univariate'):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name)
        input_path = path / 'input.json'
        certificate = path / 'Certificate.lean'
        input_path.write_text(json.dumps(data))
        report = subprocess.check_output(
            [sys.executable, f'scripts/{script}.py', str(input_path),
             '--lean', str(certificate), *options], cwd=ROOT, text=True)
        return json.loads(report), certificate

    def test_lean_isolation_over_an_algebraic_extension(self):
        subprocess.run(['lake', 'build', 'CertifiedTopology.ComputedInput'], cwd=ROOT, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        subprocess.run(['lake', 'env', 'lean', 'tests/ExecutableIsolation.lean'],
                       cwd=ROOT, check=True, timeout=60)

    def test_algebraic_crossing_computed_closure_components(self):
        report, _ = self.certificate([
            [[1, 0, 0, 1], [0, 0, 0, {'polynomial': [-2, 0, 1], 'root': 0}]],
            [[0, 1, 1, 1]],
        ], '--stratify', script='intersection')
        self.assertEqual(report['route'], 'cad')
        self.assertEqual([c['dimension'] for c in report['cells']], [1, 1, 1])
        self.assertEqual([c['closure_overlap'] for c in report['cells']], [[1, 2], [0, 2], [0, 1]])
        self.assertEqual({c['component'] for c in report['cells']}, {0})
        self.assertEqual(report['strata'], [
            {'dimension': 1, 'closure': [0, 3]},
            {'dimension': 1, 'closure': [1, 3]},
            {'dimension': 1, 'closure': [2, 3]},
            {'dimension': 0, 'closure': [3]},
        ])

    def test_curved_quadric_computed_frontier(self):
        report, _ = self.certificate([
            [[2, 0, 0, 1], [1, 0, 0, {'polynomial': [-8, 0, 1], 'root': 0}], [0, 0, 0, 2]],
            [[0, 0, 1, 1], [0, 2, 0, -1]],
        ], '--stratify', script='intersection')
        self.assertEqual(report['route'], 'cad')
        self.assertEqual([c['dimension'] for c in report['cells']], [1])
        self.assertEqual(report['strata'], [{'dimension': 1, 'closure': [0]}])

    def test_singular_quartic_computed_frontier(self):
        report, certificate = self.certificate([
            [[4, 0, 0, 1], [2, 0, 0, 1], [0, 0, 0, -2]],
            [[0, 2, 0, 1], [0, 0, 2, 1]],
        ], '--stratify', script='intersection')
        self.assertEqual(report['route'], 'cad')
        self.assertEqual(len({c['component'] for c in report['cells']}), 2)
        self.assertEqual(report['strata'], [
            {'dimension': 0, 'closure': [0]},
            {'dimension': 0, 'closure': [1]},
        ])
        subprocess.run(['lake', 'env', 'lean', str(certificate)], cwd=ROOT, check=True, timeout=60)

    def test_shared_irrational_roots_and_rejected_sign(self):
        rows, certificate = self.certificate([[4, 0, -4, 0, 1], [-2, 0, 1], []])
        self.assertEqual([r['signs'] for r in rows],
                         [[1, 1, 0], [0, 0, 0], [1, -1, 0], [0, 0, 0], [1, 1, 0]])
        certificate.write_text(certificate.read_text().replace(
            'signs := [.above, .above, .on]', 'signs := [.below, .above, .on]', 1))
        result = subprocess.run(['lake', 'env', 'lean', str(certificate)],
                                cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('⊢ False', result.stdout)

    def test_nullified_fiber(self):
        rows, _ = self.certificate([[0, 1], [], [0, -1]], '--quadratic-family')
        self.assertEqual([r['fiber'] for r in rows], ['twoPoints', 'line', 'twoPoints'])

    def test_empty_input(self):
        rows, _ = self.certificate([])
        self.assertEqual(rows, [{'cell': {'sector': [None, None], 'sample': '0'}, 'signs': []}])

    def test_quartic_graph_closure_and_rejected_incidence(self):
        report, certificate = self.certificate([
            [[0, 1, 0, 1], [4, 0, 0, -1]],
            [[0, 0, 2, 1], [3, 0, 0, -1], [4, 0, 0, 1]],
        ], script='intersection')
        cells = report['cells']
        self.assertEqual([c['cell']['dimension'] for c in cells], [0, 1, 1, 0])
        self.assertEqual([c['closure'] for c in cells], [[0], [0, 1, 3], [0, 2, 3], [3]])
        self.assertEqual(len(set(c['component'] for c in cells)), 1)
        certificate.write_text(certificate.read_text().replace(
            'decide (i = j ∨', 'decide (i ≠ j ∨', 1))
        result = subprocess.run(['lake', 'env', 'lean', str(certificate)],
                                cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)

    def test_fourth_power_height(self):
        report, _ = self.certificate([
            [[4, 0, 0, 1], [0, 4, 0, 1], [0, 0, 4, 1], [0, 0, 0, -1]],
            [[0, 0, 1, 1]],
        ], script='intersection')
        self.assertEqual(report['power'], 4)
        self.assertEqual(len(report['cells']), 4)
        self.assertEqual(len({c['component'] for c in report['cells']}), 1)

    def test_expanded_affine_factors_and_disconnected_fibers(self):
        report, _ = self.certificate([
            [[2, 0, 0, 1], [0, 2, 0, -1]],
            [[0, 0, 4, 1], [0, 0, 3, -2], [0, 0, 2, 1]],
        ], script='intersection')
        self.assertEqual(report['route'], 'affine')
        cells = report['cells']
        self.assertEqual(len(cells), 10)
        labels_by_height = {}
        for entry in cells:
            z = entry['cell']['sample'][2]
            labels_by_height.setdefault(z, set()).add(entry['component'])
        self.assertEqual(set(labels_by_height), {'0', '1'})
        self.assertEqual(len(labels_by_height['0']), 1)
        self.assertEqual(len(labels_by_height['1']), 1)
        self.assertTrue(labels_by_height['0'].isdisjoint(labels_by_height['1']))


if __name__ == '__main__':
    unittest.main()
