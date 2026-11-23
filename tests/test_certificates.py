"""Exercise certificate generation, replay, and rejection through the public CLI."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CertificateTests(unittest.TestCase):
    def certificate(self, data, *options):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name)
        input_path = path / 'input.json'
        certificate = path / 'Certificate.lean'
        input_path.write_text(json.dumps(data))
        report = subprocess.check_output(
            [sys.executable, 'scripts/univariate.py', str(input_path),
             '--lean', str(certificate), *options], cwd=ROOT, text=True)
        return json.loads(report), certificate

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


if __name__ == '__main__':
    unittest.main()
