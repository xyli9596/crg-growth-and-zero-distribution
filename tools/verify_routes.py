#!/usr/bin/env python3
"""Check the independent CRG proof route by traversing Lean proof bodies."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parents[1]
report_path = root / 'verification/verification.json'
report = json.loads(report_path.read_text())
assert report['all_requested_checks_passed'], 'Run verify.py first'
for entry in report['files']:
    assert hashlib.sha256((root / entry['file']).read_bytes()).hexdigest() == entry['sha256']
result = subprocess.run(['lake', 'env', 'lean', 'tools/ProofDependencies.lean'],
                        cwd=root, capture_output=True, text=True)
(root / 'verification/proof-routes.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0, result.stdout + result.stderr
rows = json.loads(result.stdout.split('ROUTE_AUDIT_JSON:', 1)[1])
assert len(rows) == 3
for row in rows:
    deps = row['local_dependencies']
    forbidden = [n for n in deps if n.startswith(('LiWangWen.', 'WimanValiron.', 'Helmrath', 'IncePeriodic.'))]
    assert not forbidden, (row['declaration'], forbidden)
    row['uses_LWW_growth_or_representation'] = False
    assert 'CRGOrderPhaseCriterion.exists_positive_leading' in deps
    row['uses_CRG_phase_order_criterion'] = True
    if not row['declaration'].startswith('CRGLinearPhaseEndgame.'):
        assert 'WasowConstantLinearGauge.constant_linear_normal_form' in deps
        row['uses_constructed_constant_matrix_linear_phases'] = True
out = {
    'status': 'passed',
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'method': 'Lean ConstantInfo type and proof-body transitive closure',
    'verification_sha256': hashlib.sha256(report_path.read_bytes()).hexdigest(),
    'diagnostic_source_sha256': hashlib.sha256((root / 'tools/ProofDependencies.lean').read_bytes()).hexdigest(),
    'endpoints': rows,
}
(root / 'verification/proof-routes.json').write_text(json.dumps(out, indent=2) + '\n')
print('PASS: all three endpoints use the CRG phase/order method; no LWW growth or representation dependency.')
