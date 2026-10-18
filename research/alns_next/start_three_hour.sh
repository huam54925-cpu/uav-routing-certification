#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
cd "$HERE"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
sha256sum -c THREE_HOUR_SHA256SUMS.txt
python3 -m venv --system-site-packages "$REPO/.venv-research"
PY="$REPO/.venv-research/bin/python"
"$PY" -m pip install --disable-pip-version-check 'numpy==2.1.2' 'scipy==1.15.3'
"$PY" verify_bound_certificate.py research_results_20261016/case1_connectivity_bound.json --case Case1 --fleet 3
"$PY" verify_bound_certificate.py research_results_20261016/case3_connectivity_bound.json --case Case3 --fleet 4
"$PY" -m unittest -v test_three_hour_queue.py test_solver.py test_neighborhood_entry.py
"$PY" - <<'PY'
import hashlib,json
from pathlib import Path
from run_six_hour_queue import read_input
from validate import validate
from run_three_hour_queue import resource_limits
here=Path.cwd();root=here.parents[1]
data=json.loads((here/'instances.json').read_text())
manifest=json.loads((here/'THREE_HOUR_INPUTS.json').read_text())
for case,item in manifest.items():
    path=root/item['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'], 'Snapshot SHA mismatch'
    record=read_input(path);validate(data,record)
    assert record['case']==case
print('Inputs PASS; resource limits:',resource_limits())
PY
OUT="${ALNS_OUT:-/workspace/uav-runs/three_hour_$(date -u +%Y%m%d_%H%M%S)}"
mkdir -p "$OUT"
if [ -e "$OUT/state.json" ]; then
  echo 'Output already exists. For resume, use the command documented in THREE_HOUR_GUIDE.md.' >&2
  exit 1
fi
printf '%s\n' "$OUT" > "$REPO/LATEST_RUN"
nohup "$PY" -u "$HERE/run_three_hour_queue.py" \
  --case1-warm "$REPO/inputs/case1.zip" --case3-warm "$REPO/inputs/case3.zip" \
  --out "$OUT" --hours 3 --workers 12 --bound-seconds 600 --slice-seconds 600 --port 0 \
  > "$OUT/console.log" 2>&1 < /dev/null &
PID=$!
printf '%s\n' "$PID" > "$OUT/supervisor.pid"
for i in $(seq 1 30); do
  if ! kill -0 "$PID" 2>/dev/null; then cat "$OUT/console.log"; exit 1; fi
  if [ -s "$OUT/progress.json" ]; then cat "$OUT/progress.json"; echo "Started. Output: $OUT"; exit 0; fi
  sleep 1
done
echo "Startup has not written progress yet. Inspect $OUT/console.log (PID $PID)." >&2
exit 1
