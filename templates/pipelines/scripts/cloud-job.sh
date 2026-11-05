#!/usr/bin/env bash
# The refresh as an in-cloud job (`where: cloud-job` in refresh.yml): for
# large data, where a refresh in Actions would pay egress on every byte it
# reads and has about 7 GB of RAM.
#
#   scripts/cloud-job.sh <refresh.json> <alert.md>
#
# The contract with refresh.yml: start a job in the bucket's region that runs
# `python scripts/lake.py refresh --out refresh.json --alert alert.md` from
# the sverify container image with this commit's pipelines and
# SVERIFY_LAKE; wait for it; copy its refresh.json (and alert.md) here;
# exit with its exit code. The catalog step then runs in Actions as usual.
#
#   AWS:          ECS Fargate (aws ecs run-task, aws ecs wait tasks-stopped) or AWS Batch
#   Google Cloud: Cloud Run Jobs (gcloud run jobs execute --wait)
#   Azure:        Container Apps Jobs (az containerapp job start, then poll its execution)
#
# It waits for the sverify container image (#770). Until then it reports a
# clear error, which the alerts workflow turns into an issue.
set -euo pipefail
out=${1:-refresh.json}
alert=${2:-alert.md}
message="where=cloud-job needs the sverify container image (#770); set SVERIFY_REFRESH_WHERE to actions"
echo "::error title=cloud-job::$message"
python - "$out" "$message" <<'PY'
import json, sys
from datetime import UTC, datetime
out, message = sys.argv[1], sys.argv[2]
error = {"code": "error", "type": "CloudJob", "message": message}
json.dump({"exit": 6, "at": datetime.now(UTC).isoformat(timespec="seconds"),
           "runs": [{"target": "cloud-job", "exit": 6, "result": {"status": "error", "error": error}}]},
          open(out, "w"), indent=2)
PY
printf '<!-- sverify-alert -->\nThe refresh failed: %s.\n' "$message" > "$alert"
exit 6
