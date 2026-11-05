#!/usr/bin/env bash
# Start Marquez (the OpenLineage reference server) and its Postgres in
# containers, for tests/test_openlineage.py::test_marquez_round_trip:
#
#   bash scripts/marquez.sh start      # prints the URL to export
#   SVERIFY_MARQUEZ_URL=http://localhost:5000 pytest tests/test_openlineage.py
#   bash scripts/marquez.sh stop
#
# Uses podman, or docker where podman is missing. MARQUEZ_PORT changes the
# API's port (default 5000).
set -euo pipefail
ENGINE=$(command -v podman || command -v docker)
PORT=${MARQUEZ_PORT:-5000}
POD=sverify-marquez
MARQUEZ_IMAGE=docker.io/marquezproject/marquez:0.51.1
PG_IMAGE=docker.io/library/postgres:14

case "${1:-start}" in
start)
  "$ENGINE" network create "$POD" >/dev/null 2>&1 || true
  "$ENGINE" run -d --rm --name "$POD-db" --network "$POD" --memory 512m \
    -e POSTGRES_USER=marquez -e POSTGRES_PASSWORD=marquez -e POSTGRES_DB=marquez \
    "$PG_IMAGE" >/dev/null
  until "$ENGINE" exec "$POD-db" pg_isready -U marquez >/dev/null 2>&1; do sleep 1; done
  "$ENGINE" run -d --rm --name "$POD-api" --network "$POD" --memory 1g -p "$PORT:5000" \
    -e POSTGRES_HOST="$POD-db" -e POSTGRES_PORT=5432 -e POSTGRES_DB=marquez \
    -e POSTGRES_USER=marquez -e POSTGRES_PASSWORD=marquez -e MARQUEZ_PORT=5000 \
    "$MARQUEZ_IMAGE" >/dev/null
  for _ in $(seq 120); do
    if curl -fs "http://localhost:$PORT/api/v1/namespaces" >/dev/null; then
      echo "SVERIFY_MARQUEZ_URL=http://localhost:$PORT"
      exit 0
    fi
    sleep 1
  done
  echo "Marquez did not start" >&2
  "$ENGINE" logs "$POD-api" | tail -40 >&2
  exit 1
  ;;
stop)
  "$ENGINE" rm -f "$POD-api" "$POD-db" >/dev/null 2>&1 || true
  "$ENGINE" network rm "$POD" >/dev/null 2>&1 || true
  ;;
esac
