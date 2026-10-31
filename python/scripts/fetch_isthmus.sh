#!/bin/sh
# Download Isthmus (substrait-java's SQL to Substrait compiler, as a native
# binary) into a directory, check it against its pinned SHA-256 and print its
# path, for `export SVERIFY_ISTHMUS=$(scripts/fetch_isthmus.sh <dir>)`.
# sverify does not ship it: it is ~120 MB.
set -eu
version=0.107.0
dir=${1:?usage: fetch_isthmus.sh <directory>}
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) os=ubuntu sha=aec246d44f882cb96a3a851b395da9fdabc0b1c9cfceb8c2cc8f4ef4c127731d ;;
  Darwin-arm64) os=macOS sha=4b4d5ab5cc0276ac689096797b110a2b5022a3a5c59ad3fe39355301fa472659 ;;
  *) echo "no Isthmus $version binary for $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac
bin="$dir/isthmus-$os-$version"
if [ ! -x "$bin" ]; then
  mkdir -p "$dir"
  curl -fsSL -o "$bin.part" \
    "https://github.com/substrait-io/substrait-java/releases/download/v$version/isthmus-$os-$version"
  if command -v sha256sum > /dev/null; then got=$(sha256sum "$bin.part"); else got=$(shasum -a 256 "$bin.part"); fi
  if [ "${got%% *}" != "$sha" ]; then
    echo "checksum mismatch for isthmus-$os-$version: ${got%% *}" >&2; rm -f "$bin.part"; exit 1
  fi
  chmod +x "$bin.part" && mv "$bin.part" "$bin"
fi
echo "$bin"
