#!/usr/bin/env bash
# Fetch local copies of the freely available references into references/sources/.
# (Copyrighted material — Belyi's original paper and the CUP books — must be
# obtained through a library.)
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p sources

fetch() {
  local url="$1" out="$2"
  if [ ! -s "sources/$out" ]; then
    echo "Fetching $out"
    curl -sSfL -A "Mozilla/5.0 (X11; Linux x86_64)" "$url" -o "sources/$out"
  else
    echo "Already present: $out"
  fi
}

# Köck, "Belyi's theorem revisited" (arXiv:math/0108222)
fetch "https://arxiv.org/pdf/math/0108222" koeck-belyi-revisited.pdf
# Guillot, "An elementary approach to dessins d'enfants ..." (arXiv:1309.1968)
fetch "https://arxiv.org/pdf/1309.1968" guillot-dessins.pdf
# Zapponi, "What is a dessin d'enfant?" (Notices AMS, 2003)
fetch "https://www.ams.org/notices/200307/what-is.pdf" zapponi-what-is-a-dessin.pdf

echo "Done. Files in $(pwd)/sources:"
ls -l sources
