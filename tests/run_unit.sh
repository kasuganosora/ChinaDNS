#!/bin/bash
set -eu
cd "$(dirname "$0")/.."

if [ ! -f config.h ]; then
  echo "config.h missing; run ./autogen.sh && ./configure first" >&2
  exit 1
fi

CFLAGS="-Wall -Wextra -Wno-unused-function -I. -Isrc"
if echo 'int main(void){return 0;}' | gcc -fsanitize=address,undefined -x c -o /tmp/chinadns-asan-probe - >/dev/null 2>&1 \
   && /tmp/chinadns-asan-probe; then
  CFLAGS="$CFLAGS -fsanitize=address,undefined"
fi

gcc $CFLAGS -DUNIT_TEST -o /tmp/chinadns_unit src/chinadns.c src/local_ns_parser.c -lresolv
ASAN_OPTIONS="${ASAN_OPTIONS:-detect_leaks=1}" /tmp/chinadns_unit "${1:-chnroute.txt}"
