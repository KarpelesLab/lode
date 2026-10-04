#!/bin/sh
# Builds hello world in Lode, Go, Rust and Zig with size-oriented flags and reports
# binary size and syscalls after execve. See docs/concept.md.
set -e
cd "$(dirname "$0")"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export GOWORK=off
RF="-C opt-level=z -C lto=fat -C codegen-units=1 -C panic=abort -C strip=symbols"

for f in go_*.go; do go build -ldflags='-s -w' -o "$out/${f%.go}" "$f"; done
for f in rs_*.rs; do
	rustc $RF -o "$out/${f%.rs}" "$f"
	rustc $RF -C target-feature=+crt-static -o "$out/${f%.rs}_static" "$f"
done
for f in zig_*.zig; do zig build-exe -OReleaseSmall -fstrip -femit-bin="$out/${f%.zig}" "$f"; done
(cd ../.. && cargo build --release --quiet)
target=$(cd ../.. && cargo metadata --no-deps --format-version 1 | sed 's/.*"target_directory":"\([^"]*\)".*/\1/')
for f in lode_*.lode; do "$target/release/lode" build -O2 -o "$out/${f%.lode}" "$f"; done

printf '%-18s %10s %9s\n' program bytes syscalls
for b in "$out"/*; do
	case "$b" in *.o) continue;; esac
	[ "$("$b")" = "hello world" ] || { echo "$b: wrong output" >&2; exit 1; }
	n=$(strace -f "$b" 2>&1 >/dev/null | grep -v '^+++\|^---\|execve(' | grep -c .)
	printf '%-18s %10s %9s\n' "$(basename "$b")" "$(stat -c %s "$b")" "$n"
done
