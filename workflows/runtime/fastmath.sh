#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CACHE_DIR="${FASTMATH_CACHE_DIR:-$ROOT_DIR/workflows/state/fastmath-cache}"

usage() {
  cat <<'EOF'
Usage:
  workflows/runtime/fastmath.sh doctor
  workflows/runtime/fastmath.sh new cpp path/to/search.cpp
  workflows/runtime/fastmath.sh new rust path/to/crate
  workflows/runtime/fastmath.sh new milp path/to/model.py
  workflows/runtime/fastmath.sh cpp path/to/program.cpp [-- program arguments...]
  workflows/runtime/fastmath.sh rust path/to/Cargo.toml [-- program arguments...]

Environment:
  FASTMATH_CXX       C++ compiler (default: g++)
  FASTMATH_CXXFLAGS  Additional C++ flags
  FASTMATH_LIBS      Space-separated libraries, e.g. "flint gmp"; known
                     Debian math libraries work without pkg-config metadata
  FASTMATH_CACHE_DIR Compiled-artifact cache
EOF
}

new_task() {
  local kind="${1:?missing template kind}"
  local destination="${2:?missing destination}"
  case "$destination" in
    /*) ;;
    *) destination="$ROOT_DIR/$destination" ;;
  esac
  destination="$(realpath -m "$destination")"
  [[ "$destination" == "$ROOT_DIR/"* ]] || {
    printf 'destination must stay under repository root: %s\n' "$destination" >&2
    return 2
  }
  [[ ! -e "$destination" ]] || {
    printf 'refusing to overwrite existing path: %s\n' "$destination" >&2
    return 2
  }
  mkdir -p "$(dirname "$destination")"
  case "$kind" in
    cpp)
      cp "$ROOT_DIR/workflows/runtime/templates/fastmath/streaming_search.cpp" "$destination"
      ;;
    rust)
      cp -R "$ROOT_DIR/workflows/runtime/templates/fastmath/rust-search" "$destination"
      ;;
    milp)
      cp "$ROOT_DIR/workflows/runtime/templates/fastmath/sparse_milp.py" "$destination"
      chmod +x "$destination"
      ;;
    *)
      printf 'unknown template kind: %s (expected cpp, rust, or milp)\n' "$kind" >&2
      return 2
      ;;
  esac
  printf 'created %s template at %s\n' "$kind" "$destination"
}

library_flags() {
  local library
  for library in "$@"; do
    if pkg-config --exists "$library" 2>/dev/null; then
      pkg-config --cflags --libs "$library"
      continue
    fi
    case "$library" in
      flint) printf '%s\n' -lflint ;;
      gmp) printf '%s\n' -lgmp ;;
      ntl) printf '%s\n' -lntl ;;
      openblas) printf '%s\n' -lopenblas ;;
      eigen3) printf '%s\n' -I/usr/include/eigen3 ;;
      *)
        printf 'unknown library without pkg-config metadata: %s\n' "$library" >&2
        return 2
        ;;
    esac
  done
}

doctor() {
  local failed=0
  for command in g++ cmake ninja cargo rustc pkg-config kissat drat-trim geng lean lake; do
    if command -v "$command" >/dev/null 2>&1; then
      printf 'ok   %-12s %s\n' "$command" "$(command -v "$command")"
    else
      printf 'MISS %-12s\n' "$command"
      failed=1
    fi
  done
  local probe
  probe="$(mktemp "${TMPDIR:-/tmp}/fastmath-doctor.XXXXXX")"
  if printf '%s\n' '#include <flint/fmpz.h>' \
      'int main() { fmpz_t x; fmpz_init(x); fmpz_clear(x); }' \
      | "${FASTMATH_CXX:-g++}" -x c++ - -lflint -lgmp -o "$probe" >/dev/null 2>&1; then
    printf 'ok   math:flint+gmp\n'
  else
    printf 'MISS math:flint+gmp\n'
    failed=1
  fi
  if printf '%s\n' '#include <NTL/ZZ.h>' '#include <Eigen/Core>' '#include <cblas.h>' \
      'int main() { NTL::ZZ x(1); Eigen::Matrix2d m; m.setZero(); return x == 1 ? 0 : 1; }' \
      | "${FASTMATH_CXX:-g++}" -x c++ - -I/usr/include/eigen3 -lntl -lgmp -lopenblas \
          -o "$probe" >/dev/null 2>&1; then
    printf 'ok   math:ntl+eigen+openblas\n'
  else
    printf 'MISS math:ntl+eigen+openblas\n'
    failed=1
  fi
  rm -f "$probe"
  return "$failed"
}

run_cpp() {
  local source="${1:?missing C++ source}"
  shift
  if [[ "${1:-}" == "--" ]]; then shift; fi
  source="$(realpath "$source")"
  [[ -f "$source" ]] || { printf 'missing source: %s\n' "$source" >&2; exit 2; }

  local compiler="${FASTMATH_CXX:-g++}"
  local extra_flags="${FASTMATH_CXXFLAGS:-}"
  local libraries="${FASTMATH_LIBS:-}"
  local library_output=""
  local digest
  digest="$(
    {
      sha256sum "$source"
      "$compiler" --version | head -1
      printf '%s\n%s\n' "$extra_flags" "$libraries"
    } | sha256sum | cut -c1-20
  )"
  mkdir -p "$CACHE_DIR/cpp"
  local binary="$CACHE_DIR/cpp/$(basename "${source%.cpp}")-$digest"
  if [[ ! -x "$binary" ]]; then
    local -a flags=(-O3 -DNDEBUG -std=c++23 -march=native -flto -pthread)
    local -a library_flags=()
    if [[ -n "$extra_flags" ]]; then
      read -r -a extra_array <<<"$extra_flags"
      flags+=("${extra_array[@]}")
    fi
    if [[ -n "$libraries" ]]; then
      read -r -a library_array <<<"$libraries"
      library_output="$(library_flags "${library_array[@]}")"
      read -r -a library_flags <<<"${library_output//$'\n'/ }"
    fi
    "$compiler" "${flags[@]}" "$source" -o "$binary" "${library_flags[@]}"
  fi
  exec "$binary" "$@"
}

run_rust() {
  local manifest="${1:?missing Cargo.toml}"
  shift
  if [[ "${1:-}" == "--" ]]; then shift; fi
  manifest="$(realpath "$manifest")"
  [[ -f "$manifest" ]] || { printf 'missing manifest: %s\n' "$manifest" >&2; exit 2; }
  mkdir -p "$CACHE_DIR/cargo"
  export CARGO_TARGET_DIR="$CACHE_DIR/cargo"
  exec cargo run --release --locked --manifest-path "$manifest" -- "$@"
}

case "${1:-}" in
  doctor) doctor ;;
  new) shift; new_task "$@" ;;
  cpp) shift; run_cpp "$@" ;;
  rust) shift; run_rust "$@" ;;
  *) usage >&2; exit 2 ;;
esac
