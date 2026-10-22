#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * each REQUIRED theorem (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED theorems.
# REQUIRED lists, fully qualified, every declaration of this library cited in SPIKE_REPORT.md
# plus every name queried by scratch/Ax.lean; definitions may use a subset of the standard axioms.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Lester"
LIB="Lester"
REQUIRED="Lester.ω Lester.Ccw Lester.apexOut Lester.apexIn Lester.IsFermatOuter Lester.IsFermatInner Lester.ninePointCenter Lester.lester Lester.bridge_ω Lester.bridge_Ccw Lester.norm_ω Lester.norm_conj_ω Lester.norm_ω_sub_one Lester.norm_conj_ω_sub_one Lester.bridge_apexOut Lester.bridge_apexIn Lester.bridge_IsFermatOuter Lester.bridge_IsFermatInner Lester.bridge_ninePointCenter Lester.l14b_cross_eq Lester.l14b_mem_line_of_cross Lester.l14b_sign_neg Lester.l14b_sign_pos Lester.l14b_cross_of_sOppSide Lester.l14b_cross_of_sSameSide Lester.l14b_equilateral Lester.l14b_ccw_iff Lester.l14b_cross_apex Lester.l14b_apexOut Lester.l14b_apexIn Lester.l14_lester Lester.l14b_dist_eq Lester.l14b_dist_ne Lester.l14b_not_collinear Lester.l14b_notMem_line Lester.l14b_oppSide Lester.l14b_sameSide Lester.l14b_mem_line Lester.l14b_circumcenter Lester.l14w_lester Lester.Classical.cov_cospherical_transport Lester.Classical.cov_collinear_transport Lester.Classical.cov_D3_part Lester.Classical.gap_lineMap_coord Lester.Classical.gap_pt_ext Lester.Classical.gap_cross_of_mem Lester.Classical.gap_mem_of_cross Lester.Classical.gap_opp_cross_neg Lester.Classical.gap_same_cross_pos Lester.Classical.gap_iso_re Lester.Classical.gap_iso_im Lester.Classical.gap_ccw_iff Lester.Classical.gap_apex_alg Lester.Classical.gap_apex_char Lester.Classical.gap_ne_of_apex Lester.Classical.gap_outer_apex Lester.Classical.gap_inner_apex Lester.Classical.gap_mem_line_map Lester.Classical.gap_fermat_outer Lester.Classical.gap_fermat_inner Lester.Classical.cov_D3 Lester.Classical.cov_D3_exact Lester.Classical.gap_dist_sq Lester.Classical.gap_apx_dist Lester.Classical.gap_apx_cross Lester.Classical.gap_opp_of_cross_neg Lester.Classical.gap_same_of_cross_pos Lester.Classical.gap_ne_sq Lester.Classical.gap_apx_outer Lester.Classical.gap_apx_inner Lester.Classical.gap_concurrent Lester.Classical.gap_nondeg_alg Lester.Classical.gap_nondeg Lester.Classical.cov_D3_obligation Lester.Classical.cov_D3_obligation_exact"
SOURCES="Lester/*.lean Lester.lean"
# SCAFFOLD=1 (opt-in, proof stage not done): tolerate exactly one `sorry`, as the whole proof body of
# `theorem lester` in Lester/Basic.lean, and `sorryAx` in the axiom report of Lester.lester only.
# Default (unset) is the strict final gate.
SCAFFOLD="${SCAFFOLD:-0}"
if [ "$SCAFFOLD" = 1 ]; then
  [ "$(grep -cE "\\bsorry\\b" $SOURCES | awk -F: "{s+=\$NF} END{print s}")" -eq 1 ] || { echo "FAIL: scaffold must contain exactly one sorry"; exit 1; }
  awk "/^theorem lester /{f=1} f&&/:= by$/{getline; if(\$0==\"  sorry\") ok=1; exit} END{exit !ok}" Lester/Basic.lean || { echo "FAIL: scaffold sorry is not the body of theorem lester"; exit 1; }
fi
# Never fetch: the pinned Mathlib checkout must already be present.
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "$SCAFFOLD" = 1 ]; then SORRYRE=""; else SORRYRE="\\bsorry\\b|"; fi
if grep -nE "${SORRYRE}\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
# The `#print axioms` queries are generated here rather than read from a file in the repo.
# Portable (no GNU mktemp); the leading dot keeps it out of the SOURCES glob.
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ "$SCAFFOLD" = 1 ] && bad=$(printf "%s\n" "$reports" | grep "depends on axioms" | grep -v "^.Lester\.lester. " | sed "s/.*depends on axioms: *\\[//; s/\\].*//" | tr "," "\n" | sed "s/^ *//; s/ *$//" | grep -v "^$" | sort -u | grep -vE "^(propext|Classical\\.choice|Quot\\.sound)$"; printf "%s\n" "$reports" | grep "^.Lester\.lester. " | sed "s/.*\\[//; s/\\].*//" | tr "," "\n" | sed "s/^ *//; s/ *$//" | grep -v "^$" | grep -vE "^(propext|Classical\\.choice|Quot\\.sound|sorryAx)$")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
if [ "$SCAFFOLD" = 1 ]; then echo "PASS (SCAFFOLD: $n declarations; standard axioms only, plus sorryAx in Lester.lester)"; else echo "PASS ($n declarations, standard axioms only)"; fi
