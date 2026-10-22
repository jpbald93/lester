# Lester's circle theorem in Lean 4

Lester's theorem: for a scalene triangle, the circumcentre, the nine-point centre and the two Fermat points are concyclic.

This repository is one of eight Lean 4 developments accompanying the paper *Circle configurations in
classical plane geometry, formalized in Lean 4: Clifford's chain, Miquel's five circles, Lester,
Sawayama–Thébault and Kosnita* (J. Bald, 2026). The paper states each theorem in prose with every
hypothesis, lists the degenerate configurations each statement excludes, and reports the verification
summarised below.

**Status:** all statements proved, no `sorry`. `gate.sh` checks **75** named declarations.

## Main statements

| Lean name | File:line | Statement |
|---|---|---|
| `Lester.lester` | `Lester/Basic.lean:56` | the theorem (scalene triangle; Fermat points assumed, not constructed) |
| `Lester.bridge_ninePointCenter` | `Lester/Bridge.lean:90` | the nine-point centre is the centre of Mathlib's nine-point circle |
| `Lester.bridge_apexOut` | `Lester/Bridge.lean:44` | the outward apexes are equilateral |
| `Lester.bridge_apexIn` | `Lester/Bridge.lean:60` | the inward apexes are equilateral |

Read the Lean statement for the exact hypotheses; the paper lists them in prose.

## Verification

`./gate.sh` builds the library and runs `#print axioms` on the 75 declarations in its `REQUIRED`
list. It fails if a source file contains `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
`set_option`, a macro or syntax extension; if the build fails; or if any listed declaration depends on
anything other than `propext`, `Classical.choice` and `Quot.sound`.

Expected output: `PASS (75 declarations, standard axioms only)`. Checked on x86-64 Linux and arm64
macOS at the pinned Mathlib revision.

`bash tests/tamper.sh` plants defects in scratch copies (ax2line, brokenbridge, evalfake, macro, sorry, wrap) and checks that the gate
rejects each one.

The paper also reports a statement-level battery (conclusion mutations, contradiction probe,
satisfiability witnesses, hypothesis ablation, unused-variable linter), an independent numerical
re-check, and a prior-art search. Those results, and their limits, are in the paper's Verification
section.

## Layers 14 and 15

`Lester/L14.lean` restates the main results using only Mathlib vocabulary, proves each restatement from the
library, and gives concrete witnesses showing that the hypotheses can be satisfied (21 declarations).
`Lester/L15Classical.lean` reproduces verbatim the classical statements of the paper's theorems as written
independently, from textbook statements, by an AI model that did not see this code, and proves them, or
parts of them, from this development (35 declarations). The writer's Lester theorem (D3), with Fermat points defined by the side conditions on the equilateral apices, and its construction obligation (both Fermat points exist) are proved exactly as stated (`cov_D3_exact`, `cov_D3_obligation_exact`). No writer statement was shown false.
All of these declarations are in `REQUIRED`.

## Build

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # if Lean is not installed
lake exe cache get
lake build
./gate.sh
bash tests/tamper.sh
```

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1` (revision pinned in `lake-manifest.json`). `gate.sh` never
fetches: run `lake exe cache get` first.

## Note on how this was produced

The formal proofs and documentation were developed with the help of a large-language-model AI
assistant. The author directed the work, reviewed the statements, and is responsible for the result.
The Lean kernel checks every proof.

## License

Code: Apache License 2.0 (see `LICENSE`). Documentation: CC BY 4.0.
