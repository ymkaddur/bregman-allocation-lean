# bregman-allocation-lean

Machine-checked compact certificates of infeasible allocations, in Lean 4 with Mathlib.

Producers must be placed injectively on compatible slots. When no placement exists, the absence can be
certified by one small object instead of a search over all `n!` placements. The object is a Hall
violator `S` (fewer compatible slots than producers), or, for a square compatibility matrix, a zero
rectangle `R × C` with `|R| + |C| > n`. This repository proves both certificates sound and complete,
and provides Boolean checkers whose input is the certificate alone.

Every theorem is checked by the Lean kernel, with no `sorry`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Labels: **[L]** proved in Lean; **open** means stated but not
resolved here.

## Contents

| Module | Statement | Status |
|--------|-----------|--------|
| `HallCertificate` | a set `S` with `|⋃_{i∈S} adj i| < |S|` blocks every allocation (soundness) | [L] |
| | if no allocation exists, such a set exists (completeness, via Hall's theorem in Mathlib) | [L] |
| | exact characterization, and checker `checkViolator` with soundness and completeness | [L] |
| | instance: three producers on two slots, certified by `decide` | [L] |
| `ZeroRectangle` | rows `R`, columns `C` with `|R| + |C| > n` and `A = 0` on `R × C` block every perfect matching | [L] |
| | every matrix without a perfect matching has such a rectangle | [L] |
| | exact characterization, and checker `checkRectangle` with soundness | [L] |

Related machine-checked work, not duplicated here. The repository `open-goat/pequalnp-proofs`
contains Lean proofs of the permanent form of the zero-rectangle criterion, `per(A) = 0` iff such a
rectangle exists (lemma `L-lib-457`), and of Brégman's bound for 0/1 matrices,
`per(A)^(n!) ≤ ∏ (d_i!)^(n!/d_i)` (lemma `L-lib-460`).

Open questions:

- **open**: transferring Brégman's bound to an explicit upper bound on the number of feasible
  allocations, stated in the allocation language of this repository.
- **open**: minimum certificate size for capacitated allocations, where slots hold several producers
  (the deficiency version of Hall's theorem).

## Reproduce

```bash
lake exe cache get
lake build
scripts/audit.sh     # #print axioms for every theorem; fails on sorry, warnings or extra axioms
```

Pinned toolchain: `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`).

## License

MIT
