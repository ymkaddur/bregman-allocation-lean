# bregman-allocation-lean

Machine-checked compact certificates of infeasible allocations, with slot capacities, and the
bridge from permanent bounds to allocation counts, in Lean 4 with Mathlib.

Producers must be placed on compatible slots. A slot may take one producer or, in the capacitated
version, up to `c_j` producers. When no placement exists, the absence is certified by one small
object instead of a search over all placements:

- a Hall violator `S`, whose compatible slots have total capacity below `|S|`;
- or, for a square compatibility matrix, a zero rectangle `R × C` with `|R| + |C| > n`.

When placements exist, their number is a permanent, so permanent bounds such as Brégman's become
bounds on the number of feasible allocations.

Every theorem is checked by the Lean kernel, with no `sorry`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Labels:

- **[L]**: new theorem or construction proved in Lean.
- **[L-known]**: Lean formalization of a known result.
- **refuted**: counterexample proved in Lean.
- **open**: precise statement not resolved here.

## Contents

| Module | Statement | Status | Scope |
|--------|-----------|--------|-------|
| `HallCertificate` | a set `S` with `|⋃_{i∈S} adj i| < |S|` blocks every allocation, and such a set exists whenever no allocation does | [L-known] | Hall's theorem, from Mathlib; any producer type |
| | Boolean checker `checkViolator` (sound and complete) and a decided instance | [L-known] | — |
| `ZeroRectangle` | a zero rectangle with `|R| + |C| > n` exists **iff** there is no perfect matching (Frobenius–König), with a checker | [L-known] | square `0/1` matrices; derived here from Hall |
| `CapacitatedHall` | capacities `c_j`: `S` with `∑_{j∈N(S)} c_j < |S|` blocks every capacitated allocation (fiberwise counting) | [L-known] | any capacities, including 0 |
| | completeness: without a capacitated allocation, such an `S` exists | [L-known] | proved by replicating slot `j` into `c_j` copies and applying Mathlib's Hall |
| | exact characterization, checker `checkCapViolator`, decided instance | [L-known] | — |
| `AllocationCount` | the number of feasible perfect allocations equals the permanent of the `0/1` matrix | [L-known] | square relations |
| | at most `∏_i d_i` feasible allocations (degree product) | [L-known] | — |
| | **Brégman transfer**: any permanent bound, in particular `per^(n!) ≤ ∏ (d_i!)^(n!/d_i)`, bounds the number of allocations | [L] | the Brégman inequality is an explicit hypothesis here; it is proved in Lean in `open-goat/pequalnp-proofs`, lemma `L-lib-460` |
| | the complete `2 × 2` relation attains Brégman's value (2 allocations) | [L-known] | tightness instance |

Related machine-checked work, not duplicated here: `open-goat/pequalnp-proofs` proves the permanent
form of the zero-rectangle criterion (`L-lib-457`) and Brégman's bound for `0/1` matrices
(`L-lib-460`).

Open questions:

- **open**: Brégman-type upper bounds on the number of *capacitated* allocations. These are
  permanents of matrices with repeated columns; a sharp form is not stated here.
- **open**: minimum-size certificates for capacitated infeasibility. The violator found by the
  completeness proof can be large; whether a size bound below `|S|` holds is not addressed.

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
