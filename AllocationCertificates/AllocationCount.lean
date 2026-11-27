import Mathlib

/-!
# Counting feasible allocations: the permanent bridge and degree bounds

For a square compatibility relation `B` (producer `i` may take slot `j` iff `B i j`), the feasible
perfect allocations are the permutations `σ` with `B i (σ i)` for every `i`.

* `card_feasible_eq_permanent`: their number is the permanent of the transposed `0/1` matrix of `B`.
  This is the bridge that turns permanent bounds into allocation counts;
* `card_feasible_le_prod_degrees`: at most `∏_i d_i`, where `d_i` counts the slots compatible with
  producer `i`;
* `card_feasible_pow_le_of_bregman`: Brégman's bound in its `n!`-th power form, taken as an explicit
  hypothesis (it is proved in Lean elsewhere, see README), transfers verbatim to allocation counts;
* `tight_two`: the complete `2 × 2` relation has exactly `2 = ∏ (2!)^(1/2)` feasible allocations, so
  Brégman's bound is attained there.
-/

namespace AllocationCertificates

open Finset

variable {n : ℕ}

/-- The feasible perfect allocations of a square compatibility relation. -/
def feasible (B : Fin n → Fin n → Bool) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun σ => ∀ i, B i (σ i) = true

/-- The transposed `0/1` matrix of `B`, oriented for `Matrix.permanent`. -/
def indicatorMatrix (B : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℕ :=
  fun j i => if B i j = true then 1 else 0

/-- **Bridge**: the number of feasible allocations is a permanent. -/
theorem card_feasible_eq_permanent (B : Fin n → Fin n → Bool) :
    (feasible B).card = (indicatorMatrix B).permanent := by
  unfold Matrix.permanent indicatorMatrix feasible
  rw [card_filter]
  refine sum_congr rfl fun σ _ => ?_
  rw [prod_ite_zero]
  simp

/-- At most the product of the degrees. -/
theorem card_feasible_le_prod_degrees (B : Fin n → Fin n → Bool) :
    (feasible B).card ≤ ∏ i, (univ.filter fun j => B i j = true).card := by
  calc (feasible B).card
      ≤ (Fintype.piFinset fun i => univ.filter fun j => B i j = true).card := by
        refine card_le_card_of_injOn (fun σ : Equiv.Perm (Fin n) => (⇑σ : Fin n → Fin n)) ?_ ?_
        · intro σ hσ
          simpa [feasible, Fintype.mem_piFinset] using hσ
        · intro σ _ τ _ h
          exact Equiv.ext (congrFun h)
    _ = ∏ i, (univ.filter fun j => B i j = true).card := Fintype.card_piFinset _

/-- **Brégman transfer**: any bound on the permanent of a `0/1` matrix, in particular Brégman's
`per(A)^(n!) ≤ ∏ (d_i!)^(n!/d_i)`, is a bound on the number of feasible allocations. -/
theorem card_feasible_pow_le_of_bregman (B : Fin n → Fin n → Bool) (bound : ℕ)
    (hBregman : (indicatorMatrix B).permanent ^ n.factorial ≤ bound) :
    (feasible B).card ^ n.factorial ≤ bound := by
  rw [card_feasible_eq_permanent]; exact hBregman

/-- Tight instance: the complete `2 × 2` relation has exactly `2` feasible allocations, which equals
Brégman's value `∏_i (d_i!)^(1/d_i) = (2!)^(1/2) (2!)^(1/2) = 2`. In `n!`-th power form both sides
are `4`. -/
theorem tight_two :
    (feasible (fun (_ _ : Fin 2) => true)).card = 2 ∧
      (feasible (fun (_ _ : Fin 2) => true)).card ^ (Nat.factorial 2) =
        ∏ _i : Fin 2, (Nat.factorial 2) ^ (Nat.factorial 2 / 2) := by
  have h : (feasible (fun (_ _ : Fin 2) => true)).card = 2 := by
    simp [feasible, Fintype.card_perm]
  refine ⟨h, ?_⟩
  rw [h]
  decide

end AllocationCertificates
