import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Positivity of a two-border transfer, including the constant-term test for strictness. -/
namespace RookTransfer
open Polynomial

noncomputable def corner (P : ℕ[X]) : ℕ[X] := (1+X)*P + X*(1+X)*derivative P

noncomputable def borderPair (P : ℕ[X]) : ℕ[X] :=
  corner (corner P) + ((1+X)*P + (1+X)^2*derivative P)

theorem corner_add (P Q : ℕ[X]) : corner (P+Q) = corner P + corner Q := by
  simp only [corner, map_add, mul_add]
  ring

theorem borderPair_add (P Q : ℕ[X]) : borderPair (P+Q) = borderPair P + borderPair Q := by
  simp only [borderPair, corner_add, map_add, mul_add]
  ring

theorem corner_zero (P : ℕ[X]) : (corner P).eval 0 = P.eval 0 := by
  simp [corner]

theorem constant_step (P : ℕ[X]) :
    (borderPair P).eval 0 = 2 * P.eval 0 + (derivative P).eval 0 := by
  simp [borderPair, corner_zero]
  ring

theorem strict_persists (P : ℕ[X]) (hp : 0 < P.eval 0) (n : ℕ) :
    0 < ((borderPair^[n]) P).eval 0 := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply', constant_step]
    omega

/-- This transfer certificate requires coefficientwise order at the base. -/
theorem strict_after_padding (A D : ℕ[X]) (h : 0 < D.eval 0) (n : ℕ) :
    ((borderPair^[n]) A).eval 0 < ((borderPair^[n]) (A+D)).eval 0 := by
  have hadd : (borderPair^[n]) (A+D) = (borderPair^[n]) A + (borderPair^[n]) D := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, borderPair_add]
  rw [hadd, eval_add]
  exact Nat.lt_add_of_pos_right (strict_persists D h n)

/-- An initial permanent advantage alone need not survive even one application. -/
theorem constant_only_fails :
    (3*X : ℕ[X]).eval 0 < (1 : ℕ[X]).eval 0 ∧
    (borderPair 1).eval 0 < (borderPair (3*X)).eval 0 := by
  norm_num [constant_step, derivative_mul]

end RookTransfer
