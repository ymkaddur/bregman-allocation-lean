import Mathlib

/-!
# Zero-rectangle certificates for square compatibility matrices (Frobenius–König form)

For a square `0/1` compatibility matrix `A` (rows = producers, columns = slots), a perfect matching is
an injective `f` with `A i (f i) = 1` for all `i`.

* `no_matching_of_zero_rectangle` (soundness): rows `R` and columns `C` with `|R| + |C| > n` and
  `A = 0` on `R × C` block every perfect matching;
* `zero_rectangle_of_no_matching` (completeness): every matrix without a perfect matching has such a
  rectangle;
* `no_matching_iff`: the exact characterization, and `checkRectangle` with its soundness.

The certificate is two index sets, checkable with `|R| · |C|` entry reads. The permanent form of this
criterion and Brégman's bound on the number of perfect matchings are formalized elsewhere (see
README). This module derives the allocation form directly from Hall's theorem in Mathlib.
-/

namespace AllocationCertificates

open Finset

variable {n : ℕ}

/-- The compatible slots of row `i`. -/
def nbr (A : Fin n → Fin n → Bool) (i : Fin n) : Finset (Fin n) := univ.filter fun j => A i j = true

/-- Soundness: a zero rectangle with `|R| + |C| > n` blocks every perfect matching. -/
theorem no_matching_of_zero_rectangle (A : Fin n → Fin n → Bool) (R C : Finset (Fin n))
    (hRC : n < R.card + C.card) (hz : ∀ i ∈ R, ∀ j ∈ C, A i j = false) :
    ∀ f : Fin n → Fin n, Function.Injective f → ¬ ∀ i, A i (f i) = true := by
  intro f hinj hf
  have hsub : R.biUnion (nbr A) ⊆ univ \ C := by
    intro j hj
    obtain ⟨i, hi, hj'⟩ := mem_biUnion.mp hj
    simp only [nbr, mem_filter, mem_univ, true_and] at hj'
    simp only [mem_sdiff, mem_univ, true_and]
    intro hjC
    have h0 := hz i hi j hjC
    simp [hj'] at h0
  have h1 := card_le_card hsub
  rw [card_sdiff_of_subset (subset_univ C), card_univ, Fintype.card_fin] at h1
  have hinjR : R.card ≤ (R.biUnion (nbr A)).card := by
    rw [← card_image_of_injective R hinj]
    apply card_le_card
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_biUnion.mpr ⟨i, hi, by simp [nbr, hf i]⟩
  have hC : C.card ≤ n := by simpa using card_le_univ C
  omega

/-- Completeness: without a perfect matching there is a zero rectangle with `|R| + |C| > n`. -/
theorem zero_rectangle_of_no_matching (A : Fin n → Fin n → Bool)
    (h : ∀ f : Fin n → Fin n, Function.Injective f → ¬ ∀ i, A i (f i) = true) :
    ∃ R C : Finset (Fin n), n < R.card + C.card ∧ ∀ i ∈ R, ∀ j ∈ C, A i j = false := by
  have hno : ∀ f : Fin n → Fin n, ¬ (Function.Injective f ∧ ∀ i, f i ∈ nbr A i) := by
    rintro f ⟨hinj, hf⟩
    exact h f hinj fun i => by simpa [nbr] using hf i
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), (S.biUnion (nbr A)).card < S.card := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    obtain ⟨f, hinj, hf⟩ := (all_card_le_biUnion_card_iff_exists_injective (nbr A)).mp hcon
    exact hno f ⟨hinj, hf⟩
  refine ⟨S, univ \ S.biUnion (nbr A), ?_, ?_⟩
  · rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have hN : (S.biUnion (nbr A)).card ≤ n := by simpa using card_le_univ (S.biUnion (nbr A))
    omega
  · intro i hi j hj
    simp only [mem_sdiff, mem_univ, true_and, mem_biUnion, not_exists, not_and] at hj
    have hji := hj i hi
    simp only [nbr, mem_filter, mem_univ, true_and] at hji
    simpa using hji

/-- Exact characterization by zero rectangles. -/
theorem no_matching_iff (A : Fin n → Fin n → Bool) :
    (∀ f : Fin n → Fin n, Function.Injective f → ¬ ∀ i, A i (f i) = true) ↔
      ∃ R C : Finset (Fin n), n < R.card + C.card ∧ ∀ i ∈ R, ∀ j ∈ C, A i j = false :=
  ⟨zero_rectangle_of_no_matching A, fun ⟨R, C, hRC, hz⟩ => no_matching_of_zero_rectangle A R C hRC hz⟩

/-- Boolean checker of a rectangle certificate. -/
def checkRectangle (A : Fin n → Fin n → Bool) (R C : Finset (Fin n)) : Bool :=
  decide (n < R.card + C.card ∧ ∀ i ∈ R, ∀ j ∈ C, A i j = false)

theorem checkRectangle_sound (A : Fin n → Fin n → Bool) (R C : Finset (Fin n))
    (h : checkRectangle A R C = true) :
    ∀ f : Fin n → Fin n, Function.Injective f → ¬ ∀ i, A i (f i) = true := by
  simp only [checkRectangle, decide_eq_true_eq] at h
  exact no_matching_of_zero_rectangle A R C h.1 h.2

end AllocationCertificates
