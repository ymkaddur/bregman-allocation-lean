import Mathlib

/-!
# Capacitated allocations: Hall's condition with slot capacities

Slot `j` accepts up to `c j` producers. A capacitated allocation sends every producer to a compatible
slot without exceeding any capacity. The compact certificate of infeasibility is a set `S` of
producers whose compatible slots have total capacity below `|S|`.

* `no_cap_allocation_of_violator` (soundness): such an `S` blocks every capacitated allocation,
  by counting producers fiberwise;
* `exists_cap_violator` (completeness): without a capacitated allocation such an `S` exists. The
  proof replicates slot `j` into `c j` copies and applies Hall's theorem from Mathlib;
* `no_cap_allocation_iff`: the exact characterization, plus `checkCapViolator` with its soundness
  and a decided instance.
-/

namespace AllocationCertificates

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- A capacitated allocation: compatible slots, and at most `c j` producers on slot `j`. -/
def IsCapAllocation [Fintype ι] (adj : ι → Finset α) (c : α → ℕ) (f : ι → α) : Prop :=
  (∀ i, f i ∈ adj i) ∧ ∀ j, (univ.filter fun i => f i = j).card ≤ c j

/-- Soundness of the capacitated certificate. -/
theorem no_cap_allocation_of_violator [Fintype ι] (adj : ι → Finset α) (c : α → ℕ)
    (S : Finset ι) (hS : ∑ j ∈ S.biUnion adj, c j < S.card) :
    ∀ f, ¬ IsCapAllocation adj c f := by
  rintro f ⟨hf, hcap⟩
  have h1 : S.card = ∑ j ∈ S.biUnion adj, (S.filter fun i => f i = j).card :=
    card_eq_sum_card_fiberwise fun i hi => mem_biUnion.mpr ⟨i, hi, hf i⟩
  have h2 : ∑ j ∈ S.biUnion adj, (S.filter fun i => f i = j).card ≤ ∑ j ∈ S.biUnion adj, c j :=
    sum_le_sum fun j _ => (card_le_card (filter_subset_filter _ (subset_univ S))).trans (hcap j)
  omega

/-- Completeness by slot replication and Hall's theorem. -/
theorem exists_cap_violator [Fintype ι] (adj : ι → Finset α) (c : α → ℕ)
    (h : ∀ f, ¬ IsCapAllocation adj c f) : ∃ S : Finset ι, ∑ j ∈ S.biUnion adj, c j < S.card := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  -- slot `j` replicated into `c j` copies
  let adj' : ι → Finset (Σ j : α, Fin (c j)) := fun i => (adj i).sigma fun _ => univ
  have hHall : ∀ S : Finset ι, S.card ≤ (S.biUnion adj').card := by
    intro S
    have hU : S.biUnion adj' = (S.biUnion adj).sigma fun _ => univ := by
      ext ⟨j, k⟩
      simp [adj', mem_biUnion, mem_sigma]
    rw [hU, card_sigma]
    simpa using hcon S
  obtain ⟨f', hinj, hf'⟩ := (all_card_le_biUnion_card_iff_exists_injective adj').mp hHall
  apply h (fun i => (f' i).1)
  refine ⟨fun i => (mem_sigma.mp (hf' i)).1, fun j => ?_⟩
  -- the fiber over `j` injects into `Fin (c j)` through the copy index
  calc (univ.filter fun i => (f' i).1 = j).card ≤ (range (c j)).card := by
        apply card_le_card_of_injOn (fun i => ((f' i).2 : ℕ))
        · intro i hi
          have hij : (f' i).1 = j := (mem_filter.mp hi).2
          exact mem_range.mpr (lt_of_lt_of_eq (f' i).2.isLt (congrArg c hij))
        · intro i hi i' hi' hval
          have hij : (f' i).1 = j := (mem_filter.mp hi).2
          have hij' : (f' i').1 = j := (mem_filter.mp hi').2
          have h1 : (f' i).1 = (f' i').1 := hij.trans hij'.symm
          exact hinj (Sigma.ext h1 ((Fin.heq_ext_iff (congrArg c h1)).mpr hval))
    _ = c j := card_range _

/-- Exact characterization of capacitated feasibility. -/
theorem no_cap_allocation_iff [Fintype ι] (adj : ι → Finset α) (c : α → ℕ) :
    (∀ f, ¬ IsCapAllocation adj c f) ↔ ∃ S : Finset ι, ∑ j ∈ S.biUnion adj, c j < S.card :=
  ⟨exists_cap_violator adj c, fun ⟨S, hS⟩ => no_cap_allocation_of_violator adj c S hS⟩

/-- Boolean checker of a capacitated certificate. -/
def checkCapViolator (adj : ι → Finset α) (c : α → ℕ) (S : Finset ι) : Bool :=
  decide (∑ j ∈ S.biUnion adj, c j < S.card)

theorem checkCapViolator_sound [Fintype ι] (adj : ι → Finset α) (c : α → ℕ) (S : Finset ι)
    (h : checkCapViolator adj c S = true) : ∀ f, ¬ IsCapAllocation adj c f :=
  no_cap_allocation_of_violator adj c S (by simpa [checkCapViolator] using h)

/-- Instance: three producers that all fit only slot `0`, of capacity 2, cannot be allocated. -/
theorem three_on_capacity_two :
    ∀ f : Fin 3 → Fin 2, ¬ IsCapAllocation (fun _ => ({0} : Finset (Fin 2))) (fun _ => 2) f :=
  checkCapViolator_sound _ _ univ (by decide)

end AllocationCertificates
