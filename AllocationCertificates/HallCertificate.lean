import Mathlib

/-!
# Compact certificates of infeasible allocations: Hall violators

Producers `ι` must be placed injectively on slots `α`, each producer `i` only on its compatible
slots `adj i`. An allocation is an injective `f` with `f i ∈ adj i`.

* `no_allocation_of_violator` (soundness): a set `S` of producers whose compatible slots number
  fewer than `|S|` blocks every allocation;
* `exists_violator_of_no_allocation` (completeness): if no allocation exists, such a violator exists
  (Hall's theorem, from Mathlib);
* `no_allocation_iff`: the exact characterization;
* `checkViolator`, `checkViolator_sound`, `checkViolator_complete`: a Boolean checker whose input is
  the certificate `S` alone. Infeasibility is decided by checking one set instead of searching all
  injective maps.
-/

namespace AllocationCertificates

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- `f` is an allocation: injective and compatible with `adj`. -/
def IsAllocation (adj : ι → Finset α) (f : ι → α) : Prop :=
  Function.Injective f ∧ ∀ i, f i ∈ adj i

/-- Soundness: a Hall violator blocks every allocation. -/
theorem no_allocation_of_violator (adj : ι → Finset α) (S : Finset ι)
    (hS : (S.biUnion adj).card < S.card) : ∀ f, ¬ IsAllocation adj f := by
  rintro f ⟨hinj, hf⟩
  have hle : S.card ≤ (S.biUnion adj).card := by
    rw [← card_image_of_injective S hinj]
    apply card_le_card
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_biUnion.mpr ⟨i, hi, hf i⟩
  omega

/-- Completeness: if no allocation exists, some set of producers is a Hall violator. -/
theorem exists_violator_of_no_allocation (adj : ι → Finset α)
    (h : ∀ f, ¬ IsAllocation adj f) : ∃ S : Finset ι, (S.biUnion adj).card < S.card := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  obtain ⟨f, hinj, hf⟩ := (all_card_le_biUnion_card_iff_exists_injective adj).mp hcon
  exact h f ⟨hinj, hf⟩

/-- Exact characterization: no allocation iff a Hall violator exists. -/
theorem no_allocation_iff (adj : ι → Finset α) :
    (∀ f, ¬ IsAllocation adj f) ↔ ∃ S : Finset ι, (S.biUnion adj).card < S.card :=
  ⟨exists_violator_of_no_allocation adj, fun ⟨S, hS⟩ => no_allocation_of_violator adj S hS⟩

/-- Boolean checker of a proposed certificate. -/
def checkViolator (adj : ι → Finset α) (S : Finset ι) : Bool :=
  decide ((S.biUnion adj).card < S.card)

theorem checkViolator_sound (adj : ι → Finset α) (S : Finset ι)
    (h : checkViolator adj S = true) : ∀ f, ¬ IsAllocation adj f :=
  no_allocation_of_violator adj S (by simpa [checkViolator] using h)

/-- Every infeasible instance has a certificate accepted by the checker. -/
theorem checkViolator_complete (adj : ι → Finset α) (h : ∀ f, ¬ IsAllocation adj f) :
    ∃ S, checkViolator adj S = true := by
  obtain ⟨S, hS⟩ := exists_violator_of_no_allocation adj h
  exact ⟨S, by simpa [checkViolator] using hS⟩

/-- Instance: three producers that all fit only slots `0` and `1` cannot be allocated. The
certificate is the set of all three producers. -/
theorem three_on_two : ∀ f : Fin 3 → Fin 4, ¬ IsAllocation (fun _ => ({0, 1} : Finset (Fin 4))) f :=
  checkViolator_sound _ Finset.univ (by decide)

end AllocationCertificates
