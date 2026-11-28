import ContextualPareto

namespace BudgetPins

variable {S T C : Type*} [AddCommMonoid C] [Preorder C] [IsOrderedAddMonoid C]

/-- Direct recursive specification. Every continuation has its own reserved budget. -/
def Fits (E : S → C → S → Prop) (f : S → C → Prop) : ℕ → S → C → Prop
  | 0, s, b => ∃ c, f s c ∧ c ≤ b
  | n+1, s, b => ∃ t c d, E s c t ∧ Fits E f n t d ∧ c+d ≤ b

theorem fits_iff {E : S → C → S → Prop} {f : S → C → Prop} (n : ℕ) (s : S) (b : C) :
    Fits E f n s b ↔ ContextualPareto.Within E f n s b := by
  induction n generalizing s b with
  | zero =>
    constructor
    · rintro ⟨c,h,hc⟩
      exact ⟨c,.stop h,hc⟩
    · rintro ⟨c,tr,hc⟩
      cases tr with
      | stop h => exact ⟨c,h,hc⟩
  | succ n ih =>
    constructor
    · rintro ⟨t,c,d,he,h,hle⟩
      obtain ⟨v,hv,hd⟩ := (ih t d).mp h
      exact ⟨_,.more he hv,(add_le_add le_rfl hd).trans hle⟩
    · rintro ⟨_,tr,hle⟩
      cases tr with
      | more he tail =>
        exact ⟨_,_,_,he,(ih _ _).mpr ⟨_,tail,le_rfl⟩,hle⟩

theorem cost_congruence {R : S → T → Prop} {E D f g}
    (forward : ContextualPareto.Sim (C := C) R E D f g)
    (backward : ContextualPareto.Sim (fun t s => R s t) D E g f)
    {s t} (hr : R s t) (n : ℕ) (b : C) : Fits E f n s b ↔ Fits D g n t b := by
  rw [fits_iff, fits_iff]
  exact ContextualPareto.budgets_iff forward backward hr n b

end BudgetPins
