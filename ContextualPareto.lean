import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Cost simulations for feasibility under vector budgets and reusable setup costs. -/
namespace ContextualPareto

variable {S T C : Type*} [AddCommMonoid C] [Preorder C] [IsOrderedAddMonoid C]

/-- A witness with exactly n transitions, including its terminal charge. -/
inductive Trace (step : S → C → S → Prop) (finish : S → C → Prop) : ℕ → S → C → Prop
  | stop {s c} : finish s c → Trace step finish 0 s c
  | more {s c t n d} : step s c t → Trace step finish n t d → Trace step finish (n+1) s (c+d)

def Within (step : S → C → S → Prop) (finish : S → C → Prop) (n : ℕ) (s : S) (b : C) :=
  ∃ cost, Trace step finish n s cost ∧ cost ≤ b

/-- Successors can be matched by a cheaper move with a different action name. -/
structure Sim (R : S → T → Prop) (E : S → C → S → Prop) (D : T → C → T → Prop)
    (f : S → C → Prop) (g : T → C → Prop) : Prop where
  terminal : ∀ s t c, R s t → f s c → ∃ d, g t d ∧ d ≤ c
  move : ∀ s t c s', R s t → E s c s' → ∃ d t', D t d t' ∧ d ≤ c ∧ R s' t'

theorem lift_trace {R : S → T → Prop} {E D f g} (sim : Sim (C := C) R E D f g)
    {n s c} (tr : Trace E f n s c) {t} (h : R s t) :
    ∃ d, Trace D g n t d ∧ d ≤ c := by
  induction tr generalizing t with
  | stop hf =>
    obtain ⟨d,hd,hle⟩ := sim.terminal _ _ _ h hf
    exact ⟨d,.stop hd,hle⟩
  | more he _ ih =>
    obtain ⟨d,t',hd,hle,hr⟩ := sim.move _ _ _ _ h he
    obtain ⟨d',hw,hl⟩ := ih hr
    exact ⟨_,.more hd hw,add_le_add hle hl⟩

theorem budgets_iff {R : S → T → Prop} {E D f g} (ab : Sim (C := C) R E D f g)
    (ba : Sim (fun t s => R s t) D E g f) {s t} (hr : R s t) (n : ℕ) (b : C) :
    Within E f n s b ↔ Within D g n t b := by
  constructor
  · rintro ⟨_,tr,h⟩
    obtain ⟨d,hw,hc⟩ := lift_trace ab tr hr
    exact ⟨d,hw,hc.trans h⟩
  · rintro ⟨_,tr,h⟩
    obtain ⟨d,hw,hc⟩ := lift_trace ba tr hr
    exact ⟨d,hw,hc.trans h⟩

/-- Forgetting assets outside the future demand support preserves one-time charges. -/
theorem setup_charge {I : Type*} [DecidableEq I] (stored asked future : Finset I)
    (ha : asked ⊆ future) : asked \ (stored ∩ future) = asked \ stored := by
  ext i
  simp only [Finset.mem_sdiff,Finset.mem_inter]
  exact ⟨fun ⟨h,hn⟩ => ⟨h,fun hs => hn ⟨hs,ha h⟩⟩,
    fun ⟨h,hn⟩ => ⟨h,fun p => hn p.1⟩⟩

theorem setup_successor {I : Type*} [DecidableEq I] (stored asked future next : Finset I)
    (hn : next ⊆ future) :
    ((stored ∩ future) ∪ asked) ∩ next = (stored ∪ asked) ∩ next := by
  ext i
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨(⟨hs,_⟩ | ha),h⟩
    · exact ⟨Or.inl hs,h⟩
    · exact ⟨Or.inr ha,h⟩
  · rintro ⟨(hs | ha),h⟩
    · exact ⟨Or.inl ⟨hs,hn h⟩,h⟩
    · exact ⟨Or.inr ha,h⟩

theorem unsupported (a b : ℝ) (hb : 0 < b) :
    ¬ (2*a + 3*b ≤ 4*b ∧ 2*a + 3*b ≤ 4*a) := by
  rintro ⟨h,k⟩
  linarith

theorem middle_budget :
    ((2,3) : ℕ × ℕ) ≤ (2,3) ∧ ¬ ((0,4) : ℕ × ℕ) ≤ (2,3) ∧ ¬ ((4,0) : ℕ × ℕ) ≤ (2,3) := by decide

theorem observational_merge_loses_option :
    let read : Bool → Unit := fun _ => ()
    let price : Bool → ℕ := fun b => if b then 0 else 3
    read true = read false ∧ price true ≤ 0 ∧ ¬ price false ≤ 0 := by decide

end ContextualPareto
