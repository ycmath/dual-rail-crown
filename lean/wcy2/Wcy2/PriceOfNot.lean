/-
Wcy2.PriceOfNot -- the exact equality nu = dec, D4 edition.
Boolean cube statement (nu_eq_dec_bool): for f nonconstant on the n-cube,
  - some term with EXACTLY dec(f) sigmas computes f on the cube, and
  - every term computing f on the cube has at least dec(f) sigmas.
D4 statement (nu_eq_dec_D4): the same, with terms evaluated by the absorbed
recovery-face operations meetR/joinR and sigma on resolved inputs -- the
Morizumi-type formula-exact law, four-valued edition (Theorem 5.3 of the paper).
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import Wcy2.NuUpper

namespace Wcy2
open DecBridge

/-- ★ nu = dec, Boolean cube edition (exact equality, nonconstant f). -/
theorem nu_eq_dec_bool (n : Nat) (f : List Bool → Bool)
    (hT : ∃ y ∈ cube n, f y = true) (hF : ∃ y ∈ cube n, f y = false) :
    (∃ t, sigCount t = decPts (cube n) f ∧ ∀ y ∈ cube n, beval t y = f y) ∧
    (∀ t, (∀ y ∈ cube n, beval t y = f y) → decPts (cube n) f ≤ sigCount t) := by
  constructor
  · obtain ⟨t, ht, ha⟩ :=
      nu_upper n f (decPts (cube n) f) (Nat.le_refl _) hT hF
    exact ⟨t, Nat.le_antisymm ht (dec_le_sigCount n f t ha), ha⟩
  · exact fun t ha => dec_le_sigCount n f t ha

/-- ★ nu = dec, D4 edition: terms are evaluated on the resolved face by the
    absorbed operations; agreement is stated in D4. -/
theorem nu_eq_dec_D4 (n : Nat) (f : List Bool → Bool)
    (hT : ∃ y ∈ cube n, f y = true) (hF : ∃ y ∈ cube n, f y = false) :
    (∃ t, sigCount t = decPts (cube n) f ∧
      ∀ y ∈ cube n, deval t (envOf y) = boolToR (f y)) ∧
    (∀ t, (∀ y ∈ cube n, deval t (envOf y) = boolToR (f y)) →
      decPts (cube n) f ≤ sigCount t) := by
  obtain ⟨⟨t, he, ha⟩, hlow⟩ := nu_eq_dec_bool n f hT hF
  constructor
  · exact ⟨t, he, fun y hy => by rw [deval_envOf, ha y hy]⟩
  · intro t ha
    refine hlow t (fun y hy => boolToR_inj ?_)
    rw [← deval_envOf]
    exact ha y hy

/-! ### non-vacuity smoke tests (kernel rfl, tiny instances) -/

/-- NOT on the 1-cube has dec = 1 (so nu = 1 by the theorem). -/
example : decPts (cube 1) (fun y => !(y.getD 0 false)) = 1 := rfl

/-- a monotone function on the 2-cube has dec = 0. -/
example : decPts (cube 2) (fun y => y.getD 0 false && y.getD 1 false) = 0 := rfl

/-- one negation inside a monotone context on the 2-cube: dec = 1. -/
example : decPts (cube 2)
    (fun y => y.getD 1 false || !(y.getD 0 false)) = 1 := rfl

end Wcy2
