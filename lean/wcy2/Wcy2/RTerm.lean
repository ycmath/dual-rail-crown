/-
Wcy2.RTerm -- the recovery-face term language.
Terms over {meet_R, join_R, sigma} with projections; sigma-count nu;
dual semantics: D4 (via the absorbed operations meetR/joinR and sigd)
and Boolean (via the rail value).  The correspondence theorem says the
two agree on resolved inputs, so the D4 statement of nu = dec reduces
to the Boolean cube statement.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import Wcy2.Transfer

namespace Wcy2

/-- recovery-face terms: projections, absorbed meet/join, and sigma. -/
inductive RTerm : Type
  | var (i : Nat)
  | tmeet (t u : RTerm)
  | tjoin (t u : RTerm)
  | tsig (t : RTerm)

/-- the sigma-count (negation cost) of a term. -/
def sigCount : RTerm → Nat
  | .var _ => 0
  | .tmeet t u => sigCount t + sigCount u
  | .tjoin t u => sigCount t + sigCount u
  | .tsig t => sigCount t + 1

/-- Boolean (rail-value) semantics over cube points. -/
def beval : RTerm → List Bool → Bool
  | .var i, y => y.getD i false
  | .tmeet t u, y => beval t y && beval u y
  | .tjoin t u, y => beval t y || beval u y
  | .tsig t, y => !(beval t y)

/-- D4 semantics: absorbed operations on the resolved face, plus sigma. -/
def deval : RTerm → (Nat → D4) → D4
  | .var i, env => env i
  | .tmeet t u, env => meetR (deval t env) (deval u env)
  | .tjoin t u, env => joinR (deval t env) (deval u env)
  | .tsig t, env => sigd (deval t env)

/-- embed a Boolean into the resolved face. -/
def boolToR (b : Bool) : D4 := if b then TRUd else FALd

theorem boolToR_inR (b : Bool) : inR (boolToR b) := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem boolToR_inj {a b : Bool} (h : boolToR a = boolToR b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- resolved closure: on resolved inputs every term evaluates inside R. -/
theorem deval_inR (t : RTerm) (env : Nat → D4) (henv : ∀ i, inR (env i)) :
    inR (deval t env) := by
  induction t with
  | var i => exact henv i
  | tmeet t u iht ihu => exact (recovery _ _ iht ihu).2.2.1
  | tjoin t u iht ihu => exact (recovery _ _ iht ihu).2.2.2
  | tsig t iht =>
      show inR (sigd (deval t env))
      rcases iht with h | h <;> rw [h]
      · exact Or.inr rfl
      · exact Or.inl rfl

/-- the cube environment induced by a cube point. -/
def envOf (y : List Bool) : Nat → D4 := fun i => boolToR (y.getD i false)

/-- ★ correspondence: D4 semantics on resolved cube inputs = Boolean semantics. -/
theorem deval_envOf (t : RTerm) (y : List Bool) :
    deval t (envOf y) = boolToR (beval t y) := by
  induction t with
  | var i => rfl
  | tmeet t u iht ihu =>
      show meetR (deval t (envOf y)) (deval u (envOf y)) =
        boolToR (beval t y && beval u y)
      rw [iht, ihu]
      cases beval t y <;> cases beval u y <;> rfl
  | tjoin t u iht ihu =>
      show joinR (deval t (envOf y)) (deval u (envOf y)) =
        boolToR (beval t y || beval u y)
      rw [iht, ihu]
      cases beval t y <;> cases beval u y <;> rfl
  | tsig t iht =>
      show sigd (deval t (envOf y)) = boolToR (!(beval t y))
      rw [iht]
      cases beval t y <;> rfl

end Wcy2
