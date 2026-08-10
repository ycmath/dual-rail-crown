/-
Wcy2.Transfer -- the resolved face and the absorbed recovery.
Mechanizes the paper's Prop 5.1/C.1 (plain restriction escapes on the mixed pairs)
and Prop 5.2/C.2 (with the designated re-entry data, the recovered operations
are exactly min and max on the two-point chain), plus C.4
(witness-independence at the resolved endpoints).
Core Lean 4 only; kernel proofs (finite, by cases); no native_decide; no sorry.
-/
import Wcy2.D4

namespace Wcy2

def FALd : D4 := (false, true)
def TRUd : D4 := (true, false)

/-- membership in the resolved face. -/
def inR (a : D4) : Prop := a = FALd ∨ a = TRUd

/-- ★ Prop C.1 (escape): on mixed resolved pairs the internal operations leave R. -/
theorem escape :
    meetk FALd TRUd = UNK ∧ meetk TRUd FALd = UNK ∧
    joink FALd TRUd = CON ∧ joink TRUd FALd = CON ∧
    meetk FALd FALd = FALd ∧ meetk TRUd TRUd = TRUd ∧
    joink FALd FALd = FALd ∧ joink TRUd TRUd = TRUd :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- designated re-entry data (rho_meet sends UNK to FAL; identity on R). -/
def rhoMeet (a : D4) : D4 := if a = UNK then FALd else a
/-- designated re-entry data (rho_join sends CON to TRU; identity on R). -/
def rhoJoin (a : D4) : D4 := if a = CON then TRUd else a

def meetR (a b : D4) : D4 := rhoMeet (meetk a b)
def joinR (a b : D4) : D4 := rhoJoin (joink a b)

/-- Boolean value of a resolved element (FAL = 0 < TRU = 1). -/
def rval (a : D4) : Bool := a.1

/-- ★ Prop C.2 (recovery): the absorbed operations are min and max on R. -/
theorem recovery (a b : D4) (ha : inR a) (hb : inR b) :
    rval (meetR a b) = (rval a && rval b) ∧
    rval (joinR a b) = (rval a || rval b) ∧
    inR (meetR a b) ∧ inR (joinR a b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    exact ⟨rfl, rfl, by first | exact Or.inl rfl | exact Or.inr rfl,
           by first | exact Or.inl rfl | exact Or.inr rfl⟩

/-- ★ Prop C.4 (witness-independence): any re-entry maps with the same endpoint
    values induce the same operations on R. -/
theorem reentry_independent
    (rm rj : D4 → D4)
    (hm1 : rm UNK = FALd) (hm2 : ∀ a, inR a → rm a = a)
    (hj1 : rj CON = TRUd) (hj2 : ∀ a, inR a → rj a = a)
    (a b : D4) (ha : inR a) (hb : inR b) :
    rm (meetk a b) = meetR a b ∧ rj (joink a b) = joinR a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨hm2 _ (Or.inl rfl), hj2 _ (Or.inl rfl)⟩
  · exact ⟨hm1, hj1⟩
  · exact ⟨hm1, hj1⟩
  · exact ⟨hm2 _ (Or.inr rfl), hj2 _ (Or.inr rfl)⟩

/-- on the resolved face, sigma_s and P restrict to the same flip. -/
theorem sigma_eq_P_on_R (a : D4) (ha : inR a) : sigd a = Pd a := by
  rcases ha with rfl | rfl <;> rfl

end Wcy2
