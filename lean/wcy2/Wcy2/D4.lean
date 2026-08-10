/-
Wcy2.D4 -- the dual-rail lattice, the closed core, and the confinement breaker.
Mechanizes the paper's Theorem 2.1 (closed-core soundness: every term over
{meet_k, join_k, P} is knowledge-monotone, endpoint-preserving, and
P-equivariant) by structural induction over a term syntax, and Theorem 3.1
(sigma_s facts) by kernel decide.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/

namespace Wcy2

abbrev D4 := Bool × Bool

def meetk (a b : D4) : D4 := (a.1 && b.1, a.2 && b.2)
def joink (a b : D4) : D4 := (a.1 || b.1, a.2 || b.2)
def Pd (a : D4) : D4 := (a.2, a.1)
def sigd (a : D4) : D4 := (!a.1, !a.2)

def UNK : D4 := (false, false)
def CON : D4 := (true, true)

/-- knowledge order (componentwise). -/
def leK (a b : D4) : Prop := (a.1 = true → b.1 = true) ∧ (a.2 = true → b.2 = true)

/-- carrier terms over the closed core {meet_k, join_k, P} (no sigma). -/
inductive CTerm (n : Nat) : Type
  | proj (i : Fin n) : CTerm n
  | tmeet (t u : CTerm n) : CTerm n
  | tjoin (t u : CTerm n) : CTerm n
  | tP (t : CTerm n) : CTerm n

def ceval {n : Nat} : CTerm n → (Fin n → D4) → D4
  | .proj i, x => x i
  | .tmeet t u, x => meetk (ceval t x) (ceval u x)
  | .tjoin t u, x => joink (ceval t x) (ceval u x)
  | .tP t, x => Pd (ceval t x)

theorem leK_meetk {a b a' b' : D4} (h1 : leK a a') (h2 : leK b b') :
    leK (meetk a b) (meetk a' b') := by
  constructor
  · intro h
    simp [meetk] at h ⊢
    exact ⟨h1.1 h.1, h2.1 h.2⟩
  · intro h
    simp [meetk] at h ⊢
    exact ⟨h1.2 h.1, h2.2 h.2⟩

theorem leK_joink {a b a' b' : D4} (h1 : leK a a') (h2 : leK b b') :
    leK (joink a b) (joink a' b') := by
  constructor
  · intro h
    simp [joink] at h ⊢
    rcases h with h | h
    · exact Or.inl (h1.1 h)
    · exact Or.inr (h2.1 h)
  · intro h
    simp [joink] at h ⊢
    rcases h with h | h
    · exact Or.inl (h1.2 h)
    · exact Or.inr (h2.2 h)

theorem leK_Pd {a b : D4} (h : leK a b) : leK (Pd a) (Pd b) :=
  ⟨h.2, h.1⟩

/-- ★ Theorem 2.1(i): every closed-core term is knowledge-monotone. -/
theorem cterm_monotone {n : Nat} (t : CTerm n) {x y : Fin n → D4}
    (h : ∀ i, leK (x i) (y i)) : leK (ceval t x) (ceval t y) := by
  induction t with
  | proj i => exact h i
  | tmeet t u iht ihu => exact leK_meetk iht ihu
  | tjoin t u iht ihu => exact leK_joink iht ihu
  | tP t iht => exact leK_Pd iht

/-- ★ Theorem 2.1(ii): endpoint preservation (UNK and CON). -/
theorem cterm_endpoints {n : Nat} (t : CTerm n) :
    ceval t (fun _ => UNK) = UNK ∧ ceval t (fun _ => CON) = CON := by
  induction t with
  | proj i => exact ⟨rfl, rfl⟩
  | tmeet t u iht ihu =>
      constructor
      · show meetk (ceval t _) (ceval u _) = UNK
        rw [iht.1, ihu.1]; rfl
      · show meetk (ceval t _) (ceval u _) = CON
        rw [iht.2, ihu.2]; rfl
  | tjoin t u iht ihu =>
      constructor
      · show joink (ceval t _) (ceval u _) = UNK
        rw [iht.1, ihu.1]; rfl
      · show joink (ceval t _) (ceval u _) = CON
        rw [iht.2, ihu.2]; rfl
  | tP t iht =>
      constructor
      · show Pd (ceval t _) = UNK
        rw [iht.1]; rfl
      · show Pd (ceval t _) = CON
        rw [iht.2]; rfl

theorem Pd_meetk (a b : D4) : Pd (meetk a b) = meetk (Pd a) (Pd b) := rfl
theorem Pd_joink (a b : D4) : Pd (joink a b) = joink (Pd a) (Pd b) := rfl

/-- ★ Theorem 2.1(iii): P-equivariance of every closed-core term. -/
theorem cterm_equivariant {n : Nat} (t : CTerm n) (x : Fin n → D4) :
    ceval t (fun i => Pd (x i)) = Pd (ceval t x) := by
  induction t with
  | proj i => rfl
  | tmeet t u iht ihu =>
      show meetk (ceval t _) (ceval u _) = Pd (meetk _ _)
      rw [iht, ihu, Pd_meetk]
  | tjoin t u iht ihu =>
      show joink (ceval t _) (ceval u _) = Pd (joink _ _)
      rw [iht, ihu, Pd_joink]
  | tP t iht =>
      show Pd (ceval t _) = Pd (Pd (ceval t x))
      rw [iht]

/-- ★ Theorem 3.1: sigma_s is an involution, commutes with P, breaks both
    endpoints, and is not knowledge-monotone (kernel decide). -/
theorem sigd_invol (a : D4) : sigd (sigd a) = a := by
  cases a with
  | mk x y => cases x <;> cases y <;> rfl

theorem sigd_Pd (a : D4) : sigd (Pd a) = Pd (sigd a) := rfl

theorem sigd_breaks_endpoints : sigd UNK ≠ UNK ∧ sigd CON ≠ CON := by
  constructor <;> intro h <;> cases h

/-- ★ Theorem 3.1: sigma_s is an involution, commutes with P, breaks both
    endpoints, and is not knowledge-monotone. -/
theorem sigma_not_monotone :
    ¬ (∀ a b : D4, leK a b → leK (sigd a) (sigd b)) := by
  intro h
  have h1 : leK UNK CON := ⟨fun _ => rfl, fun _ => rfl⟩
  have h2 := h UNK CON h1
  have h3 : (sigd UNK).1 = true := rfl
  have h4 := h2.1 h3
  cases h4

end Wcy2
