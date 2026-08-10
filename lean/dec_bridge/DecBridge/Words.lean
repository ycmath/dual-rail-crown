/-
DecBridge.Words -- binary chain-words: drops (descents), rises (ascents), and
the alternation lemma  rises w <= drops w + 1.
Core Lean 4 only; no mathlib; kernel proofs.
-/
namespace DecBridge

/-- number of TRU->FAL descents along a word (adjacent steps). -/
def drops : List Bool → Nat
  | a :: b :: r => (if a && !b then 1 else 0) + drops (b :: r)
  | _ => 0

/-- number of FAL->TRU ascents along a word (adjacent steps). -/
def rises : List Bool → Nat
  | a :: b :: r => (if !a && b then 1 else 0) + rises (b :: r)
  | _ => 0

@[simp] theorem drops_nil : drops [] = 0 := rfl
@[simp] theorem drops_single (a : Bool) : drops [a] = 0 := rfl
@[simp] theorem drops_cons (a b : Bool) (r : List Bool) :
    drops (a :: b :: r) = (if a && !b then 1 else 0) + drops (b :: r) := rfl
@[simp] theorem rises_nil : rises [] = 0 := rfl
@[simp] theorem rises_single (a : Bool) : rises [a] = 0 := rfl
@[simp] theorem rises_cons (a b : Bool) (r : List Bool) :
    rises (a :: b :: r) = (if !a && b then 1 else 0) + rises (b :: r) := rfl

/-- a cons never has fewer ascents than its tail. -/
theorem rises_le_cons (a : Bool) (w : List Bool) : rises w ≤ rises (a :: w) := by
  cases w with
  | nil => simp
  | cons b r => rw [rises_cons]; exact Nat.le_add_left _ _

/-- Alternation (E.1 shape): ascents exceed descents by at most one, and a word
    starting at TRU has ascents <= descents. -/
theorem alternation :
    ∀ w : List Bool, rises w ≤ drops w + 1 ∧ (w.head? = some true → rises w ≤ drops w)
  | [] => ⟨by simp, by intro h; simp at h⟩
  | [a] => ⟨by simp, by intro _; simp⟩
  | a :: b :: r => by
      obtain ⟨ih1, ih2⟩ := alternation (b :: r)
      cases a <;> cases b
      case false.false =>
        refine ⟨?_, ?_⟩
        · simpa using ih1
        · intro h; simp at h
      case false.true =>
        have h2 := ih2 rfl
        refine ⟨?_, ?_⟩
        · simp; omega
        · intro h; simp at h
      case true.false =>
        refine ⟨?_, ?_⟩
        · simp; omega
        · intro _; simp; omega
      case true.true =>
        have h2 := ih2 rfl
        refine ⟨?_, ?_⟩
        · simp; omega
        · intro _; simp; omega

theorem rises_le_drops_succ (w : List Bool) : rises w ≤ drops w + 1 :=
  (alternation w).1

end DecBridge
