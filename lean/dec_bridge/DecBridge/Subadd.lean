/-
DecBridge.Subadd -- subadditivity of the descent count: for any relation R,
any R-chain xs, monotone g and arbitrary h,
  drops (xs.map fun x => g x (not (h x))) <= drops (xs.map h) + 1.
Steps: (1) drop-transfer (a descent of f forces an ascent of h at the same
step, by monotonicity of g); (2) alternation (Words.lean). The dec-level
corollary is taken over an explicit finite family of chains (decOn).
Core Lean 4 only; kernel proofs.
-/
import DecBridge.Words

namespace DecBridge

variable {X : Type _}

/-- adjacent-step chain for an arbitrary relation R (no order axioms needed). -/
def IsChain (R : X → X → Prop) : List X → Prop
  | x :: y :: r => R x y ∧ IsChain R (y :: r)
  | _ => True

@[simp] theorem isChain_nil (R : X → X → Prop) : IsChain R [] := trivial
@[simp] theorem isChain_single (R : X → X → Prop) (x : X) : IsChain R [x] := trivial
@[simp] theorem isChain_cons (R : X → X → Prop) (x y : X) (r : List X) :
    IsChain R (x :: y :: r) ↔ R x y ∧ IsChain R (y :: r) := Iff.rfl

/-- boolean implication as Prop. -/
def Bimp (u v : Bool) : Prop := u = true → v = true

/-- g monotone in the pair (chain step, boolean input). -/
def BMono (R : X → X → Prop) (g : X → Bool → Bool) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ ⦃u v : Bool⦄, Bimp u v → Bimp (g x u) (g y v)

/-- Step 1 (drop transfer): a descent of f = g(x, not h x) across an R-step
    forces an ascent of h at that step. -/
theorem drop_transfer {R : X → X → Prop} {g : X → Bool → Bool} {h : X → Bool}
    (hg : BMono R g) {x y : X} (hR : R x y)
    (hfx : g x (!(h x)) = true) (hfy : g y (!(h y)) = false) :
    h x = false ∧ h y = true := by
  cases hx : h x <;> cases hy : h y
  case false.true => exact ⟨rfl, rfl⟩
  case false.false =>
    have himp : Bimp (!(h x)) (!(h y)) := by
      rw [hx, hy]; intro hu; exact hu
    have := hg hR himp hfx
    cases hfy ▸ this
  case true.false =>
    have himp : Bimp (!(h x)) (!(h y)) := by
      rw [hx, hy]; intro hu; cases hu
    have := hg hR himp hfx
    cases hfy ▸ this
  case true.true =>
    have himp : Bimp (!(h x)) (!(h y)) := by
      rw [hx, hy]; intro hu; cases hu
    have := hg hR himp hfx
    cases hfy ▸ this

/-- descents of f along a chain are at most ascents of h along it. -/
theorem drops_f_le_rises_h {R : X → X → Prop} {g : X → Bool → Bool} {h : X → Bool}
    (hg : BMono R g) :
    ∀ xs : List X, IsChain R xs →
      drops (xs.map fun x => g x (!(h x))) ≤ rises (xs.map h)
  | [], _ => by simp
  | [x], _ => by simp
  | x :: y :: r, hc => by
      have hR : R x y := hc.1
      have ih := drops_f_le_rises_h (h := h) hg (y :: r) hc.2
      simp only [List.map_cons] at ih ⊢
      rw [drops_cons, rises_cons]
      cases hfx : g x (!(h x)) <;> cases hfy : g y (!(h y)) <;> rw [hfy] at ih
      case true.false =>
        obtain ⟨hx, hy⟩ := drop_transfer hg hR hfx hfy
        rw [hy] at ih
        rw [hx, hy]
        have e1 : (if (true:Bool) && !(false:Bool) then (1:Nat) else 0) = 1 := rfl
        have e2 : (if !(false:Bool) && (true:Bool) then (1:Nat) else 0) = 1 := rfl
        rw [e1, e2]
        omega
      case false.false =>
        have e1 : (if (false:Bool) && !(false:Bool) then (1:Nat) else 0) = 0 := rfl
        rw [e1]
        omega
      case false.true =>
        have e1 : (if (false:Bool) && !(true:Bool) then (1:Nat) else 0) = 0 := rfl
        rw [e1]
        omega
      case true.true =>
        have e1 : (if (true:Bool) && !(true:Bool) then (1:Nat) else 0) = 0 := rfl
        rw [e1]
        omega

/-- ★ L1-c, per-chain form (all n, any relation): one adjoined twist raises the
    descent count of a chain by at most one. -/
theorem subadd_chain {R : X → X → Prop} {g : X → Bool → Bool} {h : X → Bool}
    (hg : BMono R g) (xs : List X) (hc : IsChain R xs) :
    drops (xs.map fun x => g x (!(h x))) ≤ drops (xs.map h) + 1 :=
  Nat.le_trans (drops_f_le_rises_h hg xs hc) (rises_le_drops_succ (xs.map h))

/-- dec over an explicit finite family of chains. -/
def decOn (CS : List (List X)) (f : X → Bool) : Nat :=
  CS.foldr (fun C acc => Nat.max (drops (C.map f)) acc) 0

@[simp] theorem decOn_nil (f : X → Bool) : decOn ([] : List (List X)) f = 0 := rfl
@[simp] theorem decOn_cons (C : List X) (CS : List (List X)) (f : X → Bool) :
    decOn (C :: CS) f = Nat.max (drops (C.map f)) (decOn CS f) := rfl

/-- ★ L1-c, dec-level corollary: over any finite chain family (e.g. all maximal
    chains of R^n), dec(g(x, not h)) <= dec(h) + 1. -/
theorem subadd_decOn {R : X → X → Prop} {g : X → Bool → Bool} {h : X → Bool}
    (hg : BMono R g) (CS : List (List X)) (hCS : ∀ C ∈ CS, IsChain R C) :
    decOn CS (fun x => g x (!(h x))) ≤ decOn CS h + 1 := by
  induction CS with
  | nil => simp
  | cons C CS ih =>
      have hC : IsChain R C := hCS C (by simp)
      have hrest : ∀ C' ∈ CS, IsChain R C' :=
        fun C' hm => hCS C' (by simp [hm])
      have h1 : drops (C.map fun x => g x (!(h x))) ≤ decOn (C :: CS) h + 1 := by
        have := subadd_chain (h := h) hg C hC
        have hmax : drops (C.map h) ≤ decOn (C :: CS) h := by
          rw [decOn_cons]; exact Nat.le_max_left _ _
        omega
      have h2 : decOn CS (fun x => g x (!(h x))) ≤ decOn (C :: CS) h + 1 := by
        have := ih hrest
        have hmax : decOn CS h ≤ decOn (C :: CS) h := by
          rw [decOn_cons]; exact Nat.le_max_right _ _
        omega
      rw [decOn_cons]
      exact Nat.max_le.mpr ⟨h1, h2⟩

end DecBridge
