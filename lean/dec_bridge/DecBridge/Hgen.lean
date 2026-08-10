/-
DecBridge.Hgen -- the three-zone witness
  hgen f w k x = 1 (k <= w x) | not (f x) (1 <= w x <= k-1) | 0 (w x = 0)
over an ABSTRACT descent potential w (mono along chain steps; strictly
increasing across descents of f). Results: covering of violated pairs, and
the budget bound: along ANY R-chain, drops of hgen <= k-1 (invariant B).
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import DecBridge.Words
import DecBridge.Subadd

namespace DecBridge

variable {X : Type _}

/-- the unified nested-peel witness (paper: 1 on omega>=k, not-f on mid, 0 low). -/
def hgen (f : X → Bool) (w : X → Nat) (k : Nat) (x : X) : Bool :=
  if k ≤ w x then true
  else if 1 ≤ w x then !(f x)
  else false

/-- abstract descent potential (the concrete cube omega satisfies this). -/
structure DescPotential (R : X → X → Prop) (f : X → Bool) (w : X → Nat) : Prop where
  mono : ∀ ⦃x y⦄, R x y → w x ≤ w y
  strict : ∀ ⦃x y⦄, R x y → f x = true → f y = false → w x < w y

theorem hgen_T {f : X → Bool} {w : X → Nat} {k : Nat} {x : X} (h : k ≤ w x) :
    hgen f w k x = true := by rw [hgen, if_pos h]
theorem hgen_M {f : X → Bool} {w : X → Nat} {k : Nat} {x : X}
    (h1 : ¬ k ≤ w x) (h2 : 1 ≤ w x) : hgen f w k x = !(f x) := by
  rw [hgen, if_neg h1, if_pos h2]
theorem hgen_Z {f : X → Bool} {w : X → Nat} {k : Nat} {x : X}
    (h1 : ¬ k ≤ w x) (h2 : ¬ 1 ≤ w x) : hgen f w k x = false := by
  rw [hgen, if_neg h1, if_neg h2]

/-- ★ covering: a violated pair (f x = TRU below, f y = FAL above) with the
    pair-local omega facts is covered by hgen. -/
theorem hgen_covering {f : X → Bool} {w : X → Nat} {k : Nat} {x y : X}
    (hk : 1 ≤ k) (hwx : w x ≤ k - 1) (hfx : f x = true)
    (hwy : 1 ≤ w y) (hfy : f y = false) :
    hgen f w k x = false ∧ hgen f w k y = true := by
  constructor
  · have h1 : ¬ k ≤ w x := by omega
    by_cases h2 : 1 ≤ w x
    · rw [hgen_M h1 h2, hfx]; rfl
    · exact hgen_Z h1 h2
  · by_cases h1 : k ≤ w y
    · exact hgen_T h1
    · rw [hgen_M h1 hwy, hfy]; rfl

/-- drop budget: remaining hgen-descents from a point (the induction invariant). -/
def B (f : X → Bool) (w : X → Nat) (k : Nat) (x : X) : Nat :=
  if k ≤ w x then 0
  else if 1 ≤ w x then (k - 1 - w x) + (if f x = false then 1 else 0)
  else k - 1

theorem B_T {f : X → Bool} {w : X → Nat} {k : Nat} {x : X} (h : k ≤ w x) :
    B f w k x = 0 := by rw [B, if_pos h]
theorem B_M {f : X → Bool} {w : X → Nat} {k : Nat} {x : X}
    (h1 : ¬ k ≤ w x) (h2 : 1 ≤ w x) :
    B f w k x = (k - 1 - w x) + (if f x = false then 1 else 0) := by
  rw [B, if_neg h1, if_pos h2]
theorem B_Z {f : X → Bool} {w : X → Nat} {k : Nat} {x : X}
    (h1 : ¬ k ≤ w x) (h2 : ¬ 1 ≤ w x) : B f w k x = k - 1 := by
  rw [B, if_neg h1, if_neg h2]

theorem B_le {f : X → Bool} {w : X → Nat} {k : Nat} (x : X) :
    B f w k x ≤ k - 1 := by
  by_cases h1 : k ≤ w x
  · rw [B_T h1]; omega
  · by_cases h2 : 1 ≤ w x
    · rw [B_M h1 h2]
      cases hfx : f x <;> simp <;> omega
    · rw [B_Z h1 h2]; omega

/-- per-step budget inequality: one chain step pays for any hgen-descent. -/
theorem hgen_step {R : X → X → Prop} {f : X → Bool} {w : X → Nat} {k : Nat}
    (hp : DescPotential R f w) {x y : X} (hR : R x y) :
    (if hgen f w k x && !(hgen f w k y) then 1 else 0) + B f w k y ≤ B f w k x := by
  have hm := hp.mono hR
  by_cases hTx : k ≤ w x
  · have hTy : k ≤ w y := Nat.le_trans hTx hm
    rw [hgen_T hTx, hgen_T hTy, B_T hTx, B_T hTy]
    simp
  · by_cases hMx : 1 ≤ w x
    · rw [hgen_M hTx hMx, B_M hTx hMx]
      by_cases hTy : k ≤ w y
      · rw [hgen_T hTy, B_T hTy]
        cases hfx : f x <;> simp <;> omega
      · have hMy : 1 ≤ w y := Nat.le_trans hMx hm
        rw [hgen_M hTy hMy, B_M hTy hMy]
        cases hfx : f x
        · cases hfy : f y
          · simp; omega
          · simp; omega
        · cases hfy : f y
          · have hs := hp.strict hR hfx hfy
            simp; omega
          · simp; omega
    · rw [hgen_Z hTx hMx, B_Z hTx hMx]
      simp
      exact B_le y

/-- chain lemma with the budget invariant. -/
theorem hgen_drops_le_B {R : X → X → Prop} {f : X → Bool} {w : X → Nat} {k : Nat}
    (hp : DescPotential R f w) :
    ∀ xs : List X, IsChain R xs →
      drops (xs.map (hgen f w k)) ≤ (match xs with | [] => 0 | x :: _ => B f w k x)
  | [], _ => by simp
  | [x], _ => by simp
  | x :: y :: r, hc => by
      have ih := hgen_drops_le_B (k := k) hp (y :: r) hc.2
      have hstep := hgen_step (k := k) hp hc.1
      simp only [List.map_cons] at ih ⊢
      rw [drops_cons]
      omega

/-- ★ h_gen dec bound, per chain: along any R-chain, hgen has at most k-1 descents. -/
theorem hgen_drops_le {R : X → X → Prop} {f : X → Bool} {w : X → Nat} {k : Nat}
    (hp : DescPotential R f w) (xs : List X) (hc : IsChain R xs) :
    drops (xs.map (hgen f w k)) ≤ k - 1 := by
  cases xs with
  | nil => simp
  | cons x rest =>
      have hthis : drops ((x :: rest).map (hgen f w k)) ≤ B f w k x :=
        hgen_drops_le_B (k := k) hp (x :: rest) hc
      have hB := B_le (f := f) (w := w) (k := k) x
      omega

/-- ★ h_gen dec bound over any finite chain family. -/
theorem hgen_decOn_le {R : X → X → Prop} {f : X → Bool} {w : X → Nat} {k : Nat}
    (hp : DescPotential R f w) (CS : List (List X)) (hCS : ∀ C ∈ CS, IsChain R C) :
    decOn CS (hgen f w k) ≤ k - 1 := by
  induction CS with
  | nil => simp
  | cons C CS ih =>
      rw [decOn_cons]
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · exact hgen_drops_le hp C (hCS C (by simp))
      · exact ih (fun C' hm => hCS C' (by simp [hm]))

end DecBridge
