/-
Wcy2.NuLower -- the nu lower bound:
  dec(f) <= sigma-count of ANY term computing f on the cube.
The engine is a trio of word-level subadditivity lemmas on ChainDrops:
  chainDrops_and : drops(f && g) <= drops f + drops g   (per chain)
  chainDrops_or  : drops(f || g) <= drops f + drops g   (per chain)
  chainDrops_not : drops(!f)     <= drops f + [f(top)]  (end-value-refined
                   alternation; the +1 absorbed only at a TRU top)
plus projection monotonicity (drops(var i) = 0), and congruence transport
(omega/decPts depend only on values at the fixed length).
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import Wcy2.RTerm
import DecBridge.Tower

namespace Wcy2
open DecBridge

/-! ### word-level subadditivity on chains -/

/-- ★ NEW: per-chain meet subadditivity — a descent of f && g at a cover step
    forces a descent of f or of g at that step. -/
theorem chainDrops_and {f g : List Bool → Bool} {x z : List Bool} {d : Nat}
    (h : ChainDrops (fun y => f y && g y) x z d) :
    ∃ df dg, ChainDrops f x z df ∧ ChainDrops g x z dg ∧ d ≤ df + dg := by
  induction h with
  | base => exact ⟨0, 0, .base _, .base _, Nat.zero_le _⟩
  | step hcd hc ih =>
      rename_i p z d
      obtain ⟨df, dg, hf, hg, hle⟩ := ih
      refine ⟨df + (if f p && !(f z) then 1 else 0),
              dg + (if g p && !(g z) then 1 else 0),
              .step hf hc, .step hg hc, ?_⟩
      cases hfp : f p <;> cases hgp : g p <;> cases hfz : f z <;> cases hgz : g z <;>
        simp <;> omega

/-- ★ NEW: per-chain join subadditivity (dual). -/
theorem chainDrops_or {f g : List Bool → Bool} {x z : List Bool} {d : Nat}
    (h : ChainDrops (fun y => f y || g y) x z d) :
    ∃ df dg, ChainDrops f x z df ∧ ChainDrops g x z dg ∧ d ≤ df + dg := by
  induction h with
  | base => exact ⟨0, 0, .base _, .base _, Nat.zero_le _⟩
  | step hcd hc ih =>
      rename_i p z d
      obtain ⟨df, dg, hf, hg, hle⟩ := ih
      refine ⟨df + (if f p && !(f z) then 1 else 0),
              dg + (if g p && !(g z) then 1 else 0),
              .step hf hc, .step hg hc, ?_⟩
      cases hfp : f p <;> cases hgp : g p <;> cases hfz : f z <;> cases hgz : g z <;>
        simp <;> omega

/-- ★ NEW: per-chain negation law, end-value refined — descents of !f are
    ascents of f, and ascents exceed descents by at most [f(top) = TRU]. -/
theorem chainDrops_not {f : List Bool → Bool} {x z : List Bool} {d : Nat}
    (h : ChainDrops (fun y => !(f y)) x z d) :
    ∃ df, ChainDrops f x z df ∧ d ≤ df + (if f z = true then 1 else 0) := by
  induction h with
  | base => exact ⟨0, .base _, Nat.zero_le _⟩
  | step hcd hc ih =>
      rename_i p z d
      obtain ⟨df, hf, hle⟩ := ih
      refine ⟨df + (if f p && !(f z) then 1 else 0), .step hf hc, ?_⟩
      cases hfp : f p <;> cases hfz : f z <;>
        (rw [hfp] at hle; simp at hle ⊢; try omega)

/-- projections are monotone along covers. -/
theorem getD_covers {p z : List Bool} (h : Covers p z) (i : Nat) :
    p.getD i false = true → z.getD i false = true := by
  induction h generalizing i with
  | head t =>
      cases i with
      | zero => intro h'; cases h'
      | succ i => exact fun h' => h'
  | tail b hc ih =>
      cases i with
      | zero => exact fun h' => h'
      | succ i => exact ih i

/-- projection words never descend. -/
theorem chainDrops_var {i : Nat} {x z : List Bool} {d : Nat}
    (h : ChainDrops (fun y => y.getD i false) x z d) : d = 0 := by
  induction h with
  | base => rfl
  | step hcd hc ih =>
      rename_i p z d
      show d + (if p.getD i false && !(z.getD i false) then 1 else 0) = 0
      cases hp : p.getD i false
      · simp [ih]
      · have hz := getD_covers hc i hp
        rw [hz]
        simp [ih]

/-- ★ the nu lower bound, per chain: every chain of a term's Boolean value
    has at most sigCount t descents. -/
theorem chainDrops_beval_le (t : RTerm) :
    ∀ {x z : List Bool} {d : Nat}, ChainDrops (beval t) x z d → d ≤ sigCount t := by
  induction t with
  | var i =>
      intro x z d h
      have h' : ChainDrops (fun y => y.getD i false) x z d := h
      rw [chainDrops_var h']
      exact Nat.le_refl _
  | tmeet t u iht ihu =>
      intro x z d h
      have h' : ChainDrops (fun y => beval t y && beval u y) x z d := h
      obtain ⟨df, dg, hf, hg, hle⟩ := chainDrops_and h'
      have h1 := iht hf
      have h2 := ihu hg
      show d ≤ sigCount t + sigCount u
      omega
  | tjoin t u iht ihu =>
      intro x z d h
      have h' : ChainDrops (fun y => beval t y || beval u y) x z d := h
      obtain ⟨df, dg, hf, hg, hle⟩ := chainDrops_or h'
      have h1 := iht hf
      have h2 := ihu hg
      show d ≤ sigCount t + sigCount u
      omega
  | tsig t iht =>
      intro x z d h
      have h' : ChainDrops (fun y => !(beval t y)) x z d := h
      obtain ⟨df, hf, hle⟩ := chainDrops_not h'
      have h1 := iht hf
      have h2 : (if beval t z = true then (1:Nat) else 0) ≤ 1 := by
        cases beval t z <;> simp
      show d ≤ sigCount t + 1
      omega

/-- omega of a term's value function is bounded by its sigma-count. -/
theorem omega_beval_le (t : RTerm) (z : List Bool) :
    omega (beval t) z ≤ sigCount t := by
  obtain ⟨x, h⟩ := omega_attained (beval t) z
  exact chainDrops_beval_le t h

/-! ### congruence transport at a fixed length -/

theorem covers_length {p x : List Bool} (h : Covers p x) : p.length = x.length := by
  induction h with
  | head t => rfl
  | tail b hc ih => simpa using ih

/-- chains live at a fixed length, so ChainDrops only sees values there. -/
theorem chainDrops_congr {n : Nat} {f g : List Bool → Bool}
    (hfg : ∀ y, y.length = n → f y = g y) :
    ∀ {x z : List Bool} {d : Nat}, ChainDrops f x z d → z.length = n →
      ChainDrops g x z d := by
  intro x z d h
  induction h with
  | base => exact fun _ => .base _
  | step hcd hc ih =>
      rename_i p z d
      intro hz
      have hp : p.length = n := by rw [covers_length hc]; exact hz
      have h1 := hfg p hp
      have h2 := hfg z hz
      rw [h1, h2]
      exact .step (ih hp) hc

/-- omega depends only on values at the point's length. -/
theorem omega_congr {n : Nat} {f g : List Bool → Bool}
    (hfg : ∀ y, y.length = n → f y = g y) {z : List Bool} (hz : z.length = n) :
    omega f z = omega g z := by
  apply Nat.le_antisymm
  · obtain ⟨x, h⟩ := omega_attained f z
    exact chainDrops_le_omega g (chainDrops_congr hfg h hz)
  · obtain ⟨x, h⟩ := omega_attained g z
    exact chainDrops_le_omega f
      (chainDrops_congr (fun y hy => (hfg y hy).symm) h hz)

/-- decPts depends only on values at the points' common length. -/
theorem decPts_congr {n : Nat} {f g : List Bool → Bool}
    (hfg : ∀ y, y.length = n → f y = g y) :
    ∀ {pts : List (List Bool)}, (∀ y ∈ pts, y.length = n) →
      decPts pts f = decPts pts g := by
  intro pts
  induction pts with
  | nil => intro _; rfl
  | cons z pts ih =>
      intro hlen
      rw [decPts_cons, decPts_cons,
        omega_congr hfg (hlen z (by simp)),
        ih (fun y hy => hlen y (by simp [hy]))]

/-! ### the cube -/

/-- all cube points of a given length. -/
def cube : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => ((cube n).map (false :: ·)) ++ ((cube n).map (true :: ·))

theorem mem_cube : ∀ {n : Nat} {y : List Bool}, y ∈ cube n ↔ y.length = n := by
  intro n
  induction n with
  | zero =>
      intro y
      constructor
      · intro h
        simp [cube] at h
        simp [h]
      · intro h
        have : y = [] := List.eq_nil_of_length_eq_zero h
        simp [cube, this]
  | succ n ih =>
      intro y
      constructor
      · intro h
        simp [cube] at h
        rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
          simp [ih.mp ht]
      · intro h
        cases y with
        | nil => exact Nat.noConfusion h
        | cons b t =>
            have ht : t.length = n := by simpa using h
            cases b
            · exact List.mem_append_left _ (List.mem_map.mpr ⟨t, ih.mpr ht, rfl⟩)
            · exact List.mem_append_right _ (List.mem_map.mpr ⟨t, ih.mpr ht, rfl⟩)

/-- ★ nu >= dec (Boolean cube statement): any term agreeing with f on the
    n-cube has sigma-count at least dec(f). -/
theorem dec_le_sigCount (n : Nat) (f : List Bool → Bool) (t : RTerm)
    (hagree : ∀ y ∈ cube n, beval t y = f y) :
    decPts (cube n) f ≤ sigCount t := by
  have hlen : ∀ y ∈ cube n, y.length = n := fun y hy => mem_cube.mp hy
  have hfg : ∀ y, y.length = n → beval t y = f y := fun y hy =>
    hagree y (mem_cube.mpr hy)
  rw [← decPts_congr hfg hlen]
  exact decPts_le_of_all (fun z _ => omega_beval_le t z)

end Wcy2
