/-
DecBridge.CubeDec -- omega is EXACTLY the chain-max of descents.
ChainDrops f x z d = "there is a cover-chain from x up to z whose f-word has
d descents". Results: chains are bounded by omega (chainDrops_le_omega);
omega is realized by an explicit chain witness (omega_attained); witness
chains obey the budget invariant; hence the peeled witness has
omega <= k - 1 everywhere (omega_hgen_le), and dec over any point list
follows (decPts machinery).
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import DecBridge.CubeViol

namespace DecBridge

/-- converse of mem_preds_of_covers. -/
theorem covers_of_mem_preds : ∀ {x p : List Bool}, p ∈ preds x → Covers p x
  | [], p, h => by cases h
  | b :: t, p, h => by
      rcases List.mem_append.mp h with hL | hR
      · cases b
        · simp at hL
        · simp at hL
          subst hL
          exact Covers.head t
      · rcases List.mem_map.mp hR with ⟨p', hp', rfl⟩
        exact Covers.tail b (covers_of_mem_preds hp')

/-- a fold-max is zero or attained at a member. -/
theorem foldr_max_attained {α : Type _} (g : α → Nat) :
    ∀ l : List α,
      l.foldr (fun q acc => Nat.max (g q) acc) 0 = 0 ∨
      ∃ p ∈ l, l.foldr (fun q acc => Nat.max (g q) acc) 0 = g p
  | [] => Or.inl rfl
  | a :: l => by
      rcases foldr_max_attained g l with h0 | ⟨p, hp, he⟩
      · right
        refine ⟨a, by simp, ?_⟩
        simp only [List.foldr]
        rw [h0]
        exact Nat.max_eq_left (Nat.zero_le _)
      · simp only [List.foldr]
        rw [he]
        rcases Nat.le_total (g a) (g p) with hle | hle
        · right; exact ⟨p, by simp [hp], Nat.max_eq_right hle⟩
        · right; exact ⟨a, by simp, Nat.max_eq_left hle⟩

/-- upward cover-chain from x to z with d descents of f. -/
inductive ChainDrops (f : List Bool → Bool) : List Bool → List Bool → Nat → Prop
  | base (z : List Bool) : ChainDrops f z z 0
  | step {x p z : List Bool} {d : Nat} :
      ChainDrops f x p d → Covers p z →
      ChainDrops f x z (d + (if f p && !(f z) then 1 else 0))

/-- every chain is bounded by omega at its top. -/
theorem chainDrops_le_omega (f : List Bool → Bool) {x z : List Bool} {d : Nat}
    (h : ChainDrops f x z d) : d ≤ omega f z := by
  induction h with
  | base => exact Nat.zero_le _
  | step hcd hc ih =>
      have he := omega_ge_entry (f := f) hc
      omega

/-- ★ omega is attained by an explicit chain witness. -/
theorem omega_attained (f : List Bool → Bool) (z : List Bool) :
    ∃ x, ChainDrops f x z (omega f z) := by
  suffices haux : ∀ n z, weight z ≤ n → ∃ x, ChainDrops f x z (omega f z) by
    exact haux (weight z) z (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro z hz
      have hw : weight z = 0 := Nat.le_zero.mp hz
      have h0 : omega f z = 0 := by unfold omega; rw [hw]; rfl
      rw [h0]
      exact ⟨z, .base z⟩
  | succ n ih =>
      intro z hz
      by_cases hle : weight z ≤ n
      · exact ih z hle
      · have hw : weight z = n + 1 := by omega
        have hunf : omega f z =
            (preds z).foldr
              (fun p acc => Nat.max (omegaF f n p + (if f p && !(f z) then 1 else 0)) acc) 0 := by
          unfold omega; rw [hw, omegaF_succ]
        rcases foldr_max_attained
            (fun p => omegaF f n p + (if f p && !(f z) then 1 else 0)) (preds z) with h0 | ⟨p, hp, he⟩
        · rw [hunf, h0]; exact ⟨z, .base z⟩
        · have hc := covers_of_mem_preds hp
          have hwp : weight p = n := by have := weight_covers hc; omega
          have hop : omegaF f n p = omega f p := by
            unfold omega; rw [hwp]
          obtain ⟨x, hcd⟩ := ih p (by omega)
          refine ⟨x, ?_⟩
          have heq : omega f z = omega f p + (if f p && !(f z) then 1 else 0) := by
            rw [hunf, he, hop]
          rw [heq]
          exact .step hcd hc

/-- hgen-chains obey the budget invariant (additive form). -/
theorem chainDrops_budget {f : List Bool → Bool} {w : List Bool → Nat} {k : Nat}
    (hp : DescPotential Covers f w) {x z : List Bool} {d : Nat}
    (h : ChainDrops (hgen f w k) x z d) : d + B f w k z ≤ B f w k x := by
  induction h with
  | base => omega
  | step hcd hc ih =>
      have hstep := hgen_step (k := k) hp hc
      omega

/-- ★ the peeled function's omega drops below K everywhere (global). -/
theorem omega_hgen_le (f : List Bool → Bool) (K : Nat) (z : List Bool) :
    omega (hgen f (omega f) K) z ≤ K - 1 := by
  obtain ⟨x, hcd⟩ := omega_attained (hgen f (omega f) K) z
  have hbud := chainDrops_budget (cube_descPotential f) hcd
  have hBx := B_le (f := f) (w := omega f) (k := K) x
  omega

/-- dec over an explicit list of points, via omega. -/
def decPts (pts : List (List Bool)) (f : List Bool → Bool) : Nat :=
  pts.foldr (fun z acc => Nat.max (omega f z) acc) 0

@[simp] theorem decPts_nil (f : List Bool → Bool) : decPts [] f = 0 := rfl
@[simp] theorem decPts_cons (z : List Bool) (pts : List (List Bool)) (f : List Bool → Bool) :
    decPts (z :: pts) f = Nat.max (omega f z) (decPts pts f) := rfl

theorem omega_le_decPts {pts : List (List Bool)} (f : List Bool → Bool)
    {z : List Bool} (hz : z ∈ pts) : omega f z ≤ decPts pts f :=
  le_foldr_max (fun z => omega f z) pts z hz

theorem decPts_le_of_all {pts : List (List Bool)} {f : List Bool → Bool} {k : Nat}
    (h : ∀ z ∈ pts, omega f z ≤ k) : decPts pts f ≤ k := by
  induction pts with
  | nil => simp
  | cons z pts ih =>
      rw [decPts_cons]
      exact Nat.max_le.mpr ⟨h z (by simp), ih (fun z' hm => h z' (by simp [hm]))⟩

/-- ★ dec of the peeled function over any point list is <= K - 1. -/
theorem decPts_hgen_le (pts : List (List Bool)) (f : List Bool → Bool) (K : Nat) :
    decPts pts (hgen f (omega f) K) ≤ K - 1 :=
  decPts_le_of_all (fun z _ => omega_hgen_le f K z)

end DecBridge
