/-
DecBridge.Cube -- the CONCRETE omega on the Boolean cube.
Cube points = List Bool; cover steps = flip one coordinate false -> true.
omega f x is defined constructively by weight-fuel recursion over lower
covers; it is a descent potential for the cover relation (mono + strict),
so the three-zone witness inherits its budget bound on every cover-chain.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import DecBridge.Hgen

namespace DecBridge

/-- lower-cover relation on cube points: flip exactly one true coordinate down. -/
inductive Covers : List Bool → List Bool → Prop
  | head (t : List Bool) : Covers (false :: t) (true :: t)
  | tail {p x : List Bool} (b : Bool) : Covers p x → Covers (b :: p) (b :: x)

/-- computable lower covers. -/
def preds : List Bool → List (List Bool)
  | [] => []
  | b :: t => (if b then [false :: t] else []) ++ (preds t).map (b :: ·)

/-- number of true coordinates. -/
def weight : List Bool → Nat
  | [] => 0
  | b :: t => (if b then 1 else 0) + weight t

/-- fuel-bounded descent potential over lower covers. -/
def omegaF (f : List Bool → Bool) : Nat → List Bool → Nat
  | 0, _ => 0
  | fuel+1, x =>
      (preds x).foldr
        (fun p acc => Nat.max (omegaF f fuel p + (if f p && !(f x) then 1 else 0)) acc) 0

/-- ★ the concrete omega: fuel = weight suffices (every strictly descending
    cover-path from x has length <= weight x). -/
def omega (f : List Bool → Bool) (x : List Bool) : Nat := omegaF f (weight x) x

theorem mem_preds_of_covers {p x : List Bool} (h : Covers p x) : p ∈ preds x := by
  induction h with
  | head t => simp [preds]
  | tail b hc ih =>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

theorem weight_covers {p x : List Bool} (h : Covers p x) : weight x = weight p + 1 := by
  induction h with
  | head t => simp [weight]; omega
  | tail b hc ih => cases b <;> simp [weight] <;> omega

/-- an entry is bounded by the fold-max. -/
theorem le_foldr_max {α : Type _} (g : α → Nat) :
    ∀ (l : List α) (p : α), p ∈ l → g p ≤ l.foldr (fun q acc => Nat.max (g q) acc) 0
  | [], p, hp => by cases hp
  | a :: l, p, hp => by
      rcases hp with _ | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_foldr_max g l p ‹p ∈ l›) (Nat.le_max_right _ _)

theorem omegaF_succ (f : List Bool → Bool) (fuel : Nat) (x : List Bool) :
    omegaF f (fuel+1) x =
      (preds x).foldr
        (fun p acc => Nat.max (omegaF f fuel p + (if f p && !(f x) then 1 else 0)) acc) 0 := rfl

/-- the p-entry of omega x dominates omega p (+1 on a descent). -/
theorem omega_ge_entry {f : List Bool → Bool} {p x : List Bool} (h : Covers p x) :
    omega f p + (if f p && !(f x) then 1 else 0) ≤ omega f x := by
  have hw := weight_covers h
  have hm := mem_preds_of_covers h
  have : omega f x =
      (preds x).foldr
        (fun q acc => Nat.max (omegaF f (weight p) q + (if f q && !(f x) then 1 else 0)) acc) 0 := by
    rw [omega, hw, omegaF_succ]
  rw [this]
  exact le_foldr_max (fun q => omegaF f (weight p) q + (if f q && !(f x) then 1 else 0))
    (preds x) p hm

/-- ★ the concrete cube omega IS a descent potential for Covers. -/
theorem cube_descPotential (f : List Bool → Bool) :
    DescPotential Covers f (omega f) := by
  constructor
  · intro p x h
    have := omega_ge_entry (f := f) h
    omega
  · intro p x h hfp hfx
    have := omega_ge_entry (f := f) h
    rw [hfp, hfx] at this
    have e : (if (true:Bool) && !(false:Bool) then (1:Nat) else 0) = 1 := rfl
    rw [e] at this
    omega

/-- ★ concrete h_gen dec bound on the cube: along every cover-chain,
    hgen f (omega f) k has at most k-1 descents. -/
theorem cube_hgen_drops_le (f : List Bool → Bool) (k : Nat)
    (xs : List (List Bool)) (hc : IsChain Covers xs) :
    drops (xs.map (hgen f (omega f) k)) ≤ k - 1 :=
  hgen_drops_le (cube_descPotential f) xs hc

/-- ★ concrete family version. -/
theorem cube_hgen_decOn_le (f : List Bool → Bool) (k : Nat)
    (CS : List (List (List Bool))) (hCS : ∀ C ∈ CS, IsChain Covers C) :
    decOn CS (hgen f (omega f) k) ≤ k - 1 :=
  hgen_decOn_le (cube_descPotential f) CS hCS

end DecBridge
