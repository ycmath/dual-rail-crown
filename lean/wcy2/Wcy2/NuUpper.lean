/-
Wcy2.NuUpper -- the nu upper bound:
  dec(f) <= K  ==>  some term with at most K sigmas computes f on the cube
  (for f nonconstant on the cube: the sigma-free fragment has no constants,
   so constant functions are carried through the induction as explicit
   degenerate cases).
Route: DecBridge.tower_of_decPts gives a K-rung nested tower member; each
rung is realized as a term --
  base rung  = monotone-DNF realization (minterm meet-terms joined; the
               empty-join / bottom-minterm edge cases are the two degenerate
               branches of Real3);
  peel rung  = the decomposition  g(y, !h(y)) = g(y,0) OR (g(y,1) AND !h(y))
               (monotone in each slot), consuming exactly one fresh sigma.
Real3 is the three-way realization predicate (== FAL / == TRU / term),
closed under join, meet, sigma, congruence, and bound weakening.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import Wcy2.NuLower

namespace Wcy2
open DecBridge

/-! ### minterm terms -/

/-- indices of the true coordinates. -/
def trues : List Bool → List Nat
  | [] => []
  | b :: t => (if b then [0] else []) ++ (trues t).map (· + 1)

@[simp] theorem trues_nil : trues [] = [] := rfl
@[simp] theorem trues_cons_false (t : List Bool) :
    trues (false :: t) = (trues t).map (· + 1) := rfl
@[simp] theorem trues_cons_true (t : List Bool) :
    trues (true :: t) = 0 :: (trues t).map (· + 1) := rfl

/-- meet of a nonempty variable list. -/
def bigAndV : Nat → List Nat → RTerm
  | i, [] => .var i
  | i, j :: js => .tmeet (.var i) (bigAndV j js)

theorem sigCount_bigAndV (i : Nat) (js : List Nat) : sigCount (bigAndV i js) = 0 := by
  induction js generalizing i with
  | nil => rfl
  | cons j js ih => simp [bigAndV, sigCount, ih]

theorem beval_bigAndV (i : Nat) (js : List Nat) (y : List Bool) :
    beval (bigAndV i js) y = ((i :: js).all fun j => y.getD j false) := by
  induction js generalizing i with
  | nil => simp [bigAndV, beval]
  | cons j js ih =>
      show (y.getD i false && beval (bigAndV j js) y) = _
      rw [ih]
      simp [List.all_cons, Bool.and_assoc]

/-- the minterm meet-term of a cube point (junk on the bottom point;
    only used when `trues x` is nonempty). -/
def mand (x : List Bool) : RTerm :=
  match trues x with
  | [] => .var 0
  | i :: js => bigAndV i js

theorem sigCount_mand (x : List Bool) : sigCount (mand x) = 0 := by
  unfold mand
  split
  · rfl
  · exact sigCount_bigAndV _ _

theorem beval_mand {x : List Bool} (h : trues x ≠ []) (y : List Bool) :
    beval (mand x) y = ((trues x).all fun j => y.getD j false) := by
  unfold mand
  split
  · next he => exact absurd he h
  · next i js he => rw [beval_bigAndV, he]

/-- lifting the all-check across one cons of the evaluation point. -/
theorem all_map_succ (b : Bool) (q : List Bool) :
    ∀ (l : List Nat), ((l.map (· + 1)).all fun j => (b :: q).getD j false)
      = (l.all fun j => q.getD j false)
  | [] => rfl
  | j :: l => by
      simp only [List.map_cons, List.all_cons, List.getD_cons_succ,
        all_map_succ b q l]

/-- ★ the minterm check computes the componentwise order (equal lengths). -/
theorem all_trues_eq_leCb : ∀ (x y : List Bool), x.length = y.length →
    ((trues x).all fun j => y.getD j false) = leCb x y
  | [], [], _ => rfl
  | [], _ :: _, hl => Nat.noConfusion hl
  | _ :: _, [], hl => Nat.noConfusion hl
  | a :: p, b :: q, hl => by
      have hl' : p.length = q.length := by simpa using hl
      have ih := all_trues_eq_leCb p q hl'
      cases a
      · rw [trues_cons_false, all_map_succ, ih]
        rfl
      · rw [trues_cons_true, List.all_cons, all_map_succ, ih,
          List.getD_cons_zero]
        rfl

/-- a point with no true coordinate sits below every point of its length. -/
theorem leC_of_trues_nil : ∀ {x y : List Bool}, trues x = [] →
    x.length = y.length → LeC x y
  | [], [], _, _ => trivial
  | [], _ :: _, _, hl => Nat.noConfusion hl
  | _ :: _, [], _, hl => Nat.noConfusion hl
  | a :: p, b :: q, h, hl => by
      cases a
      · rw [trues_cons_false] at h
        have hp : trues p = [] := by
          cases he : trues p
          · rfl
          · rw [he] at h
            simp at h
        exact ⟨fun h' => Bool.noConfusion h',
          leC_of_trues_nil hp (by simpa using hl)⟩
      · rw [trues_cons_true] at h
        cases h

/-- cover-monotone functions are Star-monotone. -/
theorem mono_star {m : List Bool → Bool}
    (hm : ∀ ⦃p x : List Bool⦄, Covers p x → m p = true → m x = true) :
    ∀ {x y : List Bool}, Star x y → m x = true → m y = true
  | _, _, .refl _ => id
  | _, _, .step hc hs => fun hx => mono_star hm hs (hm hc hx)

/-! ### the DNF join -/

/-- join of a nonempty minterm list. -/
def dnfT : List Bool → List (List Bool) → RTerm
  | x, [] => mand x
  | x, x' :: xs' => .tjoin (mand x) (dnfT x' xs')

theorem sigCount_dnfT : ∀ (x : List Bool) (xs : List (List Bool)),
    sigCount (dnfT x xs) = 0
  | x, [] => sigCount_mand x
  | x, x' :: xs' => by
      show sigCount (mand x) + sigCount (dnfT x' xs') = 0
      rw [sigCount_mand, sigCount_dnfT x' xs']

theorem beval_dnfT : ∀ (x : List Bool) (xs : List (List Bool)) (y : List Bool),
    beval (dnfT x xs) y = ((x :: xs).any fun x' => beval (mand x') y)
  | x, [], y => by simp [dnfT]
  | x, x' :: xs', y => by
      show (beval (mand x) y || beval (dnfT x' xs') y) = _
      rw [beval_dnfT x' xs' y]
      simp [List.any_cons]

/-! ### the three-way realization predicate -/

/-- three-way realization on pts with sigma budget K: constant-FAL,
    constant-TRU, or an honest term. -/
def Real3 (pts : List (List Bool)) (K : Nat) (f : List Bool → Bool) : Prop :=
  (∀ y ∈ pts, f y = false) ∨ (∀ y ∈ pts, f y = true) ∨
  (∃ t, sigCount t ≤ K ∧ ∀ y ∈ pts, beval t y = f y)

theorem Real3.monoK {pts : List (List Bool)} {K K' : Nat} {f : List Bool → Bool}
    (hK : K ≤ K') : Real3 pts K f → Real3 pts K' f
  | .inl h => .inl h
  | .inr (.inl h) => .inr (.inl h)
  | .inr (.inr ⟨t, ht, ha⟩) => .inr (.inr ⟨t, Nat.le_trans ht hK, ha⟩)

theorem Real3.congr {pts : List (List Bool)} {K : Nat} {f g : List Bool → Bool}
    (hfg : ∀ y ∈ pts, f y = g y) : Real3 pts K f → Real3 pts K g
  | .inl h => .inl fun y hy => (hfg y hy) ▸ h y hy
  | .inr (.inl h) => .inr (.inl fun y hy => (hfg y hy) ▸ h y hy)
  | .inr (.inr ⟨t, ht, ha⟩) =>
      .inr (.inr ⟨t, ht, fun y hy => (ha y hy).trans (hfg y hy)⟩)

theorem Real3.or {pts : List (List Bool)} {K1 K2 : Nat} {A B : List Bool → Bool}
    (hA : Real3 pts K1 A) (hB : Real3 pts K2 B) :
    Real3 pts (K1 + K2) (fun y => A y || B y) := by
  rcases hA with hA | hA | ⟨t0, ht0, ha0⟩
  · refine (hB.monoK (Nat.le_add_left _ _)).congr ?_
    intro y hy
    show B y = (A y || B y)
    rw [hA y hy]
    rfl
  · exact .inr (.inl fun y hy => by
      show (A y || B y) = true
      rw [hA y hy]
      rfl)
  · rcases hB with hB | hB | ⟨t1, ht1, ha1⟩
    · refine .inr (.inr ⟨t0, Nat.le_trans ht0 (Nat.le_add_right _ _),
        fun y hy => ?_⟩)
      show beval t0 y = (A y || B y)
      rw [hB y hy, Bool.or_false, ha0 y hy]
    · exact .inr (.inl fun y hy => by
        show (A y || B y) = true
        rw [hB y hy, Bool.or_true])
    · refine .inr (.inr ⟨.tjoin t0 t1, ?_, fun y hy => ?_⟩)
      · show sigCount t0 + sigCount t1 ≤ K1 + K2
        omega
      · show (beval t0 y || beval t1 y) = (A y || B y)
        rw [ha0 y hy, ha1 y hy]

theorem Real3.and {pts : List (List Bool)} {K1 K2 : Nat} {A B : List Bool → Bool}
    (hA : Real3 pts K1 A) (hB : Real3 pts K2 B) :
    Real3 pts (K1 + K2) (fun y => A y && B y) := by
  rcases hA with hA | hA | ⟨t0, ht0, ha0⟩
  · exact .inl fun y hy => by
      show (A y && B y) = false
      rw [hA y hy]
      rfl
  · refine (hB.monoK (Nat.le_add_left _ _)).congr ?_
    intro y hy
    show B y = (A y && B y)
    rw [hA y hy]
    rfl
  · rcases hB with hB | hB | ⟨t1, ht1, ha1⟩
    · exact .inl fun y hy => by
        show (A y && B y) = false
        rw [hB y hy, Bool.and_false]
    · refine .inr (.inr ⟨t0, Nat.le_trans ht0 (Nat.le_add_right _ _),
        fun y hy => ?_⟩)
      show beval t0 y = (A y && B y)
      rw [hB y hy, Bool.and_true, ha0 y hy]
    · refine .inr (.inr ⟨.tmeet t0 t1, ?_, fun y hy => ?_⟩)
      · show sigCount t0 + sigCount t1 ≤ K1 + K2
        omega
      · show (beval t0 y && beval t1 y) = (A y && B y)
        rw [ha0 y hy, ha1 y hy]

theorem Real3.not {pts : List (List Bool)} {K : Nat} {h : List Bool → Bool} :
    Real3 pts K h → Real3 pts (K + 1) (fun y => !(h y))
  | .inl hh => .inr (.inl fun y hy => by
      show (!(h y)) = true
      rw [hh y hy]
      rfl)
  | .inr (.inl hh) => .inl fun y hy => by
      show (!(h y)) = false
      rw [hh y hy]
      rfl
  | .inr (.inr ⟨t, ht, ha⟩) => .inr (.inr ⟨.tsig t,
      by show sigCount t + 1 ≤ K + 1; omega,
      fun y hy => by
        show (!(beval t y)) = (!(h y))
        rw [ha y hy]⟩)

/-! ### monotone-DNF realization (the base rung) -/

theorem ne_nil_of_isEmpty_false {l : List Nat} (h : l.isEmpty = false) :
    l ≠ [] := by
  cases l
  · cases h
  · intro h'
    cases h'

/-- ★ every cover-monotone function is three-way realized with zero sigmas
    (monotone DNF; the two degenerate branches absorb the missing constants). -/
theorem mono_realize (n : Nat) (pts : List (List Bool))
    (hlen : ∀ y ∈ pts, y.length = n)
    (m : List Bool → Bool)
    (hm : ∀ ⦃p x : List Bool⦄, Covers p x → m p = true → m x = true) :
    Real3 pts 0 m := by
  cases hmins : pts.filter (fun x => m x) with
  | nil =>
      refine .inl fun y hy => ?_
      cases hmy : m y
      · rfl
      · exfalso
        have : y ∈ pts.filter (fun x => m x) :=
          List.mem_filter.mpr ⟨hy, hmy⟩
        rw [hmins] at this
        cases this
  | cons x xs =>
      have hxmem : x ∈ pts.filter (fun x => m x) := by
        rw [hmins]; exact List.mem_cons_self ..
      obtain ⟨hxpts, hxm⟩ := List.mem_filter.mp hxmem
      cases hbot : (pts.filter (fun x => m x)).any
          (fun x' => (trues x').isEmpty) with
      | true =>
          -- a bottom minterm: m is constant TRU on pts
          obtain ⟨x', hx'mem, hx'bot⟩ := List.any_eq_true.mp hbot
          obtain ⟨hx'pts, hx'm⟩ := List.mem_filter.mp hx'mem
          have hx'nil : trues x' = [] := by
            cases he : trues x'
            · rfl
            · rw [he] at hx'bot
              cases hx'bot
          refine .inr (.inl fun y hy => ?_)
          have hle : LeC x' y := leC_of_trues_nil hx'nil
            ((hlen x' hx'pts).trans (hlen y hy).symm)
          exact mono_star hm (star_of_leC hle) hx'm
      | false =>
          -- honest DNF term over the minterm list
          have hne : ∀ x' ∈ pts.filter (fun x => m x), trues x' ≠ [] := by
            intro x' hx'
            cases he : (trues x').isEmpty
            · exact ne_nil_of_isEmpty_false he
            · exfalso
              have : (pts.filter (fun x => m x)).any
                  (fun x' => (trues x').isEmpty) = true :=
                List.any_eq_true.mpr ⟨x', hx', he⟩
              rw [hbot] at this
              cases this
          refine .inr (.inr ⟨dnfT x xs, ?_, ?_⟩)
          · rw [sigCount_dnfT]
            exact Nat.zero_le _
          · intro y hy
            rw [beval_dnfT]
            cases hmy : m y
            · -- no minterm can reach y
              cases hany : (x :: xs).any (fun x' => beval (mand x') y)
              · rfl
              · exfalso
                obtain ⟨x', hx'mem, hx'b⟩ := List.any_eq_true.mp hany
                have hx'filt : x' ∈ pts.filter (fun x => m x) := by
                  rw [hmins]; exact hx'mem
                obtain ⟨hx'pts, hx'm⟩ := List.mem_filter.mp hx'filt
                rw [beval_mand (hne x' hx'filt) y,
                  all_trues_eq_leCb x' y
                    ((hlen x' hx'pts).trans (hlen y hy).symm)] at hx'b
                have hle := leCb_iff.mp hx'b
                have := mono_star hm (star_of_leC hle) hx'm
                rw [hmy] at this
                cases this
            · -- y itself is a minterm
              have hyfilt : y ∈ pts.filter (fun x => m x) :=
                List.mem_filter.mpr ⟨hy, hmy⟩
              have hymem : y ∈ x :: xs := by rw [← hmins]; exact hyfilt
              refine List.any_eq_true.mpr ⟨y, hymem, ?_⟩
              rw [beval_mand (hne y hyfilt) y, all_trues_eq_leCb y y rfl]
              exact leCb_iff.mpr (LeC_refl y)

/-! ### tower-to-term assembly -/

/-- ★ every K-rung tower member is three-way realized with at most K sigmas:
    the base rung is monotone DNF, and each peel consumes exactly one sigma
    via  g(y, !h(y)) = g(y,0) OR (g(y,1) AND !h(y)). -/
theorem tower_realize (n : Nat) (pts : List (List Bool))
    (hlen : ∀ y ∈ pts, y.length = n)
    {f : List Bool → Bool} {K : Nat} (ht : Tower f K) : Real3 pts K f := by
  induction ht with
  | mono hm => exact mono_realize n pts hlen _ hm
  | lift ht ih => exact ih.monoK (Nat.le_succ _)
  | peel ht hg ih =>
      rename_i h g k
      have hm0 : ∀ ⦃p x : List Bool⦄, Covers p x →
          (fun y => g y false) p = true → (fun y => g y false) x = true :=
        fun p x hc hp => hg (covers_leC hc) (fun hv => hv) hp
      have hm1 : ∀ ⦃p x : List Bool⦄, Covers p x →
          (fun y => g y true) p = true → (fun y => g y true) x = true :=
        fun p x hc hp => hg (covers_leC hc) (fun hv => hv) hp
      have h01 : ∀ y, g y false = true → g y true = true :=
        fun y hy => hg (LeC_refl y) (fun _ => rfl) hy
      have hkey : ∀ y, (g y false || (g y true && !(h y))) = g y (!(h y)) := by
        intro y
        cases hh : h y
        · show (g y false || (g y true && true)) = g y true
          rw [Bool.and_true]
          cases hg0 : g y false
          · rfl
          · rw [h01 y hg0]
            rfl
        · show (g y false || (g y true && false)) = g y false
          rw [Bool.and_false, Bool.or_false]
      have hR : Real3 pts (0 + (0 + (k + 1)))
          (fun y => (fun y => g y false) y ||
            ((fun y => g y true) y && (fun y => !(h y)) y)) :=
        (mono_realize n pts hlen (fun y => g y false) hm0).or
          ((mono_realize n pts hlen (fun y => g y true) hm1).and ih.not)
      exact (hR.congr (fun y _ => hkey y)).monoK (by omega)

/-- ★ the nu upper bound on the cube: dec <= K and f nonconstant on the
    n-cube produce a term with at most K sigmas computing f there. -/
theorem nu_upper (n : Nat) (f : List Bool → Bool) (K : Nat)
    (hd : decPts (cube n) f ≤ K)
    (hT : ∃ y ∈ cube n, f y = true) (hF : ∃ y ∈ cube n, f y = false) :
    ∃ t, sigCount t ≤ K ∧ ∀ y ∈ cube n, beval t y = f y := by
  obtain ⟨f', hagree, htw⟩ := tower_of_decPts (cube n) K f hd
  have h3 : Real3 (cube n) K f' :=
    tower_realize n (cube n) (fun y hy => mem_cube.mp hy) htw
  rcases h3.congr hagree with hall | hall | ⟨t, ht, ha⟩
  · obtain ⟨y, hy, hyt⟩ := hT
    rw [hall y hy] at hyt
    cases hyt
  · obtain ⟨y, hy, hyf⟩ := hF
    rw [hall y hy] at hyf
    cases hyf
  · exact ⟨t, ht, ha⟩

end Wcy2
