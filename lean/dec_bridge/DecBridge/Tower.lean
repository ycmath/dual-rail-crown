/-
DecBridge.Tower -- the nested negation tower, assembled.
  Tower f K       : f is built from a cover-monotone base by K nested
                    "monotone-context + one fresh negation" peels.
  gExt            : an EXPLICIT monotone-extension witness (any-based; no
                    choice axiom).
  tower_of_decPts : UPPER: decPts pts f <= K  =>  some f agreeing with it on
                    pts lies in the K-th rung (constructive).
  F1_lower        : LOWER: Tower f K  =>  omega f z <= K for every z, via the
                    end-value-refined alternation invariant on chains.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import DecBridge.CubeDec

namespace DecBridge

theorem LeC_refl : ∀ x : List Bool, LeC x x
  | [] => trivial
  | _ :: t => ⟨fun h => h, LeC_refl t⟩

theorem LeC_trans : ∀ {x y z : List Bool}, LeC x y → LeC y z → LeC x z
  | [], [], [], _, _ => trivial
  | a :: p, b :: q, c :: r, h1, h2 => by
      have h1a : a = true → b = true := h1.1
      have h1b : LeC p q := h1.2
      have h2a : b = true → c = true := h2.1
      have h2b : LeC q r := h2.2
      exact ⟨fun ha => h2a (h1a ha), LeC_trans h1b h2b⟩
  | [], [], _ :: _, _, h2 => h2.elim
  | [], _ :: _, _, h1, _ => h1.elim
  | _ :: _, [], _, h1, _ => h1.elim
  | _ :: _, _ :: _, [], _, h2 => h2.elim

theorem covers_leC : ∀ {p x : List Bool}, Covers p x → LeC p x
  | _, _, .head t => ⟨fun h => (nomatch h), LeC_refl t⟩
  | _, _, .tail _ hc => ⟨fun h => h, covers_leC hc⟩

/-- boolean test for LeC. -/
def leCb : List Bool → List Bool → Bool
  | [], [] => true
  | a :: p, b :: q => (!a || b) && leCb p q
  | _, _ => false

theorem leCb_iff : ∀ {x y : List Bool}, leCb x y = true ↔ LeC x y
  | [], [] => by simp [leCb, LeC]
  | a :: p, b :: q => by
      have ih := leCb_iff (x := p) (y := q)
      cases a <;> cases b <;> simp [leCb, LeC, ih]
  | [], _ :: _ => by simp [leCb, LeC]
  | _ :: _, [] => by simp [leCb, LeC]

/-- explicit monotone-context witness: g(y, v) = 1 iff some x in pts with
    x <= y, (not h x -> v), f x = 1. -/
def gExt (pts : List (List Bool)) (f h : List Bool → Bool)
    (y : List Bool) (v : Bool) : Bool :=
  pts.any fun x => leCb x y && (h x || v) && f x

/-- gExt is monotone in the (point, bool) pair. -/
theorem gExt_mono (pts : List (List Bool)) (f h : List Bool → Bool)
    {y y' : List Bool} (hle : LeC y y') {v v' : Bool} (hv : v = true → v' = true)
    (hg : gExt pts f h y v = true) : gExt pts f h y' v' = true := by
  rcases List.any_eq_true.mp hg with ⟨x, hxm, hx⟩
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨hxle, hxor⟩, hxf⟩ := hx
  refine List.any_eq_true.mpr ⟨x, hxm, ?_⟩
  have hle' : leCb x y' = true := leCb_iff.mpr (LeC_trans (leCb_iff.mp hxle) hle)
  have hor' : (h x || v') = true := by
    cases hh : h x
    · rw [hh] at hxor
      have hvv : v = true := by simpa using hxor
      rw [hv hvv]
      rfl
    · rfl
  rw [hle', hor', hxf]
  rfl

/-- gExt reproduces f at pts-points, given covering of all violated pts-pairs. -/
theorem gExt_agrees (pts : List (List Bool)) (f h : List Bool → Bool)
    (hcov : ∀ x ∈ pts, ∀ y ∈ pts, LeC x y → f x = true → f y = false →
      h x = false ∧ h y = true)
    {y : List Bool} (hy : y ∈ pts) :
    gExt pts f h y (!(h y)) = f y := by
  cases hfy : f y
  · -- f y = false: no witness can exist
    cases hany : gExt pts f h y (!(h y))
    · rfl
    · exfalso
      rcases List.any_eq_true.mp hany with ⟨x, hxm, hx⟩
      simp only [Bool.and_eq_true] at hx
      obtain ⟨⟨hxle, hxor⟩, hxf⟩ := hx
      obtain ⟨hhx, hhy⟩ := hcov x hxm y hy (leCb_iff.mp hxle) hxf hfy
      rw [hhx, hhy] at hxor
      cases hxor
  · -- f y = true: y itself is a witness
    refine List.any_eq_true.mpr ⟨y, hy, ?_⟩
    have h1 : leCb y y = true := leCb_iff.mpr (LeC_refl y)
    have h2 : (h y || !(h y)) = true := by cases h y <;> rfl
    rw [h1, h2, hfy]
    rfl

/-- monotone hull (for the dec = 0 base). -/
def mExt (pts : List (List Bool)) (f : List Bool → Bool) (y : List Bool) : Bool :=
  pts.any fun x => leCb x y && f x

theorem mExt_mono (pts : List (List Bool)) (f : List Bool → Bool)
    {p x : List Bool} (hc : Covers p x) (hp : mExt pts f p = true) :
    mExt pts f x = true := by
  rcases List.any_eq_true.mp hp with ⟨x0, hxm, hx⟩
  simp only [Bool.and_eq_true] at hx
  obtain ⟨hxle, hxf⟩ := hx
  refine List.any_eq_true.mpr ⟨x0, hxm, ?_⟩
  have : leCb x0 x = true := leCb_iff.mpr (LeC_trans (leCb_iff.mp hxle) (covers_leC hc))
  rw [this, hxf]
  rfl

theorem mExt_agrees (pts : List (List Bool)) (f : List Bool → Bool)
    (h0 : decPts pts f = 0) {y : List Bool} (hy : y ∈ pts) :
    mExt pts f y = f y := by
  cases hfy : f y
  · cases hany : mExt pts f y
    · rfl
    · exfalso
      rcases List.any_eq_true.mp hany with ⟨x, hxm, hx⟩
      simp only [Bool.and_eq_true] at hx
      obtain ⟨hxle, hxf⟩ := hx
      have hv := omega_viol f (star_of_leC (leCb_iff.mp hxle)) hxf hfy
      have hb := omega_le_decPts (pts := pts) f hy
      omega
  · refine List.any_eq_true.mpr ⟨y, hy, ?_⟩
    have h1 : leCb y y = true := leCb_iff.mpr (LeC_refl y)
    rw [h1, hfy]
    rfl

/-- ★ the F1 nested chi_sigma-tower (filtration semantics: length <= K). -/
inductive Tower : (List Bool → Bool) → Nat → Prop
  | mono {f : List Bool → Bool}
      (hm : ∀ ⦃p x : List Bool⦄, Covers p x → f p = true → f x = true) :
      Tower f 0
  | lift {f : List Bool → Bool} {k : Nat} : Tower f k → Tower f (k + 1)
  | peel {h : List Bool → Bool} {g : List Bool → Bool → Bool} {k : Nat}
      (ht : Tower h k)
      (hg : ∀ ⦃y y' : List Bool⦄, LeC y y' → ∀ ⦃v v' : Bool⦄, (v = true → v' = true) →
        g y v = true → g y' v' = true) :
      Tower (fun y => g y (!(h y))) (k + 1)

theorem tower_le {f : List Bool → Bool} {k : Nat} (ht : Tower f k) :
    ∀ {k' : Nat}, k ≤ k' → Tower f k' := by
  intro k'
  induction k' with
  | zero => intro hk; have : k = 0 := Nat.le_zero.mp hk; exact this ▸ ht
  | succ k' ih =>
      intro hk
      rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
      · exact Tower.lift (ih (by omega))
      · have : k = k' + 1 := by omega
        exact this ▸ ht

/-- ★ F1 UPPER (constructive): if dec over pts is <= K, some f' agreeing with f
    on pts lies in the K-th rung of the tower. -/
theorem tower_of_decPts (pts : List (List Bool)) :
    ∀ (K : Nat) (f : List Bool → Bool), decPts pts f ≤ K →
      ∃ f', (∀ y ∈ pts, f' y = f y) ∧ Tower f' K := by
  intro K
  induction K with
  | zero =>
      intro f hd
      have h0 : decPts pts f = 0 := Nat.le_zero.mp hd
      exact ⟨mExt pts f, fun y hy => mExt_agrees pts f h0 hy,
        Tower.mono (fun p x hc hp => mExt_mono pts f hc hp)⟩
  | succ K ih =>
      intro f hd
      rcases Nat.eq_zero_or_pos (decPts pts f) with h0 | hpos
      · exact ⟨mExt pts f, fun y hy => mExt_agrees pts f h0 hy,
          tower_le (Tower.mono (fun p x hc hp => mExt_mono pts f hc hp)) (Nat.zero_le _)⟩
      · -- decPts pts f >= 1: peel with hgen at K' := decPts pts f
        have hcov : ∀ x ∈ pts, ∀ y ∈ pts, LeC x y → f x = true → f y = false →
            hgen f (omega f) (decPts pts f) x = false ∧
            hgen f (omega f) (decPts pts f) y = true := by
          intro x hx y hy hle hfx hfy
          exact cube_hgen_covering f hle hfx hfy (omega_le_decPts f hy)
        have hdech : decPts pts (hgen f (omega f) (decPts pts f)) ≤ K := by
          have := decPts_hgen_le pts f (decPts pts f)
          omega
        obtain ⟨h', hagree, hth⟩ := ih _ hdech
        refine ⟨fun y => gExt pts f (hgen f (omega f) (decPts pts f)) y (!(h' y)), ?_, ?_⟩
        · intro y hy
          show gExt pts f (hgen f (omega f) (decPts pts f)) y (!(h' y)) = f y
          rw [hagree y hy]
          exact gExt_agrees pts f _ hcov hy
        · exact Tower.peel hth (fun y y' hle v v' hv hg => gExt_mono pts f _ hle hv hg)

/-- along a chain of the peeled function, descents are matched by an h-chain,
    up to the end-value-refined alternation slack. -/
theorem chainDrops_peel {h : List Bool → Bool} {g : List Bool → Bool → Bool}
    (hg : ∀ ⦃y y' : List Bool⦄, LeC y y' → ∀ ⦃v v' : Bool⦄, (v = true → v' = true) →
      g y v = true → g y' v' = true)
    {x z : List Bool} {d : Nat}
    (hcd : ChainDrops (fun y => g y (!(h y))) x z d) :
    ∃ dh, ChainDrops h x z dh ∧ d ≤ dh + (if h z = true then 1 else 0) := by
  have hgB : BMono Covers g := fun a b hcab u v hi => hg (covers_leC hcab) hi
  have hbeta : ∀ y, (fun y => g y (!(h y))) y = g y (!(h y)) := fun _ => rfl
  induction hcd with
  | base => exact ⟨0, .base _, Nat.zero_le _⟩
  | step hcd hc ih =>
      rename_i p z d
      obtain ⟨dh, hcdh, hle⟩ := ih
      refine ⟨dh + (if h p && !(h z) then 1 else 0), .step hcdh hc, ?_⟩
      try simp only [hbeta]
      -- generic slack fact: [h p] <= [h p && !h z] + [h z]
      have hkey : (if h p = true then (1:Nat) else 0) ≤
          (if h p && !(h z) then 1 else 0) + (if h z = true then 1 else 0) := by
        cases h p <;> cases h z <;> simp
      cases hfp : g p (!(h p)) <;> cases hfz : g z (!(h z))
      · -- no f-descent (f p = false)
        have e : (if (((false:Bool) && !(false:Bool)) = true) then (1:Nat) else 0) = 0 := rfl
        rw [e]
        omega
      · have e : (if (((false:Bool) && !(true:Bool)) = true) then (1:Nat) else 0) = 0 := rfl
        rw [e]
        omega
      · -- f-descent: transfer forces h p = false, h z = true
        obtain ⟨hhp, hhz⟩ := drop_transfer hgB hc hfp hfz
        have e : (if (((true:Bool) && !(false:Bool)) = true) then (1:Nat) else 0) = 1 := rfl
        have e2 : (if ((h p && !(h z)) = true) then (1:Nat) else 0) = 0 := by
          rw [hhp]; rfl
        have e3 : (if h z = true then (1:Nat) else 0) = 1 := by
          rw [hhz]; rfl
        have e4 : (if h p = true then (1:Nat) else 0) = 0 := by
          rw [hhp]; rfl
        rw [e, e2, e3]
        rw [e4] at hle
        omega
      · have e : (if (((true:Bool) && !(true:Bool)) = true) then (1:Nat) else 0) = 0 := rfl
        rw [e]
        omega

/-- cover-monotone functions have omega = 0 chains. -/
theorem chainDrops_mono_zero {f : List Bool → Bool}
    (hm : ∀ ⦃p x : List Bool⦄, Covers p x → f p = true → f x = true)
    {x z : List Bool} {d : Nat} (h : ChainDrops f x z d) : d = 0 := by
  induction h with
  | base => rfl
  | step hcd hc ih =>
      rename_i p z d
      cases hfp : f p
      · simp [hfp, ih]
      · have hfz := hm hc hfp
        simp [hfp, hfz, ih]

/-- ★ F1 LOWER: a K-rung tower member has omega <= K everywhere
    (hence decPts pts f <= K for every pts). -/
theorem F1_lower {f : List Bool → Bool} {K : Nat} (ht : Tower f K) :
    ∀ z, omega f z ≤ K := by
  induction ht with
  | mono hm =>
      rename_i f0
      intro z
      obtain ⟨x, hcd⟩ := omega_attained f0 z
      have := chainDrops_mono_zero hm hcd
      omega
  | lift _ ih =>
      intro z
      have := ih z
      omega
  | peel ht hg ih =>
      rename_i h g k
      intro z
      obtain ⟨x, hcd⟩ := omega_attained (fun y => g y (!(h y))) z
      obtain ⟨dh, hcdh, hle⟩ := chainDrops_peel hg hcd
      have hbound := chainDrops_le_omega _ hcdh
      have hih := ih z
      have hite : (if h z = true then (1:Nat) else 0) ≤ 1 := by
        cases h z <;> simp
      omega

theorem decPts_le_of_tower (pts : List (List Bool)) {f : List Bool → Bool} {K : Nat}
    (ht : Tower f K) : decPts pts f ≤ K :=
  decPts_le_of_all (fun z _ => F1_lower ht z)

end DecBridge
