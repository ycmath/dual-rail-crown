/-
DecBridge.CubeViol -- violated pairs vs the concrete cube omega:
  omega_viol            : across a violated pair (x <= y, f x = 1, f y = 0),
                          omega f x + 1 <= omega f y;
  cube_hgen_covering    : the concrete covering theorem for the witness,
                          for any k bounding omega at the top of the pair;
  chain_drops_bound     : every cover-chain's descent count is bounded by
                          omega at a point above its head;
  cube_decOn_le_bound   : any finite chain family's dec is bounded by any
                          global omega bound.
Core Lean 4 only; kernel proofs; no native_decide; no sorry.
-/
import DecBridge.Cube

namespace DecBridge

/-- componentwise order on equal-length cube points. -/
def LeC : List Bool → List Bool → Prop
  | [], [] => True
  | a :: p, b :: q => (a = true → b = true) ∧ LeC p q
  | _, _ => False

/-- upward reflexive-transitive closure of Covers. -/
inductive Star : List Bool → List Bool → Prop
  | refl (x : List Bool) : Star x x
  | step {x y z : List Bool} : Covers x y → Star y z → Star x z

theorem Star.trans : ∀ {x y z : List Bool}, Star x y → Star y z → Star x z
  | _, _, _, .refl _, h2 => h2
  | _, _, _, .step hc hs, h2 => .step hc (Star.trans hs h2)

theorem Star.consLift (b : Bool) : ∀ {p q : List Bool}, Star p q → Star (b :: p) (b :: q)
  | _, _, .refl _ => .refl _
  | _, _, .step hc hs => .step (Covers.tail b hc) (Star.consLift b hs)

theorem star_of_leC : ∀ {x y : List Bool}, LeC x y → Star x y
  | [], [], _ => .refl _
  | a :: p, b :: q, h => by
      have h1 : a = true → b = true := h.1
      have ih := star_of_leC h.2
      cases a <;> cases b
      · exact Star.consLift false ih
      · exact Star.trans (Star.consLift false ih) (.step (Covers.head q) (.refl _))
      · cases h1 rfl
      · exact Star.consLift true ih
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem omega_mono_star (f : List Bool → Bool) :
    ∀ {x y : List Bool}, Star x y → omega f x ≤ omega f y
  | _, _, .refl _ => Nat.le_refl _
  | _, _, .step hc hs =>
      Nat.le_trans ((cube_descPotential f).mono hc) (omega_mono_star f hs)

/-- ★ across a violated pair, omega strictly increases (subsumes (d) and (e)). -/
theorem omega_viol (f : List Bool → Bool) :
    ∀ {x y : List Bool}, Star x y → f x = true → f y = false →
      omega f x + 1 ≤ omega f y
  | _, _, .refl _, hfx, hfy => by rw [hfx] at hfy; cases hfy
  | _, _, .step (y := m) hc hs, hfx, hfy => by
      cases hfm : f m
      · have hstrict := (cube_descPotential f).strict hc hfx hfm
        have hmono := omega_mono_star f hs
        omega
      · have hrec := omega_viol f hs hfm hfy
        have hmono := (cube_descPotential f).mono hc
        omega

/-- ★ concrete covering theorem: hgen with the concrete omega covers every
    violated pair, for any k bounding omega at the pair's top. -/
theorem cube_hgen_covering (f : List Bool → Bool) {k : Nat} {x y : List Bool}
    (hle : LeC x y) (hfx : f x = true) (hfy : f y = false)
    (hbk : omega f y ≤ k) :
    hgen f (omega f) k x = false ∧ hgen f (omega f) k y = true := by
  have hv := omega_viol f (star_of_leC hle) hfx hfy
  exact hgen_covering (by omega) (by omega) hfx (by omega) hfy

/-- every cover-chain's descent count is bounded by omega at (some point above
    its head reachable along the chain). -/
theorem chain_drops_bound (f : List Bool → Bool) :
    ∀ (x : List Bool) (rest : List (List Bool)), IsChain Covers (x :: rest) →
      ∃ z, Star x z ∧ omega f x + drops ((x :: rest).map f) ≤ omega f z
  | x, [], _ => ⟨x, .refl x, by simp⟩
  | x, y :: r, hc => by
      obtain ⟨z, hstar, hbd⟩ := chain_drops_bound f y r hc.2
      refine ⟨z, Star.step hc.1 hstar, ?_⟩
      have hstep := omega_ge_entry (f := f) hc.1
      simp only [List.map_cons] at hbd ⊢
      rw [drops_cons]
      omega

/-- ★ dec over any finite cover-chain family is bounded by any global omega bound
    (one half of "k = dec(f)" for the covering interface). -/
theorem cube_decOn_le_bound (f : List Bool → Bool) (k : Nat)
    (hb : ∀ z, omega f z ≤ k)
    (CS : List (List (List Bool))) (hCS : ∀ C ∈ CS, IsChain Covers C) :
    decOn CS f ≤ k := by
  induction CS with
  | nil => simp
  | cons C CS ih =>
      rw [decOn_cons]
      refine Nat.max_le.mpr ⟨?_, ih (fun C' hm => hCS C' (by simp [hm]))⟩
      cases C with
      | nil => simp
      | cons x rest =>
          obtain ⟨z, _, hbd⟩ := chain_drops_bound f x rest (hCS _ (by simp))
          have := hb z
          omega

end DecBridge
