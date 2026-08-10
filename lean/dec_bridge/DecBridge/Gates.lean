/-
DecBridge.Gates -- the gate table on the Klein four-group acting on the
dual-rail lattice, by kernel `decide` (finite, 4 gates x 16 pairs):
k-monotonicity coincides with chi_sigma-triviality on {id, sigma, P, sigma P},
and the face-flip character (chi_sigma + chi_P) mis-prices negation in BOTH
directions (witnessed by P and by sigma P).
Core Lean 4 only; plain `decide` (NO native_decide).
-/
namespace DecBridge

abbrev D4 := Bool × Bool

def idD : D4 → D4 := fun p => p
def sigmaS : D4 → D4 := fun p => (!p.1, !p.2)
def railP : D4 → D4 := fun p => (p.2, p.1)
def sPD : D4 → D4 := fun p => sigmaS (railP p)

def allD4 : List D4 := [(false,false),(false,true),(true,false),(true,true)]

/-- knowledge order UNK <= TRU,FAL <= CON as boolean test. -/
def leKb (p q : D4) : Bool := (!p.1 || q.1) && (!p.2 || q.2)

def kMonoB (γ : D4 → D4) : Bool :=
  allD4.all fun p => allD4.all fun q => !(leKb p q) || leKb (γ p) (γ q)

/-- chi_sigma coordinate of a gate: does it move the endpoint UNK? (W1 axis) -/
def chiSigmaB (γ : D4 → D4) : Bool := decide (γ (false,false) ≠ ((false,false) : D4))

/-- face-flip (= chi_sigma + chi_P = R-flip) coordinate: does it move TRU? -/
def flipB (γ : D4 → D4) : Bool := decide (γ (true,false) ≠ ((true,false) : D4))

/-- ★ L1-b gate table (kernel decide): nu(γ) = [not k-monotone] = chi_sigma(γ)
    pointwise on V4, while face-flip fails in BOTH directions (P and sP). -/
theorem gate_table :
    (kMonoB idD    = true  ∧ chiSigmaB idD    = false ∧ flipB idD    = false) ∧
    (kMonoB railP  = true  ∧ chiSigmaB railP  = false ∧ flipB railP  = true ) ∧
    (kMonoB sigmaS = false ∧ chiSigmaB sigmaS = true  ∧ flipB sigmaS = true ) ∧
    (kMonoB sPD    = false ∧ chiSigmaB sPD    = true  ∧ flipB sPD    = false) := by
  decide

/-- chi_sigma = the needs-NOT indicator on V4 (kernel decide). -/
theorem chiSigma_eq_not_kMono :
    ∀ γ ∈ [idD, sigmaS, railP, sPD], chiSigmaB γ = !(kMonoB γ) := by
  decide

end DecBridge
