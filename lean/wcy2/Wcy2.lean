/-
Wcy2 -- Lean mechanization of the D4 layer of "The Price of NOT on D4":
closed-core soundness (Thm 2.1), sigma facts (Thm 3.1), resolved-face
escape/recovery/witness-independence (C.1/C.2/C.4), and the exact equality
nu = dec on the cube (Thm 5.3, D4 edition: recovery-face term language,
word-level subadditivity lower bound, monotone-DNF + tower-peel upper bound),
on top of the DecBridge library (subadditivity, three-zone witness, tower).
Core-only; no mathlib; no native_decide; no sorry.
-/
import Wcy2.D4
import Wcy2.Transfer
import Wcy2.RTerm
import Wcy2.NuLower
import Wcy2.NuUpper
import Wcy2.PriceOfNot
import Wcy2.Crown

namespace Wcy2

#print axioms cterm_monotone
#print axioms cterm_endpoints
#print axioms cterm_equivariant
#print axioms sigd_invol
#print axioms sigma_not_monotone
#print axioms escape
#print axioms recovery
#print axioms reentry_independent
#print axioms sigma_eq_P_on_R
#print axioms deval_inR
#print axioms deval_envOf
#print axioms chainDrops_and
#print axioms chainDrops_or
#print axioms chainDrops_not
#print axioms dec_le_sigCount
#print axioms mono_realize
#print axioms tower_realize
#print axioms nu_upper
#print axioms nu_eq_dec_bool
#print axioms nu_eq_dec_D4
#print axioms crown_necessity
#print axioms crown_sufficiency
#print axioms extendSD_selfDual
#print axioms restrictRep_extendSD
#print axioms extendSD_restrictRep
#print axioms maj3_realized
#print axioms and2_not_selfDual
#print axioms sdGuard_selfDual
#print axioms sdGuard_spec
#print axioms one_constant_completion

end Wcy2
