/-
DecBridge -- Lean mechanization of "The Cohomological Price of NOT":
the alternation lemma, subadditivity, the gate table on the Klein four-group,
the three-zone witness over an abstract descent potential, the concrete cube
omega, and both directions of the nested-tower theorem.
Core-only; no mathlib; no native_decide; no sorry.
-/
import DecBridge.Words
import DecBridge.Subadd
import DecBridge.Gates
import DecBridge.Hgen
import DecBridge.Cube
import DecBridge.CubeViol
import DecBridge.CubeDec
import DecBridge.Tower

namespace DecBridge

#print axioms subadd_chain
#print axioms subadd_decOn
#print axioms rises_le_drops_succ
#print axioms gate_table
#print axioms chiSigma_eq_not_kMono
#print axioms hgen_covering
#print axioms hgen_drops_le
#print axioms hgen_decOn_le
#print axioms cube_descPotential
#print axioms cube_hgen_drops_le
#print axioms cube_hgen_decOn_le
#print axioms omega_viol
#print axioms cube_hgen_covering
#print axioms cube_decOn_le_bound
#print axioms omega_attained
#print axioms omega_hgen_le
#print axioms tower_of_decPts
#print axioms F1_lower
#print axioms decPts_le_of_tower

end DecBridge
