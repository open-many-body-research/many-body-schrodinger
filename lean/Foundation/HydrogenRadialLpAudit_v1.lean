import HydrogenRadialLp_v1

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace TheoremT.Continuum

/-- Literal-space statement: the physical exponential and its Coulomb quotient
are in Lebesgue L2, and the resulting equivalence class is nonzero. -/
theorem hydrogen_radial_L2_expanded (Z : ℝ) (hZ : 0 < Z) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 1 × Fin 3) =>
      (Real.exp (-Z * ‖x‖) : ℂ)) 2 volume ∧
    MemLp (fun x : EuclideanSpace ℝ (Fin 1 × Fin 3) =>
      (Real.exp (-Z * ‖x‖) : ℂ) / (‖x‖ : ℂ)) 2 volume ∧
    (hydrogenRadial_memLp hZ).toLp (fun x : EuclideanSpace ℝ (Fin 1 × Fin 3) =>
      (Real.exp (-Z * ‖x‖) : ℂ)) ≠ 0 :=
  ⟨hydrogenRadial_memLp hZ, hydrogenRadial_div_norm_memLp hZ,
    hydrogenRadialL2_ne_zero Z hZ⟩

set_option pp.proofs false in
set_option pp.explicit true in
#print hydrogen_radial_L2_expanded

#print axioms hydrogenRadial_memLp
#print axioms hydrogenRadial_div_norm_memLp
#print axioms hydrogenRadialL2_ne_zero
#print axioms hydrogen_radial_L2_expanded

end TheoremT.Continuum
