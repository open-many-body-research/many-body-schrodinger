import PolarThree_v1

/-! Actual integrability of polar marginals. These are Fubini and density
consequences of full-space integrability, with the physical radial Jacobian. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace TheoremT.Polar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem integrable_volumeIoiPow_iff (n : ℕ) (f : ℝ → F) :
    Integrable (fun r : Ioi (0 : ℝ) => f r.val) (Measure.volumeIoiPow n) ↔
      IntegrableOn (fun r : ℝ => r ^ n • f r) (Ioi 0) := by
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi, Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  apply integrable_congr
  apply Eventually.of_forall
  intro r
  have hr : 0 ≤ r.val ^ n := pow_nonneg r.property.le n
  simp only [Function.comp_def, ENNReal.toReal_ofReal hr]

theorem integrable_polar_radius_marginal_dim_three
    {f : EuclideanSpace ℝ (Fin 3) → F} (hf : Integrable f) :
    IntegrableOn (fun r : ℝ => r ^ 2 •
      (∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        f (r • w.val) ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)) (Ioi 0) := by
  apply (integrable_volumeIoiPow_iff 2 _).mp
  have hprod := (integrable_polar_product_iff
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) f).mp hf
  simpa only [Module.finrank_fintype_fun_eq_card, Module.finrank_self,
    Fintype.card_fin, Nat.reduceSub, finrank_euclideanSpace] using hprod.integral_prod_right

theorem integrable_polar_sphere_marginal_dim_three
    {f : EuclideanSpace ℝ (Fin 3) → F} (hf : Integrable f) :
    Integrable (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ∫ r : ℝ in Ioi 0, r ^ 2 • f (r • w.val))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  have hprod := (integrable_polar_product_iff
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) f).mp hf
  have hm := hprod.integral_prod_left
  apply hm.congr
  apply Eventually.of_forall
  intro w
  simpa only [Module.finrank_fintype_fun_eq_card, Module.finrank_self,
    Fintype.card_fin, Nat.reduceSub, finrank_euclideanSpace] using
    integral_volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)
      (fun r => f (r • w.val))

end TheoremT.Polar

#print axioms TheoremT.Polar.integrable_polar_radius_marginal_dim_three
#print axioms TheoremT.Polar.integrable_polar_sphere_marginal_dim_three
