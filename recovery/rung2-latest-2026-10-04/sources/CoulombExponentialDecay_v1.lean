import ExteriorExponentialLimit_v1

/-! An actual scalar Coulomb eigenfunction decays exponentially in L² whenever
the stated exterior H¹ form coercivity holds. The decay weight is the physical
configuration-space radius. The exterior premise is discharged for the actual
two-electron ground energy in a separate module. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem exponential_memLp_of_exterior_memLp {N : ℕ} {R a : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (f : SpatialL2 N)
    (hext : MemLp (fun x => (exteriorTaper N R x *
      Real.exp (a*smoothConfigurationRadius N x)) • f x) 2 volume) :
    MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume := by
  have hcont : Continuous (fun x : Configuration N =>
      Real.exp (a*smoothConfigurationRadius N x)) :=
    Real.continuous_exp.comp
      (continuous_const.mul (smoothConfigurationRadius_contDiff N).continuous)
  have hm : MemLp (fun x : Configuration N => scaledCutoff N R x *
      Real.exp (a*smoothConfigurationRadius N x)) ⊤ volume :=
    ((scaledCutoff_contDiff N R).continuous.mul hcont).memLp_top_of_hasCompactSupport
      ((scaledCutoff_hasCompactSupport N hR).mul_right) volume
  have hi := (Lp.memLp f).smul (r := 2) hm
  have hfull : MemLp (fun x : Configuration N =>
      Real.exp (a*smoothConfigurationRadius N x) • f x) 2 volume := by
    apply (hext.add hi).ae_eq
    exact Eventually.of_forall (fun x => by
      change (exteriorTaper N R x * Real.exp (a*smoothConfigurationRadius N x)) • f x +
        (scaledCutoff N R x * Real.exp (a*smoothConfigurationRadius N x)) • f x = _
      rw [← add_smul]
      congr 1
      unfold exteriorTaper
      ring)
  apply hfull.of_le
    ((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun x => by
    change ‖Real.exp (a*‖x‖) • f x‖ ≤
      ‖Real.exp (a*smoothConfigurationRadius N x) • f x‖
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (norm_le_smoothConfigurationRadius x) ha)) (norm_nonneg (f x)))

theorem scalar_eigen_exponential_decay_of_exterior_coercivity
    {N : ℕ} {Z E R δ a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hR : 0 < R) (ha : 0 ≤ a) (hgap : a^2 < δ)
    (hcoerc : ∀ (v : SpatialL2 N) (q : ℝ), scalarCoulombH1FormValue N Z v q →
      (∀ᵐ x, ‖x‖ ≤ R → v x = 0) → δ*‖v‖^2 ≤ q-E*‖v‖^2) :
    MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume :=
  exponential_memLp_of_exterior_memLp hR ha f
    (scalar_eigen_exterior_exponential_memLp hg hR ha hgap hcoerc)

#print axioms exponential_memLp_of_exterior_memLp
#print axioms scalar_eigen_exponential_decay_of_exterior_coercivity
end TheoremT.Continuum
