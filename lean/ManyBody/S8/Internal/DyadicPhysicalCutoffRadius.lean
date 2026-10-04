import ManyBody.S8.CoulombNormalizedRadialCompactApproximation

/-! A literal radius growing linearly with dyadic precision absorbs every
nonnegative exponential prefactor while retaining the original threshold. -/
set_option autoImplicit false
noncomputable section
namespace ManyBody.S8

def physicalDyadicCutoffRadius (a C Rmin : ℝ) (p : ℕ) : ℝ :=
  max Rmin (Real.log (1+C)/a)+(p:ℝ)*Real.log 2/a

theorem physical_dyadic_cutoff_radius_budget {a C Rmin : ℝ}
    (ha : 0<a) (hC : 0≤C) (p : ℕ) :
    Rmin≤physicalDyadicCutoffRadius a C Rmin p ∧
      Real.exp (-a*physicalDyadicCutoffRadius a C Rmin p)*C≤(1/2:ℝ)^p := by
  let R0 := max Rmin (Real.log (1+C)/a)
  have hstep : 0≤(p:ℝ)*Real.log 2/a := div_nonneg
    (mul_nonneg (Nat.cast_nonneg p) (Real.log_nonneg (by norm_num))) ha.le
  have hlarge : Rmin≤R0+(p:ℝ)*Real.log 2/a :=
    (le_max_left _ _).trans (le_add_of_nonneg_right hstep)
  have hlog : Real.log (1+C)≤R0*a := (div_le_iff₀ ha).mp (le_max_right _ _)
  have hpos : 0<1+C := by linarith
  have hbase : Real.exp (-a*R0)*C≤1 := by
    calc _≤Real.exp (-Real.log (1+C))*C :=
           mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hC
         _=(1+C)⁻¹*C := by rw [Real.exp_neg,Real.exp_log hpos]
         _≤1 := by rw [inv_mul_eq_div]; exact (div_le_one hpos).mpr (by linarith)
  have he : -a*(R0+(p:ℝ)*Real.log 2/a)=-a*R0+(p:ℝ)*(-Real.log 2) := by
    field_simp [ha.ne']
    ring
  refine ⟨hlarge,?_⟩
  change Real.exp (-a*(R0+(p:ℝ)*Real.log 2/a))*C≤_
  calc _=(Real.exp (-a*R0)*C)*(1/2:ℝ)^p := by
           rw [he,Real.exp_add,Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : 0<(2:ℝ))]
           norm_num
           ring
       _≤1*(1/2:ℝ)^p := mul_le_mul_of_nonneg_right hbase (by positivity)
       _=(1/2:ℝ)^p := one_mul _

#print axioms physical_dyadic_cutoff_radius_budget
end ManyBody.S8
