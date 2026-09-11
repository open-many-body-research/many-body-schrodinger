import NewtonPotentialLimits_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

def newtonGradient (N : ℕ) (k : Coordinate N) (x : Configuration N) : ℝ :=
  ‖x‖^(-(3*N:ℝ))*x k

theorem norm_sq_rpow_half {N : ℕ} (x : Configuration N) (α : ℝ) :
    (‖x‖^2)^(α/2)=‖x‖^α := by
  rw [← Real.rpow_natCast ‖x‖ 2,← Real.rpow_mul (norm_nonneg x)]
  congr 1
  norm_num
  ring

theorem regularizedNewtonGradient_abs_bound {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) {x : Configuration N} (hx : x ≠ 0) (k : Coordinate N) :
    |fderiv ℝ (regularizedNewtonPotential N δ) x (coordinateVector k)| ≤ ‖x‖^(1-(3*N:ℝ)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr)
    (show ‖x‖^2 ≤ ‖x‖^2+δ by linarith)
    (show -(3*N:ℝ)/2 ≤ 0 by have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  rw [norm_sq_rpow_half] at hh
  have hk : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x k
  rw [regularizedNewtonPotential_partial hN hδ,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ ‖x‖^2+δ) _)]
  calc
    _ ≤ ‖x‖^(-(3*N:ℝ))*‖x‖ := mul_le_mul hh hk (abs_nonneg _) (Real.rpow_nonneg hr.le _)
    _ = _ := by
      calc
        _ = ‖x‖^(-(3*N:ℝ)+1) := by rw [Real.rpow_add hr,Real.rpow_one]
        _ = _ := by congr 1; ring

theorem regularizedNewtonGradient_tendsto {N : ℕ} (hN : 0 < N)
    {δ : ℕ → ℝ} (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : x ≠ 0) (k : Coordinate N) :
    Tendsto (fun n => fderiv ℝ (regularizedNewtonPotential N (δ n)) x (coordinateVector k)) atTop
      (𝓝 (newtonGradient N k x)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : Tendsto (fun n => ‖x‖^2+δ n) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add hδ
  have hh := (ht.rpow_const (p := -(3*N:ℝ)/2) (Or.inl (sq_pos_of_pos hr).ne')).mul_const (x k)
  simp only [norm_sq_rpow_half] at hh
  simpa only [regularizedNewtonPotential_partial hN (hp _),newtonGradient] using hh

theorem newtonGradient_abs_bound {N : ℕ} (hN : 0 < N) (k : Coordinate N) (x : Configuration N) :
    |newtonGradient N k x| ≤ ‖x‖^(1-(3*N:ℝ)) := by
  by_cases hx : x=0
  · subst x; simp [newtonGradient,Real.rpow_nonneg]
  · apply le_of_tendsto ((regularizedNewtonGradient_tendsto hN radiusRegularization_pos
      radiusRegularization_tendsto hx k).abs)
    exact Eventually.of_forall (fun n => regularizedNewtonGradient_abs_bound hN
      (radiusRegularization_pos n) hx k)

#print axioms regularizedNewtonGradient_tendsto
#print axioms newtonGradient_abs_bound
end TheoremT.Continuum
