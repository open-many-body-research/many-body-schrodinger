import HardyLaplacianCore_v2

/-! Complex Green identities on the actual compact smooth configuration core. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def complexPairingBilinear : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem compact_complex_pairing_integrable {N : ℕ} {u v : Configuration N → ℂ}
    (hu : Continuous u) (hv : Continuous v) (huc : HasCompactSupport u) :
    Integrable (fun x => star (u x) * v x) volume := by
  apply (hu.star.mul hv).integrable_of_hasCompactSupport
  apply huc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by simp [hz])

theorem compact_complex_partial_ibp {N : ℕ} {u v : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (huc : HasCompactSupport u)
    (k : Coordinate N) :
    (∫ x, star (u x) * smoothPartial v k x) =
      -(∫ x, star (smoothPartial u k x) * v x) := by
  have hdu := smoothPartial_contDiff hu k
  have hdv := smoothPartial_contDiff hv k
  have hh := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := complexPairingBilinear) (v := coordinateVector k)
    (compact_complex_pairing_integrable hdu.continuous hv.continuous (smoothPartial_compact huc k))
    (compact_complex_pairing_integrable hu.continuous hdv.continuous huc)
    (compact_complex_pairing_integrable hu.continuous hv.continuous huc)
    (fun x _ => hu.differentiable (by simp) x)
    (fun x _ => hv.differentiable (by simp) x)
  exact hh

theorem compact_complex_second_symmetric {N : ℕ} {u v : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (huc : HasCompactSupport u)
    (k : Coordinate N) :
    (∫ x, star (u x) * smoothPartial (smoothPartial v k) k x) =
      (∫ x, star (smoothPartial (smoothPartial u k) k x) * v x) := by
  rw [compact_complex_partial_ibp hu (smoothPartial_contDiff hv k) huc k,
    compact_complex_partial_ibp (smoothPartial_contDiff hu k) hv (smoothPartial_compact huc k) k,
    neg_neg]

/-- The true complex Laplacian pairing is symmetric on compact smooth inputs. -/
theorem compact_complex_laplacian_symmetric {N : ℕ} {u v : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (huc : HasCompactSupport u) :
    (∫ x, star (u x) * smoothLaplacian v x) =
      (∫ x, star (smoothLaplacian u x) * v x) := by
  have hleft := fun k => compact_complex_pairing_integrable hu.continuous
    (smoothPartial_contDiff (smoothPartial_contDiff hv k) k).continuous huc
  have hright := fun k => compact_complex_pairing_integrable
    (smoothPartial_contDiff (smoothPartial_contDiff hu k) k).continuous hv.continuous
    (smoothPartial_compact (smoothPartial_compact huc k) k)
  simp only [smoothLaplacian, Finset.mul_sum, star_sum, Finset.sum_mul]
  rw [integral_finset_sum Finset.univ (fun k _ => hleft k),
    integral_finset_sum Finset.univ (fun k _ => hright k)]
  exact Finset.sum_congr rfl (fun k _ => compact_complex_second_symmetric hu hv huc k)

#print axioms compact_complex_partial_ibp
#print axioms compact_complex_laplacian_symmetric
end TheoremT.Continuum
