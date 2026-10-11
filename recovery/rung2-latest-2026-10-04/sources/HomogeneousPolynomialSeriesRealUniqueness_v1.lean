import FormalMultilinearDiagonalUniqueness_v1
import HomogeneousPolynomialSeriesAnalytic_v1
import RealCoordinateEmbedding_v1

/-! Local equality of actual real homogeneous-polynomial sums forces
equality of each polynomial evaluation. The exact series coefficients
are obtained by restriction of the proved complex multilinear
representation. Only diagonal uniqueness is used. -/
noncomputable section
set_option autoImplicit false
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum
variable {σ : Type*} [Fintype σ]

def realHomogeneousPolynomialSeriesSum (Q : ℕ → MvPolynomial σ ℂ)
    (x : σ → ℝ) : ℂ := ∑' n, MvPolynomial.eval (fun i => (x i : ℂ)) (Q n)

def realHomogeneousPolynomialMultilinearSeries
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n) :
    FormalMultilinearSeries ℝ (σ → ℝ) ℂ :=
  ((homogeneousPolynomialMultilinearSeries Q hQ).restrictScalars ℝ).compContinuousLinearMap
    realCoordinateEmbedding

theorem realHomogeneousPolynomialMultilinearSeries_diagonal
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    (n : ℕ) (x : σ → ℝ) :
    realHomogeneousPolynomialMultilinearSeries Q hQ n (fun _ => x) =
      MvPolynomial.eval (fun i => (x i : ℂ)) (Q n) := by
  change homogeneousPolynomialMultilinearSeries Q hQ n
    (fun _ => realCoordinateEmbedding x) = _
  exact homogeneousPolynomialMultilinearSeries_diagonal Q hQ n _

theorem realHomogeneousPolynomialMultilinearSeries_hasFPowerSeriesAt
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n) :
    HasFPowerSeriesAt (realHomogeneousPolynomialSeriesSum Q)
      (realHomogeneousPolynomialMultilinearSeries Q hQ) 0 := by
  let p := homogeneousPolynomialMultilinearSeries Q hQ
  have hR : 0 < (B+1)⁻¹ := inv_pos.mpr (by linarith)
  have hBR : B*(B+1)⁻¹≤1 := by
    rw [mul_inv_le_iff₀ (by linarith : 0<B+1)]
    linarith
  have hrad : 0 < p.radius :=
    (ENNReal.ofReal_pos.mpr hR).trans_le
      (formalMultilinearSeries_radius_geometric p hC hB hR.le hBR
        (fun n => (homogeneousPolynomialMultilinearSeries_norm Q hQ n).trans (hL n)))
  have hp := (p.hasFPowerSeriesOnBall hrad).hasFPowerSeriesAt
  have hr : HasFPowerSeriesAt p.sum (p.restrictScalars ℝ)
      (realCoordinateEmbedding (0 : σ → ℝ)) := by
    simpa only [map_zero] using hp.restrictScalars (𝕜 := ℝ)
  have hc := hr.compContinuousLinearMap
  unfold realHomogeneousPolynomialSeriesSum
  simpa only [p,homogeneousPolynomialMultilinearSeries_sum,Function.comp_def,
    realCoordinateEmbedding_coe,realHomogeneousPolynomialSeriesSum,
    realHomogeneousPolynomialMultilinearSeries] using hc

theorem homogeneous_polynomial_series_real_linear_invariant_of_eventually
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (L : (σ → ℝ) →L[ℝ] (σ → ℝ))
    (hi : (realHomogeneousPolynomialSeriesSum Q ∘ L) =ᶠ[𝓝 0]
      realHomogeneousPolynomialSeriesSum Q) (n : ℕ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => (L x i : ℂ)) (Q n) =
      MvPolynomial.eval (fun i => (x i : ℂ)) (Q n) := by
  have hp := realHomogeneousPolynomialMultilinearSeries_hasFPowerSeriesAt Q hQ hC hB hL
  have hp' : HasFPowerSeriesAt (realHomogeneousPolynomialSeriesSum Q)
      (realHomogeneousPolynomialMultilinearSeries Q hQ) (L 0) := by
    simpa only [map_zero] using hp
  have he := formalMultilinear_diagonal_eq_of_eventually
    hp'.compContinuousLinearMap hp hi n x
  change realHomogeneousPolynomialMultilinearSeries Q hQ n (fun _ => L x) =
    realHomogeneousPolynomialMultilinearSeries Q hQ n (fun _ => x) at he
  simpa only [realHomogeneousPolynomialMultilinearSeries_diagonal] using he

theorem homogeneous_polynomial_series_real_linear_invariant_of_hasSum
    (Q : ℕ → MvPolynomial σ ℂ) (hQ : ∀ n, (Q n).IsHomogeneous n)
    {C B : ℝ} (hC : 0≤C) (hB : 0≤B)
    (hL : ∀ n, polynomialCoeffL1 (Q n) ≤ C*B^n)
    (F : (σ → ℝ) → ℂ) (L : (σ → ℝ) →L[ℝ] (σ → ℝ))
    (hsum : ∀ᶠ x in 𝓝 0,
      HasSum (fun n => MvPolynomial.eval (fun i => (x i : ℂ)) (Q n)) (F x))
    (hi : (F ∘ L) =ᶠ[𝓝 0] F) (n : ℕ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => (L x i : ℂ)) (Q n) =
      MvPolynomial.eval (fun i => (x i : ℂ)) (Q n) := by
  have he : realHomogeneousPolynomialSeriesSum Q =ᶠ[𝓝 0] F := by
    filter_upwards [hsum] with y hy
    exact hy.tsum_eq
  have ht : Filter.Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using L.continuous.tendsto (0 : σ → ℝ)
  apply homogeneous_polynomial_series_real_linear_invariant_of_eventually Q hQ hC hB hL L
    ((he.comp_tendsto ht).trans (hi.trans he.symm)) n x

end TheoremT.Continuum
