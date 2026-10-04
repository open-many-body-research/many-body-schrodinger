import ManyBody.S8.Internal.PhysicalOriginalCollisionDerivativeBudget
/-! Original unscaled physical A/B mixed derivatives with exact scale powers.

One positive quarter-polydisc shrink and a finite annular family precede the
state. The original graph supplies the same representative and all normalized
mixed data. Actual Euclidean physical coordinate derivatives then have common
original-state norm amplitudes, with epsilon^(1-n) for A at positive order and
epsilon^(-n) for B. A retains u(0) at order zero. Nuclear epsilon=rho; the
restored coefficient-1 pair epsilon=rho/sqrt2. No differentiated PDE or norm
budget is a principal input. Collision-free bulk, triple origin, exterior
analytic estimates, global approximation and solver guarantees remain open.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

theorem coulomb_spin_annular_original_mixed_derivative_budgets (Z E : ℝ) :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 η : ℝ,
    ∃ centers : Finset PhysicalUnitCenter,
      1≤M ∧ 1≤A ∧ 0≤Csrc ∧ 0≤CH12 ∧ 0<η ∧ η<1/16 ∧
      Real.sqrt 2*η ≤ physicalDescentPositionRadius M A ∧
      Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A ∧
      (32*(7*physicalKSPointwiseRate M A)^2)*(Real.sqrt 2*η) ≤ 1/4 ∧
      (7*physicalKSPointwiseRate M A)*(Real.sqrt 2*η) ≤ 1/4 ∧
      (∀ ρ : ℝ, 0<ρ → {x : Configuration 2 | ‖x‖=ρ} ⊆
        ⋃ t ∈ centers, scaledAnnularPhysicalChartCover ρ η t) ∧
      ∀ ψ : SpinSpace 2, hamiltonianGraph 2 Z ψ ((E:ℂ) • ψ) →
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith (C_L*‖ψ‖₊) (u σ) (ball 0 1)) ∧
        (∀ᵐ x ∂volume, ∀ σ, ψ σ x=u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z E*‖ψ‖) ∧
        ∀ ρ : ℝ, 0<ρ → ρ≤1/4 → ∀ σ : SpinConfiguration 2,
          ∀ t : PhysicalUnitCenter, t∈centers →
          (∀ i : Fin 2, AnnularNuclearOriginalDerivativeData (u σ) i ρ η t
            (coulombMoserBoundCoefficient 2 Z E) M A Csrc CH12 ψ) ∧
          AnnularPairOriginalDerivativeData (u σ) ρ η t
            (coulombMoserBoundCoefficient 2 Z E) M A Csrc CH12 ψ := by
  obtain ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,hgain⟩ :=
    coulomb_spin_physical_original_norm_analytic_derivative Z E
  obtain ⟨η,hη,hsmall,hηX,hηT,hηD,hηS⟩ := exists_annular_derivative_width hA
  obtain ⟨centers,hcover⟩ := two_electron_all_radii_finite_physical_chart_cover hη
  refine ⟨M,A,C_L,Csrc,CH12,η,centers,hM,hA,hsrc,hH12,hη,hsmall,
    hηX,hηT,hηD,hηS,hcover,?_⟩
  intro ψ hgraph
  obtain ⟨u,hu,hLip,hAE,hperm,hbound,hN,hP⟩ := hgain ψ hgraph
  refine ⟨u,hu,hLip,hAE,hperm,hbound,?_⟩
  have hF0 : 0≤Csrc*‖ψ‖ := mul_nonneg hsrc (norm_nonneg ψ)
  have hu0 (σ : SpinConfiguration 2) :
      ‖u σ 0‖≤coulombMoserBoundCoefficient 2 Z E*‖ψ‖ :=
    (complex_component_norm_le_sqrt_sum_sq (fun τ => u τ 0) σ).trans (hbound 0)
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1≤Real.sqrt 2 := by
    have hsq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hS : 0≤7*physicalKSPointwiseRate M A :=
    (mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)).le
  have hD : 0≤32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hηscale : η≤Real.sqrt 2*η := by
    calc
      η = 1*η := by ring
      _ ≤ Real.sqrt 2*η := mul_le_mul_of_nonneg_right hs1 hη.le
  have hnX : η≤physicalDescentPositionRadius M A := hηscale.trans hηX
  have hnT : η≤physicalDescentNeighborhoodRadius M A := hηscale.trans hηT
  have hnD : (32*(7*physicalKSPointwiseRate M A)^2)*η≤1/4 :=
    (mul_le_mul_of_nonneg_left hηscale hD).trans hηD
  have hnS : (7*physicalKSPointwiseRate M A)*η≤1/4 :=
    (mul_le_mul_of_nonneg_left hηscale hS).trans hηS
  intro ρ hρ hlim σ t _
  have hε : 0<ρ / Real.sqrt 2 := div_pos hρ hs
  have hεlim : ρ / Real.sqrt 2 ≤ 1/4 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith
  constructor
  · intro i
    exact nuclear_annular_original_derivative_data (u σ) i hρ hA hF0 hnX hnT hnD hnS
      (hN ρ hρ hlim σ i t t.property) (hu0 σ)
  · exact pair_annular_original_derivative_data (u σ) hρ hA hF0 hηX hηT hηD hηS
      (hP (ρ / Real.sqrt 2) hε hεlim σ t t.property) (hu0 σ)

#print axioms coulomb_spin_annular_original_mixed_derivative_budgets
end ManyBody.S8
