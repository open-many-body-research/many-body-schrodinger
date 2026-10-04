import ManyBody.S8.Internal.PhysicalAnnularAnalyticApplicability
/-! A finite annular family with actual physical analytic applicability.

The width and finite unit-center family are chosen before every physical
state. At every 0<rho<=1/4 the actual selected-collision neighborhoods admit
literal real analytic unscaled A+distance*B reconstruction of the same graph
representative. Nuclear scale is rho; the restored c=1 pair scale is rho/sqrt2.
The geometric collision-free bulk is covered but receives no analytic bound
from this theorem. The triple origin and exterior analytic control remain open.
-/
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

/-- One finite state-independent annular family has actual analytic
    reconstruction on all of its isolated nuclear and pair neighborhoods. -/
theorem coulomb_spin_finite_annular_collision_analytic_applicability (Z E : ℝ) :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 η : ℝ,
    ∃ centers : Finset PhysicalUnitCenter,
      1≤M ∧ 1≤A ∧ 0≤Csrc ∧ 0≤CH12 ∧ 0<η ∧ η<1/16 ∧
      Real.sqrt 2*η ≤ physicalDescentPositionRadius M A ∧
      Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A ∧
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
          (∀ i : Fin 2, AnnularNuclearAnalyticReconstruction (u σ) i ρ η t) ∧
          AnnularPairAnalyticReconstruction (u σ) ρ η t := by
  obtain ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,hgain⟩ :=
    coulomb_spin_physical_original_norm_pointwise Z E
  obtain ⟨η,hη,hsmall,hηX,hηT⟩ := exists_annular_analytic_width hA
  obtain ⟨centers,hcover⟩ := two_electron_all_radii_finite_physical_chart_cover hη
  refine ⟨M,A,C_L,Csrc,CH12,η,centers,hM,hA,hsrc,hH12,hη,hsmall,hηX,hηT,hcover,?_⟩
  intro ψ hgraph
  obtain ⟨u,hu,hLip,hAE,hperm,hbound,hN,hP⟩ := hgain ψ hgraph
  refine ⟨u,hu,hLip,hAE,hperm,hbound,?_⟩
  have hF0 : 0≤Csrc*‖ψ‖ := mul_nonneg hsrc (norm_nonneg ψ)
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1≤Real.sqrt 2 := by
    have hsq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hηscale : η≤Real.sqrt 2*η := by
    calc
      η = 1*η := by ring
      _ ≤ Real.sqrt 2*η := mul_le_mul_of_nonneg_right hs1 hη.le
  have hnX : η≤physicalDescentPositionRadius M A := hηscale.trans hηX
  have hnT : η≤physicalDescentNeighborhoodRadius M A := hηscale.trans hηT
  intro ρ hρ hlim σ t _
  have hε : 0<ρ / Real.sqrt 2 := div_pos hρ hs
  have hεlim : ρ / Real.sqrt 2 ≤ 1/4 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith
  constructor
  · intro i
    exact nuclear_annular_analytic_reconstruction_of_pointwise (u σ) i hρ hA hF0
      hnX hnT (hN ρ hρ hlim σ i t t.property)
  · exact pair_annular_analytic_reconstruction_of_pointwise (u σ) hρ hA hF0
      hηX hηT (hP (ρ / Real.sqrt 2) hε hεlim σ t t.property)

#print axioms coulomb_spin_finite_annular_collision_analytic_applicability
end ManyBody.S8
