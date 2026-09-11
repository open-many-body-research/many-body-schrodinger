import BoundedCoefficientGradientEndpoint_v1
import CoulombInteriorTransformedEquation_v1
import CoulombEigenfunctionBounded_v1
import ContinuousBallMultiplier_v1

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem scalar_coulomb_transformed_locally_bounded_weak_gradient {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {A : ℝ} (hA : 0 < A) :
    ∃ g : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        HasH2 g ∧ (∀ k, WeakPartial g (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        (g : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 A)]
          (fun x => Real.exp (-coulombCusp N Z x) • f x) ∧
        MemLp g ⊤ (volume.restrict (Metric.ball 0 A)) ∧
        ∀ k, MemLp (a k) ⊤ (volume.restrict (Metric.ball 0 A)) := by
  let R : ℝ := (4:ℝ)^(3*N)*A+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hAR : (4:ℝ)^(3*N)*A < R := by dsimp [R]; linarith
  have hA' : A < R := by
    have hp : (1:ℝ) ≤ 4^(3*N) := one_le_pow₀ (by norm_num)
    dsimp [R]
    nlinarith
  have hμ : volume.restrict (Metric.ball (0 : Configuration N) A) ≤ volume.restrict (Metric.ball 0 R) :=
    Measure.restrict_mono_set volume (Metric.ball_subset_ball hA'.le)
  obtain ⟨g,a,b,hg2,hga,hab,hEq⟩ := scalar_coulomb_interior_transformed_equation hg hR
  have hv : (g : Configuration N → ℂ) =ᵐ[volume.restrict (Metric.ball 0 R)]
      (fun x => Real.exp (-coulombCusp N Z x) • f x) := hEq.mono (fun x hx => hx.1)
  have hgb : MemLp g ⊤ (volume.restrict (Metric.ball 0 R)) := by
    apply MemLp.ae_eq hv.symm
    exact continuous_ball_multiplier_memLp (Real.continuous_exp.comp (coulombCusp_continuous N Z).neg)
      ((scalar_coulomb_eigen_memLp_top hN hg).mono_measure Measure.restrict_le_self)
  have hgrad := bounded_coefficient_gradient_memLp_top hN hga hab
    (fun k => coulombCuspGradient_memLp_top N Z (coordinateVector k))
    (coulombCusp_zero_order_memLp_top N Z E) hgb (hEq.mono (fun x hx => hx.2)) hA hAR
  exact ⟨g,a,b,hg2,hga,hab,hv.filter_mono (ae_mono hμ),hgb.mono_measure hμ,hgrad⟩

#print axioms scalar_coulomb_transformed_locally_bounded_weak_gradient
end TheoremT.Continuum
