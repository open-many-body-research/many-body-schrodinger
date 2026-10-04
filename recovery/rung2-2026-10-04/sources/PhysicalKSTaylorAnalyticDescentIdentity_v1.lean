import PhysicalKSTaylorAnalyticDescentData_v1
import PhysicalKSTaylorSpectatorReconstruction_v1
import PhysicalKSTaylorOddSpectator_v1
import EvenFirstCoordinateHasSum_v1
import KSRealSpectatorSeriesDescent_v1

/-! Identification of the literal descended A/B sums with the actual
physical KS base. The domain is explicitly the intersection of its real
Taylor ball and the two proved convergence domains. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

def PhysicalKSAnalyticDescentIdentityOnTaylorBall
    (f : Space (Fin 3) → ℂ) (t0 : Position) (M A : ℝ) : Prop :=
  ∃ r : ℝ≥0, 0<r ∧ (r : ℝ)=min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹ ∧
    ∀ q ∈ Metric.eball (0 : Space (Fin 3)) (r : ℝ≥0∞),
      (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => (ksMap q.1 i : ℂ)‖<1 →
      (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => (q.2 i : ℂ)‖<1 →
      f ((0,t0)+q) =
        physicalKSAnalyticDescentA f t0
          (Sum.elim (fun i => (ksMap q.1 i : ℂ)) (fun i => (q.2 i : ℂ))) +
        (‖q.1‖^2 : ℝ)*physicalKSAnalyticDescentB f t0
          (Sum.elim (fun i => (ksMap q.1 i : ℂ)) (fun i => (q.2 i : ℂ)))

theorem physicalKSAnalyticDescent_identity_of_balanced_odd_zero
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ)).support → e 0+e 1=e 2+e 3)
    (hodd : ∀ m γ, physicalKSTaylorSpectatorFamily f (0,t0) (2*m+1) γ=0) :
    PhysicalKSAnalyticDescentIdentityOnTaylorBall f t0 M A := by
  obtain ⟨r,hr,he,hsum⟩ := physicalKSTaylorSpectatorFamily_hasSum_real_ball hdata hA hF0
  refine ⟨r,hr,he,?_⟩
  intro q hq hrad hspec
  have hcenter : (0,t0) ∈ rectangularClosedBox (0,t0) (1/1024) (1/1024) := by
    intro i
    cases i <;> norm_num [boxHalfWidth]
  have hfull := hsum (0,t0) hcenter q hq
  have heven := hasSum_even_first_coordinate hfull (fun m γ => by simp only [hodd,map_zero,zero_mul])
  have hS : 0 ≤ 7*physicalKSPointwiseRate M A :=
    mul_nonneg (by norm_num) (physicalKSPointwiseRate_pos hA).le
  have hdes := ks_real_spectator_series_physical_descent
    (physicalKSTaylorEvenSpectatorFamily f (0,t0))
    (physicalKSTaylorEvenSpectatorFamily_homogeneous f (0,t0)) hbal
    (physicalKSPointwiseAmplitude_nonneg hA hF0) hS hS
    (norm_nonneg (fun i : Fin 3 => (ksMap q.1 i : ℂ)))
    (norm_nonneg (fun i : Fin 3 => (q.2 i : ℂ))) hrad hspec
    (fun m γ e _ => physicalKSTaylorEvenSpectatorFamily_coeff_bound hdata hA hF0 m γ e)
    q.1 (fun i => (q.2 i : ℂ))
    (fun i => norm_le_pi_norm (fun j : Fin 3 => (ksMap q.1 j : ℂ)) i)
    (fun i => norm_le_pi_norm (fun j : Fin 3 => (q.2 j : ℂ)) i)
  exact heven.tsum_eq.symm.trans hdes.2.2

theorem nuclearKSPhysicalAnalyticDescent_identity
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSAnalyticDescentIdentityOnTaylorBall
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A := by
  apply physicalKSAnalyticDescent_identity_of_balanced_odd_zero hdata hA hF0
  · intro m γ e he
    exact nuclearKSPhysicalTaylorSpectatorCoefficient_balanced_support g i hdata hA hF0
      (2*m) (Finsupp.equivFunOnFinite.symm γ) e he
  · intro m γ
    exact nuclearKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero g i hdata hA hF0
      m (Finsupp.equivFunOnFinite.symm γ)

theorem pairKSPhysicalAnalyticDescent_identity
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSAnalyticDescentIdentityOnTaylorBall
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A := by
  apply physicalKSAnalyticDescent_identity_of_balanced_odd_zero hdata hA hF0
  · intro m γ e he
    exact pairKSPhysicalTaylorSpectatorCoefficient_balanced_support g hdata hA hF0
      (2*m) (Finsupp.equivFunOnFinite.symm γ) e he
  · intro m γ
    exact pairKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero g hdata hA hF0
      m (Finsupp.equivFunOnFinite.symm γ)

end TheoremT.Continuum
