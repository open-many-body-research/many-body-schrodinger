import PhysicalKSTaylorAnalyticDescentIdentity_v1
import KSMapSurjective_v1

/-! Transfer the established KS identity to every physical position in a
quantitative neighborhood, including the collision point. The preimage norm
is proved; the physical coordinate is not restricted to an assumed image. -/
noncomputable section
set_option autoImplicit false
open scoped NNReal ENNReal
namespace TheoremT.Continuum
open WeakGrushin

def nuclearKSPhysicalCoordinates (i : Fin 2) (X T : Position) : Configuration 2 :=
  (configurationProductEquiv i).symm (X,(twoElectronSpectatorPositionEquiv i).symm T)

def pairKSPhysicalCoordinates (X T : Position) : Configuration 2 :=
  pairCoordinates (X,pairCenterEquiv.symm T)

def PhysicalKSAnalyticDescentOnPhysicalNeighborhood
    (f : Space (Fin 3) → ℂ) (g : Position → Position → ℂ)
    (t0 : Position) (M A : ℝ) : Prop :=
  ∃ r : ℝ≥0, 0<r ∧ (r : ℝ)=min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹ ∧
    ∀ X T : Position,
      ‖X‖ < min ((r : ℝ)^2) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ →
      ‖T‖ < (r : ℝ) →
      g X (t0+T) =
        physicalKSAnalyticDescentA f t0 (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))) +
        (‖X‖ : ℂ)*physicalKSAnalyticDescentB f t0
          (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ)))

theorem physicalKSAnalyticDescent_descend_surjective
    {f : Space (Fin 3) → ℂ} {g : Position → Position → ℂ} {t0 : Position} {M A : ℝ}
    (hA : 1≤A) (hid : PhysicalKSAnalyticDescentIdentityOnTaylorBall f t0 M A)
    (hlift : ∀ Y T, f (Y,T)=g (ksMap Y) T) :
    PhysicalKSAnalyticDescentOnPhysicalNeighborhood f g t0 M A := by
  obtain ⟨r,hr,he,hid⟩ := hid
  refine ⟨r,hr,he,?_⟩
  intro X T hX hT
  have hrR : (0 : ℝ)<r := hr
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  obtain ⟨Y,hYX,hnY⟩ := ksMap_exists_preimage_with_norm X
  have hnYlt : ‖Y‖ < (r : ℝ) := by
    have h := hX.trans_le (min_le_left _ _)
    nlinarith [norm_nonneg Y]
  have hq : (Y,T) ∈ Metric.eball (0 : Space (Fin 3)) (r : ℝ≥0∞) := by
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right,Prod.norm_def]
    exact max_lt hnYlt hT
  have hXsup : ‖(fun i : Fin 3 => (X i : ℂ))‖ ≤ ‖X‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr
    intro i
    simpa only [Complex.norm_real] using PiLp.norm_apply_le X i
  have hTsup : ‖(fun i : Fin 3 => (T i : ℂ))‖ ≤ ‖T‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).mpr
    intro i
    simpa only [Complex.norm_real] using PiLp.norm_apply_le T i
  have hrad : (32*(7*physicalKSPointwiseRate M A)^2)*
      ‖fun i : Fin 3 => (ksMap Y i : ℂ)‖<1 := by
    rw [hYX]
    have hlt := hXsup.trans_lt (hX.trans_le (min_le_right _ _))
    calc
      _ < (32*(7*physicalKSPointwiseRate M A)^2)*(32*(7*physicalKSPointwiseRate M A)^2)⁻¹ :=
        mul_lt_mul_of_pos_left hlt hD
      _ = 1 := mul_inv_cancel₀ hD.ne'
  have hspec : (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => (T i : ℂ)‖<1 := by
    have hlt := hTsup.trans_lt (hT.trans_le (he ▸ min_le_right _ _))
    calc
      _ < (7*physicalKSPointwiseRate M A)*(7*physicalKSPointwiseRate M A)⁻¹ :=
        mul_lt_mul_of_pos_left hlt hS
      _ = 1 := mul_inv_cancel₀ hS.ne'
  have h := hid (Y,T) hq hrad hspec
  have hadd : ((0,t0) : Space (Fin 3))+(Y,T) = (Y,t0+T) := by simp
  rw [hadd] at h
  rw [hlift,hYX,hnY] at h
  exact h

theorem nuclearKSPhysicalAnalyticDescent_physical_neighborhood
    (g : Configuration 2 → ℂ) (i : Fin 2) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSAnalyticDescentOnPhysicalNeighborhood
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (fun X T => g (nuclearKSPhysicalCoordinates i X T)) t0 M A := by
  apply physicalKSAnalyticDescent_descend_surjective hA
    (nuclearKSPhysicalAnalyticDescent_identity g i hdata hA hF0)
  intro Y T
  rfl

theorem pairKSPhysicalAnalyticDescent_physical_neighborhood
    (g : Configuration 2 → ℂ) {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    PhysicalKSAnalyticDescentOnPhysicalNeighborhood
      ((g ∘ pairKSLift) ∘ (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      (fun X T => g (pairKSPhysicalCoordinates X T)) t0 M A := by
  apply physicalKSAnalyticDescent_descend_surjective hA
    (pairKSPhysicalAnalyticDescent_identity g hdata hA hF0)
  intro Y T
  rfl

end TheoremT.Continuum
