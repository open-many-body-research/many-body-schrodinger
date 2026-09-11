import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasureOnCompacts μ]

def compactPartialIntegral (G : Y × T → F) (y : Y) : F := ∫ t, G (y,t) ∂μ

def firstParameterFDeriv (G : Y × T → F) (p : Y × T) : Y →L[ℝ] F :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ Y T)

theorem compact_slice_hasCompactSupport {G : Y × T → F} (hc : HasCompactSupport G) (y : Y) :
    HasCompactSupport (fun t => G (y,t)) := by
  apply HasCompactSupport.intro (hc.isCompact.image continuous_snd)
  intro t ht
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact ht ⟨(y,t),hp,rfl⟩

theorem compact_slice_integrable {G : Y × T → F} (hG : Continuous G)
    (hc : HasCompactSupport G) (y : Y) : Integrable (fun t => G (y,t)) μ :=
  (hG.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (compact_slice_hasCompactSupport hc y)

theorem compactPartialIntegral_hasCompactSupport {G : Y × T → F} (hc : HasCompactSupport G) :
    HasCompactSupport (compactPartialIntegral (μ := μ) G) := by
  apply HasCompactSupport.intro (hc.isCompact.image continuous_fst)
  intro y hy
  have hz (t : T) : G (y,t)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hy ⟨(y,t),hp,rfl⟩
  simp only [compactPartialIntegral,hz,integral_zero]

theorem firstParameterFDeriv_contDiff {G : Y × T → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (firstParameterFDeriv G) :=
  (hG.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_comp contDiff_const

theorem firstParameterFDeriv_hasCompactSupport {G : Y × T → F} (hc : HasCompactSupport G) :
    HasCompactSupport (firstParameterFDeriv G) := by
  apply (hc.fderiv ℝ).mono
  intro p hp
  change fderiv ℝ G p ≠ 0
  intro hz
  exact hp (by simp [firstParameterFDeriv,hz])

theorem firstParameterFDeriv_hasFDerivAt {G : Y × T → F} (hG : ContDiff ℝ ∞ G)
    (y : Y) (t : T) : HasFDerivAt (fun x => G (x,t)) (firstParameterFDeriv G (y,t)) y := by
  have hpair : HasFDerivAt (fun x : Y => (x,t)) (ContinuousLinearMap.inl ℝ Y T) y := by
    have he : (ContinuousLinearMap.id ℝ Y).prod (0 : Y →L[ℝ] T) =
        ContinuousLinearMap.inl ℝ Y T := by ext x <;> rfl
    rw [← he]
    exact (hasFDerivAt_id y).prodMk (hasFDerivAt_const t y)
  exact ((hG.differentiable (by simp) (y,t)).hasFDerivAt).comp y hpair

#print axioms compact_slice_integrable
#print axioms compactPartialIntegral_hasCompactSupport
#print axioms firstParameterFDeriv_contDiff
#print axioms firstParameterFDeriv_hasCompactSupport
#print axioms firstParameterFDeriv_hasFDerivAt
end TheoremT.Continuum
