import NonlinearFieldL2_v1
import HardyLaplacianCore_v1
import Mathlib.Analysis.Calculus.MeanValue

/-! Identify the real C1 chain rule with the project's unchanged weak derivative
predicate on compact smooth inputs. Complex-valued functions are treated as
two real components, not assumed holomorphic. -/
noncomputable section
open MeasureTheory
open scoped ContDiff NNReal
namespace TheoremT.Continuum
set_option maxHeartbeats 800000

theorem boundedC1_lipschitz (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (K : ℝ≥0) (hb : ∀ z, ‖fderiv ℝ F z‖ ≤ K) : LipschitzWith K F :=
  lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by norm_num))
    (fun z => by exact_mod_cast hb z)

theorem weakPartial_compact_C1_chain {N : ℕ} (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (h0 : F 0 = 0) (K : ℝ≥0) (hb : ∀ z, ‖fderiv ℝ F z‖ ≤ K)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (g d : SpatialL2 N) (k : Coordinate N)
    (hgu : (g : Configuration N → ℂ) =ᵐ[volume] u)
    (hdu : (d : Configuration N → ℂ) =ᵐ[volume] smoothPartial u k) :
    WeakPartial ((boundedC1_lipschitz F hF K hb).compLp h0 g)
      (nonlinearFieldL2 (fderiv ℝ F) (hF.continuous_fderiv (by norm_num)) K hb g d) k := by
  let hL := boundedC1_lipschitz F hF K hb
  let A := fderiv ℝ F
  have hA : Continuous A := hF.continuous_fderiv (by norm_num)
  have hv : MemLp (F ∘ u) 2 volume :=
    hL.comp_memLp h0 (hu.continuous.memLp_of_hasCompactSupport hc)
  have hder (x : Configuration N) :
      fderiv ℝ (F ∘ u) x (coordinateVector k) = A (u x) (smoothPartial u k x) := by
    rw [fderiv_comp x (hF.differentiable (by norm_num) (u x))
      (hu.differentiable (by simp) x)]
    rfl
  have hdeq : (fun x => A (g x) (d x)) =ᵐ[volume]
      (fun x => fderiv ℝ (F ∘ u) x (coordinateVector k)) := by
    filter_upwards [hgu,hdu] with x hgx hdx
    rw [hder,hgx,hdx]
  have he : MemLp (fun x => fderiv ℝ (F ∘ u) x (coordinateVector k)) 2 volume :=
    (nonlinearField_memLp A hA K hb g d).ae_eq hdeq
  have hvg : hv.toLp (F ∘ u) = hL.compLp h0 g := by
    apply Lp.ext
    filter_upwards [hv.coeFn_toLp,hL.coeFn_compLp h0 g,hgu] with x h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1,h2,h3]
  have hed : he.toLp (fun x => fderiv ℝ (F ∘ u) x (coordinateVector k)) =
      nonlinearFieldL2 A hA K hb g d := by
    apply Lp.ext
    filter_upwards [he.coeFn_toLp,nonlinearFieldL2_ae A hA K hb g d,hdeq]
      with x h1 h2 h3
    rw [h1,h2,h3]
  have hw := classicalDerivative_to_WeakPartial (hF.comp (hu.of_le (by simp))) k hv he
  rw [hvg,hed] at hw
  exact hw

#print axioms boundedC1_lipschitz
#print axioms weakPartial_compact_C1_chain
end TheoremT.Continuum
