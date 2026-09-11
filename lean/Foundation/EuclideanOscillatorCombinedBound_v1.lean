import EuclideanOscillatorComponentBounds_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compact_euclidean_oscillator_combined_bound {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {a : ℝ} (ha : 0 ≤ a) :
    (Fintype.card ι : ℝ)*((∫ x,‖oscillatorLaplacian u x‖^2)+
      a^4*(∫ x,‖x‖^4*‖u x‖^2)+
      2*a^2*(∫ x,‖x‖^2*(∑ k : ι,‖oscillatorPartial u k x‖^2))) ≤
      ((Fintype.card ι : ℝ)+2)*(∫ x,‖euclideanOscillator a u x‖^2) := by
  have he := compact_euclidean_oscillator_norm_square a hu hc
  have hb := compact_euclidean_oscillator_integral_lower hu hc ha
  have hed := congrArg (fun t : ℝ => (Fintype.card ι : ℝ)*t) he
  nlinarith only [hed,hb]

theorem compact_four_dimensional_oscillator_combined_bound {u : EuclideanSpace ℝ (Fin 4) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,‖oscillatorLaplacian u x‖^2)+a^4*(∫ x,‖x‖^4*‖u x‖^2)+
      2*a^2*(∫ x,‖x‖^2*(∑ k : Fin 4,‖oscillatorPartial u k x‖^2)) ≤
      (3/2:ℝ)*(∫ x,‖euclideanOscillator a u x‖^2) := by
  have h := compact_euclidean_oscillator_combined_bound hu hc ha
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at h
  nlinarith only [h]

#print axioms compact_euclidean_oscillator_combined_bound
#print axioms compact_four_dimensional_oscillator_combined_bound
end TheoremT.Continuum
