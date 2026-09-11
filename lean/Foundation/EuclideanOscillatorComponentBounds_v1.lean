import EuclideanOscillatorSquare_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compact_euclidean_oscillator_component_bounds {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {a : ℝ} (ha : 0 ≤ a) :
    (Fintype.card ι : ℝ)*((∫ x,‖oscillatorLaplacian u x‖^2)+a^4*(∫ x,‖x‖^4*‖u x‖^2)) ≤
      ((Fintype.card ι : ℝ)+2)*(∫ x,‖euclideanOscillator a u x‖^2) ∧
    (Fintype.card ι : ℝ)*2*a^2*(∫ x,‖x‖^2*(∑ k : ι,‖oscillatorPartial u k x‖^2)) ≤
      ((Fintype.card ι : ℝ)+2)*(∫ x,‖euclideanOscillator a u x‖^2) := by
  have he := compact_euclidean_oscillator_norm_square a hu hc
  have hb := compact_euclidean_oscillator_integral_lower hu hc ha
  have hd : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hG : (0:ℝ) ≤ ∫ x,‖x‖^2*(∑ k : ι,‖oscillatorPartial u k x‖^2) :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun k _ => sq_nonneg _)))
  have hL : (0:ℝ) ≤ ∫ x,‖oscillatorLaplacian u x‖^2 := integral_nonneg (fun x => sq_nonneg _)
  have hW : (0:ℝ) ≤ ∫ x,‖x‖^4*‖u x‖^2 :=
    integral_nonneg (fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 4) (sq_nonneg _))
  have hGd := mul_nonneg (mul_nonneg hd (sq_nonneg a)) hG
  have hLW := mul_nonneg hd (add_nonneg hL (mul_nonneg (pow_nonneg ha 4) hW))
  have hed := congrArg (fun t : ℝ => (Fintype.card ι : ℝ)*t) he
  constructor <;> nlinarith only [hed,hb,hGd,hLW]

theorem compact_four_dimensional_oscillator_component_bounds {u : EuclideanSpace ℝ (Fin 4) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,‖oscillatorLaplacian u x‖^2)+a^4*(∫ x,‖x‖^4*‖u x‖^2) ≤
      (3/2:ℝ)*(∫ x,‖euclideanOscillator a u x‖^2) ∧
    2*a^2*(∫ x,‖x‖^2*(∑ k : Fin 4,‖oscillatorPartial u k x‖^2)) ≤
      (3/2:ℝ)*(∫ x,‖euclideanOscillator a u x‖^2) := by
  obtain ⟨h1,h2⟩ := compact_euclidean_oscillator_component_bounds hu hc ha
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at h1 h2
  constructor <;> nlinarith only [h1,h2]

#print axioms compact_euclidean_oscillator_component_bounds
#print axioms compact_four_dimensional_oscillator_component_bounds
end TheoremT.Continuum
