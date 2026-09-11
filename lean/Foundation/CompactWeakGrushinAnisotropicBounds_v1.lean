import ProductCompactWeakDirectionalEnergy_v1
import CompactWeakGrushinOutputEstimates_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_weakH2_anisotropic_output_bounds {c : ℝ} (hc : 0 < c)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ((∑ i : Fin 4, ‖d (yDir i)‖^2) ≤ 2*‖f‖^2+(3/4 : ℝ)*‖h‖^2) ∧
    ((∑ j : κ, ‖d (tDir j)‖^2) ≤ ‖h‖^2/(16*c)) ∧
    ((∑ i : Fin 4, ∑ j : Fin 4, ‖e (yDir i) (yDir j)‖^2) ≤ (3/2 : ℝ)*‖h‖^2) := by
  obtain ⟨_,hT,hFull⟩ := compact_weakH2_output_estimates hc.le d e hd he hK hs hP
  have hMix : 0 ≤ 2*c*(∑ i : Fin 4, ∑ j : κ,
      ∫ p, ‖p.1‖^2 * ‖e (yDir i) (tDir j) p‖^2) := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))))
  have hW : 0 ≤ ∫ p, ‖tWeighted c e p‖^2 := integral_nonneg (fun p => sq_nonneg _)
  have hYY : (∑ i : Fin 4, ∑ j : Fin 4, ‖e (yDir i) (yDir j)‖^2) ≤
      (3/2 : ℝ)*‖h‖^2 := by
    simp_rw [← l2_norm_sq_integral] at hFull
    linarith
  have hD : (∑ i : Fin 4, ‖d (yDir i)‖^2) ≤
      2*‖f‖^2 + (1/2 : ℝ)*(∑ i : Fin 4, ‖e (yDir i) (yDir i)‖^2) := by
    have hx := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      product_compact_weak_directional_half_square_bound (hd (yDir i)) (he (yDir i) (yDir i)) hK hs)
    simp only [add_div,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,← Finset.sum_div] at hx
    norm_num at hx
    linarith
  have hDiag : (∑ i : Fin 4, ‖e (yDir i) (yDir i)‖^2) ≤
      ∑ i : Fin 4, ∑ j : Fin 4, ‖e (yDir i) (yDir j)‖^2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum (f := fun j : Fin 4 => ‖e (yDir i) (yDir j)‖^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  refine ⟨by nlinarith,?_,hYY⟩
  apply (le_div_iff₀ (by positivity : 0 < 16*c)).mpr
  simpa only [← l2_norm_sq_integral,mul_comm] using hT

#print axioms compact_weakH2_anisotropic_output_bounds
end TheoremT.Continuum.WeakGrushin
