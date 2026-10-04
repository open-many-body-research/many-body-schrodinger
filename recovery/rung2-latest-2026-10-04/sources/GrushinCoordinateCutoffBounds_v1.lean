import WeakGrushinCutoffNormCoefficients_v1

/-! Explicit dimension dependence of cutoff coefficients, from coordinate
derivative bounds in the actual product space. No norm equivalence constant
is silently suppressed. The spectator count is card kappa and the Y count is4. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoffGradientWeight_coordinate_bound {c : ℝ} (hc : 0 ≤ c)
    (L R : ℝ) (χ : Space κ → ℝ)
    (hY : ∀ p i, |fderiv ℝ χ p (yDir i)| ≤ L)
    (hT : ∀ p j, |fderiv ℝ χ p (tDir j)| ≤ L)
    (hR : ∀ p ∈ tsupport χ, ‖p.1‖ ≤ R) :
    ∀ p, cutoffGradientWeight c χ p ≤ (4+c*R^2*(Fintype.card κ : ℝ))*L^2 := by
  intro p
  have hy : (∑ i : Fin 4, (fderiv ℝ χ p (yDir i))^2) ≤ 4*L^2 := by
    calc
      _ ≤ ∑ i : Fin 4, L^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hY p i) 2)
      _ = _ := by simp
  have ht : (∑ j : κ, (fderiv ℝ χ p (tDir j))^2) ≤ (Fintype.card κ : ℝ)*L^2 := by
    calc
      _ ≤ ∑ j : κ, L^2 := Finset.sum_le_sum (fun j _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hT p j) 2)
      _ = _ := by simp
  by_cases hp : p ∈ tsupport χ
  · have hR2 := pow_le_pow_left₀ (norm_nonneg _) (hR p hp) 2
    have hcR : c*‖p.1‖^2 ≤ c*R^2 := mul_le_mul_of_nonneg_left hR2 hc
    calc
      _ ≤ 4*L^2+(c*‖p.1‖^2)*((Fintype.card κ : ℝ)*L^2) :=
        add_le_add hy (mul_le_mul_of_nonneg_left ht (by positivity))
      _ ≤ 4*L^2+(c*R^2)*((Fintype.card κ : ℝ)*L^2) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcR
          (by positivity : 0 ≤ (Fintype.card κ : ℝ)*L^2))
      _ = _ := by ring
  · rw [cutoffGradientWeight_eq_grushinCutoffWeight,grushinCutoffWeight_zero_off_support c χ hp]
    positivity

theorem combinedCutoffScalar_coordinate_bound {c : ℝ} (hc : 0 ≤ c)
    (L R : ℝ) (hL : 0 ≤ L) (χ : Space κ → ℝ)
    (hY : ∀ p i, |fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i)| ≤ L)
    (hT : ∀ p j, |fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j)| ≤ L)
    (hR : ∀ p ∈ tsupport χ, ‖p.1‖ ≤ R) :
    ∀ p, |combinedCutoffScalar c χ p| ≤ (4+c*R^2*(Fintype.card κ : ℝ))*L := by
  have hy : ∀ p, |∑ i : Fin 4, fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i)| ≤ 4*L := by
    intro p
    calc
      _ ≤ ∑ i : Fin 4, |fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 4, L := Finset.sum_le_sum (fun i _ => hY p i)
      _ = _ := by simp
  have ht : ∀ p, |∑ j : κ, fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j)| ≤
      (Fintype.card κ : ℝ)*L := by
    intro p
    calc
      _ ≤ ∑ j : κ, |fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : κ, L := Finset.sum_le_sum (fun j _ => hT p j)
      _ = _ := by simp
  intro p
  have hb := combinedCutoffScalar_explicit_bound hc (4*L) ((Fintype.card κ : ℝ)*L) R
    (by positivity) (by positivity) χ hy ht hR p
  convert hb using 1 <;> ring

#print axioms cutoffGradientWeight_coordinate_bound
#print axioms combinedCutoffScalar_coordinate_bound
end TheoremT.Continuum.WeakGrushin
