import GrushinFactorialSpectatorWeightedL2_v1
import WeakGrushinCutoffNormSupport_v1

/-! The actual raw cutoff error underlying the factorial commutator.
It is the negative of [P_c,chi] when the input first components are the
corresponding weak derivatives. No derivative relation is assumed merely
to define or bound this finite expression. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

def rawGrushinCutoffError (c : ℝ) (χ : Space (Fin 3) → ℝ)
    (f : Space (Fin 3) → ℂ) (gy : Fin 4 → Space (Fin 3) → ℂ)
    (gt : Fin 3 → Space (Fin 3) → ℂ) (p : Space (Fin 3)) : ℂ :=
  (∑ i : Fin 4, fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i) • f p) +
    (2 : ℝ) • (∑ i : Fin 4, fderiv ℝ χ p (yDir i) • gy i p) +
    (∑ j : Fin 3, (c*‖p.1‖^2) • (fderiv ℝ
      (fun q => fderiv ℝ χ q (tDir j)) p (tDir j) • f p)) +
    (2 : ℝ) • (∑ j : Fin 3, (c*‖p.1‖^2) • (fderiv ℝ χ p (tDir j) • gt j p))

theorem rawGrushinCutoffError_eq_combined (c : ℝ) (χ : Space (Fin 3) → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) :
    rawGrushinCutoffError c χ f (fun i => d (yDir i)) (fun j => d (tDir j)) =
      combinedCutoffError c χ f d := by
  funext p
  simp only [rawGrushinCutoffError,combinedCutoffError,cutoffYError,cutoffTError,
    Finset.sum_add_distrib,mul_smul,← Finset.sum_smul,← Finset.smul_sum,smul_add]
  module

theorem lp_four_blocks_ae {μ : Measure (Space (Fin 3))}
    (A B C D : Lp ℂ 2 μ) (a b c d : Space (Fin 3) → ℂ)
    (hA : A =ᵐ[μ] a) (hB : B =ᵐ[μ] b) (hC : C =ᵐ[μ] c) (hD : D =ᵐ[μ] d) :
    (A+(2 : ℝ) • B+C+(2 : ℝ) • D) =ᵐ[μ]
      (fun p => a p+(2 : ℝ) • b p+c p+(2 : ℝ) • d p) := by
  filter_upwards [hA,hB,hC,hD,
    Lp.coeFn_add (A+(2 : ℝ) • B+C) ((2 : ℝ) • D),
    Lp.coeFn_add (A+(2 : ℝ) • B) C,Lp.coeFn_add A ((2 : ℝ) • B),
    Lp.coeFn_smul (2 : ℝ) B,Lp.coeFn_smul (2 : ℝ) D] with p ha hb hc hd h3 h2 h1 hsB hsD
  simp only [Pi.add_apply,Pi.smul_apply] at *
  rw [h3,h2,h1,hsB,hsD,ha,hb,hc,hd]

theorem lp_four_blocks_norm {μ : Measure (Space (Fin 3))} (A B C D : Lp ℂ 2 μ) :
    ‖A+(2 : ℝ) • B+C+(2 : ℝ) • D‖ ≤ ‖A‖+2*‖B‖+‖C‖+2*‖D‖ := by
  have h1 := norm_add_le A ((2 : ℝ) • B)
  have h2 := norm_add_le (A+(2 : ℝ) • B) C
  have h3 := norm_add_le (A+(2 : ℝ) • B+C) ((2 : ℝ) • D)
  simp only [norm_smul,Real.norm_eq_abs,show |(2 : ℝ)| = 2 by norm_num] at h1 h3
  linarith

theorem factorial_raw_cutoff_error_L2 (a : Space (Fin 3)) (ha : a.1 = 0) (c : ℝ)
    {aY aT ρ s e C1 C2 : ℝ} (he : 0 < e) (hse : s+e ≤ ρ) (hρ : ρ < aY)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {μ : Measure (Space (Fin 3))} (f : Space (Fin 3) → ℂ)
    (gy : Fin 4 → Space (Fin 3) → ℂ) (gt : Fin 3 → Space (Fin 3) → ℂ)
    (hf : AEStronglyMeasurable f μ) (hgy : ∀ i, AEStronglyMeasurable (gy i) μ)
    (w0 : Fin 4 → Lp ℂ 2 μ)
    (wy : Fin 4 → Fin 4 → Lp ℂ 2 μ) (wt : Fin 3 → Fin 4 → Lp ℂ 2 μ)
    (hw0 : ∀ l, w0 l =ᵐ[μ] (fun p => (p.1 l)^2 • f p))
    (hwy : ∀ i l, wy i l =ᵐ[μ] (fun p => (p.1 l)^2 • gy i p))
    (hwt : ∀ j l, wt j l =ᵐ[μ] (fun p => (p.1 l)^2 • gt j p))
    (N1 N2 : ℝ) (hw0n : (∑ l, ‖w0 l‖) ≤ N2)
    (hwyn : ∀ i, (∑ l, ‖wy i l‖) ≤ N1) (hwtn : ∀ j, (∑ l, ‖wt j l‖) ≤ N1) :
    ∃ H : Lp ℂ 2 μ,
      H =ᵐ[μ] rawGrushinCutoffError c (factorialRectCutoff a aY aT s e) f gy gt ∧
      ‖H‖ ≤ (((8/3 : ℝ)*C1)/e)*(8/(aY-ρ)^2+6*|c|)*N1+
        (((32/9 : ℝ)*(C2+C1^2))/e^2)*(4/(aY-ρ)^2+3*|c|)*N2 := by
  let K1 : ℝ := ((8/3 : ℝ)*C1)/e
  let K2 : ℝ := ((32/9 : ℝ)*(C2+C1^2))/e^2
  let k : ℝ := aY-ρ
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp [K2]; positivity
  choose Y0 hY0 hY0n using fun i : Fin 4 =>
    factorial_y_second_weighted_L2 a ha he hse hρ hC1 hC2 hf i w0 hw0
  choose Y1 hY1 hY1n using fun i : Fin 4 =>
    factorial_y_first_weighted_L2 a ha he hse hρ hC1 hC2 (hgy i) i (wy i) (hwy i)
  choose T0 hT0 hT0n using fun j : Fin 3 =>
    factorial_t_second_weighted_L2 a aY aT s c he hC1 hC2 j w0 hw0
  choose T1 hT1 hT1n using fun j : Fin 3 =>
    factorial_t_first_weighted_L2 a aY aT s c he hC1 hC2 j (wt j) (hwt j)
  let A : Lp ℂ 2 μ := ∑ i, Y0 i
  let B : Lp ℂ 2 μ := ∑ i, Y1 i
  let C : Lp ℂ 2 μ := ∑ j, T0 j
  let D : Lp ℂ 2 μ := ∑ j, T1 j
  have hA : A =ᵐ[μ] (fun p => ∑ i : Fin 4, fderiv ℝ
      (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (yDir i)) p (yDir i) • f p) :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun i _ => hY0 i))
  have hB : B =ᵐ[μ] (fun p => ∑ i : Fin 4,
      fderiv ℝ (factorialRectCutoff a aY aT s e) p (yDir i) • gy i p) :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun i _ => hY1 i))
  have hC : C =ᵐ[μ] (fun p => ∑ j : Fin 3, (c*‖p.1‖^2) • (fderiv ℝ
      (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (tDir j)) p (tDir j) • f p)) :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun j _ => hT0 j))
  have hD : D =ᵐ[μ] (fun p => ∑ j : Fin 3, (c*‖p.1‖^2) •
      (fderiv ℝ (factorialRectCutoff a aY aT s e) p (tDir j) • gt j p)) :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun j _ => hT1 j))
  have hAn : ‖A‖ ≤ 4*(K2/k^2*N2) := by
    calc
      ‖A‖ ≤ ∑ i, ‖Y0 i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, K2/k^2*N2 := Finset.sum_le_sum (fun i _ =>
        (hY0n i).trans (mul_le_mul_of_nonneg_left hw0n (by positivity)))
      _ = _ := by simp
  have hBn : ‖B‖ ≤ 4*(K1/k^2*N1) := by
    calc
      ‖B‖ ≤ ∑ i, ‖Y1 i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, K1/k^2*N1 := Finset.sum_le_sum (fun i _ =>
        (hY1n i).trans (mul_le_mul_of_nonneg_left (hwyn i) (by positivity)))
      _ = _ := by simp
  have hCn : ‖C‖ ≤ 3*(|c| * K2*N2) := by
    calc
      ‖C‖ ≤ ∑ j, ‖T0 j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, |c| * K2*N2 := Finset.sum_le_sum (fun j _ =>
        (hT0n j).trans (mul_le_mul_of_nonneg_left hw0n (by positivity)))
      _ = _ := by simp
  have hDn : ‖D‖ ≤ 3*(|c| * K1*N1) := by
    calc
      ‖D‖ ≤ ∑ j, ‖T1 j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, |c| * K1*N1 := Finset.sum_le_sum (fun j _ =>
        (hT1n j).trans (mul_le_mul_of_nonneg_left (hwtn j) (by positivity)))
      _ = _ := by simp
  refine ⟨A+(2 : ℝ) • B+C+(2 : ℝ) • D,lp_four_blocks_ae A B C D _ _ _ _ hA hB hC hD,?_⟩
  calc
    _ ≤ ‖A‖+2*‖B‖+‖C‖+2*‖D‖ := lp_four_blocks_norm A B C D
    _ ≤ 4*(K2/k^2*N2)+2*(4*(K1/k^2*N1))+3*(|c| * K2*N2)+2*(3*(|c| * K1*N1)) := by
      linarith
    _ = _ := by dsimp [K1,K2,k]; ring

end TheoremT.Continuum.WeakGrushin
