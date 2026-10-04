import ManyBody.S8.Internal.BinomialSeriesMixedBounds
import ManyBody.S8.Internal.AnisotropicCoordinateScaling
import ManyBody.S8.Internal.CoordinateWordFactorials
import SpectatorScalingMap_v1
import Mathlib.Tactic
/-! Explicit mixed Frechet derivative bounds for the literal double-index
homogeneous/spectator sum. The proof normalizes the two actual coefficient
rates, identifies the original sum with its grouped multilinear series on
a neighborhood, and transports the actual Frechet derivatives through the
inverse coordinate scaling. -/
noncomputable section
open scoped BigOperators Topology
namespace ManyBody.S8.MixedAnalytic
open TheoremT.Continuum

theorem blockScalingCLM_eq_spectatorScalingMap (D S : ℝ)
    (z : Fin 3 ⊕ Fin 3 → ℂ) :
    blockScalingCLM D S z = spectatorScalingMap D S z := by
  ext i
  cases i <;> rfl

theorem homogeneous_spectator_sum_eq_multilinear_sum
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M : ℝ} (hM : 0 ≤ M)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M)
    {z : Fin 3 ⊕ Fin 3 → ℂ} (hz : ‖z‖ < 1) :
    (homogeneousPolynomialMultilinearSeries (groupedHomogeneousSpectatorPolynomial A)
      (groupedHomogeneousSpectatorPolynomial_isHomogeneous A hA)).sum z =
      homogeneousSpectatorSum A z := by
  rw [homogeneousPolynomialMultilinearSeries_sum]
  have hL' : ∀ m γ, polynomialCoeffL1 (A m γ) ≤
      M*(1:ℝ)^m*(1:ℝ)^(∑ i : Fin 3, γ i) := by simpa using hL
  have hbound := homogeneous_spectator_series_closed_polydiscs A hA hM
    zero_le_one (norm_nonneg z) zero_le_one (norm_nonneg z)
    (by simpa using hz) (by simpa using hz) hL'
  have hmem : ((fun i : Fin 3 => z (.inl i)),(fun i : Fin 3 => z (.inr i))) ∈
      complexClosedPolydisc (Fin 3) ‖z‖ ×ˢ complexClosedPolydisc (Fin 3) ‖z‖ :=
    ⟨fun i => norm_le_pi_norm z (.inl i), fun i => norm_le_pi_norm z (.inr i)⟩
  have hs := (hbound.1 _ hmem).2.1
  have heq := groupedHomogeneousSpectatorPolynomial_tsum_eq A
    (fun i : Fin 3 => z (.inl i)) (fun i : Fin 3 => z (.inr i)) hs
  have hzeta : Sum.elim (fun i : Fin 3 => z (.inl i))
      (fun i : Fin 3 => z (.inr i)) = z := by
    ext i
    cases i <;> rfl
  simpa only [hzeta, homogeneousSpectatorSum, homogeneousSpectatorTerm] using heq

theorem homogeneous_spectator_sum_mixed_derivative_bound
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D S : ℝ} (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin 3, γ i))
    {z : Fin 3 ⊕ Fin 3 → ℂ}
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hT : S*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4)
    (n : ℕ) (v : Fin n → (Fin 3 ⊕ Fin 3 → ℂ)) :
    ‖iteratedFDeriv ℂ n (homogeneousSpectatorSum A) z v‖ ≤
      16*M*4^n*(n.factorial : ℝ)*∏ i, blockDirectionWeight D S (v i) := by
  let A' := rescaledHomogeneousSpectatorFamily A D⁻¹ S⁻¹
  have hA' := rescaledHomogeneousSpectatorFamily_isHomogeneous A hA D⁻¹ S⁻¹
  have hL' : ∀ m γ, polynomialCoeffL1 (A' m γ) ≤ M := by
    have h := polynomialCoeffL1_rescaledHomogeneousSpectatorFamily A hM hD.le hS.le
      (inv_nonneg.mpr hD.le) (inv_nonneg.mpr hS.le)
      (by simp [ne_of_gt hD] : D*D⁻¹ ≤ 1)
      (by simp [ne_of_gt hS] : S*S⁻¹ ≤ 1) hL
    simpa using h
  let G := groupedHomogeneousSpectatorPolynomial A'
  have hG : ∀ n, (G n).IsHomogeneous n :=
    groupedHomogeneousSpectatorPolynomial_isHomogeneous A' hA'
  let p := homogeneousPolynomialMultilinearSeries G hG
  have hp : ∀ n, ‖p n‖ ≤ M*((n+3).choose 3 : ℝ) := by
    intro n
    apply (homogeneousPolynomialMultilinearSeries_norm G hG n).trans
    have h := polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial A'
      (M := M) (T := 1) (by simpa using hL') n
    simpa using h
  let e := blockScalingEquiv D S hD hS
  have hze : ‖e z‖ ≤ 1/4 :=
    blockScalingCLM_norm_quarter D S hD.le hS.le z hX hT
  have heq : (p.sum ∘ e) =ᶠ[𝓝 z] homogeneousSpectatorSum A := by
    have hn : ∀ᶠ w in 𝓝 z, ‖e w‖ < 1 :=
      (isOpen_lt (continuous_norm.comp e.continuous) continuous_const).mem_nhds
        (by change ‖e z‖ < 1; linarith)
    filter_upwards [hn] with w hw
    change p.sum (e w) = homogeneousSpectatorSum A w
    rw [homogeneous_spectator_sum_eq_multilinear_sum A' hA' hM hL' hw,
      homogeneousSpectatorSum_rescaling A hA D⁻¹ S⁻¹]
    congr 1
    ext i
    cases i <;> simp [spectatorScalingMap, e, blockScalingEquiv_apply,
      ne_of_gt hD, ne_of_gt hS]
  rw [← (heq.iteratedFDeriv ℂ n).eq_of_nhds]
  apply (iteratedFDeriv_sum_scaled_quarter_le p hM hp e hze n v).trans
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod₀
    · intro i _
      exact norm_nonneg _
    · intro i _
      exact blockScalingCLM_norm_le D S hD.le hS.le (v i)
  · positivity

#print axioms homogeneous_spectator_sum_eq_multilinear_sum
#print axioms homogeneous_spectator_sum_mixed_derivative_bound

theorem homogeneous_spectator_sum_coordinate_word_bound
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D S : ℝ} (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin 3, γ i))
    {z : Fin 3 ⊕ Fin 3 → ℂ}
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hT : S*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4)
    (n : ℕ) (word : Fin n → Fin 3 ⊕ Fin 3) :
    ‖iteratedFDeriv ℂ n (homogeneousSpectatorSum A) z
      (fun i => Pi.single (word i) (1:ℂ))‖ ≤
      16*M*(n.factorial : ℝ)*
        ∏ i, 4*(Sum.elim (fun _ : Fin 3 => D) (fun _ : Fin 3 => S) (word i)) := by
  have h := homogeneous_spectator_sum_mixed_derivative_bound A hA hM hD hS hL
    hX hT n (fun i => Pi.single (word i) (1:ℂ))
  simp_rw [blockDirectionWeight_single D S hD.le hS.le] at h
  convert h using 1
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

#print axioms homogeneous_spectator_sum_coordinate_word_bound


theorem homogeneous_spectator_sum_coordinate_multiFactorial_bound
    (A : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D S : ℝ} (hM : 0 ≤ M) (hD : 0 < D) (hS : 0 < S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin 3, γ i))
    {z : Fin 3 ⊕ Fin 3 → ℂ}
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hT : S*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4)
    (n : ℕ) (word : Fin n → Fin 3 ⊕ Fin 3) :
    ‖iteratedFDeriv ℂ n (homogeneousSpectatorSum A) z
      (fun i => Pi.single (word i) (1:ℂ))‖ ≤
      16*M*(∏ j, ((coordinateWordMultiplicity word j).factorial : ℝ))*
        ∏ i, 24*(Sum.elim (fun _ : Fin 3 => D) (fun _ : Fin 3 => S) (word i)) := by
  let rate := Sum.elim (fun _ : Fin 3 => D) (fun _ : Fin 3 => S)
  have hrate (j : Fin 3 ⊕ Fin 3) : 0 ≤ rate j := by
    cases j with
    | inl j => exact hD.le
    | inr j => exact hS.le
  have hn : (n.factorial : ℝ) ≤ (6:ℝ)^n*
      ∏ j, ((coordinateWordMultiplicity word j).factorial : ℝ) := by
    exact_mod_cast coordinate_word_factorial_bound word
  have hp : (∏ i, 24*rate (word i)) = (6:ℝ)^n*∏ i, 4*rate (word i) := by
    calc
      _ = ∏ i, 6*(4*rate (word i)) := by
        apply Finset.prod_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  apply (homogeneous_spectator_sum_coordinate_word_bound A hA hM hD hS hL
    hX hT n word).trans
  calc
    16*M*(n.factorial : ℝ)*∏ i, 4*rate (word i) ≤
        16*M*((6:ℝ)^n*∏ j, ((coordinateWordMultiplicity word j).factorial : ℝ))*
          ∏ i, 4*rate (word i) := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hrate (word i))))
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by rw [hp]; ring

#print axioms homogeneous_spectator_sum_coordinate_multiFactorial_bound

end ManyBody.S8.MixedAnalytic
