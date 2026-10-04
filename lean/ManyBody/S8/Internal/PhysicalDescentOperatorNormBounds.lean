import ManyBody.S8.Internal.HomogeneousSpectatorMixedBounds
import ManyBody.S8.Internal.AnisotropicPhysicalDerivativeBounds
import ManyBody.S8.Internal.PhysicalOriginalCollisionDerivativeBudget
/-! Full Frechet operator norms of the literal physical A/B series, derived
from actual Taylor coefficients and balanced KS support. Generic balance is
explicit; the physical nuclear and pair consumers discharge it. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin MixedAnalytic

theorem blockDirectionWeight_le_max_norm (D S : ℝ) (hD : 0≤D) (hS : 0≤S)
    (z : Fin 3 ⊕ Fin 3 → ℂ) : blockDirectionWeight D S z≤max D S*‖z‖ := by
  have hleft : ‖fun i : Fin 3 => z (.inl i)‖≤‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    exact norm_le_pi_norm z (.inl i)
  have hright : ‖fun i : Fin 3 => z (.inr i)‖≤‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    exact norm_le_pi_norm z (.inr i)
  apply max_le
  · exact (mul_le_mul_of_nonneg_left hleft hD).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  · exact (mul_le_mul_of_nonneg_left hright hS).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg z))

theorem homogeneous_spectator_sum_operator_norm_bound
    (P : ℕ → (Fin 3 → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous m)
    {B D S : ℝ} (hB : 0≤B) (hD : 0<D) (hS : 0<S)
    (hL : ∀ m γ, polynomialCoeffL1 (P m γ)≤B*D^m*S^(∑ i,γ i))
    (z : Fin 3 ⊕ Fin 3 → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖≤1/4)
    (hT : S*‖fun i : Fin 3 => z (.inr i)‖≤1/4) (n : ℕ) :
    ‖iteratedFDeriv ℂ n (homogeneousSpectatorSum P) z‖≤
      16*B*(4*max D S)^n*(n.factorial:ℝ) := by
  have hmax : 0≤max D S := hD.le.trans (le_max_left _ _)
  apply (iteratedFDeriv ℂ n (homogeneousSpectatorSum P) z).opNorm_le_bound (by positivity)
  intro v
  have hb := homogeneous_spectator_sum_mixed_derivative_bound P hP hB hD hS hL hX hT n v
  calc
    _≤16*B*4^n*(n.factorial:ℝ)*∏ i,max D S*‖v i‖ := by
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.prod_le_prod₀
      · intro i _
        exact (mul_nonneg hD.le (norm_nonneg _)).trans (le_max_left _ _)
      · intro i _
        exact blockDirectionWeight_le_max_norm D S hD.le hS.le (v i)
    _=(16*B*(4*max D S)^n*(n.factorial:ℝ))*∏ i,‖v i‖ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]
      ring

def physicalKSDescentOperatorBudget (M A F0 W : ℝ) (n : ℕ) : ℝ :=
  (16*physicalKSPointwiseAmplitude M A F0 W)*
    (4*max (32*(7*physicalKSPointwiseRate M A)^2) (7*physicalKSPointwiseRate M A))^n*
    (n.factorial:ℝ)

theorem physicalKSDescentOperatorBudget_nonneg {M A F0 W : ℝ}
    (hA : 1≤A) (hF0 : 0≤F0) (n : ℕ) :
    0≤physicalKSDescentOperatorBudget M A F0 W n := by
  have hP := physicalKSPointwiseAmplitude_nonneg (M:=M) (W:=W) hA hF0
  have hS := physicalKSPointwiseRate_pos (M:=M) hA
  dsimp [physicalKSDescentOperatorBudget]
  positivity

theorem physicalKSDescentOperatorBudget_original_norm (ψ : SpinSpace 2)
    (M A Csrc CH12 : ℝ) (hCH12 : 0≤CH12) (n : ℕ) :
    physicalKSDescentOperatorBudget M A (Csrc*‖ψ‖) (CH12*‖ψ‖^2) n=
      physicalKSDescentOperatorBudget M A Csrc CH12 n*‖ψ‖ := by
  unfold physicalKSDescentOperatorBudget
  rw [physicalKSPointwiseAmplitude_original_norm ψ M A Csrc CH12 hCH12]
  ring

theorem physical_descent_operator_norm_of_balanced
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hbal : ∀ m γ e, e∈(ksRealPolynomialToSpinor
      (physicalKSTaylorEvenSpectatorFamily f (0,t0) m γ)).support → e 0+e 1=e 2+e 3)
    (p : Position × Position)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖p.1‖≤1/4)
    (hT : (7*physicalKSPointwiseRate M A)*‖p.2-t0‖≤1/4) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (physicalDescentAReal f t0) p‖≤
      physicalKSDescentOperatorBudget M A F0 W n ∧
    ‖iteratedFDeriv ℝ n (physicalDescentBReal f t0) p‖≤
      (32*(7*physicalKSPointwiseRate M A)^2)*physicalKSDescentOperatorBudget M A F0 W n := by
  let D : ℝ := 32*(7*physicalKSPointwiseRate M A)^2
  let S : ℝ := 7*physicalKSPointwiseRate M A
  let P : ℝ := physicalKSPointwiseAmplitude M A F0 W
  let z := physicalComplexCoordinatesAt t0 p
  have hS : 0<S := mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0<D := by dsimp [D]; positivity
  have hP : 0≤P := physicalKSPointwiseAmplitude_nonneg hA hF0
  have hXc : D*‖fun i : Fin 3 => z (.inl i)‖≤1/4 :=
    (mul_le_mul_of_nonneg_left (physicalComplexCoordinatesCLM_left_norm_le (p.1,p.2-t0)) hD.le).trans hX
  have hTc : S*‖fun i : Fin 3 => z (.inr i)‖≤1/4 :=
    (mul_le_mul_of_nonneg_left (physicalComplexCoordinatesCLM_right_norm_le (p.1,p.2-t0)) hS.le).trans hT
  obtain ⟨hFA,hFB,_,hLA,hLB⟩ := ks_real_spectator_series_data
    (physicalKSTaylorEvenSpectatorFamily f (0,t0))
    (physicalKSTaylorEvenSpectatorFamily_homogeneous f (0,t0)) hbal hP hS.le hS.le
    (fun m γ e _ => physicalKSTaylorEvenSpectatorFamily_coeff_bound hdata hA hF0 m γ e)
  have hLB' : ∀ m γ, polynomialCoeffL1
      (ksRealSpectatorFamilyB (physicalKSTaylorEvenSpectatorFamily f (0,t0)) m γ)≤
        (P*D)*D^m*S^(∑ i,γ i) := by
    intro m γ
    apply (hLB m γ).trans_eq
    change P*D^(m+1)*S^(∑ i,γ i)=(P*D)*D^m*S^(∑ i,γ i)
    rw [pow_succ]
    ring
  have hca := homogeneous_spectator_sum_operator_norm_bound _ hFA hP hD hS hLA z hXc hTc n
  have hcb := homogeneous_spectator_sum_operator_norm_bound _ hFB (mul_nonneg hP hD.le)
    hD hS hLB' z hXc hTc n
  obtain ⟨hanA,hanB⟩ := physicalKSAnalyticDescent_analytic_of_balanced hdata hA hF0 hbal
  have hmem : D*‖fun i : Fin 3 => z (.inl i)‖<1 ∧ S*‖fun i : Fin 3 => z (.inr i)‖<1 :=
    ⟨lt_of_le_of_lt hXc (by norm_num),lt_of_le_of_lt hTc (by norm_num)⟩
  constructor
  · apply (physical_centered_iteratedFDeriv_norm_le_complex t0 (hanA z hmem) n).trans
    exact hca
  · apply (physical_centered_iteratedFDeriv_norm_le_complex t0 (hanB z hmem) n).trans
    convert hcb using 1 <;> first | rfl | dsimp [physicalKSDescentOperatorBudget,D,S,P]; ring

#print axioms homogeneous_spectator_sum_operator_norm_bound
#print axioms physicalKSDescentOperatorBudget_original_norm
#print axioms physical_descent_operator_norm_of_balanced
end ManyBody.S8