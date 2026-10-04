import ManyBody.S8.Internal.PhysicalCompactL2Domination
import ManyBody.S8.Internal.NormalizedPhysicalH2Approximation

/-! Compact inverse-distance domination controls the actual physical L2 class
norms and the true 43-component H2 norm, without weak-derivative premises. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalDistanceCompactBudgetClass (K : Set (Configuration 2)) (hK : IsCompact K) :
    Lp ℝ 2 (volume : Measure (Configuration 2)) :=
  (physical_compact_inverse_distance_domination_memLp hK).toLp
    (K.indicator (fun x => 1+physicalInverseDistanceBudget x))

theorem physical_compact_distance_L2_norm_le
    {K : Set (Configuration 2)} (hK : IsCompact K) (F : SpatialL2 2) {c : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖F x‖≤c*‖K.indicator (fun y => 1+physicalInverseDistanceBudget y) x‖) :
    ‖F‖≤c*‖physicalDistanceCompactBudgetClass K hK‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hb,(physical_compact_inverse_distance_domination_memLp hK).coeFn_toLp] with x hx hy
  change (physicalDistanceCompactBudgetClass K hK) x=
    K.indicator (fun y => 1+physicalInverseDistanceBudget y) x at hy
  rw [hy]
  exact hx

theorem physical_distance_43_component_error_budget
    {K : Set (Configuration 2)} (hK : IsCompact K)
    (F : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) {ζ C : ℝ}
    (hζ : 0≤ζ) (hC : 0≤C)
    (h0 : ∀ᵐ x ∂volume, ‖F x‖≤ζ*C*‖K.indicator (fun y => 1+physicalInverseDistanceBudget y) x‖)
    (h1 : ∀ k, ∀ᵐ x ∂volume, ‖d k x‖≤ζ*C*‖K.indicator (fun y => 1+physicalInverseDistanceBudget y) x‖)
    (h2 : ∀ k l, ∀ᵐ x ∂volume, ‖e k l x‖≤ζ*C*‖K.indicator (fun y => 1+physicalInverseDistanceBudget y) x‖) :
    ‖F‖≤ζ*C*‖physicalDistanceCompactBudgetClass K hK‖ ∧
    (∀ k, ‖d k‖≤ζ*C*‖physicalDistanceCompactBudgetClass K hK‖) ∧
    (∀ k l, ‖e k l‖≤ζ*C*‖physicalDistanceCompactBudgetClass K hK‖) ∧
    physicalH2ComponentNorm F d e≤7*ζ*C*‖physicalDistanceCompactBudgetClass K hK‖ ∧
    ‖F‖+(∑ k,‖d k‖)+(∑ k,∑ l,‖e k l‖)≤43*ζ*C*‖physicalDistanceCompactBudgetClass K hK‖ := by
  let T := ζ*C*‖physicalDistanceCompactBudgetClass K hK‖
  have hT : 0≤T := mul_nonneg (mul_nonneg hζ hC) (norm_nonneg _)
  have hF : ‖F‖≤T := physical_compact_distance_L2_norm_le hK F h0
  have hd (k : Coordinate 2) : ‖d k‖≤T := physical_compact_distance_L2_norm_le hK (d k) (h1 k)
  have he (k l : Coordinate 2) : ‖e k l‖≤T := physical_compact_distance_L2_norm_le hK (e k l) (h2 k l)
  refine ⟨hF,hd,he,?_,?_⟩
  · simpa only [T,mul_assoc] using physicalH2ComponentNorm_le_common F d e T hT hF hd he
  · have hs1 := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => hd k)
    have hs2 := Finset.sum_le_sum (s:=Finset.univ) (fun k _ =>
      Finset.sum_le_sum (s:=Finset.univ) (fun l _ => he k l))
    have hcard : Fintype.card (Coordinate 2)=6 := by simp [Coordinate]
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at hs1 hs2
    norm_num only [Nat.cast_ofNat] at hs1 hs2
    dsimp [T] at hF hs1 hs2
    nlinarith

#print axioms physical_compact_distance_L2_norm_le
#print axioms physical_distance_43_component_error_budget
end ManyBody.S8
