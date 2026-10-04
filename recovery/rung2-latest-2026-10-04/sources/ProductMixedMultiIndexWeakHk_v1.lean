import ProductCoordinateWeakWordPermutation_v1
import MixedMultiIndexWord_v1
import LocalSmoothWeakGrushinFiniteRegularity_v1

/-! Natural multiindices for genuine finite local weak coordinate jets.
Canonical words count each of the four Y and three T derivatives literally.
Word permutation and open-domain uniqueness prove the shifted derivative
identities. The raw-equation corollary assumes no solution derivatives.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

def ProductMixedMultiIndexWeakHk (Ω : Set (Space (Fin 3)))
    (f : Space (Fin 3) → ℂ) (m : ℕ) (W : ℝ) : Prop :=
  ∃ F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ,
    F 0 0 = f ∧
    (∀ α β, (∑ i, α i)+(∑ j, β j) ≤ m → RegionL2Budget (F α β) Ω W) ∧
    (∀ α β i, (∑ k, α k)+(∑ j, β j) < m →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
    ∀ α β j, (∑ i, α i)+(∑ k, β k) < m →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j)

theorem coordinateWeakHk_mixed_multiIndex
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : Space (Fin 3) → ℂ} {m : ℕ} {W : ℝ}
    (hf : ProductCoordinateWeakHk Ω f m W) : ProductMixedMultiIndexWeakHk Ω f m W := by
  obtain ⟨D,h0,hBudget,hChain⟩ := hf
  let F := fun α β => D (mixedMultiIndexWord α β)
  refine ⟨F,?_,?_,?_,?_⟩
  · change D (mixedMultiIndexWord (fun _ => 0) (fun _ => 0)) = f
    rw [mixedMultiIndexWord_zero]
    exact h0
  · intro α β hαβ
    exact hBudget _ (by rwa [mixedMultiIndexWord_length])
  · intro α β i hαβ
    exact product_coordinate_family_derivative_of_perm hΩ D hBudget hChain (Sum.inl i)
      (mixedMultiIndexWord_add_single_y_perm α β i).symm
      (by rwa [mixedMultiIndexWord_length])
  · intro α β j hαβ
    exact product_coordinate_family_derivative_of_perm hΩ D hBudget hChain (Sum.inr j)
      (mixedMultiIndexWord_add_single_t_perm α β j).symm
      (by rwa [mixedMultiIndexWord_length])

theorem local_smooth_weak_grushin_mixed_multiIndex_regularity
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) {aY aT bY bT c : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • s p)
    (m : ℕ) : ∃ W : ℝ, 0 ≤ W ∧
      ProductMixedMultiIndexWeakHk (rectangularOpenBox a bY bT) f m W := by
  obtain ⟨W,hW,hJets⟩ := local_smooth_weak_grushin_finite_regularity
    hΩ a hby hbt hy ht hKΩ hc hB hs hf hEq m
  exact ⟨W,hW,coordinateWeakHk_mixed_multiIndex (rectangularOpenBox_isOpen a bY bT) hJets⟩

#print axioms ProductMixedMultiIndexWeakHk
#print axioms coordinateWeakHk_mixed_multiIndex
#print axioms local_smooth_weak_grushin_mixed_multiIndex_regularity
end TheoremT.Continuum.WeakGrushin
