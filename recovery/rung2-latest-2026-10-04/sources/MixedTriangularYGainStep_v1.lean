import MixedTriangularExtension_v1
import LocalWeakYLaplacianExplicitRecovery_v1

/-! One quantitative two-level triangular Y recovery, using the actual
weak negative Y-Laplacian equations and the scheduled genuine spectator jets.
No recovered Y jets are inputs. The source family and its norm bound remain
explicit; the next composition derives them from the potential equation.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem mixed_triangular_y_gain_step
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {V : Set (Space κ)} (hV : IsOpen V) (hχV : tsupport χ ⊆ V)
    (hη1 : ∀ p ∈ V, η p = 1)
    (M A L D Q : ℝ) (hL0 : 0 ≤ L) (hD0 : 0 ≤ D) (hQ0 : 0 ≤ Q)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar 0 χ p| ≤ A)
    (hL : ∀ p ∈ tsupport χ, cutoffGradientWeight 0 χ p ≤ L)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight 0 η p ≤ Q)
    {O : Set (Space κ)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) (hχ1 : ∀ p ∈ O, χ p = 1)
    {r m : ℕ} (hr : 1 ≤ r) (W R : ℝ)
    (F H : List (Fin 4) → List κ → Space κ → ℂ)
    (hF : ∀ a b, a.length ≤ r → a.length+b.length ≤ m → RegionL2Budget (F a b) Ω W)
    (hY : ∀ a b i, a.length < r → a.length+b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (hT : ∀ b j, b.length < m →
      ProductLocalWeakDirectional Ω (F [] b) (F [] (j :: b)) (tDir j))
    (hH : ∀ a b, a.length ≤ r → r ≤ a.length+1 → a.length+b.length+2 ≤ m →
      RegionL2Budget (H a b) Ω R)
    (hP : ∀ a b, a.length ≤ r → r ≤ a.length+1 → a.length+b.length+2 ≤ m →
      ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F a b p) =
          ∫ p, φ p • H a b p) :
    MixedTriangularState O (F [] []) (r+2) m
      (max W ((3/2 : ℝ)*((4*A^2+16*L*(D/2+Q))*W+(2*M^2+8*L*D)*R))) := by
  let C0 : ℝ := 4*A^2+16*L*(D/2+Q)
  let C1 : ℝ := 2*M^2+8*L*D
  let U : ℝ := max W ((3/2 : ℝ)*(C0*W+C1*R))
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  obtain ⟨K,V',hK,hKΩ,_,_,_,_,hrec⟩ :=
    local_y_laplacian_explicit_recovery hΩ hχ hcχ hη hcη hηΩ hV hχV hη1
      M A L D Q hL0 hD0 hQ0 hM hA hL hD hQ
  have hnew : ∀ a b,
      ∃ gy : Fin 4 → Space κ → ℂ,
      ∃ hyy : Fin 4 → Fin 4 → Space κ → ℂ,
        a.length ≤ r → r ≤ a.length+1 → a.length+b.length+2 ≤ m →
          (∀ i, ProductLocalWeakDirectional O (F a b) (gy i) (yDir i)) ∧
          (∀ i j, ProductLocalWeakDirectional O (gy i) (hyy i j) (yDir j)) ∧
          ∀ i j, RegionL2Budget (hyy i j) O U := by
    intro a b
    by_cases hh : a.length ≤ r ∧ r ≤ a.length+1 ∧ a.length+b.length+2 ≤ m
    · obtain ⟨ha,hb,hab⟩ := hh
      have hd (j : κ) := mixed_word_second_spectator_compatibility F hY hT a b j j ha hab
      obtain ⟨u,gy,hyy,hu,_,_,hEn,hgy,he⟩ := hrec (F a b) (H a b)
        (fun j => F a (j :: b)) (fun j => F a (j :: j :: b))
        (hF a b ha (by omega)).local (hH a b ha hb hab).local
        (fun j => (hd j).1.2.1) (fun j => (hd j).2.2.1)
        (fun j => (hd j).1.2.2) (fun j => (hd j).2.2.2) (hP a b ha hb hab)
      have hFW : (∫ p in K, ‖F a b p‖^2) ≤ W :=
        ((hF a b ha (by omega)).restrict hKΩ le_rfl).2
      have hHR : (∫ p in K, ‖H a b p‖^2) ≤ R :=
        ((hH a b ha hb hab).restrict hKΩ le_rfl).2
      have hbound : (∑ i, ∑ j, ‖hyy i j‖^2) ≤ U := by
        apply hEn.trans
        apply le_trans _ (le_max_right W ((3/2 : ℝ)*(C0*W+C1*R)))
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3/2)
        exact add_le_add (mul_le_mul_of_nonneg_left hFW hC0)
          (mul_le_mul_of_nonneg_left hHR hC1)
      refine ⟨fun i => gy i,fun i j => hyy i j,fun _ _ _ => ⟨?_,?_,?_⟩⟩
      · exact fun i => ProductLocalWeakDirectional.of_cutoff_plateau hu hχ1 (hgy i)
      · exact fun i j => ProductLocalWeakDirectional.of_global (he i j) O
      · intro i j
        apply regionL2Budget_of_global
        apply le_trans (Finset.single_le_sum (fun k _ => sq_nonneg ‖hyy i k‖) (Finset.mem_univ j))
        apply le_trans (Finset.single_le_sum
          (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖hyy k l‖)) (Finset.mem_univ i))
        exact hbound
    · exact ⟨fun _ _ => 0,fun _ _ _ => 0,fun ha hb hab => (hh ⟨ha,hb,hab⟩).elim⟩
  choose gy hyy hnew using hnew
  exact mixed_triangular_extend_two hO hr F gy hyy (le_max_left _ _)
    (fun a b ha hab => (hF a b ha hab).restrict hOΩ le_rfl)
    (fun a b i ha hab => (hY a b i ha hab).mono hOΩ)
    (fun b j hb => (hT b j hb).mono hOΩ) hnew

#print axioms mixed_triangular_y_gain_step
end TheoremT.Continuum.WeakGrushin
