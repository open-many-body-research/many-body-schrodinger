import FiniteCoordinateMultilinearBound_v1
import ProductCoordinateExpansion_v1
import ProductWordArrayFDeriv_v1

/-! Bounds for actual Frechet operator norms from all actual coordinate-word
values. The physical product norm is unchanged, with four Y coordinates
and card(kappa) spectator coordinates. Smoothness remains explicit. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem product_coordinate_multilinear_opNorm_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space κ) G)
    {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ a : Fin k → Fin 4 ⊕ κ, ‖T (fun i => productCoordinateDirection (a i))‖ ≤ M) :
    ‖T‖ ≤ (4 + (Fintype.card κ : ℝ))^k*M := by
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using
    finite_coordinate_multilinear_opNorm_le productCoordinateDirection productCoordinateComponent
      productCoordinateComponent_reconstruct productCoordinateComponent_abs_le T hM hT

theorem product_iteratedFDeriv_norm_le_coordinate_words
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {f : Space κ → ℂ}
    (hf : ContDiffOn ℝ ∞ f Ω) {x : Space κ} (hx : x ∈ Ω)
    (k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hword : ∀ w : List (Fin 4 ⊕ κ), w.length = k →
      ‖complexDirectionalWordDeriv productCoordinateDirection f w x‖ ≤ M) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ (4 + (Fintype.card κ : ℝ))^k*M := by
  apply product_coordinate_multilinear_opNorm_le _ hM
  intro a
  rw [← complexDirectionalWordDeriv_ofFn_eq_iteratedFDeriv productCoordinateDirection hΩ hf a hx]
  exact hword (List.ofFn a) (List.length_ofFn)

theorem physical_iteratedFDeriv_norm_le_seven_pow_words
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω) {f : Space (Fin 3) → ℂ}
    (hf : ContDiffOn ℝ ∞ f Ω) {x : Space (Fin 3)} (hx : x ∈ Ω)
    (k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hword : ∀ w : List (Fin 4 ⊕ Fin 3), w.length = k →
      ‖complexDirectionalWordDeriv productCoordinateDirection f w x‖ ≤ M) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ (7 : ℝ)^k*M := by
  have hb := product_iteratedFDeriv_norm_le_coordinate_words hΩ hf hx k hM hword
  norm_num at hb
  exact hb

theorem product_iteratedFDeriv_factorial_bound_of_coordinate_words
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {f : Space κ → ℂ}
    (hf : ContDiffOn ℝ ∞ f Ω) {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hword : ∀ x ∈ Ω, ∀ w : List (Fin 4 ⊕ κ),
      ‖complexDirectionalWordDeriv productCoordinateDirection f w x‖ ≤
        C*A^w.length*(w.length.factorial : ℝ)) :
    ∀ x ∈ Ω, ∀ k : ℕ, ‖iteratedFDeriv ℝ k f x‖ ≤
      C*((4 + (Fintype.card κ : ℝ))*A)^k*(k.factorial : ℝ) := by
  intro x hx k
  have hb := product_iteratedFDeriv_norm_le_coordinate_words hΩ hf hx k
    (M := C*A^k*(k.factorial : ℝ)) (by positivity)
    (fun w hw => by simpa only [hw] using hword x hx w)
  calc
    _ ≤ _ := hb
    _ = _ := by rw [mul_pow]; ring

end TheoremT.Continuum.WeakGrushin
