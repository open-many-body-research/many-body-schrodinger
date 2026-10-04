import SmoothWordBoxContinuousRepresentative_v1
import TensorBoxFrechetLimit_v1
import SmoothFiniteCoordinateJetRegularity_v1

/-! Actual finite classical representatives from strong L2 limits of smooth
coordinate jets. A reserve of seven derivatives produces continuous limits;
the uniform derivative-limit theorem supplies their compatibility. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem smooth_words7_finite_representatives_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (u : ℕ → (Fin 7 → ℝ) → ℂ) (hu : ∀ n, ContDiff ℝ ∞ (u n)) {m : ℕ}
    (V : ℕ → List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n w, w.length ≤ m+7 →
      (V n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] coordinateWordDeriv7 (u n) w)
    (W : List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ w, w.length ≤ m+7 → Tendsto (fun n => V n w) atTop (𝓝 (W w))) :
    ∃ G : List (Fin 7) → (Fin 7 → ℝ) → ℂ,
      (∀ w, w.length ≤ m →
        ContinuousOn (G w) (tensorClosedBox7 a b) ∧
        TendstoUniformlyOn (fun n => coordinateWordDeriv7 (u n) w) (G w) atTop (tensorClosedBox7 a b) ∧
        (W w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] G w) ∧
      (∀ w, w.length < m → ∀ x ∈ U,
        HasFDerivAt (G w) (coordinateDerivativeMap7 (fun i => G (i :: w) x)) x) ∧
      (∀ k w, w.length + k ≤ m → ContDiffOn ℝ k (G w) U) := by
  obtain ⟨G, hG⟩ := smooth_words7_continuous_representatives_of_L2_limits hab u hu V hV W hW
  have hder (w : List (Fin 7)) (hw : w.length < m) (x : Fin 7 → ℝ) (hx : x ∈ U) :
      HasFDerivAt (G w) (coordinateDerivativeMap7 (fun i => G (i :: w) x)) x := by
    apply tensor_box7_limit_hasFDerivAt (h := fun x i => G (i :: w) x) hU hUK
      (fun n => coordinateWordDeriv7 (u n) w)
      (fun n y _ => ((normedComplexDirectionalWordDeriv_contDiff _ (hu n) w).differentiable (by simp)) y)
      (hG w (by omega)).2.1
    · intro i
      simpa only [coordinateWordDeriv7, normedComplexDirectionalWordDeriv] using
        (hG (i :: w) (by simp only [List.length_cons]; omega)).2.1
    · exact hx
  refine ⟨G, hG, hder, ?_⟩
  intro k w hw
  exact finite_coordinate_jet_contDiffOn hU G
    (fun w hw => (hG w hw).1.mono hUK) hder k w hw

end TheoremT.Continuum
