import SmoothWordBoxAllOrderRepresentative_v1
import TensorBoxLimitPointwiseBound_v1

/-! Quantitative smooth representative theorem for actual strong L2 limits of
smooth seven-coordinate word jets. The 128 limiting mixed norms, not bounds
on arbitrarily chosen pointwise representatives, supply every pointwise bound. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem smooth_words7_quantitative_representative_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (u : ℕ → (Fin 7 → ℝ) → ℂ) (hu : ∀ n, ContDiff ℝ ∞ (u n))
    (V : ℕ → List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n w,
      (V n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] coordinateWordDeriv7 (u n) w)
    (W : List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ w, Tendsto (fun n => V n w) atTop (𝓝 (W w)))
    (M : List (Fin 7) → ℝ) (hM : ∀ w, 0 ≤ M w)
    (hWM : ∀ w s, ‖W (canonicalSubsetWord7 s ++ w)‖ ≤ M w) :
    ∃ g : (Fin 7 → ℝ) → ℂ,
      ContinuousOn g (tensorClosedBox7 a b) ∧ ContDiffOn ℝ ∞ g U ∧
      (W [] : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] g ∧
      (∀ w, (W w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict U] coordinateWordDeriv7 g w) ∧
      (∀ w x, x ∈ U → ‖coordinateWordDeriv7 g w x‖ ≤ boxEvaluationConstant a b * M w) := by
  obtain ⟨G,hG,hder,hsm,heq⟩ :=
    smooth_words7_allOrder_representative_of_L2_limits hab hU hUK u hu V hV W hW
  refine ⟨G [], (hG []).1, hsm [], (hG []).2.2, ?_, ?_⟩
  · intro w
    have ha := ((hG w).2.2).filter_mono (ae_mono (Measure.restrict_mono_set volume hUK))
    filter_upwards [ha,ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (heq w hxU).symm
  · intro w x hx
    rw [heq w hx]
    have hcs (n : ℕ) : ContDiff ℝ ∞ (coordinateWordDeriv7 (u n) w) :=
      normedComplexDirectionalWordDeriv_contDiff _ (hu n) w
    apply tensor_box7_pointwise_bound_of_L2_limits hab
      (fun n s => smoothSubsetField7 (coordinateWordDeriv7 (u n) w) s)
      (fun n s => (smoothSubsetField7_contDiff (hcs n) s).continuous.continuousOn)
      (fun n s i hi y _ => smoothSubsetField7_coordinate_hasDerivAt (hcs n) s i hi y)
      (fun n s => V n (canonicalSubsetWord7 s ++ w))
      (fun n s => by rw [smoothSubsetField7_word_base]; exact hV n _)
      (fun s => W (canonicalSubsetWord7 s ++ w))
      (fun s => hW _) ?_ (hM w) (hWM w) (hUK hx)
    simpa only [smoothSubsetField7_empty] using (hG w).2.1

end TheoremT.Continuum
