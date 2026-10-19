import SmoothWordBoxQuantitativeRepresentative_v1

/-! Finite-order quantitative version. The mollifier sequence and L2 choices
may depend on the finite requested order; no common all-order choice is needed. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem compatible_finite_coordinate_words7_eq
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) {m : ℕ}
    (G : List (Fin 7) → (Fin 7 → ℝ) → ℂ)
    (hdG : ∀ w, w.length < m → ∀ x ∈ U,
      HasFDerivAt (G w) (coordinateDerivativeMap7 (fun i => G (i :: w) x)) x)
    (w : List (Fin 7)) (hw : w.length ≤ m) :
    EqOn (coordinateWordDeriv7 (G []) w) (G w) U := by
  induction w with
  | nil => intro x hx; rfl
  | cons i w ih =>
    intro x hx
    have hw' : w.length < m := by simp only [List.length_cons] at hw; omega
    have he : coordinateWordDeriv7 (G []) w =ᶠ[𝓝 x] G w :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => ih (by omega) hy)
    have hd := (hdG w hw' x hx).congr_of_eventuallyEq he
    change fderiv ℝ (coordinateWordDeriv7 (G []) w) x (Pi.single i 1) = G (i :: w) x
    rw [hd.fderiv]
    exact congrFun ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) (Fin 7)).apply_symm_apply
      (fun j => G (j :: w) x)) i

theorem smooth_words7_finite_quantitative_representative_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (u : ℕ → (Fin 7 → ℝ) → ℂ) (hu : ∀ n, ContDiff ℝ ∞ (u n)) {m : ℕ}
    (V : ℕ → List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n w, w.length ≤ m+7 →
      (V n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] coordinateWordDeriv7 (u n) w)
    (W : List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ w, w.length ≤ m+7 → Tendsto (fun n => V n w) atTop (𝓝 (W w)))
    (M : List (Fin 7) → ℝ) (hM : ∀ w, w.length ≤ m → 0 ≤ M w)
    (hWM : ∀ w, w.length ≤ m → ∀ s, ‖W (canonicalSubsetWord7 s ++ w)‖ ≤ M w) :
    ∃ g : (Fin 7 → ℝ) → ℂ,
      ContinuousOn g (tensorClosedBox7 a b) ∧ ContDiffOn ℝ m g U ∧
      (W [] : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] g ∧
      (∀ w, w.length ≤ m → (W w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict U] coordinateWordDeriv7 g w) ∧
      (∀ w, w.length ≤ m → ∀ x ∈ U,
        ‖coordinateWordDeriv7 g w x‖ ≤ boxEvaluationConstant a b * M w) := by
  obtain ⟨G,hG,hder,hsm⟩ :=
    smooth_words7_finite_representatives_of_L2_limits hab hU hUK u hu V hV W hW
  have heq := compatible_finite_coordinate_words7_eq hU G hder
  refine ⟨G [], (hG [] (by simp)).1, hsm m [] (by simp), (hG [] (by simp)).2.2, ?_, ?_⟩
  · intro w hw
    have ha := ((hG w hw).2.2).filter_mono (ae_mono (Measure.restrict_mono_set volume hUK))
    filter_upwards [ha,ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (heq w hw hxU).symm
  · intro w hw x hx
    rw [heq w hw hx]
    have hs (s : Finset (Fin 7)) : (canonicalSubsetWord7 s ++ w).length ≤ m+7 :=
      (canonicalSubsetWord7_append_length s w).trans (Nat.add_le_add_right hw 7)
    have hcs (n : ℕ) : ContDiff ℝ ∞ (coordinateWordDeriv7 (u n) w) :=
      normedComplexDirectionalWordDeriv_contDiff _ (hu n) w
    apply tensor_box7_pointwise_bound_of_L2_limits hab
      (fun n s => smoothSubsetField7 (coordinateWordDeriv7 (u n) w) s)
      (fun n s => (smoothSubsetField7_contDiff (hcs n) s).continuous.continuousOn)
      (fun n s i hi y _ => smoothSubsetField7_coordinate_hasDerivAt (hcs n) s i hi y)
      (fun n s => V n (canonicalSubsetWord7 s ++ w))
      (fun n s => by rw [smoothSubsetField7_word_base]; exact hV n _ (hs s))
      (fun s => W (canonicalSubsetWord7 s ++ w))
      (fun s => hW _ (hs s)) ?_ (hM w hw) (hWM w hw) (hUK hx)
    simpa only [smoothSubsetField7_empty] using (hG w hw).2.1

end TheoremT.Continuum
