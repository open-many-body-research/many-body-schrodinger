import SmoothWordBoxFiniteRepresentative_v1

/-! One actual smooth local representative of all strong L2 coordinate-word
limits of one smooth approximating sequence. Every representative derivative
is identified pointwise; smoothness is concluded rather than assumed. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem compatible_coordinate_words7_eq
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U)
    (G : List (Fin 7) → (Fin 7 → ℝ) → ℂ)
    (hdG : ∀ w, ∀ x ∈ U,
      HasFDerivAt (G w) (coordinateDerivativeMap7 (fun i => G (i :: w) x)) x)
    (w : List (Fin 7)) : EqOn (coordinateWordDeriv7 (G []) w) (G w) U := by
  induction w with
  | nil => intro x hx; rfl
  | cons i w ih =>
    intro x hx
    have he : coordinateWordDeriv7 (G []) w =ᶠ[𝓝 x] G w :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => ih hy)
    have hd := (hdG w x hx).congr_of_eventuallyEq he
    change fderiv ℝ (coordinateWordDeriv7 (G []) w) x (Pi.single i 1) = G (i :: w) x
    rw [hd.fderiv]
    exact congrFun ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) (Fin 7)).apply_symm_apply
      (fun j => G (j :: w) x)) i

theorem smooth_words7_allOrder_representative_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (u : ℕ → (Fin 7 → ℝ) → ℂ) (hu : ∀ n, ContDiff ℝ ∞ (u n))
    (V : ℕ → List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n w,
      (V n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] coordinateWordDeriv7 (u n) w)
    (W : List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ w, Tendsto (fun n => V n w) atTop (𝓝 (W w))) :
    ∃ G : List (Fin 7) → (Fin 7 → ℝ) → ℂ,
      (∀ w, ContinuousOn (G w) (tensorClosedBox7 a b) ∧
        TendstoUniformlyOn (fun n => coordinateWordDeriv7 (u n) w) (G w) atTop (tensorClosedBox7 a b) ∧
        (W w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] G w) ∧
      (∀ w, ∀ x ∈ U,
        HasFDerivAt (G w) (coordinateDerivativeMap7 (fun i => G (i :: w) x)) x) ∧
      (∀ w, ContDiffOn ℝ ∞ (G w) U) ∧
      (∀ w, EqOn (coordinateWordDeriv7 (G []) w) (G w) U) := by
  classical
  have hex (w : List (Fin 7)) :=
    smooth_word7_continuous_representative_of_L2_limits hab u hu (m := w.length)
      V (fun n w _ => hV n w) W (fun w _ => hW w) w le_rfl
  choose G hG using hex
  have hder (w : List (Fin 7)) (x : Fin 7 → ℝ) (hx : x ∈ U) :
      HasFDerivAt (G w) (coordinateDerivativeMap7 (fun i => G (i :: w) x)) x := by
    apply tensor_box7_limit_hasFDerivAt (h := fun x i => G (i :: w) x) hU hUK
      (fun n => coordinateWordDeriv7 (u n) w)
      (fun n y _ => ((normedComplexDirectionalWordDeriv_contDiff _ (hu n) w).differentiable (by simp)) y)
      (hG w).2.1
    · intro i
      simpa only [coordinateWordDeriv7, normedComplexDirectionalWordDeriv] using (hG (i :: w)).2.1
    · exact hx
  refine ⟨G, hG, hder, ?_, compatible_coordinate_words7_eq hU G hder⟩
  intro w
  apply contDiffOn_infty.mpr
  intro k
  exact finite_coordinate_jet_contDiffOn (m := w.length+k) hU G
    (fun v _ => (hG v).1.mono hUK) (fun v _ => hder v) k w le_rfl

end TheoremT.Continuum
