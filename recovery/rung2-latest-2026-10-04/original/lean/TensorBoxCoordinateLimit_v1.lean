import TensorBoxPointwiseFTC_v1
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Genuine coordinate derivatives pass to uniform limits on a fixed box.
The proof uses the open coordinate interval and actual derivatives of the
approximants. No differentiability of a limit is an input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace TheoremT.Continuum

theorem tensor_box7_uniform_coordinate_slice
    {a b : Fin 7 → ℝ} {f : ℕ → (Fin 7 → ℝ) → ℂ} {g : (Fin 7 → ℝ) → ℂ}
    (hU : TendstoUniformlyOn f g atTop (tensorClosedBox7 a b))
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) (i : Fin 7) :
    TendstoUniformlyOn (fun n r => f n (Function.update x i r))
      (fun r => g (Function.update x i r)) atTop (Ioo (a i) (b i)) := by
  exact (hU.comp (Function.update x i)).mono
    (fun r hr => tensorClosedBox7_update hx i ⟨hr.1.le,hr.2.le⟩)

theorem tensor_box7_coordinate_hasDerivAt_of_uniform_limits
    {a b : Fin 7 → ℝ} (i : Fin 7)
    (f df : ℕ → (Fin 7 → ℝ) → ℂ) {g h : (Fin 7 → ℝ) → ℂ}
    (hU : TendstoUniformlyOn f g atTop (tensorClosedBox7 a b))
    (hDU : TendstoUniformlyOn df h atTop (tensorClosedBox7 a b))
    (hd : ∀ n y, y ∈ tensorClosedBox7 a b →
      HasDerivAt (fun r => f n (Function.update y i r)) (df n y) (y i))
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b)
    (hxi : x i ∈ Ioo (a i) (b i)) :
    HasDerivAt (fun r => g (Function.update x i r)) (h x) (x i) := by
  have hdline : ∀ᶠ n in atTop, ∀ r ∈ Ioo (a i) (b i),
      HasDerivAt (fun t => f n (Function.update x i t))
        (df n (Function.update x i r)) r := by
    apply Eventually.of_forall
    intro n r hr
    simpa only [Function.update_idem,Function.update_self] using
      hd n (Function.update x i r) (tensorClosedBox7_update hx i ⟨hr.1.le,hr.2.le⟩)
  have hh := hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    (tensor_box7_uniform_coordinate_slice hDU hx i) hdline
    (fun r hr => (tensor_box7_uniform_coordinate_slice hU hx i).tendsto_at hr) hxi
  simpa only [Function.update_eq_self] using hh

theorem tensor_box7_partial_derivative_eq_of_uniform_limits
    {a b : Fin 7 → ℝ} (i : Fin 7)
    (f df : ℕ → (Fin 7 → ℝ) → ℂ) {g h : (Fin 7 → ℝ) → ℂ}
    (hU : TendstoUniformlyOn f g atTop (tensorClosedBox7 a b))
    (hDU : TendstoUniformlyOn df h atTop (tensorClosedBox7 a b))
    (hd : ∀ n y, y ∈ tensorClosedBox7 a b →
      HasDerivAt (fun r => f n (Function.update y i r)) (df n y) (y i))
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b)
    (hxi : x i ∈ Ioo (a i) (b i)) :
    deriv (fun r => g (Function.update x i r)) (x i) = h x :=
  (tensor_box7_coordinate_hasDerivAt_of_uniform_limits i f df hU hDU hd hx hxi).deriv

theorem tensor_box7_coordinate_limit_inside
    {a b : Fin 7 → ℝ}
    (f : ℕ → (Fin 7 → ℝ) → ℂ) (df : ℕ → Fin 7 → (Fin 7 → ℝ) → ℂ)
    {g : (Fin 7 → ℝ) → ℂ} {h : Fin 7 → (Fin 7 → ℝ) → ℂ}
    (hU : TendstoUniformlyOn f g atTop (tensorClosedBox7 a b))
    (hDU : ∀ i, TendstoUniformlyOn (fun n => df n i) (h i) atTop (tensorClosedBox7 a b))
    (hd : ∀ n i y, y ∈ tensorClosedBox7 a b →
      HasDerivAt (fun r => f n (Function.update y i r)) (df n i y) (y i))
    {x : Fin 7 → ℝ} (hx : ∀ i, x i ∈ Ioo (a i) (b i)) :
    ∀ i, HasDerivAt (fun r => g (Function.update x i r)) (h i x) (x i) := by
  have hxbox : x ∈ tensorClosedBox7 a b := fun i _ => ⟨(hx i).1.le,(hx i).2.le⟩
  intro i
  exact tensor_box7_coordinate_hasDerivAt_of_uniform_limits i f (fun n => df n i)
    hU (hDU i) (fun n y hy => hd n i y hy) hxbox (hx i)

end TheoremT.Continuum
