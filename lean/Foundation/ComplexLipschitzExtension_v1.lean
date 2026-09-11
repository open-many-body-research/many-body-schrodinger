import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Extension of a complex Lipschitz function from an arbitrary subset,
with the explicit harmless factor two from separate real and imaginary extensions. -/
noncomputable section
open Filter
open scoped Topology NNReal
namespace TheoremT.Continuum

theorem complex_lipschitzOn_extension {X : Type*} [PseudoMetricSpace X]
    {f : X → ℂ} {S : Set X} {K : ℝ≥0} (hf : LipschitzOnWith K f S) :
    ∃ g : X → ℂ, LipschitzWith (K+K) g ∧ Set.EqOn f g S := by
  have hr : LipschitzOnWith K (fun x => (f x).re) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply le_trans _ (hf.dist_le_mul x hx y hy)
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Complex.sub_re] using
      Complex.abs_re_le_norm (f x-f y)
  have hi : LipschitzOnWith K (fun x => (f x).im) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply le_trans _ (hf.dist_le_mul x hx y hy)
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Complex.sub_im] using
      Complex.abs_im_le_norm (f x-f y)
  obtain ⟨r,hr,her⟩ := hr.extend_real
  obtain ⟨i,hi,hei⟩ := hi.extend_real
  refine ⟨fun x => (r x : ℂ)+(i x : ℂ)*Complex.I,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist ((r x : ℂ)+(i x : ℂ)*Complex.I) ((r y : ℂ)+(i y : ℂ)*Complex.I)
          ≤ dist (r x : ℂ) (r y : ℂ)+dist ((i x : ℂ)*Complex.I) ((i y : ℂ)*Complex.I) :=
        dist_add_add_le _ _ _ _
      _ = dist (r x) (r y)+dist (i x) (i y) := by
        simp only [dist_eq_norm,← sub_mul,norm_mul,Complex.norm_I,mul_one,
          ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Real.dist_eq]
      _ ≤ (K:ℝ)*dist x y+(K:ℝ)*dist x y :=
        add_le_add (hr.dist_le_mul x y) (hi.dist_le_mul x y)
      _ = ((K+K:ℝ≥0):ℝ)*dist x y := by rw [NNReal.coe_add]; ring
  · intro x hx
    change f x = (r x : ℂ)+(i x : ℂ)*Complex.I
    rw [← her hx,← hei hx]
    exact (Complex.re_add_im (f x)).symm

theorem uniform_lipschitz_pointwise_limit_on {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {u : ℕ → X → Y} {f : X → Y} {S : Set X} {K : ℝ≥0}
    (hu : ∀ n, LipschitzWith K (u n))
    (hl : ∀ x ∈ S, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    LipschitzOnWith K f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact le_of_tendsto ((hl x hx).dist (hl y hy))
    (Eventually.of_forall (fun n => (hu n).dist_le_mul x y))

#print axioms complex_lipschitzOn_extension
#print axioms uniform_lipschitz_pointwise_limit_on
end TheoremT.Continuum
