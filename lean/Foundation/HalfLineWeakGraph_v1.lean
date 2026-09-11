import HalfLineDomain_v1
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Every member of the compact derivative graph closure has a genuine weak
half-line derivative. The value projection is injective, proved with the
open-set fundamental lemma for compact smooth tests. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace TheoremT.HalfLine

instance : CoeFun Test (fun _ => ℝ → ℂ) := ⟨Subtype.val⟩

theorem Test.inner_value (φ : Test) (u : E) :
    inner ℂ φ.value u = ∫ x, star (φ x) * u x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coe_value] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

theorem Test.inner_gradient (φ : Test) (u : E) :
    inner ℂ φ.gradient u = ∫ x, star (deriv (φ : ℝ → ℂ) x) * u x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coe_gradient] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

theorem Test.pair_ibp (φ f : Test) :
    inner ℂ φ.value f.gradient = -inner ℂ φ.gradient f.value := by
  rw [φ.inner_value, φ.inner_gradient]
  have ha : (∫ x, star (φ x) * f.gradient x ∂μ) =
      ∫ x, star (φ x) * deriv (f : ℝ → ℂ) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [f.coe_gradient] with x hx
    rw [hx]
  have hb : (∫ x, star (deriv (φ : ℝ → ℂ) x) * f.value x ∂μ) =
      ∫ x, star (deriv (φ : ℝ → ℂ) x) * f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [f.coe_value] with x hx
    rw [hx]
  rw [ha, hb]
  have hφc : Continuous (fun x => star (φ x)) := φ.smooth.continuous.star
  have hφd : Continuous (fun x => star (deriv (φ : ℝ → ℂ) x)) :=
    (φ.smooth.continuous_deriv (by simp)).star
  have hfc := f.smooth.continuous
  have hfd := f.smooth.continuous_deriv (by simp)
  have hφs : HasCompactSupport (fun x => star (φ x)) := φ.compact.comp_left (by simp)
  have hφds : HasCompactSupport (fun x => star (deriv (φ : ℝ → ℂ) x)) :=
    φ.compact.deriv.comp_left (by simp)
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => star (φ x)) (u' := fun x => star (deriv (φ : ℝ → ℂ) x))
    (v := (f : ℝ → ℂ)) (v' := deriv (f : ℝ → ℂ))
    (fun x _ => (φ.smooth.differentiable (by simp) x).hasDerivAt.star)
    (fun x _ => (f.smooth.differentiable (by simp) x).hasDerivAt)
    ((hφc.mul hfd).integrable_of_hasCompactSupport (hφs.mul_right))
    ((hφd.mul hfc).integrable_of_hasCompactSupport (hφds.mul_right))
    ((hφc.mul hfc).integrable_of_hasCompactSupport (hφs.mul_right))
  have hsa : (∫ x, star (φ x) * deriv (f : ℝ → ℂ) x ∂μ) =
      ∫ x, star (φ x) * deriv (f : ℝ → ℂ) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hp : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (φ.support hm))
    simp [hp]
  have hsb : (∫ x, star (deriv (φ : ℝ → ℂ) x) * f x ∂μ) =
      ∫ x, star (deriv (φ : ℝ → ℂ) x) * f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hp : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (f.support hm))
    simp [hp]
  rw [hsa, hsb]
  exact hi

def Weak (f d : E) : Prop :=
  ∀ φ : Test, inner ℂ φ.value d = -inner ℂ φ.gradient f

def weakGraph : Submodule ℂ (E × E) where
  carrier := {p | Weak p.1 p.2}
  zero_mem' := by intro φ; simp
  add_mem' := by
    intro u v hu hv φ
    change inner ℂ φ.value (u.2+v.2) = -inner ℂ φ.gradient (u.1+v.1)
    rw [inner_add_right, inner_add_right, hu φ, hv φ, neg_add]
  smul_mem' := by
    intro c u hu φ
    change inner ℂ φ.value (c • u.2) = -inner ℂ φ.gradient (c • u.1)
    rw [inner_smul_right, inner_smul_right, hu φ]
    ring

theorem weakGraph_closed : IsClosed (weakGraph : Set (E × E)) := by
  change IsClosed {p : E × E | ∀ φ : Test, inner ℂ φ.value p.2 = -inner ℂ φ.gradient p.1}
  simp_rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro φ
  exact isClosed_eq (continuous_const.inner continuous_snd)
    ((continuous_const.inner continuous_fst).neg)

theorem domain_weak (u : D) : Weak (J u) (dJ u) := by
  have hc : core ≤ weakGraph := by
    rintro _ ⟨f, rfl⟩ φ
    exact φ.pair_ibp f
  exact (core.topologicalClosure_minimal hc weakGraph_closed) u.property

#print axioms Test.pair_ibp
#print axioms domain_weak
end TheoremT.HalfLine
