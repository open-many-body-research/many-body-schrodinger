import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Algebra.Module.Basic

/-! The actual half-line zero-boundary domain, defined by closure of compact
smooth derivative pairs. No trace characterization is assumed. The product
uses its usual max norm, equivalent to the standard H¹ norm. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace TheoremT.HalfLine

abbrev μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
abbrev E := Lp ℂ 2 μ

def testFunctions : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi 0}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, ?_⟩
    · exact HasCompactSupport.zero
    · simp
  add_mem' := by
    rintro f g ⟨hf,hcf,hsf⟩ ⟨hg,hcg,hsg⟩
    exact ⟨hf.add hg, hcf.add hcg, (tsupport_add f g).trans (union_subset hsf hsg)⟩
  smul_mem' := by
    rintro c f ⟨hf,hcf,hsf⟩
    exact ⟨contDiff_const.smul hf, hcf.smul_left, (tsupport_smul_subset_right (fun _ : ℝ => c) f).trans hsf⟩

abbrev Test : Type := testFunctions

theorem Test.smooth (f : Test) : ContDiff ℝ ∞ (f : ℝ → ℂ) := f.property.1
theorem Test.compact (f : Test) : HasCompactSupport (f : ℝ → ℂ) := f.property.2.1
theorem Test.support (f : Test) : tsupport (f : ℝ → ℂ) ⊆ Ioi 0 := f.property.2.2

theorem Test.memLp (f : Test) : MemLp (f : ℝ → ℂ) 2 μ :=
  f.smooth.continuous.memLp_of_hasCompactSupport f.compact

theorem Test.deriv_memLp (f : Test) : MemLp (deriv (f : ℝ → ℂ)) 2 μ :=
  (f.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport f.compact.deriv

def Test.value (f : Test) : E := f.memLp.toLp (f : ℝ → ℂ)
def Test.gradient (f : Test) : E := f.deriv_memLp.toLp (deriv (f : ℝ → ℂ))

theorem Test.coe_value (f : Test) : (f.value : ℝ → ℂ) =ᵐ[μ] f := f.memLp.coeFn_toLp

theorem Test.coe_gradient (f : Test) : (f.gradient : ℝ → ℂ) =ᵐ[μ] deriv (f : ℝ → ℂ) :=
  f.deriv_memLp.coeFn_toLp

def graphMap : Test →ₗ[ℂ] E × E where
  toFun f := (f.value, f.gradient)
  map_add' f g := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [(f+g).coe_value, f.coe_value, g.coe_value, Lp.coeFn_add f.value g.value] with x hfg hf hg hadd
      simp only [Prod.fst_add]
      simp only [Pi.add_apply] at hadd
      rw [hfg, hadd, hf, hg]
      rfl
    · apply Lp.ext
      filter_upwards [(f+g).coe_gradient, f.coe_gradient, g.coe_gradient, Lp.coeFn_add f.gradient g.gradient] with x hfg hf hg hadd
      simp only [Prod.snd_add]
      simp only [Pi.add_apply] at hadd
      rw [hfg, hadd, hf, hg]
      exact deriv_add (f.smooth.differentiable (by simp) x) (g.smooth.differentiable (by simp) x)
  map_smul' c f := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [(c • f).coe_value, f.coe_value, Lp.coeFn_smul c f.value] with x hcf hf hc
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd]
      simp only [Pi.smul_apply] at hc
      rw [hcf, hc, hf]
      rfl
    · apply Lp.ext
      filter_upwards [(c • f).coe_gradient, f.coe_gradient, Lp.coeFn_smul c f.gradient] with x hcf hf hc
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd]
      simp only [Pi.smul_apply] at hc
      rw [hcf, hc, hf]
      exact deriv_const_smul c (f.smooth.differentiable (by simp) x)

def core : Submodule ℂ (E × E) := graphMap.range

def domain : Submodule ℂ (E × E) := core.topologicalClosure
abbrev D : Type := domain

instance : CompleteSpace D := core.isClosed_topologicalClosure.completeSpace_coe

def J : D →L[ℂ] E := (ContinuousLinearMap.fst ℂ E E).comp domain.subtypeL

def dJ : D →L[ℂ] E := (ContinuousLinearMap.snd ℂ E E).comp domain.subtypeL

theorem domain_eq_closure_span :
    domain = (Submodule.span ℂ (Set.range fun f : Test => (f.value, f.gradient))).topologicalClosure := by
  change core.topologicalClosure = (Submodule.span ℂ (core : Set (E × E))).topologicalClosure
  rw [Submodule.span_eq]

theorem J_apply (u : D) : J u = u.val.1 := rfl
theorem dJ_apply (u : D) : dJ u = u.val.2 := rfl

theorem domain_norm (u : D) : ‖u‖ = max ‖J u‖ ‖dJ u‖ := rfl

#print axioms domain_eq_closure_span
#print axioms domain_norm
#synth CompleteSpace D
end TheoremT.HalfLine
