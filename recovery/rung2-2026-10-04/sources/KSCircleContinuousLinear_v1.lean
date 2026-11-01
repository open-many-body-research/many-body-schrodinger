import KSDescentSpinorAlgebra_v1
import WeakGrushinJetFields_v1
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The literal real KS circle action as a continuous linear map, together
with its product action on the actual KS/spectator space. The product norm
is the ordinary max norm. Unit phases preserve both that norm and the
physical KS pullback, and every center (0,t0) is fixed. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum

def ksCircleActionCLM (a b : ℝ) : KSSpace →L[ℝ] KSSpace :=
  ({ toFun := ksCircleAction a b
     map_add' := by
       intro x y
       ext i
       fin_cases i <;> simp [ksCircleAction] <;> ring
     map_smul' := by
       intro c y
       ext i
       fin_cases i <;> simp [ksCircleAction] <;> ring } : KSSpace →ₗ[ℝ] KSSpace).toContinuousLinearMap

theorem ksCircleActionCLM_apply (a b : ℝ) (y : KSSpace) :
    ksCircleActionCLM a b y = ksCircleAction a b y := rfl

theorem ksCircleAction_norm {a b : ℝ} (h : a^2+b^2=1) (y : KSSpace) :
    ‖ksCircleAction a b y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← ksMap_norm,ksMap_circle_invariant h,ksMap_norm]

theorem ksCircleActionCLM_norm {a b : ℝ} (h : a^2+b^2=1) (y : KSSpace) :
    ‖ksCircleActionCLM a b y‖ = ‖y‖ := ksCircleAction_norm h y

def ksCircleProductCLM (a b : ℝ) :
    WeakGrushin.Space (Fin 3) →L[ℝ] WeakGrushin.Space (Fin 3) :=
  (ksCircleActionCLM a b).prodMap (ContinuousLinearMap.id ℝ Position)

theorem ksCircleProductCLM_apply (a b : ℝ) (q : WeakGrushin.Space (Fin 3)) :
    ksCircleProductCLM a b q = (ksCircleAction a b q.1,q.2) := rfl

theorem ksCircleProductCLM_fixed (a b : ℝ) (t0 : Position) :
    ksCircleProductCLM a b (0,t0) = (0,t0) := by
  change (ksCircleActionCLM a b 0,t0) = (0,t0)
  rw [map_zero]

theorem ksCircleProductCLM_norm {a b : ℝ} (h : a^2+b^2=1)
    (q : WeakGrushin.Space (Fin 3)) : ‖ksCircleProductCLM a b q‖=‖q‖ := by
  change max ‖ksCircleAction a b q.1‖ ‖q.2‖ = max ‖q.1‖ ‖q.2‖
  rw [ksCircleAction_norm h]

theorem ksCircleProductCLM_pullback_invariant (Ψ : Position × Position → ℂ)
    {a b : ℝ} (h : a^2+b^2=1) (q : WeakGrushin.Space (Fin 3)) :
    Ψ (ksMap (ksCircleProductCLM a b q).1,(ksCircleProductCLM a b q).2) =
      Ψ (ksMap q.1,q.2) := by
  change Ψ (ksMap (ksCircleAction a b q.1),q.2)=Ψ (ksMap q.1,q.2)
  exact ks_pullback_circle_invariant Ψ h q.1 q.2

end TheoremT.Continuum
