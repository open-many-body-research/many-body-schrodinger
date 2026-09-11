import ProductL2Contraction_v1

/-! Genuine coordinate projections on actual product L2.
Unit normalization makes each map an orthogonal projection. Their commutation
and joint rank-one formula are proved from actual product-function inner products. -/
noncomputable section
open MeasureTheory
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def projectLeft (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (embedLeft f).comp (contractLeft f)

def projectRight (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (embedRight g).comp (contractRight g)

theorem projectLeft_apply (f : Lp ℂ 2 μ) (F : Lp ℂ 2 (μ.prod ν)) :
    projectLeft f F = tensor f (contractLeft f F) := rfl

theorem projectRight_apply (g : Lp ℂ 2 ν) (F : Lp ℂ 2 (μ.prod ν)) :
    projectRight g F = tensor (contractRight g F) g := rfl

theorem unit_inner_self (f : Lp ℂ 2 μ) (hf : ‖f‖=1) : inner ℂ f f = 1 := by
  rw [inner_self_eq_norm_sq_to_K,hf]
  norm_num

theorem projectLeft_idempotent (f : Lp ℂ 2 μ) (hf : ‖f‖=1)
    (F : Lp ℂ 2 (μ.prod ν)) : projectLeft f (projectLeft f F)=projectLeft f F := by
  rw [projectLeft_apply,projectLeft_apply,contractLeft_tensor,unit_inner_self f hf,one_smul]

theorem projectRight_idempotent (g : Lp ℂ 2 ν) (hg : ‖g‖=1)
    (F : Lp ℂ 2 (μ.prod ν)) : projectRight g (projectRight g F)=projectRight g F := by
  rw [projectRight_apply,projectRight_apply,contractRight_tensor,unit_inner_self g hg,one_smul]

theorem projectLeft_symmetric (f : Lp ℂ 2 μ) :
    (projectLeft (ν := ν) f).toLinearMap.IsSymmetric := by
  intro F G
  change inner ℂ (tensor f (contractLeft f F)) G = inner ℂ F (tensor f (contractLeft f G))
  rw [← contractLeft_pairing]
  exact ContinuousLinearMap.adjoint_inner_left (embedLeft f) (contractLeft f G) F

theorem projectRight_symmetric (g : Lp ℂ 2 ν) :
    (projectRight (μ := μ) g).toLinearMap.IsSymmetric := by
  intro F G
  change inner ℂ (tensor (contractRight g F) g) G = inner ℂ F (tensor (contractRight g G) g)
  rw [← contractRight_pairing]
  exact ContinuousLinearMap.adjoint_inner_left (embedRight g) (contractRight g G) F

theorem projectLeft_isSymmetricProjection (f : Lp ℂ 2 μ) (hf : ‖f‖=1) :
    (projectLeft (ν := ν) f).toLinearMap.IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro F
    exact projectLeft_idempotent f hf F
  · exact projectLeft_symmetric f

theorem projectRight_isSymmetricProjection (g : Lp ℂ 2 ν) (hg : ‖g‖=1) :
    (projectRight (μ := μ) g).toLinearMap.IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro F
    exact projectRight_idempotent g hg F
  · exact projectRight_symmetric g

theorem projectLeft_projectRight (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) :
    projectLeft f (projectRight g F) = inner ℂ (tensor f g) F • tensor f g := by
  rw [projectLeft_apply,projectRight_apply,contractLeft_tensor,tensor_smul_right,
    contractRight_pairing]

theorem projectRight_projectLeft (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) :
    projectRight g (projectLeft f F) = inner ℂ (tensor f g) F • tensor f g := by
  rw [projectRight_apply,projectLeft_apply,contractRight_tensor,tensor_smul_left,
    contractLeft_pairing]

theorem projectLeft_projectRight_commute (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    Commute (projectLeft f).toLinearMap (projectRight g).toLinearMap := by
  apply LinearMap.ext
  intro F
  exact (projectLeft_projectRight f g F).trans (projectRight_projectLeft f g F).symm

#print axioms projectLeft_isSymmetricProjection
#print axioms projectRight_isSymmetricProjection
#print axioms projectLeft_projectRight
#print axioms projectRight_projectLeft
#print axioms projectLeft_projectRight_commute
end TheoremT.ProductL2
