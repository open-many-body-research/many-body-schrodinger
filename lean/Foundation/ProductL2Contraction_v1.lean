import ProductL2Tensor_v1

/-! Bounded partial contractions on actual product-measure L2 spaces.
Each contraction is the Hilbert adjoint of a literal product-function embedding.
The pairing identity specifies its actual continuum meaning; this is mathematical
operator construction, not an executable quadrature procedure. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def embedLeft (f : Lp ℂ 2 μ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := tensor f
      map_add' := tensor_add_right f
      map_smul' := fun c g => tensor_smul_right f g c }
    ‖f‖ (fun g => (tensor_norm f g).le)

def embedRight (g : Lp ℂ 2 ν) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun f => tensor f g
      map_add' := fun f h => tensor_add_left f h g
      map_smul' := fun c f => tensor_smul_left f g c }
    ‖g‖ (fun f => by
      change ‖tensor f g‖ ≤ ‖g‖ * ‖f‖
      rw [tensor_norm,mul_comm])

theorem embedLeft_apply (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : embedLeft f g = tensor f g := rfl

theorem embedRight_apply (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : embedRight g f = tensor f g := rfl

theorem embedLeft_norm_le (f : Lp ℂ 2 μ) : ‖(embedLeft (ν := ν) f)‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  exact (tensor_norm f g).le

theorem embedRight_norm_le (g : Lp ℂ 2 ν) : ‖(embedRight (μ := μ) g)‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [embedRight_apply,tensor_norm,mul_comm]

def contractLeft (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν :=
  ContinuousLinearMap.adjoint (embedLeft f)

def contractRight (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 μ :=
  ContinuousLinearMap.adjoint (embedRight g)

theorem contractLeft_norm_bound (f : Lp ℂ 2 μ) (F : Lp ℂ 2 (μ.prod ν)) :
    ‖contractLeft f F‖ ≤ ‖f‖ * ‖F‖ := by
  have hn : ‖(contractLeft (ν := ν) f)‖ ≤ ‖f‖ := by
    rw [contractLeft,ContinuousLinearMap.adjoint.norm_map]
    exact embedLeft_norm_le f
  exact ((contractLeft f).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem contractRight_norm_bound (g : Lp ℂ 2 ν) (F : Lp ℂ 2 (μ.prod ν)) :
    ‖contractRight g F‖ ≤ ‖g‖ * ‖F‖ := by
  have hn : ‖(contractRight (μ := μ) g)‖ ≤ ‖g‖ := by
    rw [contractRight,ContinuousLinearMap.adjoint.norm_map]
    exact embedRight_norm_le g
  exact ((contractRight g).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem contractLeft_pairing (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ g (contractLeft f F) = inner ℂ (tensor f g) F :=
  ContinuousLinearMap.adjoint_inner_right (embedLeft f) g F

theorem contractRight_pairing (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν)
    (F : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ f (contractRight g F) = inner ℂ (tensor f g) F :=
  ContinuousLinearMap.adjoint_inner_right (embedRight g) f F

theorem contractLeft_tensor (f h : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    contractLeft f (tensor h g) = inner ℂ f h • g := by
  apply ext_inner_left ℂ
  intro k
  rw [contractLeft_pairing,tensor_inner,inner_smul_right]

theorem contractRight_tensor (f : Lp ℂ 2 μ) (g k : Lp ℂ 2 ν) :
    contractRight g (tensor f k) = inner ℂ g k • f := by
  apply ext_inner_left ℂ
  intro h
  rw [contractRight_pairing,tensor_inner,inner_smul_right]
  ring

#print axioms embedLeft
#print axioms embedRight
#print axioms contractLeft_norm_bound
#print axioms contractRight_norm_bound
#print axioms contractLeft_pairing
#print axioms contractRight_pairing
#print axioms contractLeft_tensor
#print axioms contractRight_tensor
end TheoremT.ProductL2
