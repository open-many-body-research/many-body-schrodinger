import PhysicalDistanceWeakLaplacian_v1
import LinearRadiusWeakGradient_v1
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic
/-! Literal two-electron physical distance map and its genuine classical jets.
The three coordinates are exactly the two nuclear radii and unnormalized
pair distance. Away from the actual collision set, its true first and second
Frechet derivatives have proved physical bounds. The inverse-distance sum
in the Hessian bound is in actual L2 on every physical compact set.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalDistanceLinearMaps : Fin 3 → Configuration 2 →L[ℝ] Position :=
  ![electronPositionCLM 0,electronPositionCLM 1,pairDifferenceCLM 0 1]

def physicalDistanceTriple (x : Configuration 2) : Fin 3 → ℝ :=
  fun j => ‖physicalDistanceLinearMaps j x‖

def physicalDistanceGradient (x v : Configuration 2) : Fin 3 → ℝ :=
  fun j => linearRadiusGradient (physicalDistanceLinearMaps j) v x

def physicalDistanceHessian (x v w : Configuration 2) : Fin 3 → ℝ :=
  fun j => linearRadiusHessian (physicalDistanceLinearMaps j) v w x

def physicalInverseDistanceBudget (x : Configuration 2) : ℝ :=
  ∑ j : Fin 3, ‖physicalDistanceLinearMaps j x‖⁻¹

def physicalDistanceDerivative (x : Configuration 2) : Configuration 2 →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    (‖physicalDistanceLinearMaps j x‖⁻¹ • innerSL ℝ (physicalDistanceLinearMaps j x)).comp
      (physicalDistanceLinearMaps j))

theorem actual_position_norm_hasFDerivAt (x : Position) (hx : x≠0) :
    HasFDerivAt (norm : Position → ℝ) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hf : (fun y : Position => Real.sqrt (‖y‖^2))=norm := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [hf,Real.sqrt_sq (norm_nonneg x)] at h
  have heq : ‖x‖⁻¹ • innerSL ℝ x=(1/(2*‖x‖)) • (2 • innerSL ℝ x) := by
    ext v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  rw [heq]
  exact h

theorem actual_linear_radius_fderiv (A : Configuration 2 →L[ℝ] Position)
    {x : Configuration 2} (hx : A x≠0) (v : Configuration 2) :
    fderiv ℝ (fun y => ‖A y‖) x v=linearRadiusGradient A v x := by
  change fderiv ℝ (norm ∘ A) x v=_
  rw [((actual_position_norm_hasFDerivAt (A x) hx).comp x A.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,smul_eq_mul,
    linearRadiusGradient,div_eq_mul_inv]
  ring

theorem actual_linear_radius_mixed_fderiv (A : Configuration 2 →L[ℝ] Position)
    {x : Configuration 2} (hx : A x≠0) (v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => ‖A z‖) y v) x w=
      linearRadiusHessian A v w x := by
  have heq : (fun y => fderiv ℝ (fun z => ‖A z‖) y v)=ᶠ[𝓝 x]
      (fun y => inner ℝ (A y) (A v)/‖A y‖) := by
    have he : ∀ᶠ y in 𝓝 x, A y≠0 :=
      A.continuous.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hx)
    filter_upwards [he] with y hy
    exact actual_linear_radius_fderiv A hy v
  rw [heq.fderiv_eq]
  have hn := (actual_position_norm_hasFDerivAt (A x) hx).comp x A.hasFDerivAt
  have hnum := A.hasFDerivAt.inner ℝ (hasFDerivAt_const (A v) x)
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn
  have h := hnum.mul hi
  change HasFDerivAt (fun y => inner ℝ (A y) (A v)*‖A y‖⁻¹) _ x at h
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp [linearRadiusHessian,Function.comp_def]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

theorem physical_distance_maps_nonzero {x : Configuration 2} (hx : collisionFree x)
    (j : Fin 3) : physicalDistanceLinearMaps j x≠0 := by
  fin_cases j
  · exact hx.1 0
  · exact hx.1 1
  · exact sub_ne_zero.mpr (hx.2 0 1 (by decide))

theorem physical_distance_triple_hasFDerivAt {x : Configuration 2}
    (hx : collisionFree x) :
    HasFDerivAt physicalDistanceTriple (physicalDistanceDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro j
  exact (actual_position_norm_hasFDerivAt (physicalDistanceLinearMaps j x)
    (physical_distance_maps_nonzero hx j)).comp x (physicalDistanceLinearMaps j).hasFDerivAt

theorem physical_distance_triple_fderiv {x : Configuration 2} (hx : collisionFree x)
    (v : Configuration 2) :
    fderiv ℝ physicalDistanceTriple x v=physicalDistanceGradient x v := by
  rw [(physical_distance_triple_hasFDerivAt hx).fderiv]
  ext j
  simp only [physicalDistanceDerivative,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,smul_eq_mul,
    physicalDistanceGradient,linearRadiusGradient,div_eq_mul_inv]
  ring

theorem physical_distance_map_norm_le (j : Fin 3) (v : Configuration 2) :
    ‖physicalDistanceLinearMaps j v‖≤2*‖v‖ := by
  have h0 : ‖position v 0‖≤‖v‖ := by
    have hh := WithLp.norm_fst_le Position (configurationSplit (0:Fin 2) v)
    change ‖(configurationSplit (0:Fin 2) v).ofLp.1‖≤‖configurationSplit (0:Fin 2) v‖ at hh
    simpa only [configurationSplit_fst,LinearIsometryEquiv.norm_map] using hh
  have h1 : ‖position v 1‖≤‖v‖ := by
    have hh := WithLp.norm_fst_le Position (configurationSplit (1:Fin 2) v)
    change ‖(configurationSplit (1:Fin 2) v).ofLp.1‖≤‖configurationSplit (1:Fin 2) v‖ at hh
    simpa only [configurationSplit_fst,LinearIsometryEquiv.norm_map] using hh
  fin_cases j
  · change ‖position v 0‖≤2*‖v‖; linarith [norm_nonneg v]
  · change ‖position v 1‖≤2*‖v‖; linarith [norm_nonneg v]
  · change ‖position v 0-position v 1‖≤2*‖v‖
    exact (norm_sub_le _ _).trans (by linarith)

theorem physical_distance_gradient_norm_le (x v : Configuration 2) :
    ‖physicalDistanceGradient x v‖≤2*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  exact (linearRadiusGradient_abs_bound (physicalDistanceLinearMaps j) v x).trans
    (physical_distance_map_norm_le j v)

theorem physical_distance_hessian_norm_le {x : Configuration 2} (hx : collisionFree x)
    (v w : Configuration 2) :
    ‖physicalDistanceHessian x v w‖≤8*‖v‖*‖w‖*physicalInverseDistanceBudget x := by
  have hb : 0≤physicalInverseDistanceBudget x := Finset.sum_nonneg fun j _ => by positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hi : ‖physicalDistanceLinearMaps j x‖⁻¹≤physicalInverseDistanceBudget x :=
    (show ‖physicalDistanceLinearMaps j x‖⁻¹≤∑ k:Fin 3, ‖physicalDistanceLinearMaps k x‖⁻¹ from
      Finset.single_le_sum (f:=fun k:Fin 3 => ‖physicalDistanceLinearMaps k x‖⁻¹)
        (fun k _ => inv_nonneg.mpr (norm_nonneg _)) (Finset.mem_univ j))
  have hc := linearRadiusHessian_bound (physicalDistanceLinearMaps j)
    (physical_distance_maps_nonzero hx j) v w
  have hprod : 2*‖physicalDistanceLinearMaps j v‖*‖physicalDistanceLinearMaps j w‖≤
      8*‖v‖*‖w‖ := by
    have hh := mul_le_mul (physical_distance_map_norm_le j v)
      (physical_distance_map_norm_le j w) (norm_nonneg _) (by positivity)
    nlinarith
  exact hc.trans ((div_le_div_of_nonneg_right hprod (norm_nonneg _)).trans
    (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hi (by positivity : 0≤8*‖v‖*‖w‖)))

theorem physical_inverse_distance_budget_memLp_on_compact
    {K : Set (Configuration 2)} (hK : IsCompact K) :
    MemLp physicalInverseDistanceBudget 2 (volume.restrict K) := by
  have h0 := nuclear_inverse_memLp_two_on_compact (0:Fin 2) hK
  have h1 := nuclear_inverse_memLp_two_on_compact (1:Fin 2) hK
  have h2 := pair_inverse_memLp_two_on_compact (0:Fin 2) 1 (by decide) hK
  have he : physicalInverseDistanceBudget =
      (fun x => ‖position x 0‖⁻¹+‖position x 1‖⁻¹+‖position x 0-position x 1‖⁻¹) := by
    funext x
    simp [physicalInverseDistanceBudget,Fin.sum_univ_three,physicalDistanceLinearMaps,
      electronPositionCLM_apply,pairDifferenceCLM_apply]
  rw [he]
  exact (h0.add h1).add h2

#print axioms physical_distance_triple_hasFDerivAt
#print axioms physical_distance_hessian_norm_le
#print axioms physical_inverse_distance_budget_memLp_on_compact
theorem physical_distance_triple_contDiffAt {x : Configuration 2} (hx : collisionFree x) :
    ContDiffAt ℝ ∞ physicalDistanceTriple x :=
  contDiffAt_pi.mpr fun j => (physicalDistanceLinearMaps j).contDiff.contDiffAt.norm ℝ
    (physical_distance_maps_nonzero hx j)

theorem physical_distance_maps_nonzero_iff (x : Configuration 2) :
    collisionFree x ↔ ∀ j : Fin 3, physicalDistanceLinearMaps j x≠0 := by
  refine ⟨fun hx j => physical_distance_maps_nonzero hx j,?_⟩
  intro h
  have hp : position x 0≠position x 1 := sub_ne_zero.mp (h 2)
  refine ⟨?_,?_⟩
  · intro i
    fin_cases i
    · exact h 0
    · exact h 1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact Ne.symm hp

theorem physical_collisionFree_eventually {x : Configuration 2} (hx : collisionFree x) :
    ∀ᶠ y in 𝓝 x, collisionFree y := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j : Fin 3, physicalDistanceLinearMaps j y≠0 := by
    apply eventually_all.mpr
    intro j
    exact (physicalDistanceLinearMaps j).continuous.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds (physical_distance_maps_nonzero hx j))
  exact hh.mono fun y hy => (physical_distance_maps_nonzero_iff y).mpr hy

theorem actual_linear_radius_gradient_fderiv (A : Configuration 2 →L[ℝ] Position)
    {x : Configuration 2} (hx : A x≠0) (v w : Configuration 2) :
    fderiv ℝ (linearRadiusGradient A v) x w=linearRadiusHessian A v w x := by
  have heq : linearRadiusGradient A v =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fun z => ‖A z‖) y v) := by
    have he : ∀ᶠ y in 𝓝 x, A y≠0 :=
      A.continuous.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hx)
    exact he.mono fun y hy => (actual_linear_radius_fderiv A hy v).symm
  rw [heq.fderiv_eq]
  exact actual_linear_radius_mixed_fderiv A hx v w

theorem actual_linear_radius_gradient_differentiableAt
    (A : Configuration 2 →L[ℝ] Position) {x : Configuration 2} (hx : A x≠0)
    (v : Configuration 2) : DifferentiableAt ℝ (linearRadiusGradient A v) x := by
  have hn := (actual_position_norm_hasFDerivAt (A x) hx).comp x A.hasFDerivAt
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn
  have hnum := A.hasFDerivAt.inner ℝ (hasFDerivAt_const (A v) x)
  have hh := hnum.mul hi
  change HasFDerivAt (fun y => inner ℝ (A y) (A v)*‖A y‖⁻¹) _ x at hh
  change DifferentiableAt ℝ (fun y => inner ℝ (A y) (A v)/‖A y‖) x
  simpa only [div_eq_mul_inv] using hh.differentiableAt

theorem physical_distance_gradient_fderiv {x : Configuration 2} (hx : collisionFree x)
    (v w : Configuration 2) :
    fderiv ℝ (fun y => physicalDistanceGradient y v) x w=physicalDistanceHessian x v w := by
  change fderiv ℝ (fun y j => linearRadiusGradient (physicalDistanceLinearMaps j) v y) x w=_
  rw [fderiv_pi (fun j => actual_linear_radius_gradient_differentiableAt
    (physicalDistanceLinearMaps j) (physical_distance_maps_nonzero hx j) v)]
  ext j
  exact actual_linear_radius_gradient_fderiv (physicalDistanceLinearMaps j)
    (physical_distance_maps_nonzero hx j) v w

theorem physical_distance_triple_mixed_fderiv {x : Configuration 2} (hx : collisionFree x)
    (v w : Configuration 2) :
    fderiv ℝ (fun y => fderiv ℝ physicalDistanceTriple y v) x w=physicalDistanceHessian x v w := by
  have heq : (fun y => fderiv ℝ physicalDistanceTriple y v)=ᶠ[𝓝 x]
      (fun y => physicalDistanceGradient y v) :=
    (physical_collisionFree_eventually hx).mono fun y hy => physical_distance_triple_fderiv hy v
  rw [heq.fderiv_eq]
  exact physical_distance_gradient_fderiv hx v w

#print axioms physical_distance_triple_mixed_fderiv
end ManyBody.S8