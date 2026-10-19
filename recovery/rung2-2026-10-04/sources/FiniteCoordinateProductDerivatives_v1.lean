import GrushinRescaledCutoffCoefficients_v1
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Exact coordinate derivatives of a finite tensor product. These lemmas
will be instantiated with the seven actual coordinate projections of the
Grushin product space; no derivative estimate is supplied as a premise. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateProduct (L : ι → E →L[ℝ] ℝ) (φ : ι → ℝ → ℝ) (x : E) : ℝ :=
  ∏ i, φ i (L i x)

theorem coordinateProduct_contDiff (L : ι → E →L[ℝ] ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) : ContDiff ℝ ∞ (coordinateProduct L φ) :=
  contDiff_prod (fun i _ => (hφ i).comp (L i).contDiff)

theorem scalar_comp_clm_directional (L : E →L[ℝ] ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (fun y => φ (L y)) x v = deriv φ (L x) * L v := by
  have hh := ((hφ.differentiable (by simp) (L x)).hasDerivAt).comp_hasFDerivAt x
    L.hasFDerivAt
  change HasFDerivAt (fun y => φ (L y)) _ x at hh
  rw [hh.fderiv]
  rfl

theorem coordinateProduct_first (L : ι → E →L[ℝ] ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (j : ι) (v : E)
    (hv : ∀ i, L i v = if i = j then 1 else 0) (x : E) :
    fderiv ℝ (coordinateProduct L φ) x v =
      (∏ i ∈ Finset.univ.erase j, φ i (L i x)) * deriv (φ j) (L j x) := by
  change (fderiv ℝ (fun y => ∏ i, φ i (L i y)) x) v = _
  have hf := congrArg (fun A : E →L[ℝ] ℝ => A v)
    (fderiv_finsetProd (u := Finset.univ) (g := fun i y => φ i (L i y))
      (fun i _ => ((hφ i).comp (L i).contDiff).differentiable (by simp) x))
  simpa [Finset.prod_apply,ContinuousLinearMap.sum_apply,
    scalar_comp_clm_directional,hφ,hv,mul_ite] using hf

theorem coordinateProduct_update (L : ι → E →L[ℝ] ℝ) (φ : ι → ℝ → ℝ)
    (j : ι) (g : ℝ → ℝ) (x : E) :
    coordinateProduct L (Function.update φ j g) x =
      (∏ i ∈ Finset.univ.erase j, φ i (L i x)) * g (L j x) := by
  unfold coordinateProduct
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

theorem coordinateProduct_second (L : ι → E →L[ℝ] ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (j : ι) (v : E)
    (hv : ∀ i, L i v = if i = j then 1 else 0) (x : E) :
    fderiv ℝ (fun y => fderiv ℝ (coordinateProduct L φ) y v) x v =
      (∏ i ∈ Finset.univ.erase j, φ i (L i x)) * deriv (deriv (φ j)) (L j x) := by
  let ψ := Function.update φ j (deriv (φ j))
  have hψ (i : ι) : ContDiff ℝ ∞ (ψ i) := by
    by_cases hi : i = j
    · subst i
      simpa [ψ] using (contDiff_infty_iff_deriv.mp (hφ j)).2
    · simpa [ψ,Function.update_of_ne hi] using hφ i
  have he : (fun y => fderiv ℝ (coordinateProduct L φ) y v) = coordinateProduct L ψ := by
    funext y
    rw [coordinateProduct_first L hφ j v hv]
    exact (coordinateProduct_update L φ j (deriv (φ j)) y).symm
  rw [he,coordinateProduct_first L hψ j v hv]
  have hp : (∏ i ∈ Finset.univ.erase j, ψ i (L i x)) =
      ∏ i ∈ Finset.univ.erase j, φ i (L i x) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [ψ,Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hp]
  simp only [ψ,Function.update_self]

theorem coordinateProduct_first_bound (L : ι → E →L[ℝ] ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (j : ι) (v : E)
    (hv : ∀ i, L i v = if i = j then 1 else 0)
    (hM : ∀ i t, |φ i t| ≤ 1) {C : ℝ}
    (hD : ∀ i t, |deriv (φ i) t| ≤ C) (x : E) :
    |fderiv ℝ (coordinateProduct L φ) x v| ≤ C := by
  rw [coordinateProduct_first L hφ j v hv,abs_mul]
  have hp : |∏ i ∈ Finset.univ.erase j, φ i (L i x)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hM i _)
  exact (mul_le_mul hp (hD j _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans
    (by simp)

theorem coordinateProduct_second_bound (L : ι → E →L[ℝ] ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (j : ι) (v : E)
    (hv : ∀ i, L i v = if i = j then 1 else 0)
    (hM : ∀ i t, |φ i t| ≤ 1) {C : ℝ}
    (hD : ∀ i t, |deriv (deriv (φ i)) t| ≤ C) (x : E) :
    |fderiv ℝ (fun y => fderiv ℝ (coordinateProduct L φ) y v) x v| ≤ C := by
  rw [coordinateProduct_second L hφ j v hv,abs_mul]
  have hp : |∏ i ∈ Finset.univ.erase j, φ i (L i x)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hM i _)
  exact (mul_le_mul hp (hD j _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans
    (by simp)

#print axioms coordinateProduct_first
#print axioms coordinateProduct_second
end TheoremT.Continuum
