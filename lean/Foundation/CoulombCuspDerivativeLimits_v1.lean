import RegularizedCoulombCuspDerivatives_v1

noncomputable section
open Filter
open scoped BigOperators Topology
namespace TheoremT.Continuum

def coulombCuspGradient (N : ℕ) (Z : ℝ) (v x : Configuration N) : ℝ :=
  -Z*(∑ i : Fin N, linearRadiusGradient (electronPositionCLM i) v x)+
    (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      linearRadiusGradient (pairDifferenceCLM i j) v x)

def coulombCuspHessian (N : ℕ) (Z : ℝ) (v w x : Configuration N) : ℝ :=
  -Z*(∑ i : Fin N, linearRadiusHessian (electronPositionCLM i) v w x)+
    (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      linearRadiusHessian (pairDifferenceCLM i j) v w x)

theorem regularizedCoulombCusp_partial_tendsto (N : ℕ) (Z : ℝ)
    {δ : ℕ → ℝ} (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : collisionFree x) (v : Configuration N) :
    Tendsto (fun n => fderiv ℝ (regularizedCoulombCusp N Z (δ n)) x v) atTop
      (𝓝 (coulombCuspGradient N Z v x)) := by
  simp_rw [regularizedCoulombCusp_partial_sum _ _ (hp _)]
  have hn := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => regularizedLinearRadius_partial_tendsto (electronPositionCLM i) hp hδ (hx.1 i) v)
  have hh := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => tendsto_finsetSum (Finset.univ.filter (fun j : Fin N => i<j))
      (fun j hj => regularizedLinearRadius_partial_tendsto (pairDifferenceCLM i j) hp hδ
        (sub_ne_zero.mpr (hx.2 i j (ne_of_lt (Finset.mem_filter.mp hj).2))) v))
  exact (hn.const_mul (-Z)).add (hh.const_mul (1/2:ℝ))

theorem regularizedCoulombCusp_hessian_tendsto (N : ℕ) (Z : ℝ)
    {δ : ℕ → ℝ} (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : collisionFree x) (v w : Configuration N) :
    Tendsto (fun n => fderiv ℝ
      (fun y => fderiv ℝ (regularizedCoulombCusp N Z (δ n)) y v) x w) atTop
      (𝓝 (coulombCuspHessian N Z v w x)) := by
  simp_rw [regularizedCoulombCusp_mixed_sum _ _ (hp _)]
  have hn := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => regularizedLinearRadius_hessian_tendsto (electronPositionCLM i) hp hδ (hx.1 i) v w)
  have hh := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => tendsto_finsetSum (Finset.univ.filter (fun j : Fin N => i<j))
      (fun j hj => regularizedLinearRadius_hessian_tendsto (pairDifferenceCLM i j) hp hδ
        (sub_ne_zero.mpr (hx.2 i j (ne_of_lt (Finset.mem_filter.mp hj).2))) v w))
  exact (hn.const_mul (-Z)).add (hh.const_mul (1/2:ℝ))

#print axioms regularizedCoulombCusp_hessian_tendsto
end TheoremT.Continuum
