import CoulombCuspWeakLaplacian_v1
import LinearRadiusLimits_v1

noncomputable section
open Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Continuum

def regularizedCoulombCusp (N : ℕ) (Z δ : ℝ) (x : Configuration N) : ℝ :=
  -Z*(∑ i : Fin N, regularizedLinearRadius (electronPositionCLM i) δ x)+
    (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      regularizedLinearRadius (pairDifferenceCLM i j) δ x)

theorem regularizedCoulombCusp_contDiff (N : ℕ) (Z : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (regularizedCoulombCusp N Z δ) := by
  unfold regularizedCoulombCusp
  apply ContDiff.add
  · apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro i _
    exact regularizedLinearRadius_contDiff _ hδ
  · apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact regularizedLinearRadius_contDiff _ hδ

theorem regularizedCoulombCusp_tendsto (N : ℕ) (Z : ℝ) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (x : Configuration N) :
    Tendsto (fun n => regularizedCoulombCusp N Z (δ n) x) atTop (𝓝 (coulombCusp N Z x)) := by
  have hn := tendsto_finset_sum (Finset.univ : Finset (Fin N))
    (fun i _ => regularizedLinearRadius_tendsto (electronPositionCLM i) hδ x)
  have hp := tendsto_finset_sum (Finset.univ : Finset (Fin N))
    (fun i _ => tendsto_finset_sum (Finset.univ.filter (fun j : Fin N => i<j))
      (fun j _ => regularizedLinearRadius_tendsto (pairDifferenceCLM i j) hδ x))
  exact (hn.const_mul (-Z)).add (hp.const_mul (1/2:ℝ))

#print axioms regularizedCoulombCusp_contDiff
#print axioms regularizedCoulombCusp_tendsto
end TheoremT.Continuum
