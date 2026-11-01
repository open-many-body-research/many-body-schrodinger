import CoulombFirstDerivativeDecay_v1
import CoulombSecondDerivativeDecay_v1
import ExponentialH2Tail_v1

/-! Actual H² tail transfer for arbitrary finite electron count. All ordered
mixed weak derivatives occur. The supplied L² decay is the only decay premise;
no attainment, isolation, uniqueness or binding assumption is imposed. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem scalar_eigen_H2_exponential_tail {N : ℕ} {Z E a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0 ≤ a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C :=
  exponential_H2_tail_of_weighted_components ha f d e hw
    (scalar_eigen_first_derivative_exponential_decay hg d hd ha hw)
    (scalar_eigen_second_derivative_exponential_decay hg d e hd he ha hw)

#print axioms scalar_eigen_H2_exponential_tail
end TheoremT.Continuum
