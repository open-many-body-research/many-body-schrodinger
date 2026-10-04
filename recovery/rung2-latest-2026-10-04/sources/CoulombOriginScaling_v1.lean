import CoulombDilation_v1
import CoulombPointwiseEquation_v1
import SecondDirectionalLinearAt_v1

/-! Actual spatial dilation of a physical Coulomb eigenfunction. The resulting
equation scales the entire Coulomb potential, including electron repulsion.
No new charge-only Hamiltonian graph is asserted for the scaled function. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem collisionFree_real_smul {N : ℕ} {ε : ℝ} (hε : ε ≠ 0)
    {x : Configuration N} (hx : collisionFree x) : collisionFree (ε • x) := by
  constructor
  · intro i
    rw [position_real_smul]
    exact smul_ne_zero hε (hx.1 i)
  · intro i j hij heq
    simp only [position_real_smul] at heq
    have hz : ε • (position x i-position x j)=0 := by rw [smul_sub,heq,sub_self]
    exact hx.2 i j hij (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hε))

theorem smoothLaplacian_comp_real_smul_at {N : ℕ} (ε : ℝ)
    {g : Configuration N → ℂ} (x : Configuration N)
    (hg : ContDiffAt ℝ 2 g (ε • x)) :
    smoothLaplacian (fun z => g (ε • z)) x = ε^2 • smoothLaplacian g (ε • x) := by
  let L : Configuration N →L[ℝ] Configuration N := ε • ContinuousLinearMap.id ℝ _
  have hd (v : Configuration N) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => g (ε • w)) z v) x v =
        fderiv ℝ (fun z => fderiv ℝ g z (ε • v)) (ε • x) (ε • v) :=
    second_directional_linear_at L x v v hg
  change (∑ k : Coordinate N, fderiv ℝ
    (fun z => fderiv ℝ (fun w => g (ε • w)) z (coordinateVector k)) x (coordinateVector k)) =
      ε^2 • ∑ k : Coordinate N, fderiv ℝ
        (fun z => fderiv ℝ g z (coordinateVector k)) (ε • x) (coordinateVector k)
  simp_rw [hd,second_directional_fderiv_evaluation_at _ _ _ hg]
  simp only [map_smul,smul_apply,smul_smul,← pow_two,Finset.smul_sum]

theorem scalar_coulomb_origin_scaled_classical_equation
    {N : ℕ} {Z E ε : ℝ} (hε : 0 < ε)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g)
    {x : Configuration N} (hx : collisionFree x) :
    ContDiffAt ℝ ∞ (fun z => g (ε • z)) x ∧
      smoothLaplacian (fun z => g (ε • z)) x =
        2*((ε*coulombPotential N Z x-ε^2*E : ℝ) : ℂ)*g (ε • x) := by
  have hs := collisionFree_real_smul hε.ne' hx
  have hgs := scalar_coulomb_continuous_rep_smooth_away hgraph hg hfg hs
  have hscale : ContDiff ℝ ∞ (fun z : Configuration N => ε • z) :=
    (ε • ContinuousLinearMap.id ℝ (Configuration N)).contDiff
  refine ⟨hgs.comp x hscale.contDiffAt,?_⟩
  rw [smoothLaplacian_comp_real_smul_at ε x (hgs.of_le (by simp)),
    scalar_coulomb_continuous_rep_pointwise_equation hgraph hg hfg hs,
    coulombPotential_smul N Z hε]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_pow,
    Complex.ofReal_inv]
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  field_simp
  <;> ring

#print axioms collisionFree_real_smul
#print axioms smoothLaplacian_comp_real_smul_at
#print axioms scalar_coulomb_origin_scaled_classical_equation
end TheoremT.Continuum
