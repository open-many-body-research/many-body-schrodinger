import SmoothRadialEnergyL2_v1
import WeakCoulombNorm_v2

/-! Nonlinear power-test energy control for actual continuum Coulomb H2
eigenfunctions. The estimate is uniform in both positive smooth truncation
parameters. Its polynomial power coefficient is separate from the paper's
sharper nonsmooth-truncation coefficient. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_eigen_smooth_power_energy {N : ℕ} {Z E a b r : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r)
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k) :
    (∑ k, ‖smoothRadialPowerDerivativeL2 ha hab hr f (d k)‖^2) ≤
      (4*(1+4*r^2)*|E| + 4*(1+4*r^2)^2*
        (2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2)*‖smoothRadialPowerL2 ha hab hr f‖^2 := by
  let g := smoothRadialPowerL2 ha hab hr f
  let dg := fun k => smoothRadialPowerDerivativeL2 ha hab hr f (d k)
  let hr2 : 0 ≤ 2*r := by positivity
  let t := smoothRadialPowerL2 ha hab hr2 f
  let dt := fun k => smoothRadialPowerDerivativeL2 ha hab hr2 f (d k)
  have hdg (k : Coordinate N) : WeakPartial g (dg k) k := weakH1_smoothRadialPower ha hab hr d hd k
  have hdt (k : Coordinate N) : WeakPartial t (dt k) k := weakH1_smoothRadialPower ha hab hr2 d hd k
  have hVf := coulombProductL2_of_scalar_graph hg
  have hVg := coulombProductL2_of_hasH1 Z (show HasH1 g from ⟨dg,hdg⟩)
  let vf : SpatialL2 N := hVf.toLp _
  let vg : SpatialL2 N := hVg.toLp _
  have hvf : vf =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*f x := hVf.coeFn_toLp
  have hvg : vg =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*g x := hVg.coeFn_toLp
  have hpair := scalar_graph_h1_pairing_real hg d dt hd hdt hvf
  have hl : inner ℝ t ((E : ℂ) • f) = E*‖g‖^2 := by
    have hh : inner ℝ t ((E : ℂ) • f) = E*inner ℝ t f := by
      simp only [spatialL2_real_inner_eq_re]
      rw [inner_smul_right]
      simp
    rw [hh,smoothRadialPowerL2_inner ha hab hr]
  have hv := smoothRadialPowerL2_potential_inner ha hab hr f vf vg
    (coulombPotential N Z) hvf hvg
  change inner ℝ t vf = inner ℝ g vg at hv
  rw [hl,hv] at hpair
  let D : ℝ := ∑ k : Coordinate N, ‖dg k‖^2
  let M : ℝ := 1+4*r^2
  let C : ℝ := 2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hM : 0 < M := by dsimp [M]; positivity
  have hgrad : D ≤ M*∑ k, inner ℝ (dt k) (d k) :=
    smoothRadialPowerL2_gradient_energy ha hab hr f d
  have hineq : D ≤ 2*M*(E*‖g‖^2-inner ℝ g vg) := by nlinarith
  have hnorm : ‖vg‖ ≤ C*Real.sqrt D := coulomb_product_norm_le Z g dg hdg vg hvg
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm g vg)
  have hnv := mul_le_mul_of_nonneg_left hnorm (norm_nonneg g)
  have he := mul_le_mul_of_nonneg_right (le_abs_self E) (sq_nonneg ‖g‖)
  have hlarge : D ≤ 2*M*(|E| *‖g‖^2+C*Real.sqrt D*‖g‖) := by nlinarith
  have hs := sq_nonneg (Real.sqrt D-2*M*C*‖g‖)
  rw [sub_sq,mul_pow,Real.sq_sqrt hD] at hs
  change D ≤ (4*M*|E| +4*M^2*C^2)*‖g‖^2
  nlinarith

#print axioms scalar_eigen_smooth_power_energy
end TheoremT.Continuum
