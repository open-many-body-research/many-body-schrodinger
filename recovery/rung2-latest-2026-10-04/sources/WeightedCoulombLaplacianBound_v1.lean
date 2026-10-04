import BoundedMultiplierNormComparison_v1
import WeakCoulombNorm_v2
import HardyCoulombSymmetry_v1

/-! Weighted potential and Laplacian bounds on the actual Coulomb graph.
The potential is untruncated. Weighted first-derivative bounds suffice; no
weighted second-derivative or Laplacian bound is assumed in the final theorem. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem scalar_graph_diagonal_sum {N : ℕ} {Z E : ℝ} {f v : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*f x) :
    (∑ k, e k k) = (2 : ℂ) • v + (-2*(E : ℂ)) • f := by
  obtain ⟨d',e',hd',he',hout⟩ := hg
  have hdeq : d' = d := funext (fun k => weakPartial_unique (hd' k) (hd k))
  subst d'
  have heeq : e' = e := funext (fun k => funext (fun l => weakPartial_unique (he' k l) (he k l)))
  subst e'
  have hrel := scalar_graph_value_decomposition e hout hv
  calc
    (∑ k, e k k) = (2 : ℂ) • v - (2 : ℂ) •
      ((-((1 : ℂ)/2)) • (∑ k, e k k)+v) := by module
    _ = (2 : ℂ) • v - (2 : ℂ) • ((E : ℂ) • f) := by rw [← hrel]
    _ = (2 : ℂ) • v + (-2*(E : ℂ)) • f := by module

theorem scalar_eigen_weighted_laplacian_bound {N : ℕ} {Z E : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N, MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume)
    {A C0 C1 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hfirst : ∀ x k, |fderiv ℝ χ x (coordinateVector k)| ≤ A*|χ x|)
    (h0 : ‖boundedRealMul χ hm f‖ ≤ C0)
    (h1 : ∀ k, ‖boundedRealMul χ hm (d k)‖ ≤ C1) :
    ‖boundedRealMul χ hm (∑ k, e k k)‖ ≤ 2 *
      (|E| * C0 + (2*(|Z| * (N : ℝ)+(N.choose 2 : ℝ))) *
        Real.sqrt ((Fintype.card (Coordinate N) : ℝ)*(C1+A*C0)^2)) := by
  let M := boundedRealMul χ hm
  let P (i : Coordinate N) := boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector i)) (hdm i)
  let D (i : Coordinate N) := M (d i)+P i f
  have hD (i : Coordinate N) : WeakPartial (M f) (D i) i :=
    weakPartial_boundedRealMul (hd i) χ hχ hm (hdm i)
  have hP (i : Coordinate N) : ‖P i f‖ ≤ A*C0 :=
    (boundedRealMul_norm_le_relative _ χ (hdm i) hm A (fun x => hfirst x i) f).trans
      (mul_le_mul_of_nonneg_left h0 hA)
  have hDb (i : Coordinate N) : ‖D i‖ ≤ C1+A*C0 :=
    (norm_add_le _ _).trans (add_le_add (h1 i) (hP i))
  have hsum : (∑ i, ‖D i‖^2) ≤
      (Fintype.card (Coordinate N) : ℝ)*(C1+A*C0)^2 := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hDb i) 2)
  have hV := coulombProductL2_of_hasH1 Z (show HasH1 f from ⟨d,hd⟩)
  let v := hV.toLp (fun x => (coulombPotential N Z x : ℂ)*f x)
  have hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*f x := hV.coeFn_toLp
  have hCV := coulomb_product_norm_le Z (M f) D hD (M v)
    (boundedRealMul_coulomb_ae χ hm hv)
  have hCV' : ‖M v‖ ≤ (2*(|Z| * (N : ℝ)+(N.choose 2 : ℝ))) *
      Real.sqrt ((Fintype.card (Coordinate N) : ℝ)*(C1+A*C0)^2) :=
    hCV.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (by positivity))
  rw [scalar_graph_diagonal_sum hg d e hd he hv,boundedRealMul_add,
    boundedRealMul_smul,boundedRealMul_smul]
  have hn := norm_add_le ((2 : ℂ) • M v) ((-2*(E : ℂ)) • M f)
  simp only [norm_smul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs] at hn
  norm_num at hn
  have hE := mul_le_mul_of_nonneg_left h0 (abs_nonneg E)
  change |E| * ‖M f‖ ≤ |E| * C0 at hE
  change ‖(2 : ℂ) • M v+(-2*(E : ℂ)) • M f‖ ≤ _
  simp only [neg_mul,neg_smul]
  nlinarith

#print axioms scalar_graph_diagonal_sum
#print axioms scalar_eigen_weighted_laplacian_bound
end TheoremT.Continuum
