import CoulombWeakFormPairing_v1
import WeightedGradientIdentity_v1
import ScalarCoulombForm_v1

/-! Exact weighted eigenfunction identity on the physical Coulomb model.
Only an actual H² eigenpair and a bounded smooth weight with bounded first
derivatives are required. The weighted test is in H¹; no D(H²) is assumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem scalar_eigen_weighted_form_value {N : ℕ} {Z E : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume) :
    scalarCoulombH1FormValue N Z (boundedRealMul χ hm f)
      (E * ‖boundedRealMul χ hm f‖^2 +
        (1/2 : ℝ) * ∑ k : Coordinate N,
          ‖boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f‖^2) := by
  classical
  obtain ⟨d,hd,_⟩ := scalar_graph_hasH2 hg
  let M := boundedRealMul χ hm
  let B : Coordinate N → SpatialL2 N := fun k =>
    boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f
  let D : Coordinate N → SpatialL2 N := fun k => M (d k) + B k
  have hD (k : Coordinate N) : WeakPartial (M f) (D k) k :=
    weakPartial_boundedRealMul (hd k) χ hχ hm (hdm k)
  let A : Coordinate N → SpatialL2 N := fun k => M (D k) +
    boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) (M f)
  have hA (k : Coordinate N) : WeakPartial (M (M f)) (A k) k :=
    weakPartial_boundedRealMul (hD k) χ hχ hm (hdm k)
  have hV := coulombProductL2_of_scalar_graph hg
  let v : SpatialL2 N := hV.toLp _
  have hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x := hV.coeFn_toLp
  have hpair := scalar_graph_h1_pairing_real hg d A hd hA hv
  have hleft : inner ℝ (M (M f)) ((E : ℂ) • f) = E * ‖M f‖^2 := by
    have he : inner ℝ (M (M f)) ((E : ℂ) • f) = E * inner ℝ (M (M f)) f := by
      simp only [spatialL2_real_inner_eq_re]
      rw [inner_smul_right]
      simp
    rw [he]
    change E * inner ℝ (boundedRealMul χ hm (M f)) f = E * ‖M f‖^2
    rw [boundedRealMul_real_inner,real_inner_self_eq_norm_sq]
  have hp : inner ℝ (M (M f)) v = inner ℝ (M f) (M v) :=
    boundedRealMul_real_inner χ hm (M f) v
  rw [hleft,hp] at hpair
  have hsum : (∑ k, ‖D k‖^2) = (∑ k, inner ℝ (A k) (d k)) + ∑ k, ‖B k‖^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact boundedRealMul_gradient_identity χ
      (fun x => fderiv ℝ χ x (coordinateVector k)) hm (hdm k) f (d k)
  refine ⟨D,M v,hD,boundedRealMul_coulomb_ae χ hm hv,?_⟩
  unfold scalarCoulombH1Energy
  rw [← spatialL2_real_inner_eq_re,hsum]
  change E * ‖M f‖^2 + (1/2 : ℝ) * (∑ k, ‖B k‖^2) = _
  linarith

theorem scalar_eigen_weighted_form_identity {N : ℕ} {Z E q : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume)
    (hq : scalarCoulombH1FormValue N Z (boundedRealMul χ hm f) q) :
    q - E * ‖boundedRealMul χ hm f‖^2 =
      (1/2 : ℝ) * ∑ k : Coordinate N,
        ‖boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f‖^2 := by
  have h := scalarCoulombH1FormValue_unique hq (scalar_eigen_weighted_form_value hg χ hχ hm hdm)
  linarith

#print axioms scalar_eigen_weighted_form_value
#print axioms scalar_eigen_weighted_form_identity
end TheoremT.Continuum
