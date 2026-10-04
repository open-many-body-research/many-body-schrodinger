import ManyBody.S8.Internal.PhysicalPolynomialMomentBounds

/-! All polynomial H2 moments of the actual scalar Coulomb state and its
ordered first and second weak derivatives. A common weighted norm precedes
every moment order. These are actual L2 functions, not formal moments or an
algorithm for evaluating their integrals. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalH2PolynomialMoments {N : ℕ} (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    ∃ F : SpatialL2 N, ∃ D : Coordinate N → SpatialL2 N,
    ∃ E : Coordinate N → Coordinate N → SpatialL2 N,
      (F : Configuration N → ℂ) =ᵐ[volume] (fun x => ‖x‖^k • f x) ∧
      (∀ i, (D i : Configuration N → ℂ) =ᵐ[volume] (fun x => ‖x‖^k • d i x)) ∧
      (∀ i j, (E i j : Configuration N → ℂ) =ᵐ[volume] (fun x => ‖x‖^k • e i j x)) ∧
      Real.sqrt (‖F‖^2 + (∑ i, ‖D i‖^2) + (∑ i, ∑ j, ‖E i j‖^2)) ≤
        ((k.factorial : ℝ)/a^k)*C

theorem physical_H2_polynomial_moments_of_exponential_components
    {N : ℕ} {a : ℝ} (ha : 0 < a) (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (hdw : ∀ i, MemLp (fun x => Real.exp (a*‖x‖) • d i x) 2 volume)
    (hew : ∀ i j, MemLp (fun x => Real.exp (a*‖x‖) • e i j x) 2 volume) :
    PhysicalH2PolynomialMoments f d e a := by
  let U := hw.toLp (fun x => Real.exp (a*‖x‖) • f x)
  let V (i : Coordinate N) := (hdw i).toLp (fun x => Real.exp (a*‖x‖) • d i x)
  let W (i j : Coordinate N) := (hew i j).toLp (fun x => Real.exp (a*‖x‖) • e i j x)
  let S := ‖U‖^2 + (∑ i, ‖V i‖^2) + (∑ i, ∑ j, ‖W i j‖^2)
  refine ⟨Real.sqrt S,Real.sqrt_nonneg _,?_⟩
  intro k
  let F := physicalPolynomialMomentL2 ha f hw k
  let D (i : Coordinate N) := physicalPolynomialMomentL2 ha (d i) (hdw i) k
  let E (i j : Coordinate N) := physicalPolynomialMomentL2 ha (e i j) (hew i j) k
  refine ⟨F,D,E,physicalPolynomialMomentL2_ae ha f hw k,
    fun i => physicalPolynomialMomentL2_ae ha (d i) (hdw i) k,
    fun i j => physicalPolynomialMomentL2_ae ha (e i j) (hew i j) k,?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _)
    (physicalPolynomialMomentL2_norm_bound ha f hw k) 2
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _)
      (physicalPolynomialMomentL2_norm_bound ha (d i) (hdw i) k) 2)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _)
        (physicalPolynomialMomentL2_norm_bound ha (e i j) (hew i j) k) 2))
  simp only [mul_pow,← Finset.mul_sum] at h0 h1 h2
  have h : ‖F‖^2+(∑ i, ‖D i‖^2)+(∑ i, ∑ j, ‖E i j‖^2) ≤
      ((k.factorial : ℝ)/a^k)^2*S := by
    dsimp [F,D,E,U,V,W,S] at h0 h1 h2 ⊢
    nlinarith
  apply (Real.sqrt_le_sqrt h).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show 0 ≤ (k.factorial : ℝ)/a^k by positivity)]

theorem scalar_eigen_H2_polynomial_moments
    {N : ℕ} {Z E a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ i, WeakPartial f (d i) i) (he : ∀ i j, WeakPartial (d i) (e i j) j)
    (ha : 0 < a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    PhysicalH2PolynomialMoments f d e a :=
  physical_H2_polynomial_moments_of_exponential_components ha f d e hw
    (scalar_eigen_first_derivative_exponential_decay hg d hd ha.le hw)
    (scalar_eigen_second_derivative_exponential_decay hg d e hd he ha.le hw)

theorem twoElectron_ground_H2_polynomial_moments_of_graph (Z : ℝ) (hZ : 2 ≤ Z)
    {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal : ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ i, WeakPartial f (d i) i) (he : ∀ i j, WeakPartial (d i) (e i j) j)
    {a : ℝ} (ha : 0 < a) (hgap : a^2 < Z^2/112) :
    PhysicalH2PolynomialMoments f d e a :=
  scalar_eigen_H2_polynomial_moments hg d e hd he ha
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_H2_polynomial_moments (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ f : SpatialL2 2, ‖f‖ = 1 ∧ pullback twoElectronSwap f = f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
      (∀ᵐ x, (f x).im = 0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f = f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ i, WeakPartial f (d i) i) ∧ (∀ i j, WeakPartial (d i) (e i j) j) ∧
        ∀ a : ℝ, 0 < a → a^2 < Z^2/112 → PhysicalH2PolynomialMoments f d e a := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_H2_polynomial_moments_of_graph Z hZ hg d e hd he ha hgap⟩

#print axioms physical_H2_polynomial_moments_of_exponential_components
#print axioms scalar_eigen_H2_polynomial_moments
#print axioms twoElectron_ground_H2_polynomial_moments_of_graph
#print axioms twoElectron_physical_ground_with_H2_polynomial_moments
end ManyBody.S8
