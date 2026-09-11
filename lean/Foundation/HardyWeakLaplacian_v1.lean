import HardyWeakIBP_v2

/-! Energy, interpolation and complex symmetry on the actual weak derivative
graph. Only genuine WeakPartial witnesses occur in the hypotheses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem spatialL2_real_inner_eq_re {N : ℕ} (f g : SpatialL2 N) :
    inner ℝ f g = (inner ℂ f g).re := by
  change inner ℝ f g = RCLike.re (inner ℂ f g)
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]

theorem weak_second_energy_identity {N : ℕ} {f d e : SpatialL2 N} {k : Coordinate N}
    (hd : WeakPartial f d k) (he : WeakPartial d e k) :
    ‖d‖^2 = -inner ℝ f e := by
  have h := congrArg Complex.re (weakPartial_complex_ibp hd he)
  rw [Complex.neg_re, ← spatialL2_real_inner_eq_re, ← spatialL2_real_inner_eq_re,
    real_inner_self_eq_norm_sq] at h
  linarith

/-- The weak Laplacian energy identity, valid in every finite configuration dimension. -/
theorem weak_laplacian_energy_identity {N : ℕ} {f : SpatialL2 N}
    (d e : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k, WeakPartial (d k) (e k) k) :
    (∑ k : Coordinate N, ‖d k‖^2) = -inner ℝ f (∑ k : Coordinate N, e k) := by
  rw [inner_sum]
  simp_rw [weak_second_energy_identity (hd _) (he _)]
  simp only [Finset.sum_neg_distrib]

/-- The actual weak H² interpolation estimate needed for infinitesimal
relative boundedness; no smooth-core assumption remains. -/
theorem weak_laplacian_interpolation {N : ℕ} {f : SpatialL2 N}
    (d e : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k, WeakPartial (d k) (e k) k) :
    (∑ k : Coordinate N, ‖d k‖^2) ≤ ‖f‖ * ‖∑ k : Coordinate N, e k‖ := by
  rw [weak_laplacian_energy_identity d e hd he]
  exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

theorem weak_second_symmetric {N : ℕ} {f g df dg ef eg : SpatialL2 N} {k : Coordinate N}
    (hdf : WeakPartial f df k) (hdg : WeakPartial g dg k)
    (hef : WeakPartial df ef k) (heg : WeakPartial dg eg k) :
    inner ℂ f eg = inner ℂ ef g := by
  rw [weakPartial_complex_ibp hdf heg, weakPartial_complex_ibp hef hdg, neg_neg]

/-- The true complex L² pairing of the actual weak Laplacian is symmetric. -/
theorem weak_laplacian_symmetric {N : ℕ} {f g : SpatialL2 N}
    (df dg ef eg : Coordinate N → SpatialL2 N)
    (hdf : ∀ k, WeakPartial f (df k) k) (hdg : ∀ k, WeakPartial g (dg k) k)
    (hef : ∀ k, WeakPartial (df k) (ef k) k) (heg : ∀ k, WeakPartial (dg k) (eg k) k) :
    inner ℂ f (∑ k : Coordinate N, eg k) = inner ℂ (∑ k : Coordinate N, ef k) g := by
  rw [inner_sum, sum_inner]
  exact Finset.sum_congr rfl (fun k _ => weak_second_symmetric (hdf k) (hdg k) (hef k) (heg k))

#print axioms weak_laplacian_energy_identity
#print axioms weak_laplacian_interpolation
#print axioms weak_laplacian_symmetric
end TheoremT.Continuum
