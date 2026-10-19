import FermionicGraphAssembly_v2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual complex conjugation on continuum L² and weak Coulomb graphs. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def spatialConj {N : ℕ} : SpatialL2 N →L[ℝ] SpatialL2 N :=
  Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 volume

theorem spatialConj_coeFn {N : ℕ} (f : SpatialL2 N) :
    ∀ᵐ x, spatialConj f x = starRingEnd ℂ (f x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem spatialConj_smul {N : ℕ} (c : ℂ) (f : SpatialL2 N) :
    spatialConj (c • f) = (starRingEnd ℂ c) • spatialConj f := by
  apply Lp.ext
  filter_upwards [spatialConj_coeFn (c • f),spatialConj_coeFn f,
    Lp.coeFn_smul c f,Lp.coeFn_smul (starRingEnd ℂ c) (spatialConj f)] with x h1 h2 h3 h4
  rw [h1,h3,h4]
  change starRingEnd ℂ (c * f x) = starRingEnd ℂ c * spatialConj f x
  rw [h2,map_mul]

theorem spatialConj_involutive {N : ℕ} (f : SpatialL2 N) :
    spatialConj (spatialConj f) = f := by
  apply Lp.ext
  filter_upwards [spatialConj_coeFn (spatialConj f),spatialConj_coeFn f] with x h1 h2
  rw [h1,h2,Complex.conj_conj]

theorem spatialConj_pullback {N : ℕ} (π : Equiv.Perm (Fin N)) (f : SpatialL2 N) :
    spatialConj (pullback π f) = pullback π (spatialConj f) := by
  apply Lp.ext
  have h := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae (spatialConj_coeFn f)
  filter_upwards [spatialConj_coeFn (pullback π f),pullback_coeFn_ae π f,
    pullback_coeFn_ae π (spatialConj f),h] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

theorem spatialConj_integral_test {N : ℕ} (f : SpatialL2 N) (φ : Configuration N → ℝ) :
    (∫ x, φ x • spatialConj f x) = starRingEnd ℂ (∫ x, φ x • f x) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [spatialConj_coeFn f] with x hx
  rw [hx]
  change (φ x : ℂ) * starRingEnd ℂ (f x) = starRingEnd ℂ ((φ x : ℂ) * f x)
  rw [map_mul,Complex.conj_ofReal]

theorem weakPartial_conj {N : ℕ} {f d : SpatialL2 N} {k : Coordinate N}
    (h : WeakPartial f d k) : WeakPartial (spatialConj f) (spatialConj d) k := by
  intro φ hφ hc
  rw [spatialConj_integral_test,spatialConj_integral_test,h φ hφ hc,map_neg]

theorem scalar_graph_conj {N : ℕ} {Z : ℝ} {f h : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) :
    scalarHamiltonianGraph N Z (spatialConj f) (spatialConj h) := by
  obtain ⟨d,e,hd,he,hout⟩ := hg
  refine ⟨fun k => spatialConj (d k),fun k l => spatialConj (e k l),
    fun k => weakPartial_conj (hd k),fun k l => weakPartial_conj (he k l),?_⟩
  have hall : ∀ᵐ x, ∀ k : Coordinate N,
      spatialConj (e k k) x = starRingEnd ℂ (e k k x) := by
    rw [ae_all_iff]
    exact fun k => spatialConj_coeFn (e k k)
  filter_upwards [spatialConj_coeFn h,spatialConj_coeFn f,hall,hout] with x hh hf heq ho
  rw [hh,hf]
  simp_rw [heq]
  have hv := congrArg (starRingEnd ℂ) ho
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
    change starRingEnd ℂ ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal 2
  simpa [htwo] using hv

theorem spatialConj_fixed_im_zero {N : ℕ} {f : SpatialL2 N} (h : spatialConj f = f) :
    ∀ᵐ x, (f x).im = 0 := by
  have ha := spatialConj_coeFn f
  rw [h] at ha
  filter_upwards [ha] with x hx
  have hi := congrArg Complex.im hx
  simp only [Complex.conj_im] at hi
  linarith

#print axioms weakPartial_conj
#print axioms scalar_graph_conj
end TheoremT.Continuum
