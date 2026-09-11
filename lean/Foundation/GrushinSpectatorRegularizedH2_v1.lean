import GrushinLaplacianTestRewrite_v1
import ProductLocalEllipticH2_v1
import CompactSupportWeightedL2_v1

/-! Preliminary local H2 for a weak Grushin solution once actual second
spectator derivatives are available. No y derivative is assumed. This
qualitative step legitimizes applying compact weak H2 estimates to partial
regularizations; it gives no bound uniform in a regularization parameter. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

theorem grushin_laplacian_rhs_locally_l2
    (c : ℝ) (h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (e : κ → Lp ℂ 2 (volume : Measure (KSSpace × T))) (Ω : Set (KSSpace × T)) :
    ProductLocallyL2On (fun p => -h p+(1-c*‖p.1‖^2) • (∑ j,e j p)) Ω := by
  intro K hK _
  have hA : Continuous (fun p : KSSpace × T => 1-c*‖p.1‖^2) := by fun_prop
  have hm : MemLp (fun p : KSSpace × T => 1-c*‖p.1‖^2) ⊤ (volume.restrict K) :=
    (memLp_indicator_iff_restrict hK.measurableSet).mp
      (compact_indicator_continuous_memLp_top (μ := volume) hK hA)
  have he : MemLp (fun p => ∑ j,e j p) 2 (volume.restrict K) :=
    memLp_finsetSum _ (fun j _ => (Lp.memLp (e j)).mono_measure Measure.restrict_le_self)
  exact ((Lp.memLp h).mono_measure Measure.restrict_le_self).neg.add (he.smul hm)

theorem grushin_local_h2_of_spectator_second_jets
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    (f h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (d e : κ → Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hd : ∀ j, WeakProductL2Directional f (d j) (0,b j))
    (he : ∀ j, WeakProductL2Directional (d j) (e j) (0,b j))
    {Ω : Set (KSSpace × T)} (hΩ : IsOpen Ω)
    (hP : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ProductLocalWeakH2On (f : KSSpace × T → ℂ) Ω := by
  apply product_local_elliptic_h2_on (EuclideanSpace.basisFun (Fin 4) ℝ) b hΩ f
    (fun p => -h p+(1-c*‖p.1‖^2) • (∑ j,e j p))
  · intro K _ _
    exact (Lp.memLp f).mono_measure Measure.restrict_le_self
  · exact grushin_laplacian_rhs_locally_l2 c h e Ω
  · intro φ hφ hc hs
    exact grushin_to_product_laplacian_tests c b f h d e hd he hP hφ hc hs

#print axioms grushin_laplacian_rhs_locally_l2
#print axioms grushin_local_h2_of_spectator_second_jets
end TheoremT.Continuum
