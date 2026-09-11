import ProductCutoffJetTransport_v1
import GenericCompactCutoffWeakJet_v1

/-! Actual product-space weak first and second derivatives of a compact smooth
cutoff. The input and output derivatives use all real compact smooth tests and
the actual product Lebesgue measure. The output product rules are proved by
exact transport of the generic Euclidean cutoff-jet theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_compact_cutoff_weak_jet
    {χ : Y × T → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    {d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T))}
    {e : (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T))}
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w) :
    ∃ U : Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ a : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ b : (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, a v =ᵐ[volume] (fun p => χ p • d v p + fderiv ℝ χ p v • f p)) ∧
      (∀ v w, b v w =ᵐ[volume] (fun p =>
        (χ p • e v w p + fderiv ℝ χ p w • d v p) +
        (fderiv ℝ χ p v • d w p +
          fderiv ℝ (fun q => fderiv ℝ χ q v) p w • f p))) := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  let dE (v : WithLp 2 (Y × T)) := productEuclideanLift (d v.ofLp)
  let eE (v w : WithLp 2 (Y × T)) := productEuclideanLift (e v.ofLp w.ofLp)
  have hdE (v : WithLp 2 (Y × T)) :
      WeakL2Directional (productEuclideanLift f) (dE v) v := by
    simpa only [WithLp.toLp_ofLp] using weakL2Directional_productEuclideanLift (hd v.ofLp)
  have heE (v w : WithLp 2 (Y × T)) : WeakL2Directional (dE v) (eE v w) w := by
    simpa only [WithLp.toLp_ofLp] using weakL2Directional_productEuclideanLift (he v.ofLp w.ofLp)
  have hχE : ContDiff ℝ ∞ (χ ∘ WithLp.ofLp (p := 2)) := hχ.comp c.contDiff
  have hcχE : HasCompactSupport (χ ∘ WithLp.ofLp (p := 2)) := hcχ.comp_homeomorph c.toHomeomorph
  obtain ⟨U,a,b,hUa,hab,hU,ha,hb⟩ := generic_compact_cutoff_weak_jet
    hχE hcχE hdE heE
  refine ⟨productEuclideanUnlift U,
    (fun v => productEuclideanUnlift (a (WithLp.toLp 2 v))),
    (fun v w => productEuclideanUnlift (b (WithLp.toLp 2 v) (WithLp.toLp 2 w))),
    ?_,?_,?_,?_,?_⟩
  · intro v
    exact weakProductL2Directional_of_euclidean (hUa (WithLp.toLp 2 v))
  · intro v w
    exact weakProductL2Directional_of_euclidean (hab (WithLp.toLp 2 v) (WithLp.toLp 2 w))
  · filter_upwards [productEuclideanUnlift_ae U,
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae hU,
      productEuclideanLift_toLp_ae f] with p hp hq hf
    change productEuclideanUnlift U p = _
    have hq' : U (WithLp.toLp 2 p) = χ p • productEuclideanLift f (WithLp.toLp 2 p) := by
      simpa only [Function.comp_apply,WithLp.ofLp_toLp] using hq
    exact hp.trans (hq'.trans (congrArg (fun z : ℂ => χ p • z) hf))
  · intro v
    filter_upwards [productEuclideanUnlift_ae (a (WithLp.toLp 2 v)),
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae (ha (WithLp.toLp 2 v)),
      productEuclideanLift_toLp_ae (d v), productEuclideanLift_toLp_ae f] with p hp hq hdv hf
    have hq' : a (WithLp.toLp 2 v) (WithLp.toLp 2 p) =
        χ p • productEuclideanLift (d v) (WithLp.toLp 2 p) +
          fderiv ℝ χ p v • productEuclideanLift f (WithLp.toLp 2 p) := by
      simpa only [dE,Function.comp_apply,WithLp.ofLp_toLp, product_cutoff_lift_directional hχ] using hq
    change productEuclideanUnlift (a (WithLp.toLp 2 v)) p = _
    rw [hp,Function.comp_apply,hq',hdv,hf]
  · intro v w
    filter_upwards [productEuclideanUnlift_ae (b (WithLp.toLp 2 v) (WithLp.toLp 2 w)),
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae
        (hb (WithLp.toLp 2 v) (WithLp.toLp 2 w)),
      productEuclideanLift_toLp_ae (e v w), productEuclideanLift_toLp_ae (d v),
      productEuclideanLift_toLp_ae (d w), productEuclideanLift_toLp_ae f] with p hp hq hevw hdv hdw hf
    have hq' : b (WithLp.toLp 2 v) (WithLp.toLp 2 w) (WithLp.toLp 2 p) =
        (χ p • productEuclideanLift (e v w) (WithLp.toLp 2 p) +
          fderiv ℝ χ p w • productEuclideanLift (d v) (WithLp.toLp 2 p)) +
        (fderiv ℝ χ p v • productEuclideanLift (d w) (WithLp.toLp 2 p) +
          fderiv ℝ (fun q => fderiv ℝ χ q v) p w • productEuclideanLift f (WithLp.toLp 2 p)) := by
      rw [product_cutoff_lift_second_directional hχ] at hq
      simpa only [dE,eE,Function.comp_apply,WithLp.ofLp_toLp,
        product_cutoff_lift_directional hχ] using hq
    change productEuclideanUnlift (b (WithLp.toLp 2 v) (WithLp.toLp 2 w)) p = _
    rw [hp,Function.comp_apply,hq',hevw,hdv,hdw,hf]

#print axioms product_compact_cutoff_weak_jet
end TheoremT.Continuum
