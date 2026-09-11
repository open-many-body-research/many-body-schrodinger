import LocalizedCuspH2Multiplier_v1

/-! Actual weak product jet with explicit almost-everywhere physical formulas.
The input derivatives are genuine weak derivatives on the unchanged domain. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem localizedCusp_weak_jet (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l) :
    ∃ g : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial g (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        g =ᵐ[volume] (fun x => localizedCusp N Z χ x • f x) ∧
        (∀ k, a k =ᵐ[volume] (fun x =>
          localizedCusp N Z χ x • d k x+
            localizedCuspGradient N Z χ (coordinateVector k) x • f x)) ∧
        (∀ k l, b k l =ᵐ[volume] (fun x =>
          (localizedCusp N Z χ x • e k l x+
            localizedCuspGradient N Z χ (coordinateVector l) x • d k x)+
          (localizedCuspGradient N Z χ (coordinateVector k) x • d l x+
            localizedCuspHessian N Z χ (coordinateVector k) (coordinateVector l) x • f x))) := by
  have hf : HasH1 f := ⟨d,hd⟩
  obtain ⟨h₀,hUlim⟩ := localizedCusp_value_multiplier_limit N Z hχ hc
  have hexD (k : Coordinate N) := localizedCusp_gradient_multiplier_limit N Z hχ hc (coordinateVector k)
  choose hD hDlim using hexD
  have hexE (k l : Coordinate N) := localizedCusp_hessian_multiplier_limit N Z hχ hc
    (coordinateVector k) (coordinateVector l) f hf
  choose hE hElim using hexE
  let U := boundedRealMul (localizedCusp N Z χ) h₀
  let D (k : Coordinate N) := boundedRealMul (localizedCuspGradient N Z χ (coordinateVector k)) (hD k)
  let E (k l : Coordinate N) : SpatialL2 N := (hE k l).toLp
    (fun x => localizedCuspHessian N Z χ (coordinateVector k) (coordinateVector l) x • f x)
  let a (k : Coordinate N) := U (d k)+D k f
  let b (k l : Coordinate N) := (U (e k l)+D l (d k))+(D k (d l)+E k l)
  refine ⟨U f,a,b,?_,?_,boundedRealMul_ae _ h₀ f,?_,?_⟩
  · intro k
    exact WeakPartial.of_tendsto
      (fun n => weakPartial_boundedRealMul (hd k) (regularizedLocalizedCusp N Z χ n)
        (regularizedLocalizedCusp_contDiff N Z hχ n)
        (regularizedLocalizedCusp_memLp_top N Z hχ hc n)
        (regularizedLocalizedCusp_partial_memLp_top N Z hχ hc n (coordinateVector k)))
      (hUlim f) ((hUlim (d k)).add (hDlim k f))
  · intro k l
    exact WeakPartial.of_tendsto
      (fun n => boundedRealMul_second_weakPartial (hd l) (he k l) (regularizedLocalizedCusp N Z χ n)
        (regularizedLocalizedCusp_contDiff N Z hχ n)
        (regularizedLocalizedCusp_memLp_top N Z hχ hc n)
        (regularizedLocalizedCusp_partial_memLp_top N Z hχ hc n (coordinateVector k))
        (regularizedLocalizedCusp_partial_memLp_top N Z hχ hc n (coordinateVector l))
        (regularizedLocalizedCusp_mixed_memLp_top N Z hχ hc n (coordinateVector k) (coordinateVector l)))
      ((hUlim (d k)).add (hDlim k f))
      (((hUlim (e k l)).add (hDlim l (d k))).add ((hDlim k (d l)).add (hElim k l)))
  · intro k
    filter_upwards [Lp.coeFn_add (U (d k)) (D k f),
      boundedRealMul_ae _ h₀ (d k),boundedRealMul_ae _ (hD k) f] with x hx hux hdx
    change (U (d k)+D k f) x = _
    rw [hx]
    change U (d k) x+D k f x = _
    rw [hux,hdx]
  · intro k l
    filter_upwards [Lp.coeFn_add (U (e k l)+D l (d k)) (D k (d l)+E k l),
      Lp.coeFn_add (U (e k l)) (D l (d k)),Lp.coeFn_add (D k (d l)) (E k l),
      boundedRealMul_ae _ h₀ (e k l),boundedRealMul_ae _ (hD l) (d k),
      boundedRealMul_ae _ (hD k) (d l),(hE k l).coeFn_toLp] with x hx hx1 hx2 hu hd1 hd2 hh
    change ((U (e k l)+D l (d k))+(D k (d l)+E k l)) x = _
    rw [hx]
    change (U (e k l)+D l (d k)) x+(D k (d l)+E k l) x = _
    rw [hx1,hx2]
    change (U (e k l) x+D l (d k) x)+(D k (d l) x+E k l x) = _
    rw [hu,hd1,hd2,hh]

#print axioms localizedCusp_weak_jet
end TheoremT.Continuum
