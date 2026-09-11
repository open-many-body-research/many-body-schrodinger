import BoundedSmoothMultiplierJet_v1
import LocalWeakLaplacian_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum

theorem compact_cutoff_weak_jet {N : ℕ}
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l) :
    ∃ u : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial u (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        u =ᵐ[volume] (fun x => χ x • f x) ∧
        (∀ k, a k =ᵐ[volume] (fun x => χ x • d k x+fderiv ℝ χ x (coordinateVector k) • f x)) ∧
        (∀ k l, b k l =ᵐ[volume] (fun x =>
          (χ x • e k l x+fderiv ℝ χ x (coordinateVector l) • d k x)+
          (fderiv ℝ χ x (coordinateVector k) • d l x+
            fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector l) • f x))) := by
  have h₀ : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hc volume
  have hcD (k : Coordinate N) : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hD (k : Coordinate N) : MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume :=
    (hcD k).continuous.memLp_top_of_hasCompactSupport (hc.fderiv_apply ℝ (coordinateVector k)) volume
  have hE (k l : Coordinate N) : MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector l)) ⊤ volume :=
    (((hcD k).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      ((hc.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector l)) volume
  let U := boundedRealMul χ h₀
  let D (k : Coordinate N) := boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hD k)
  let E (k l : Coordinate N) := boundedRealMul (fun x => fderiv ℝ
    (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector l)) (hE k l)
  let a (k : Coordinate N) := U (d k)+D k f
  let b (k l : Coordinate N) := (U (e k l)+D l (d k))+(D k (d l)+E k l f)
  refine ⟨U f,a,b,?_,?_,boundedRealMul_ae _ h₀ f,?_,?_⟩
  · intro k
    exact weakPartial_boundedRealMul (hd k) χ hχ h₀ (hD k)
  · intro k l
    exact boundedRealMul_second_weakPartial (hd l) (he k l) χ hχ h₀ (hD k) (hD l) (hE k l)
  · intro k
    filter_upwards [Lp.coeFn_add (U (d k)) (D k f),boundedRealMul_ae _ h₀ (d k),
      boundedRealMul_ae _ (hD k) f] with x hx hux hdx
    change (U (d k)+D k f) x = _
    rw [hx]
    change U (d k) x+D k f x = _
    rw [hux,hdx]
  · intro k l
    filter_upwards [Lp.coeFn_add (U (e k l)+D l (d k)) (D k (d l)+E k l f),
      Lp.coeFn_add (U (e k l)) (D l (d k)),Lp.coeFn_add (D k (d l)) (E k l f),
      boundedRealMul_ae _ h₀ (e k l),boundedRealMul_ae _ (hD l) (d k),
      boundedRealMul_ae _ (hD k) (d l),boundedRealMul_ae _ (hE k l) f] with x hx hx1 hx2 hu hd1 hd2 hh
    change ((U (e k l)+D l (d k))+(D k (d l)+E k l f)) x = _
    rw [hx]
    change (U (e k l)+D l (d k)) x+(D k (d l)+E k l f) x = _
    rw [hx1,hx2]
    change (U (e k l) x+D l (d k) x)+(D k (d l) x+E k l f x) = _
    rw [hu,hd1,hd2,hh]

#print axioms compact_cutoff_weak_jet
end TheoremT.Continuum
