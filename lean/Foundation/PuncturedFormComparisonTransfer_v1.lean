import PuncturedIntegralDensity_v1

/-! Transfer a proved scalar hydrogen comparison on the actual punctured smooth
core to the full actual weak H¹ domain. The core comparison remains an explicit
hypothesis. No spectral comparison or angular/radial inequality is assumed to
have been discharged by this continuity theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum

theorem punctured_core_rankOne_bound_extends_weakH1
    (Z β C : ℝ) (l : SpatialL2 1 →L[ℂ] ℂ)
    (hcore : ∀ (u : Configuration 1 → ℂ) (g v : SpatialL2 1)
      (dg : Coordinate 1 → SpatialL2 1),
      ContDiff ℝ ∞ u → HasCompactSupport u → (0 : Configuration 1) ∉ tsupport u →
      (g =ᵐ[volume] u) →
      (∀ k, dg k =ᵐ[volume] smoothPartial u k) →
      (v =ᵐ[volume] fun x => g x / (‖x‖ : ℂ)) →
      β * ‖g‖ ^ 2 ≤ (1 / 2 : ℝ) * (∑ k : Coordinate 1, ‖dg k‖ ^ 2) -
        Z * (inner ℂ g v).re + C * ‖l g‖ ^ 2)
    (f v : SpatialL2 1) (d : Coordinate 1 → SpatialL2 1)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ)) :
    β * ‖f‖ ^ 2 ≤ (1 / 2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖ ^ 2) -
      Z * (inner ℂ f v).re + C * ‖l f‖ ^ 2 := by
  classical
  obtain ⟨u,g,dg,hu,hc,hzero,hgu,hdgu,hdg,hH2,hgt,hdt⟩ :=
    weakH1_punctured_smooth_compact_graph_sequence d hd
  let vnm (n : ℕ) := weakH1_div_configuration_norm_memLp (g n) (dg n) (hdg n)
  let vn (n : ℕ) : SpatialL2 1 := (vnm n).toLp (fun x => g n x / (‖x‖ : ℂ))
  have hvn (n : ℕ) : vn n =ᵐ[volume] fun x => g n x / (‖x‖ : ℂ) :=
    (vnm n).coeFn_toLp
  have hvt := weakH1_inverse_radius_tendsto g f dg d vn v hdg hd hvn hv hdt
  have hD := tendsto_finsetSum Finset.univ (fun k _ => (hdt k).norm.pow 2)
  have hl := ((l.continuous.tendsto f).comp hgt).norm.pow 2
  have hV := Complex.continuous_re.tendsto (inner ℂ f v) |>.comp (hgt.inner hvt)
  exact le_of_tendsto_of_tendsto
    ((hgt.norm.pow 2).const_mul β)
    (((hD.const_mul (1 / 2 : ℝ)).sub (hV.const_mul Z)).add (hl.const_mul C))
    (Filter.Eventually.of_forall (fun n =>
      hcore (u n) (g n) (vn n) (dg n) (hu n) (hc n) (hzero n) (hgu n) (hdgu n) (hvn n)))

#print axioms punctured_core_rankOne_bound_extends_weakH1
end TheoremT.Continuum
