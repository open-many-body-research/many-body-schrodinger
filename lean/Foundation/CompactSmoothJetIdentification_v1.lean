import HardyLaplacianCore_v1
import HardyWeakCore_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem WeakPartial.ae_eq_smoothPartial_of_compact_rep {N : ℕ}
    {f d : SpatialL2 N} {k : Coordinate N} (hd : WeakPartial f d k)
    {g : Configuration N → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) :
    (d : Configuration N → ℂ) =ᵐ[volume] smoothPartial g k := by
  have hgm : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hc
  have hdm : MemLp (smoothPartial g k) 2 volume :=
    (smoothPartial_contDiff hg k).continuous.memLp_of_hasCompactSupport (smoothPartial_compact hc k)
  have hgf : hgm.toLp g=f := Lp.ext (hgm.coeFn_toLp.trans hfg.symm)
  have hw := classicalDerivative_to_WeakPartial (hg.of_le (by simp)) k hgm hdm
  rw [hgf] at hw
  rw [weakPartial_unique hd hw]
  exact hdm.coeFn_toLp

theorem weakH2_jet_ae_smooth_jet_of_compact_rep {N : ℕ}
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {g : Configuration N → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) :
    (∀ k, (d k : Configuration N → ℂ) =ᵐ[volume] smoothPartial g k) ∧
    (∀ k l, (e k l : Configuration N → ℂ) =ᵐ[volume] smoothPartial (smoothPartial g k) l) := by
  have hdg (k : Coordinate N) := (hd k).ae_eq_smoothPartial_of_compact_rep hg hc hfg
  exact ⟨hdg,fun k l => (he k l).ae_eq_smoothPartial_of_compact_rep
    (smoothPartial_contDiff hg k) (smoothPartial_compact hc k) (hdg k)⟩

theorem weakH2_laplacian_ae_smooth_of_compact_rep {N : ℕ}
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {g : Configuration N → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) :
    ((∑ k : Coordinate N,e k k : SpatialL2 N) : Configuration N → ℂ) =ᵐ[volume] smoothLaplacian g := by
  have ha := (weakH2_jet_ae_smooth_jet_of_compact_rep d e hd he hg hc hfg).2
  have hall : ∀ᵐ x ∂volume, ∀ k, e k k x=smoothPartial (smoothPartial g k) k x := by
    rw [ae_all_iff]
    exact fun k => ha k k
  filter_upwards [hall,Lp.coeFn_fun_finsetSum Finset.univ (fun k => e k k)] with x hx hs
  simp only [hs,smoothLaplacian,hx]

theorem smoothLaplacian_congr_of_eventuallyEq {N : ℕ}
    {f g : Configuration N → ℂ} {x : Configuration N}
    (h : f =ᶠ[𝓝 x] g) : smoothLaplacian f x=smoothLaplacian g x := by
  apply Finset.sum_congr rfl
  intro k _
  have he : smoothPartial f k =ᶠ[𝓝 x] smoothPartial g k := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L => L (coordinateVector k)) hy
  exact congrArg (fun L => L (coordinateVector k)) (he.fderiv_eq (𝕜 := ℝ))

#print axioms weakH2_laplacian_ae_smooth_of_compact_rep
#print axioms smoothLaplacian_congr_of_eventuallyEq
end TheoremT.Continuum
