import ManyBody.S8.Internal.PhysicalScalarGraphImageSymmetry
import ManyBody.S8.CoulombNormalizedSymmetricGraphApproximation

/-! Symmetric actual graph images of norm-one smooth compact approximants.

The original graph image and the same approximate graph images retain true
exchange, AE reality and every simultaneous orthogonal symmetry. These facts
follow from actual graph covariance and uniqueness; no graph-image symmetry
or approximation-existence premise is added to the physical graph endpoint. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalNormalizedRadialSmoothSymmetricGraphApproximationData
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z : ℝ) (h : SpatialL2 2) (ε R : ℝ) (hR : 1 ≤ R) (m : ℕ) : Prop :=
  let F := physicalRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f
  let g := physicalRadialMollifyLp m F
  let v := physicalNormalizationScalar g • g
  PhysicalNormalizedRadialSmoothGraphApproximationData f d e Z h ε R hR m ∧
    ∃ H : SpatialL2 2, scalarHamiltonianGraph 2 Z v H ∧ ‖H - h‖ ≤ ε ∧
      |(inner ℂ v H).re - (inner ℂ f h).re| ≤ ε ∧
      PhysicalTwoElectronScalarSymmetryData H

theorem physical_normalized_radial_smooth_graph_output_symmetry
    {f : SpatialL2 2} {d : Coordinate 2 → SpatialL2 2}
    {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {Z : ℝ} {h : SpatialL2 2} {ε R : ℝ} {hR : 1 ≤ R} {m : ℕ}
    (hdata : PhysicalNormalizedRadialSmoothGraphApproximationData f d e Z h ε R hR m) :
    PhysicalNormalizedRadialSmoothSymmetricGraphApproximationData f d e Z h ε R hR m := by
  refine ⟨hdata, ?_⟩
  have hcopy := hdata
  dsimp only [PhysicalNormalizedRadialSmoothGraphApproximationData] at hcopy
  rcases hcopy with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨H, hH, herror, hRayleigh⟩, hswap, hreal, hrot, _, _, _⟩
  exact ⟨H, hH, herror, hRayleigh,
    physical_twoElectron_scalar_graph_output_symmetries hH ⟨hswap, hreal, hrot⟩⟩

theorem twoElectron_normalized_symmetric_scalar_graph_image_smooth_approximation
    (Z : ℝ) {f h : SpatialL2 2} (hg : scalarHamiltonianGraph 2 Z f h) (hf : ‖f‖ = 1)
    (hs : pullback twoElectronSwap f = f) (hreal : ∀ᵐ x, (f x).im = 0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f = f) :
    ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
      PhysicalTwoElectronScalarSymmetryData h ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∃ hR : 1 ≤ R, ∀ᶠ m : ℕ in atTop,
        PhysicalNormalizedRadialSmoothSymmetricGraphApproximationData f d e Z h ε R hR m := by
  obtain ⟨d, e, hd, he, happ⟩ :=
    twoElectron_normalized_symmetric_scalar_graph_smooth_approximation Z hg hf hs hreal hrot
  refine ⟨d, e, hd, he, physical_twoElectron_scalar_graph_output_symmetries hg ⟨hs, hreal, hrot⟩, ?_⟩
  intro ε hε
  obtain ⟨R, hR, hm⟩ := happ ε hε
  exact ⟨R, hR, hm.mono fun _ hdata => physical_normalized_radial_smooth_graph_output_symmetry hdata⟩

#print axioms physical_normalized_radial_smooth_graph_output_symmetry
#print axioms twoElectron_normalized_symmetric_scalar_graph_image_smooth_approximation
end ManyBody.S8
