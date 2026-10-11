import CoulombH2Decay_v1
import TwoElectronGroundDecay_v1

/-! Actual two-electron ground H² exponential tails, and a composed physical
real exchange-symmetric rotation-invariant normalized eigenfunction. The ground
energy is the previously proved bottom of the full fermionic spectrum. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectron_ground_H2_exponential_tail (Z : ℝ) (hZ : 2 ≤ Z)
    {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal : ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0 ≤ a) (hgap : a^2 < Z^2/112) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C :=
  scalar_eigen_H2_exponential_tail hg d e hd he ha
    (twoElectron_ground_exponential_decay Z hZ hg ha hgap)

theorem twoElectron_physical_ground_with_H2_decay (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u (((variationalGroundEnergy 2 Z).toReal : ℂ) • u) ∧
      (∀ᵐ x, (u x).im = 0) ∧
      (∀ R : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 R u = u) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial u (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm u d e r ≤ Real.exp (-a*r)*C := by
  obtain ⟨u,hu,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨u,hu,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_H2_exponential_tail Z hZ hg d e hd he ha hgap⟩

#print axioms twoElectron_ground_H2_exponential_tail
#print axioms twoElectron_physical_ground_with_H2_decay
end TheoremT.Continuum
