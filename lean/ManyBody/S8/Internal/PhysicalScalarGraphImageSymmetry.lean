import CoulombConjugation_v1
import CoulombRotation_v1
import FermionicGraphAssembly_v2
import TwoElectronTensorExchange_v1
import Mathlib.Tactic
/-! Symmetries of the actual scalar Coulomb graph image.

Permutation and simultaneous orthogonal covariance, complex conjugation and
uniqueness of the actual graph output derive its symmetries directly from
those of its original input, for every finite electron count and real charge.
No eigenvalue, spectral gap, norm or output-symmetry premise is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_scalar_graph_output_permutation {N : ℕ} {Z : ℝ}
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h)
    (π : Equiv.Perm (Fin N)) (hf : pullback π f = f) : pullback π h = h := by
  have hgp := scalar_graph_pullback π hg
  rw [hf] at hgp
  exact scalar_graph_unique hgp hg

theorem physical_spatial_conj_fixed_of_ae_real {N : ℕ} {f : SpatialL2 N}
    (hf : ∀ᵐ x, (f x).im = 0) : spatialConj f = f := by
  apply Lp.ext
  filter_upwards [spatialConj_coeFn f, hf] with x hx hreal
  rw [hx]
  apply Complex.ext
  · simp
  · simp only [Complex.conj_im, hreal, neg_zero]

theorem physical_scalar_graph_output_real {N : ℕ} {Z : ℝ}
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h)
    (hf : ∀ᵐ x, (f x).im = 0) : ∀ᵐ x, (h x).im = 0 := by
  have hgc := scalar_graph_conj hg
  rw [physical_spatial_conj_fixed_of_ae_real hf] at hgc
  exact spatialConj_fixed_im_zero (scalar_graph_unique hgc hg)

theorem physical_scalar_graph_output_rotation {N : ℕ} {Z : ℝ}
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h)
    (Q : Position ≃ₗᵢ[ℝ] Position) (hf : spatialRotation N Q f = f) :
    spatialRotation N Q h = h := by
  have hgr := scalar_graph_spatialRotation Q hg
  rw [hf] at hgr
  exact scalar_graph_unique hgr hg

def PhysicalTwoElectronScalarSymmetryData (f : SpatialL2 2) : Prop :=
  pullback twoElectronSwap f = f ∧ (∀ᵐ x, (f x).im = 0) ∧
    ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f = f

theorem physical_twoElectron_scalar_graph_output_symmetries {Z : ℝ}
    {f h : SpatialL2 2} (hg : scalarHamiltonianGraph 2 Z f h)
    (hf : PhysicalTwoElectronScalarSymmetryData f) :
    PhysicalTwoElectronScalarSymmetryData h :=
  ⟨physical_scalar_graph_output_permutation hg twoElectronSwap hf.1,
    physical_scalar_graph_output_real hg hf.2.1,
    fun Q => physical_scalar_graph_output_rotation hg Q (hf.2.2 Q)⟩

#print axioms physical_scalar_graph_output_permutation
#print axioms physical_scalar_graph_output_real
#print axioms physical_scalar_graph_output_rotation
#print axioms physical_twoElectron_scalar_graph_output_symmetries
end ManyBody.S8
