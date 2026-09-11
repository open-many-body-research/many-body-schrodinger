import TwoElectronNormalizedSinglet_v1
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Restrict only the proved invariant joint map, with its exact rank-one range. -/
noncomputable section
namespace TheoremT.Continuum

def twoElectronFermionicSinglet (f : SpatialL2 1) : FermionicSpace 2 :=
  ⟨twoElectronSinglet f,twoElectronSinglet_fermionic f⟩

def twoElectronFermionicJoint (f : SpatialL2 1) : FermionicSpace 2 →L[ℂ] FermionicSpace 2 :=
  ((twoElectronSpinProjectFirst f).comp (twoElectronSpinProjectSecond f)).restrict
    (fun _ hψ => twoElectron_jointProjection_fermionic f hψ)

theorem twoElectronFermionicJoint_val (f : SpatialL2 1) (ψ : FermionicSpace 2) :
    (twoElectronFermionicJoint f ψ).val =
      twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ.val) := rfl

theorem twoElectronFermionicSinglet_norm (f : SpatialL2 1) (hf : ‖f‖=1) :
    ‖twoElectronFermionicSinglet f‖ = 1 := twoElectronSinglet_norm f hf

theorem twoElectronFermionicJoint_apply (f : SpatialL2 1) (ψ : FermionicSpace 2) :
    twoElectronFermionicJoint f ψ =
      inner ℂ (twoElectronFermionicSinglet f) ψ • twoElectronFermionicSinglet f := by
  apply Subtype.ext
  exact twoElectron_jointProjection_singlet f ψ.property

theorem twoElectronFermionicJoint_fix_singlet (f : SpatialL2 1) (hf : ‖f‖=1) :
    twoElectronFermionicJoint f (twoElectronFermionicSinglet f) =
      twoElectronFermionicSinglet f := by
  rw [twoElectronFermionicJoint_apply,inner_self_eq_norm_sq_to_K,
    twoElectronFermionicSinglet_norm f hf]
  norm_num

theorem twoElectronFermionicJoint_range (f : SpatialL2 1) (hf : ‖f‖=1) :
    LinearMap.range (twoElectronFermionicJoint f).toLinearMap =
      Submodule.span ℂ {twoElectronFermionicSinglet f} := by
  apply Submodule.ext
  intro ψ
  constructor
  · rintro ⟨χ,rfl⟩
    change twoElectronFermionicJoint f χ ∈ _
    rw [twoElectronFermionicJoint_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hψ
    rcases Submodule.mem_span_singleton.mp hψ with ⟨c,rfl⟩
    refine ⟨c • twoElectronFermionicSinglet f,?_⟩
    change twoElectronFermionicJoint f (c • twoElectronFermionicSinglet f) = _
    rw [map_smul,twoElectronFermionicJoint_fix_singlet f hf]

theorem twoElectronFermionicJoint_range_finrank (f : SpatialL2 1) (hf : ‖f‖=1) :
    Module.finrank ℂ (LinearMap.range (twoElectronFermionicJoint f).toLinearMap) = 1 := by
  rw [twoElectronFermionicJoint_range f hf]
  apply finrank_span_singleton
  intro hzero
  have h := twoElectronFermionicSinglet_norm f hf
  rw [hzero,norm_zero] at h
  norm_num at h

#print axioms twoElectronFermionicJoint_apply
#print axioms twoElectronFermionicJoint_range
#print axioms twoElectronFermionicJoint_range_finrank
end TheoremT.Continuum
