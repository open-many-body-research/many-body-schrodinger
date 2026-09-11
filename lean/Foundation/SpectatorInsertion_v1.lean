import NuclearHardySlicing_v2
import KSHessianTraceContraction_v1

noncomputable section
namespace TheoremT.Continuum

def spectatorInsertion {N : ℕ} (i : Fin N) : SpectatorConfiguration i →L[ℝ] Configuration N :=
  (configurationProductEquiv i).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ Position (SpectatorConfiguration i))

def spectatorBasis {N : ℕ} {i : Fin N} (k : SpectatorCoordinate i) : SpectatorConfiguration i :=
  WithLp.toLp 2 (Pi.single k 1)

theorem spectatorInsertion_position {N : ℕ} (i : Fin N) (s : SpectatorConfiguration i) :
    position (spectatorInsertion i s) i=0 := configurationReassemble_position i 0 s

theorem spectatorInsertion_coordinate {N : ℕ} (i : Fin N) (s : SpectatorConfiguration i)
    (k : SpectatorCoordinate i) : spectatorInsertion i s k.val=s k :=
  configurationReassemble_spectator i 0 s k

theorem spectatorInsertion_basis {N : ℕ} (i : Fin N) (k : SpectatorCoordinate i) :
    spectatorInsertion i (spectatorBasis k)=coordinateVector k.val := by
  ext q
  rcases q with ⟨j,l⟩
  by_cases hq : j=i
  · subst j
    have he := congrArg (fun p : Position => p l) (spectatorInsertion_position i (spectatorBasis k))
    have hne : k.val ≠ (i,l) := by
      intro h
      exact k.property (congrArg Prod.fst h)
    have hz : coordinateVector k.val (i,l)=0 := by simp [coordinateVector,PiLp.single_apply,hne]
    rw [hz]
    exact he
  · rw [spectatorInsertion_coordinate i (spectatorBasis k) ⟨(j,l),hq⟩]
    simp [spectatorBasis,coordinateVector,Pi.single_apply,Subtype.ext_iff]

theorem electronInsertion_ksTargetBasis {N : ℕ} (i : Fin N) (k : Fin 3) :
    electronInsertion i (ksTargetBasis k)=coordinateVector (i,k) := electronInsertion_basis i k

theorem sum_coordinates_split {N : ℕ} {A : Type*} [AddCommMonoid A]
    (i : Fin N) (f : Coordinate N → A) :
    (∑ k : Coordinate N,f k)=(∑ k : Fin 3,f (i,k)) + ∑ k : SpectatorCoordinate i,f k.val := by
  have hh := (electronCoordinateSplit i).symm.sum_comp f
  rw [← hh,Fintype.sum_sum_type]
  rfl

#print axioms spectatorInsertion_basis
#print axioms electronInsertion_ksTargetBasis
#print axioms sum_coordinates_split
end TheoremT.Continuum
