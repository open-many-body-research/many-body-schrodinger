import PuncturedCoreSemanticReview_v1
import ComplexSpherePoincare_v1
import ConfigurationSlicing_v2

/-! Exact physical one-electron configuration to Euclidean Fin 3 transport.
This supplies actual volume, derivative and integral identities for applying
the radial/angular calculation in the unchanged continuum model. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
open TheoremT.HydrogenPolynomial

def oneElectronCoordinateEquiv : Coordinate 1 ≃ Fin 3 where
  toFun := Prod.snd
  invFun i := (0, i)
  left_inv k := by rcases k with ⟨j,i⟩; simp [Fin.eq_zero j]
  right_inv _ := rfl

def oneElectronEuclidean : Configuration 1 ≃ₗᵢ[ℝ] AngularR3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ oneElectronCoordinateEquiv

theorem oneElectronEuclidean_apply (x : Configuration 1) (i : Fin 3) :
    oneElectronEuclidean x i = x (0,i) := rfl

theorem oneElectronEuclidean_symm_apply (x : AngularR3) (k : Coordinate 1) :
    oneElectronEuclidean.symm x k = x k.2 := by
  simp only [oneElectronEuclidean, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

theorem oneElectronEuclidean_symm_single (i : Fin 3) :
    oneElectronEuclidean.symm (EuclideanSpace.single i 1) = coordinateVector (0,i) := by
  ext k
  rcases k with ⟨j,k⟩
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simp [oneElectronEuclidean_symm_apply, coordinateVector, PiLp.single_apply,
    EuclideanSpace.single_apply, Prod.mk.injEq]

theorem oneElectronEuclidean_integral_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (g : Configuration 1 → F) :
    (∫ x : AngularR3, g (oneElectronEuclidean.symm x)) = ∫ x, g x :=
  oneElectronEuclidean.symm.measurePreserving.integral_comp
    oneElectronEuclidean.symm.toHomeomorph.measurableEmbedding g

theorem oneElectronEuclidean_fderiv (f : Configuration 1 → ℂ)
    (hf : Differentiable ℝ f) (x : AngularR3) (i : Fin 3) :
    fderiv ℝ (fun y => f (oneElectronEuclidean.symm y)) x
      (EuclideanSpace.single i 1) = smoothPartial f (0,i) (oneElectronEuclidean.symm x) := by
  have h := (hf (oneElectronEuclidean.symm x)).hasFDerivAt.comp x
    oneElectronEuclidean.symm.toContinuousLinearEquiv.hasFDerivAt
  change fderiv ℝ (f ∘ oneElectronEuclidean.symm) x (EuclideanSpace.single i 1) = _
  rw [h.fderiv]
  change fderiv ℝ f (oneElectronEuclidean.symm x)
    (oneElectronEuclidean.symm (EuclideanSpace.single i 1)) = _
  rw [oneElectronEuclidean_symm_single]
  rfl

theorem oneElectronEuclidean_kinetic_pointwise (f : Configuration 1 → ℂ)
    (hf : Differentiable ℝ f) (x : AngularR3) :
    (∑ i : Fin 3, ‖fderiv ℝ (fun y => f (oneElectronEuclidean.symm y)) x
      (EuclideanSpace.single i 1)‖^2) =
      ∑ k : Coordinate 1, ‖smoothPartial f k (oneElectronEuclidean.symm x)‖^2 := by
  simp_rw [oneElectronEuclidean_fderiv f hf]
  simp [Fintype.sum_prod_type]

theorem oneElectronEuclidean_kinetic_integral (f : Configuration 1 → ℂ)
    (hf : Differentiable ℝ f) :
    (∫ x : AngularR3, ∑ i : Fin 3,
      ‖fderiv ℝ (fun y => f (oneElectronEuclidean.symm y)) x
        (EuclideanSpace.single i 1)‖^2) =
      ∫ x : Configuration 1, ∑ k : Coordinate 1, ‖smoothPartial f k x‖^2 := by
  simp_rw [oneElectronEuclidean_kinetic_pointwise f hf]
  exact oneElectronEuclidean_integral_comp (F := ℝ)
    (fun x => ∑ k : Coordinate 1, ‖smoothPartial f k x‖^2)

theorem oneElectronEuclidean_nuclear_integral (f : Configuration 1 → ℂ) :
    (∫ x : AngularR3, ‖f (oneElectronEuclidean.symm x)‖^2 / ‖x‖) =
      ∫ x : Configuration 1, ‖f x‖^2 / ‖x‖ := by
  have h := oneElectronEuclidean_integral_comp (fun x => ‖f x‖^2 / ‖x‖)
  simpa only [LinearIsometryEquiv.norm_map] using h

#print axioms oneElectronEuclidean_fderiv
#print axioms oneElectronEuclidean_kinetic_integral
#print axioms oneElectronEuclidean_nuclear_integral
end TheoremT.Continuum
