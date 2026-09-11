import HydrogenRadialLaplacian_v1
import HydrogenRadialTrace_v1

/-! Readable semantic audit: the v1 explicit-printer output retains typeclass proof
elisions; this version compiles the same physical restatements without expanding
implementation dictionaries. The actual Euclidean configuration type and coordinate
basis expanded. The exact profile definitions are printed below. -/
noncomputable section
set_option pp.maxSteps 1000000
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem audit2_hydrogen_smooth (Z δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1 × Fin 3) =>
      (Real.exp (-Z * Real.sqrt (‖x‖^2 + δ)) : ℂ)) :=
  hydrogenSmooth_contDiff hδ Z

theorem audit2_hydrogen_first (Z δ : ℝ) (hδ : 0 < δ)
    (k : Fin 1 × Fin 3) (x : EuclideanSpace ℝ (Fin 1 × Fin 3)) :
    fderiv ℝ (hydrogenSmooth Z δ) x (PiLp.single 2 k 1) =
      ((-Z * x k / Real.sqrt (‖x‖^2 + δ) : ℝ) : ℂ) * hydrogenSmooth Z δ x :=
  hydrogenSmooth_first_derivative hδ Z k x

theorem audit2_hydrogen_mixed (Z δ : ℝ) (hδ : 0 < δ)
    (k l : Fin 1 × Fin 3) (x : EuclideanSpace ℝ (Fin 1 × Fin 3)) :
    fderiv ℝ (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (PiLp.single 2 k 1))
      x (PiLp.single 2 l 1) =
      ((Z^2 * x k * x l / (‖x‖^2 + δ) -
        Z * (if k = l then 1 else 0) / Real.sqrt (‖x‖^2 + δ) +
        Z * x k * x l / (Real.sqrt (‖x‖^2 + δ))^3 : ℝ) : ℂ) * hydrogenSmooth Z δ x :=
  hydrogenSmooth_mixed_second_derivative hδ Z k l x

theorem audit2_hydrogen_laplacian (Z δ : ℝ) (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin 1 × Fin 3)) :
    (∑ k : Fin 1 × Fin 3, fderiv ℝ
      (fun y => fderiv ℝ (hydrogenSmooth Z δ) y (PiLp.single 2 k 1))
      x (PiLp.single 2 k 1)) =
      ((Z^2 * ‖x‖^2 / (‖x‖^2 + δ) -
        Z * (2*‖x‖^2 + 3*δ) / (Real.sqrt (‖x‖^2 + δ))^3 : ℝ) : ℂ) *
        hydrogenSmooth Z δ x :=
  hydrogenSmooth_laplacian hδ Z x

theorem audit2_hydrogen_trace (Z : ℝ) (x : EuclideanSpace ℝ (Fin 1 × Fin 3))
    (hx : x ≠ 0) :
    (∑ k : Fin 1 × Fin 3, hydrogenSecond Z k k x) =
      ((Z^2 - 2*Z/‖x‖ : ℝ) : ℂ) * hydrogenRadial Z x :=
  hydrogenSecond_trace Z hx

theorem audit2_one_electron_potential (Z : ℝ) (x : EuclideanSpace ℝ (Fin 1 × Fin 3)) :
    coulombPotential 1 Z x = -Z / ‖x‖ :=
  coulombPotential_one_electron Z x

#print hydrogenRadial
#print hydrogenSecond
#print hydrogenSmoothReal
#print hydrogenSmooth
#print coordinateVector
#check audit2_hydrogen_smooth
#check audit2_hydrogen_first
#check audit2_hydrogen_mixed
#check audit2_hydrogen_laplacian
#print axioms audit2_hydrogen_smooth
#print axioms audit2_hydrogen_first
#print axioms hydrogenSmooth_first_contDiff
#print axioms audit2_hydrogen_mixed
#print axioms audit2_hydrogen_laplacian
#check audit2_hydrogen_trace
#check audit2_one_electron_potential
#print axioms audit2_hydrogen_trace
#print axioms audit2_one_electron_potential
end TheoremT.Continuum
