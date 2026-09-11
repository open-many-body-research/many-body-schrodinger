import HydrogenSphereC1LimitIntegral_v1
import HydrogenSphereC1LimitSequence_v1
import HydrogenPolynomialSpherePoincare_v1

/-! Unconditional sharp sphere Poincare for globally ambient C1 real functions.
The measure is the genuine Euclidean unit sphere area measure, the mean is its
area-normalized integral, and the gradient is the actual tangent projection of
the Frechet derivative. Polynomial density and all limiting integrals are proved.
This does not assert Sobolev H1 density or the hydrogen complement theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.HydrogenSphereC1Limit
open TheoremT.HydrogenPolynomial

theorem sphere_poincare_contDiff_one {f : AngularR3 → ℝ} (hf : ContDiff ℝ 1 f) :
    2 * sphereAngularInner (fun x => f x - sphereMean f) (fun x => f x - sphereMean f) ≤
      sphereTangentialEnergy f := by
  obtain ⟨P, hv, hd⟩ := exists_sphere_C1_polynomial_sequence hf
  have hvar := integral_centered_square_of_continuousMap_limit
    (volume : Measure AngularR3).toSphere (4 * Real.pi) hv
  have hleft : Tendsto (fun n => 2 * sphereAngularInner
      (fun x => euclideanEvaluation (P n) x - sphereMean (euclideanEvaluation (P n)))
      (fun x => euclideanEvaluation (P n) x - sphereMean (euclideanEvaluation (P n))))
      atTop (𝓝 (2 * sphereAngularInner
        (fun x => f x - sphereMean f) (fun x => f x - sphereMean f))) := by
    simpa only [sphereAngularInner, sphereMean, sphereValueMap, ContinuousMap.coe_mk,
      pow_two] using tendsto_const_nhds.mul hvar
  have hright : Tendsto (fun n => sphereTangentialEnergy (euclideanEvaluation (P n)))
      atTop (𝓝 (sphereTangentialEnergy f)) := by
    unfold sphereTangentialEnergy
    apply tendsto_finsetSum
    intro i _
    simpa only [sphereTangentMap, sphereValueMap, ContinuousMap.coe_mk] using
      integral_square_of_continuousMap_limit (volume : Measure AngularR3).toSphere (hd i)
  exact le_of_tendsto_of_tendsto' hleft hright (fun n => polynomial_sphere_poincare (P n))

theorem sphere_poincare_contDiff_one_explicit {f : AngularR3 → ℝ} (hf : ContDiff ℝ 1 f) :
    2 * (∫ w : Metric.sphere (0 : AngularR3) 1,
      (f w.val - (∫ v : Metric.sphere (0 : AngularR3) 1,
        f v.val ∂(volume : Measure AngularR3).toSphere) / (4 * Real.pi)) ^ 2
      ∂(volume : Measure AngularR3).toSphere) ≤
    ∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
      (fderiv ℝ f w.val (EuclideanSpace.single i 1) -
        w.val i * fderiv ℝ f w.val w.val) ^ 2 ∂(volume : Measure AngularR3).toSphere := by
  simpa only [sphereAngularInner, sphereMean, sphereTangentialEnergy,
    tangentialPartial, euclideanPartial, pow_two] using sphere_poincare_contDiff_one hf

theorem sphere_poincare_contDiff_one_mean_zero {f : AngularR3 → ℝ}
    (hf : ContDiff ℝ 1 f) (hm : sphereMean f = 0) :
    2 * sphereAngularInner f f ≤ sphereTangentialEnergy f := by
  simpa only [hm, sub_zero] using sphere_poincare_contDiff_one hf

end TheoremT.HydrogenSphereC1Limit

#print axioms TheoremT.HydrogenSphereC1Limit.sphere_poincare_contDiff_one
#print axioms TheoremT.HydrogenSphereC1Limit.sphere_poincare_contDiff_one_explicit
