import HydrogenFiniteHarmonicCentered_v1
import HydrogenSphereTangential_v1
import HydrogenGroupedHarmonicEuclidean_v1

/-! Sharp Poincaré inequality for every actual polynomial restricted to the
Euclidean unit sphere. Finite harmonic decomposition and all angular identities
are discharged in the imported source proofs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology
namespace TheoremT.HydrogenPolynomial

def sphereTangentialEnergy (f : AngularR3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
    (tangentialPartial i f w.val) ^ 2 ∂(volume : Measure AngularR3).toSphere

theorem grouped_retraction_eq {P : Polynomial3} {s : Finset ℕ} {H : ℕ → Polynomial3}
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m)
    (he : ∀ x : AngularR3, ‖x‖ = 1 → euclideanEvaluation P x =
      ∑ m ∈ s, euclideanEvaluation (H m) x)
    {x : AngularR3} (hx : x ≠ 0) :
    angularRetraction (euclideanEvaluation P) x = finiteHarmonicSum s H x := by
  rw [angularRetraction, he _ (unitRadialRetraction_norm hx)]
  unfold finiteHarmonicSum
  apply Finset.sum_congr rfl
  intro m hm
  rw [← harmonicAngularExtension_unitSphere m (H m) (unitRadialRetraction_norm hx)]
  exact harmonicAngularExtension_scale (hH m hm) (inv_pos.mpr (norm_pos_iff.mpr hx)) x

theorem grouped_tangential_partial_eq {P : Polynomial3} {s : Finset ℕ} {H : ℕ → Polynomial3}
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m)
    (he : ∀ x : AngularR3, ‖x‖ = 1 → euclideanEvaluation P x =
      ∑ m ∈ s, euclideanEvaluation (H m) x)
    {x : AngularR3} (hx : ‖x‖ = 1) (i : Fin 3) :
    euclideanPartial i (finiteHarmonicSum s H) x = tangentialPartial i (euclideanEvaluation P) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hloc : angularRetraction (euclideanEvaluation P) =ᶠ[𝓝 x] finiteHarmonicSum s H := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx0] with y hy
    exact grouped_retraction_eq hH he hy
  have hd := hloc.fderiv_eq (𝕜 := ℝ)
  rw [← angularRetraction_partial_unit
    ((euclideanEvaluation_contDiff P).differentiable (by simp) x) hx i]
  exact congrArg (fun L : AngularR3 →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd.symm

theorem polynomial_sphere_poincare (P : Polynomial3) :
    2 * sphereAngularInner
      (fun x => euclideanEvaluation P x - sphereMean (euclideanEvaluation P))
      (fun x => euclideanEvaluation P x - sphereMean (euclideanEvaluation P)) ≤
        sphereTangentialEnergy (euclideanEvaluation P) := by
  obtain ⟨s, H, hH, he⟩ := polynomial_has_grouped_euclidean_sphere_representation P
  have ht (x : AngularR3) (hx : ‖x‖ = 1) :
      euclideanEvaluation P x = finiteHarmonicSum s H x := by
    rw [he x hx]
    unfold finiteHarmonicSum
    apply Finset.sum_congr rfl
    intro m _
    exact (harmonicAngularExtension_unitSphere m (H m) hx).symm
  have hmean : sphereMean (euclideanEvaluation P) = sphereMean (finiteHarmonicSum s H) := by
    unfold sphereMean
    congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    exact ht w.val (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)
  have hi : sphereAngularInner
      (fun x => euclideanEvaluation P x - sphereMean (euclideanEvaluation P))
      (fun x => euclideanEvaluation P x - sphereMean (euclideanEvaluation P)) =
    sphereAngularInner
      (fun x => finiteHarmonicSum s H x - sphereMean (finiteHarmonicSum s H))
      (fun x => finiteHarmonicSum s H x - sphereMean (finiteHarmonicSum s H)) := by
    unfold sphereAngularInner
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    dsimp only
    rw [ht w.val (by simpa [Metric.mem_sphere, dist_zero_right] using w.property), hmean]
  have hg : sphereTangentialEnergy (euclideanEvaluation P) =
      sphereAngularEnergy (finiteHarmonicSum s H) (finiteHarmonicSum s H) := by
    unfold sphereTangentialEnergy sphereAngularEnergy
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    dsimp only
    rw [grouped_tangential_partial_eq (fun m hm => (hH m hm).1) he
      (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)]
    ring
  rw [hi, hg]
  exact finiteHarmonicSum_centered_poincare s H
    (fun m hm => (hH m hm).1) (fun m hm => (hH m hm).2)

end TheoremT.HydrogenPolynomial
