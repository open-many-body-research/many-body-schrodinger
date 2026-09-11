import HydrogenSphereHarmonic_v2
import HydrogenSphereBilinear_v1

/-! Sharp constant-two angular inequality for any finite sum of positive-degree
homogeneous harmonic polynomials, with genuine sphere measure and derivatives. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

def finiteHarmonicSum (s : Finset ℕ) (H : ℕ → MvPolynomial (Fin 3) ℝ) (x : AngularR3) : ℝ :=
  ∑ m ∈ s, harmonicAngularExtension m (H m) x

theorem finiteHarmonicSum_smoothAwayZero (s : Finset ℕ) (H : ℕ → MvPolynomial (Fin 3) ℝ) :
    SmoothAwayZero (finiteHarmonicSum s H) :=
  smoothAwayZero_sum s _ (fun m _ x hx => harmonicAngularExtension_contDiffAt m (H m) hx)

theorem finiteHarmonicSum_inner_diagonal (s : Finset ℕ) (H : ℕ → MvPolynomial (Fin 3) ℝ)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0) :
    sphereAngularInner (finiteHarmonicSum s H) (finiteHarmonicSum s H) =
      ∑ m ∈ s, sphereAngularInner (harmonicAngularExtension m (H m))
        (harmonicAngularExtension m (H m)) := by
  have hf (m : ℕ) : SmoothAwayZero (harmonicAngularExtension m (H m)) :=
    fun x hx => harmonicAngularExtension_contDiffAt m (H m) hx
  rw [show finiteHarmonicSum s H = (fun x => ∑ m ∈ s, harmonicAngularExtension m (H m) x) from rfl,
    sphereAngularInner_sum_left s _ (fun m _ => hf m) (smoothAwayZero_sum s _ (fun m _ => hf m))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sphereAngularInner_sum_right s _ (fun j _ => hf j) (hf m)]
  apply Finset.sum_eq_single m
  · intro j hj hjm
    exact actual_sphere_harmonic_distinct_degree_orthogonal
      (hH j hj) (hL j hj) (hH m hm) (hL m hm) hjm
  · exact fun hn => False.elim (hn hm)

theorem finiteHarmonicSum_energy_diagonal (s : Finset ℕ) (H : ℕ → MvPolynomial (Fin 3) ℝ)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0) :
    sphereAngularEnergy (finiteHarmonicSum s H) (finiteHarmonicSum s H) =
      ∑ m ∈ s, ((m : ℝ) * (m + 1)) *
        sphereAngularInner (harmonicAngularExtension m (H m)) (harmonicAngularExtension m (H m)) := by
  have hf (m : ℕ) : SmoothAwayZero (harmonicAngularExtension m (H m)) :=
    fun x hx => harmonicAngularExtension_contDiffAt m (H m) hx
  rw [show finiteHarmonicSum s H = (fun x => ∑ m ∈ s, harmonicAngularExtension m (H m) x) from rfl,
    sphereAngularEnergy_sum_left s _ (fun m _ => hf m) (smoothAwayZero_sum s _ (fun m _ => hf m))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sphereAngularEnergy_sum_right s _ (fun j _ => hf j) (hf m)]
  rw [Finset.sum_eq_single m]
  · exact actual_sphere_harmonic_energy_identity (hH m hm) (hL m hm) (hH m hm)
  · intro j hj hjm
    rw [actual_sphere_harmonic_energy_identity (hH j hj) (hL j hj) (hH m hm),
      actual_sphere_harmonic_distinct_degree_orthogonal (hH j hj) (hL j hj) (hH m hm) (hL m hm) hjm,
      mul_zero]
  · exact fun hn => False.elim (hn hm)

theorem finiteHarmonicSum_positive_degree_mean_zero (s : Finset ℕ)
    (H : ℕ → MvPolynomial (Fin 3) ℝ)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0)
    (hs : ∀ m ∈ s, 0 < m) :
    (∫ w : Metric.sphere (0 : AngularR3) 1,
      finiteHarmonicSum s H w.val ∂(volume : Measure AngularR3).toSphere) = 0 := by
  unfold finiteHarmonicSum
  rw [integral_finsetSum s]
  · apply Finset.sum_eq_zero
    intro m hm
    exact actual_sphere_harmonic_positive_degree_mean_zero (hH m hm) (hL m hm) (hs m hm)
  · intro m _
    exact (smoothAwayZero_sphere_continuous
      (fun x hx => harmonicAngularExtension_contDiffAt m (H m) hx)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem finiteHarmonicSum_poincare (s : Finset ℕ) (H : ℕ → MvPolynomial (Fin 3) ℝ)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0)
    (hs : ∀ m ∈ s, 0 < m) :
    2 * sphereAngularInner (finiteHarmonicSum s H) (finiteHarmonicSum s H) ≤
      sphereAngularEnergy (finiteHarmonicSum s H) (finiteHarmonicSum s H) := by
  rw [finiteHarmonicSum_inner_diagonal s H hH hL, finiteHarmonicSum_energy_diagonal s H hH hL,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_right _ (sphereAngularInner_self_nonneg _)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hs m hm
  nlinarith

end TheoremT.HydrogenPolynomial
