import HydrogenFiniteHarmonicPoincare_v1

/-! The constant-degree piece is exactly the area-normalized sphere mean.
Thus the finite harmonic sum inequality applies without an imposed zero mean. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

def sphereMean (f : AngularR3 → ℝ) : ℝ :=
  (∫ w : Metric.sphere (0 : AngularR3) 1, f w.val ∂(volume : Measure AngularR3).toSphere) /
    (4 * Real.pi)

theorem degree_zero_angular_constant {P : Polynomial3} (hP : P.IsHomogeneous 0) :
    harmonicAngularExtension 0 P = fun _ : AngularR3 => eval (fun _ => 0) P := by
  have he := (totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hP
  rw [totalDegree_eq_zero_iff_eq_C] at he
  rw [he]
  funext x
  simp [harmonicAngularExtension, radialPolynomialProduct, radialSquaredPower, euclideanEvaluation]

def finiteHarmonicConstant (s : Finset ℕ) (H : ℕ → Polynomial3) : ℝ :=
  if 0 ∈ s then eval (fun _ => 0) (H 0) else 0

theorem finiteHarmonicSum_constant_split (s : Finset ℕ) (H : ℕ → Polynomial3)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (x : AngularR3) :
    finiteHarmonicSum s H x = finiteHarmonicConstant s H + finiteHarmonicSum (s.erase 0) H x := by
  classical
  by_cases hs : 0 ∈ s
  · have he := Finset.sum_erase_add s (fun m => harmonicAngularExtension m (H m) x) hs
    rw [degree_zero_angular_constant (hH 0 hs)] at he
    simpa [finiteHarmonicSum, finiteHarmonicConstant, hs, add_comm] using he.symm
  · simp [finiteHarmonicConstant, hs, Finset.erase_eq_of_notMem hs]

theorem finiteHarmonicSum_mean (s : Finset ℕ) (H : ℕ → Polynomial3)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0) :
    sphereMean (finiteHarmonicSum s H) = finiteHarmonicConstant s H := by
  have hHs : ∀ m ∈ s.erase 0, (H m).IsHomogeneous m :=
    fun m hm => hH m (Finset.mem_of_mem_erase hm)
  have hLs : ∀ m ∈ s.erase 0, polynomialLaplace (H m) = 0 :=
    fun m hm => hL m (Finset.mem_of_mem_erase hm)
  have hpos : ∀ m ∈ s.erase 0, 0 < m := fun m hm =>
    Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hm)
  have hmean := finiteHarmonicSum_positive_degree_mean_zero (s.erase 0) H hHs hLs hpos
  have hint : Integrable (fun w : Metric.sphere (0 : AngularR3) 1 =>
      finiteHarmonicSum (s.erase 0) H w.val) (volume : Measure AngularR3).toSphere :=
    (smoothAwayZero_sphere_continuous
    (finiteHarmonicSum_smoothAwayZero (s.erase 0) H)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold sphereMean
  simp_rw [finiteHarmonicSum_constant_split s H hH]
  rw [integral_add (integrable_const _) hint, hmean, add_zero, integral_const]
  rw [TheoremT.Polar.sphere_volume_real_dim_three (by simp : Module.finrank ℝ AngularR3 = 3)]
  simp only [smul_eq_mul]
  field_simp

theorem finiteHarmonicSum_centered_eq (s : Finset ℕ) (H : ℕ → Polynomial3)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0) :
    (fun x => finiteHarmonicSum s H x - sphereMean (finiteHarmonicSum s H)) =
      finiteHarmonicSum (s.erase 0) H := by
  funext x
  rw [finiteHarmonicSum_mean s H hH hL, finiteHarmonicSum_constant_split s H hH]
  ring

theorem finiteHarmonicSum_centered_poincare (s : Finset ℕ) (H : ℕ → Polynomial3)
    (hH : ∀ m ∈ s, (H m).IsHomogeneous m) (hL : ∀ m ∈ s, polynomialLaplace (H m) = 0) :
    2 * sphereAngularInner
      (fun x => finiteHarmonicSum s H x - sphereMean (finiteHarmonicSum s H))
      (fun x => finiteHarmonicSum s H x - sphereMean (finiteHarmonicSum s H)) ≤
        sphereAngularEnergy (finiteHarmonicSum s H) (finiteHarmonicSum s H) := by
  rw [finiteHarmonicSum_centered_eq s H hH hL]
  have he : sphereAngularEnergy (finiteHarmonicSum s H) (finiteHarmonicSum s H) =
      sphereAngularEnergy (finiteHarmonicSum (s.erase 0) H) (finiteHarmonicSum (s.erase 0) H) := by
    unfold sphereAngularEnergy
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext w
    have hf : finiteHarmonicSum s H =
        fun x => finiteHarmonicConstant s H + finiteHarmonicSum (s.erase 0) H x :=
      funext (finiteHarmonicSum_constant_split s H hH)
    simp [hf, euclideanPartial, fderiv_const_add]
  rw [he]
  exact finiteHarmonicSum_poincare (s.erase 0) H
    (fun m hm => hH m (Finset.mem_of_mem_erase hm))
    (fun m hm => hL m (Finset.mem_of_mem_erase hm))
    (fun m hm => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hm))

end TheoremT.HydrogenPolynomial
