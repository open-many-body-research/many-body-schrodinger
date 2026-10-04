import GrushinCenteredCutoffLowerRadius_v1

/-! The exact three-quarter-gap tensor cutoff used in the centered
factorial commutator. Its C-infinity transition constants are retained
explicitly; the paper's quintic numerical bounds are not asserted. -/
noncomputable section
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

def factorialRectCutoff (a : Space (Fin 3)) (aY aT s e : ℝ) : Space (Fin 3) → ℝ :=
  grushinRectCutoff a (aY-s-e) (aT-s-e) (3*e/4)

theorem factorialRectCutoff_geometry (a : Space (Fin 3)) {aY aT ρ s e : ℝ}
    (he : 0 < e) (hse : s+e ≤ ρ) (hρy : ρ < aY) (hρt : ρ < aT) :
    ContDiff ℝ ∞ (factorialRectCutoff a aY aT s e) ∧
    HasCompactSupport (factorialRectCutoff a aY aT s e) ∧
    (∀ p, 0 ≤ factorialRectCutoff a aY aT s e p ∧ factorialRectCutoff a aY aT s e p ≤ 1) ∧
    (∀ p ∈ rectangularOpenBox a (aY-(s+e)) (aT-(s+e)),
      factorialRectCutoff a aY aT s e p = 1) ∧
    tsupport (factorialRectCutoff a aY aT s e) ⊆
      rectangularClosedBox a (aY-s-e/4) (aT-s-e/4) ∧
    tsupport (factorialRectCutoff a aY aT s e) ⊆ rectangularOpenBox a (aY-s) (aT-s) := by
  have hg : 0 < 3*e/4 := by positivity
  have hs := grushinRectCutoff_tsupport a (aY-s-e) (aT-s-e) hg
  have heY : aY-s-e+3*e/4 = aY-s-e/4 := by ring
  have heT : aT-s-e+3*e/4 = aT-s-e/4 := by ring
  rw [heY,heT] at hs
  refine ⟨grushinRectCutoff_contDiff a _ _ _,
    grushinRectCutoff_compact a (by linarith) (by linarith) hg,?_,?_,hs,?_⟩
  · intro p
    exact ⟨grushinRectCutoff_nonneg a _ _ _ p,grushinRectCutoff_le_one a _ _ _ p⟩
  · intro p hp
    have hy : aY-(s+e) = aY-s-e := by ring
    have ht : aT-(s+e) = aT-s-e := by ring
    rw [hy,ht] at hp
    exact grushinRectCutoff_plateau a _ _ hg (rectangularOpenBox_subset_closedBox a _ _ hp)
  · exact hs.trans (rectangularClosedBox_subset_openBox a (by linarith) (by linarith))

theorem factorialRectCutoff_derivative_bounds (a : Space (Fin 3)) (aY aT s : ℝ)
    {C1 C2 e : ℝ} (he : 0 < e)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    (∀ j p, |fderiv ℝ (factorialRectCutoff a aY aT s e) p (boxDirection j)| ≤
      ((8/3 : ℝ)*C1)/e) ∧
    (∀ j p, |fderiv ℝ (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q
      (boxDirection j)) p (boxDirection j)| ≤ ((32/9 : ℝ)*(C2+C1^2))/e^2) := by
  have hg : 0 < 3*e/4 := by positivity
  have he1 : 2*C1/(3*e/4) = ((8/3 : ℝ)*C1)/e := by field_simp; ring
  have he2 : 2*(C2+C1^2)/(3*e/4)^2 = ((32/9 : ℝ)*(C2+C1^2))/e^2 := by field_simp; ring
  refine ⟨?_,?_⟩
  · intro j p
    exact (grushinRectCutoff_first_bound a (aY-s-e) (aT-s-e) hC1 hg j p).trans_eq he1
  · intro j p
    exact (grushinRectCutoff_second_bound a (aY-s-e) (aT-s-e) hC1 hC2 hg j p).trans_eq he2

theorem factorialRectCutoff_y_lower_radius (a : Space (Fin 3)) (ha : a.1 = 0)
    {aY aT ρ s e : ℝ} (he : 0 < e) (hse : s+e ≤ ρ) (i : Fin 4)
    {p : Space (Fin 3)}
    (hp : p ∈ tsupport (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (yDir i)) ∨
      p ∈ tsupport (fun q => fderiv ℝ
        (fun z => fderiv ℝ (factorialRectCutoff a aY aT s e) z (yDir i)) q (yDir i))) :
    aY-ρ ≤ ‖p.1‖ :=
  factorial_rectangular_cutoff_y_lower_radius a ha aY aT s he (by linarith) i hp

theorem factorialRectCutoff_uniform_data :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧
    ∀ (a : Space (Fin 3)) (aY aT ρ s e : ℝ), a.1 = 0 →
      0 < e → s+e ≤ ρ → ρ < aY → ρ < aT →
      ContDiff ℝ ∞ (factorialRectCutoff a aY aT s e) ∧
      HasCompactSupport (factorialRectCutoff a aY aT s e) ∧
      (∀ p, 0 ≤ factorialRectCutoff a aY aT s e p ∧ factorialRectCutoff a aY aT s e p ≤ 1) ∧
      (∀ p ∈ rectangularOpenBox a (aY-(s+e)) (aT-(s+e)),
        factorialRectCutoff a aY aT s e p = 1) ∧
      tsupport (factorialRectCutoff a aY aT s e) ⊆
        rectangularClosedBox a (aY-s-e/4) (aT-s-e/4) ∧
      tsupport (factorialRectCutoff a aY aT s e) ⊆ rectangularOpenBox a (aY-s) (aT-s) ∧
      (∀ j p, |fderiv ℝ (factorialRectCutoff a aY aT s e) p (boxDirection j)| ≤ ((8/3 : ℝ)*C1)/e) ∧
      (∀ j p, |fderiv ℝ (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q
        (boxDirection j)) p (boxDirection j)| ≤ ((32/9 : ℝ)*(C2+C1^2))/e^2) ∧
      (∀ i p, p ∈ tsupport (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (yDir i)) ∨
        p ∈ tsupport (fun q => fderiv ℝ
          (fun z => fderiv ℝ (factorialRectCutoff a aY aT s e) z (yDir i)) q (yDir i)) →
        aY-ρ ≤ ‖p.1‖) := by
  obtain ⟨C1,C2,hC10,hC20,hC1,hC2⟩ := smoothTransition_derivative_bounds
  refine ⟨C1,C2,hC10,hC20,?_⟩
  intro a aY aT ρ s e ha he hse hρy hρt
  obtain ⟨hχ,hcχ,hval,hplateau,hs,hso⟩ := factorialRectCutoff_geometry a he hse hρy hρt
  obtain ⟨hd,hdd⟩ := factorialRectCutoff_derivative_bounds a aY aT s he hC1 hC2
  exact ⟨hχ,hcχ,hval,hplateau,hs,hso,hd,hdd,
    fun i p hp => factorialRectCutoff_y_lower_radius a ha he hse i hp⟩

end TheoremT.Continuum.WeakGrushin
