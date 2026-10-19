import KSRealSpectatorSeriesData_v1
import PairSeriesZeroFirstShift_v1

/-! Exact physical KS evaluation identity for the original pair-indexed
polynomial/spectator series. Absolute summability of the input is derived
from the two output majorants; no physical Taylor identification is assumed.
The original zero radial slice of the odd family is proved to vanish before
its infinite spectator slice is removed by an injective index transport. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem ks_real_spectator_series_uniform_convergence
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous (2*m))
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor (P m γ)).support → e 0+e 1=e 2+e 3)
    {M b S r h : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hDr : (32*b^2)*r < 1) (hSh : S*h < 1)
    (hc : ∀ m γ e, e ∈ (P m γ).support →
      ‖(P m γ).coeff e‖ ≤ M*b^(2*m)*S^(∑ i : Fin d, γ i)) :
    HasSumUniformlyOn (homogeneousSpectatorTerm (ksRealSpectatorFamilyA P))
      (fun z => ∑' k, homogeneousSpectatorTerm (ksRealSpectatorFamilyA P) k z)
      (complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h) ∧
    HasSumUniformlyOn (homogeneousSpectatorTerm (ksRealSpectatorFamilyB P))
      (fun z => ∑' k, homogeneousSpectatorTerm (ksRealSpectatorFamilyB P) k z)
      (complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_spectator_series_data P hP hbal hM hb hS hc
  exact ⟨(homogeneous_spectator_series_closed_polydiscs _ hA hM (by positivity) hr hS hh
      hDr hSh hLA).2,
    (shifted_homogeneous_spectator_series_closed_polydiscs _ hB hM (by positivity) hr hS hh
      hDr hSh hLB).2⟩

theorem ks_real_spectator_series_physical_descent
    (P : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 4) ℂ)
    (hP : ∀ m γ, (P m γ).IsHomogeneous (2*m))
    (hbal : ∀ m γ e, e ∈ (ksRealPolynomialToSpinor (P m γ)).support → e 0+e 1=e 2+e 3)
    {M b S r h : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hDr : (32*b^2)*r < 1) (hSh : S*h < 1)
    (hc : ∀ m γ e, e ∈ (P m γ).support →
      ‖(P m γ).coeff e‖ ≤ M*b^(2*m)*S^(∑ i : Fin d, γ i))
    (y : KSSpace) (s : Fin d → ℂ)
    (hy : (fun i => (ksMap y i : ℂ)) ∈ complexClosedPolydisc (Fin 3) r)
    (hs : s ∈ complexClosedPolydisc (Fin d) h) :
    Summable (fun k : ℕ × (Fin d → ℕ) =>
      ‖MvPolynomial.eval (fun i => (y i : ℂ)) (P k.1 k.2) * ∏ i : Fin d, s i ^ k.2 i‖) ∧
    Summable (fun k : ℕ × (Fin d → ℕ) =>
      MvPolynomial.eval (fun i => (y i : ℂ)) (P k.1 k.2) * ∏ i : Fin d, s i ^ k.2 i) ∧
    (∑' k : ℕ × (Fin d → ℕ),
      MvPolynomial.eval (fun i => (y i : ℂ)) (P k.1 k.2) * ∏ i : Fin d, s i ^ k.2 i) =
      homogeneousSpectatorSum (ksRealSpectatorFamilyA P)
        (Sum.elim (fun i => (ksMap y i : ℂ)) s) +
      (‖y‖^2 : ℝ)*homogeneousSpectatorSum (ksRealSpectatorFamilyB P)
        (Sum.elim (fun i => (ksMap y i : ℂ)) s) := by
  obtain ⟨hA,hB,hB0,hLA,hLB⟩ := ks_real_spectator_series_data P hP hbal hM hb hS hc
  let X : Fin 3 → ℂ := fun i => (ksMap y i : ℂ)
  let c : ℂ := (‖y‖^2 : ℝ)
  let a := fun k : ℕ × (Fin d → ℕ) =>
    homogeneousSpectatorTerm (ksRealSpectatorFamilyA P) k (X,s)
  let b0 := fun k : ℕ × (Fin d → ℕ) =>
    MvPolynomial.eval X (ksRealPolynomialDescentB (P k.1 k.2)) * ∏ i : Fin d, s i ^ k.2 i
  have hAs := ((homogeneous_spectator_series_closed_polydiscs _ hA hM (by positivity) hr hS hh
    hDr hSh hLA).1 (X,s) ⟨hy,hs⟩).1
  have hBshift := ((shifted_homogeneous_spectator_series_closed_polydiscs _ hB hM
    (by positivity) hr hS hh hDr hSh hLB).1 (X,s) ⟨hy,hs⟩).1
  have hBzero (γ : Fin d → ℕ) : b0 (0,γ) = 0 := by
    simp [b0,hB0 γ]
  have hBs := pair_series_zero_first_shift b0 hBzero hBshift
  have hterm (k : ℕ × (Fin d → ℕ)) :
      MvPolynomial.eval (fun i => (y i : ℂ)) (P k.1 k.2) * ∏ i : Fin d, s i ^ k.2 i =
      a k + c*b0 k := by
    rw [ks_real_polynomial_physical_descent (P k.1 k.2) (hbal k.1 k.2) y]
    simp only [a,b0,homogeneousSpectatorTerm,ksRealSpectatorFamilyA]
    change (_+c*_)*_ = _*_+c*(_*_)
    ring
  have habs : Summable (fun k : ℕ × (Fin d → ℕ) =>
      ‖MvPolynomial.eval (fun i => (y i : ℂ)) (P k.1 k.2) * ∏ i : Fin d, s i ^ k.2 i‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => ?_) (hAs.add (hBs.1.mul_left ‖c‖))
    rw [hterm]
    exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
  refine ⟨habs,habs.of_norm,?_⟩
  calc
    _ = ∑' k : ℕ × (Fin d → ℕ), (a k+c*b0 k) := tsum_congr hterm
    _ = (∑' k, a k)+(∑' k, c*b0 k) := Summable.tsum_add hAs.of_norm (hBs.2.1.mul_left c)
    _ = _ := by rw [tsum_mul_left,hBs.2.2]; rfl

end TheoremT.Continuum
