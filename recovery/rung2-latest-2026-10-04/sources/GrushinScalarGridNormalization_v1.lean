import GrushinScaledFallingFactorial_v1

/-! Exact fixed-gap scalar rescaling for the Grushin recurrence. The norm
profile is an arbitrary nonnegative scalar family with explicit monotonicity
in the shrinking-box parameter. No PDE estimate or normalized bound is assumed. -/
noncomputable section
namespace TheoremT.Continuum

def grushinGridNorm (N : ℕ → ℝ → ℝ) (h : ℝ) (r : ℕ) : ℝ :=
  h^r * N r (((r : ℝ)+1)*h)

theorem grushin_grid_time_bounds {ρ : ℝ} {ell r : ℕ}
    (hρ : 0 < ρ) (hr : r < ell) :
    0 ≤ ((r : ℝ)+1)*(ρ/(ell : ℝ)) ∧ ((r : ℝ)+1)*(ρ/(ell : ℝ)) ≤ ρ := by
  have hell : 0 < ell := by omega
  have hh := grushin_normalization_scale_pos hρ hell
  have hr' : (r : ℝ)+1 ≤ ell := by exact_mod_cast (show r+1 ≤ ell by omega)
  constructor
  · positivity
  · calc
      ((r : ℝ)+1)*(ρ/(ell : ℝ)) ≤ (ell : ℝ)*(ρ/(ell : ℝ)) :=
        mul_le_mul_of_nonneg_right hr' hh.le
      _ = ρ := by field_simp

theorem grushin_gridNorm_nonneg (N : ℕ → ℝ → ℝ) {ρ : ℝ} {ell r : ℕ}
    (hρ : 0 < ρ) (hr : r < ell)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s) :
    0 ≤ grushinGridNorm N (ρ/(ell : ℝ)) r := by
  obtain ⟨ht0,htρ⟩ := grushin_grid_time_bounds hρ hr
  exact mul_nonneg (pow_nonneg (grushin_normalization_scale_nonneg hρ.le ell) _)
    (hN r _ ht0 htρ)

theorem grushin_gridNorm_base (N : ℕ → ℝ → ℝ) {ρ H0 : ℝ} {ell r : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : r < ell) (hH0 : 0 ≤ H0)
    (hbase : ∀ s, 0 ≤ s → s ≤ ρ → N r s ≤ H0) :
    grushinGridNorm N (ρ/(ell : ℝ)) r ≤ H0 := by
  obtain ⟨ht0,htρ⟩ := grushin_grid_time_bounds hρ hr
  have hh0 := grushin_normalization_scale_nonneg hρ.le ell
  have hh1 := grushin_normalization_scale_le_one hρ1 (show 0 < ell by omega)
  have hp : (ρ/(ell : ℝ))^r ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hh0 hh1 r
  exact (mul_le_mul_of_nonneg_left (hbase _ ht0 htρ) (pow_nonneg hh0 r)).trans
    (mul_le_of_le_one_left hH0 hp)

theorem grushin_grid_lower_norm_le (N : ℕ → ℝ → ℝ) {ρ h : ℝ} {r j : ℕ}
    (hh : 0 < h) (hj0 : 1 ≤ j) (hjr : j ≤ r) (htop : ((r : ℝ)+1)*h ≤ ρ)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s) :
    h^(r-j)*N (r-j) ((r : ℝ)*h) ≤ grushinGridNorm N h (r-j) := by
  have htime : ((r-j : ℕ) : ℝ)+1 ≤ r := by
    exact_mod_cast (show r-j+1 ≤ r by omega)
  have hsmall0 : 0 ≤ (((r-j : ℕ) : ℝ)+1)*h := by positivity
  have hsmall : (((r-j : ℕ) : ℝ)+1)*h ≤ (r : ℝ)*h :=
    mul_le_mul_of_nonneg_right htime hh.le
  have hlarge : (r : ℝ)*h ≤ ρ := by nlinarith
  exact mul_le_mul_of_nonneg_left (hmono (r-j) _ _ hsmall0 hsmall hlarge)
    (pow_nonneg hh.le _)

theorem grushin_inverse_gap_term_le (N : ℕ → ℝ → ℝ) {ρ h : ℝ} {r j : ℕ}
    (hh : 0 < h) (hj0 : 1 ≤ j) (hjr : j ≤ r) (htop : ((r : ℝ)+1)*h ≤ ρ)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s) :
    h^r*((h⁻¹)^j*N (r-j) ((r : ℝ)*h)) ≤ grushinGridNorm N h (r-j) := by
  have he : h^r*(h⁻¹)^j = h^(r-j) := by
    rw [inv_pow,← pow_sub₀ h hh.ne' hjr]
  calc
    _ = (h^r*(h⁻¹)^j)*N (r-j) ((r : ℝ)*h) := by ring
    _ = h^(r-j)*N (r-j) ((r : ℝ)*h) := by rw [he]
    _ ≤ _ := grushin_grid_lower_norm_le N hh hj0 hjr htop hmono

theorem grushin_scaled_source_le {ρ F A S : ℝ} {ell r : ℕ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : r < ell)
    (hF : 0 ≤ F) (hA : 0 ≤ A) (hFS : F ≤ S) :
    (ρ/(ell : ℝ))^r*(F*A^r*(r.factorial : ℝ)) ≤ S*A^r := by
  have hfac := grushin_scaled_factorial_le_one hρ hρ1 hr
  calc
    _ = (F*A^r)*((ρ/(ell : ℝ))^r*(r.factorial : ℝ)) := by ring
    _ ≤ (F*A^r)*1 := mul_le_mul_of_nonneg_left hfac (mul_nonneg hF (pow_nonneg hA _))
    _ ≤ S*A^r := by simpa only [mul_one] using mul_le_mul_of_nonneg_right hFS (pow_nonneg hA _)

theorem grushin_scaled_factorial_term_le (N : ℕ → ℝ → ℝ)
    {ρ A : ℝ} {ell r j : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hA : 0 ≤ A)
    (hr : r < ell) (hj0 : 1 ≤ j) (hjr : j ≤ r)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s) :
    (ρ/(ell : ℝ))^r *
      (A^j*((r.factorial : ℝ)/((r-j).factorial : ℝ))*N (r-j) ((r : ℝ)*(ρ/(ell : ℝ)))) ≤
      A^j*grushinGridNorm N (ρ/(ell : ℝ)) (r-j) := by
  let h := ρ/(ell : ℝ)
  have hh : 0 < h := grushin_normalization_scale_pos hρ (by omega)
  have htop : ((r : ℝ)+1)*h ≤ ρ := (grushin_grid_time_bounds hρ hr).2
  have htime : (r : ℝ)*h ≤ ρ := by nlinarith
  have hzero : 0 ≤ h^(r-j)*N (r-j) ((r : ℝ)*h) :=
    mul_nonneg (pow_nonneg hh.le _) (hN _ _ (by positivity) htime)
  have hfac : h^j*(r.factorial : ℝ)/((r-j).factorial : ℝ) ≤ 1 :=
    grushin_scaled_falling_factorial_le_one hρ.le hρ1 hr hjr
  have hp : h^j*h^(r-j) = h^r := by rw [← pow_add,Nat.add_sub_of_le hjr]
  change h^r * (A^j*((r.factorial : ℝ)/((r-j).factorial : ℝ))*N (r-j) ((r : ℝ)*h)) ≤ _
  calc
    _ = A^j*(h^j*(r.factorial : ℝ)/((r-j).factorial : ℝ))*
        (h^(r-j)*N (r-j) ((r : ℝ)*h)) := by rw [← hp]; ring
    _ ≤ A^j*1*(h^(r-j)*N (r-j) ((r : ℝ)*h)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (pow_nonneg hA _)) hzero
    _ = A^j*(h^(r-j)*N (r-j) ((r : ℝ)*h)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (grushin_grid_lower_norm_le N hh hj0 hjr htop hmono) (pow_nonneg hA _)

#print axioms grushin_inverse_gap_term_le
#print axioms grushin_scaled_factorial_term_le
end TheoremT.Continuum
