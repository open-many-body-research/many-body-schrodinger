import GrushinScalarGridNormalization_v1

/-! The precise scalar fixed-gap recurrence from R18, and its derived grid
recurrence. Actual PDE estimates are not asserted: the displayed unnormalized
recurrence and shrinking-domain monotonicity remain explicit hypotheses. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def GrushinScalarFixedGapRecurrence (N : ℕ → ℝ → ℝ) (ρ C A F : ℝ) : Prop :=
  ∀ r : ℕ, 9 ≤ r → ∀ s e : ℝ, 0 ≤ s → 0 < e → s+e ≤ ρ →
    N r (s+e) ≤ C*(F*A^r*(r.factorial : ℝ) +
      e⁻¹*N (r-1) s + (e⁻¹)^2*N (r-2) s +
      ∑ j ∈ Finset.range r,
        A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j) s)

theorem grushin_grid_recurrence_from_fixed_gap (N : ℕ → ℝ → ℝ)
    {ρ C A F S : ℝ} {ell r : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hFS : F ≤ S) (hr : r < ell) (hr9 : 9 ≤ r)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F) :
    let d := grushinGridNorm N (ρ/(ell : ℝ))
    d r ≤ C*(S*A^r+d (r-1)+d (r-2)+
      ∑ j ∈ Finset.range r, A^(j+1)*d (r-1-j)) := by
  let h := ρ/(ell : ℝ)
  let d := grushinGridNorm N h
  have hh : 0 < h := grushin_normalization_scale_pos hρ (by omega)
  have htop : ((r : ℝ)+1)*h ≤ ρ := (grushin_grid_time_bounds hρ hr).2
  have he : (r : ℝ)*h+h = ((r : ℝ)+1)*h := by ring
  have hraw := hrec r hr9 ((r : ℝ)*h) h (by positivity) hh (by nlinarith)
  rw [he] at hraw
  have hsource : h^r*(F*A^r*(r.factorial : ℝ)) ≤ S*A^r :=
    grushin_scaled_source_le hρ.le hρ1 hr hF hA hFS
  have hfirst : h^r*(h⁻¹*N (r-1) ((r : ℝ)*h)) ≤ d (r-1) := by
    simpa only [pow_one] using
      grushin_inverse_gap_term_le N hh (j := 1) (by omega) (by omega) htop hmono
  have hsecond : h^r*((h⁻¹)^2*N (r-2) ((r : ℝ)*h)) ≤ d (r-2) :=
    grushin_inverse_gap_term_le N hh (by omega) (by omega) htop hmono
  have hsum : h^r*(∑ j ∈ Finset.range r,
      A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j) ((r : ℝ)*h)) ≤
      ∑ j ∈ Finset.range r, A^(j+1)*d (r-1-j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_range.mp hj
    have hb := grushin_scaled_factorial_term_le N hρ hρ1 hA hr
      (j := j+1) (by omega) (by omega) hN hmono
    simpa only [show r-(j+1)=r-1-j by omega] using hb
  have hall : h^r*(F*A^r*(r.factorial : ℝ) +
      h⁻¹*N (r-1) ((r : ℝ)*h) + (h⁻¹)^2*N (r-2) ((r : ℝ)*h) +
      ∑ j ∈ Finset.range r,
        A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j) ((r : ℝ)*h)) ≤
      S*A^r+d (r-1)+d (r-2)+∑ j ∈ Finset.range r, A^(j+1)*d (r-1-j) := by
    simpa only [mul_add] using add_le_add (add_le_add (add_le_add hsource hfirst) hsecond) hsum
  change d r ≤ _
  calc
    d r ≤ h^r*(C*(F*A^r*(r.factorial : ℝ) +
        h⁻¹*N (r-1) ((r : ℝ)*h) + (h⁻¹)^2*N (r-2) ((r : ℝ)*h) +
        ∑ j ∈ Finset.range r,
          A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j) ((r : ℝ)*h))) :=
      mul_le_mul_of_nonneg_left hraw (pow_nonneg hh.le _)
    _ = C*(h^r*(F*A^r*(r.factorial : ℝ) +
        h⁻¹*N (r-1) ((r : ℝ)*h) + (h⁻¹)^2*N (r-2) ((r : ℝ)*h) +
        ∑ j ∈ Finset.range r,
          A^(j+1)*((r.factorial : ℝ)/((r-1-j).factorial : ℝ))*N (r-1-j) ((r : ℝ)*h))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hall hC

#print axioms grushin_grid_recurrence_from_fixed_gap
end TheoremT.Continuum
