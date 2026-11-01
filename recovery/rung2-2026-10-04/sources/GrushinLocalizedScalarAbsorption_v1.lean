import GrushinRecurrenceForcingAbsorption_v1
import GrushinScalarFixedGapRecurrence_v1

/-! Order-independent scalar constants for the localized graph estimate.
The last implication retains the decomposed local PDE estimate as an explicit
hypothesis. It does not silently supply cutoff or weak-derivative semantics. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def grushinLocalizedCoefficient (C0 M c K1 K2 : ℝ) : ℝ :=
  max 1 (C0*(1+2*M+6*|c|+K1+K2))

theorem grushin_localized_scalar_absorption
    {A C0 M K1 K2 e Q : ℝ} (hA : 1 ≤ A) (hC0 : 0 ≤ C0)
    (hM : 0 ≤ M) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (he : 0 < e) (he1 : e ≤ 1) (hQ : 0 ≤ Q)
    (c : ℝ) (r : ℕ) (hr : 2 ≤ r) (N : ℕ → ℝ) (hN : ∀ k, 0 ≤ N k) :
    C0*(Q + M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
        ((j+1).factorial : ℝ)*N (r-(j+1))) +
      6*|c| *(r : ℝ)*N (r-1)+3*|c| *((r*(r-1) : ℕ) : ℝ)*N (r-2)+
      M*N (r-1)+K1*e⁻¹*N (r-1)+K2*(e⁻¹)^2*N (r-2)) ≤
    grushinLocalizedCoefficient C0 M c K1 K2 *
      (Q+e⁻¹*N (r-1)+(e⁻¹)^2*N (r-2)+grushinFactorialLossSum A r N) := by
  let L := grushinFactorialLossSum A r N
  let X := e⁻¹*N (r-1)
  let Y := (e⁻¹)^2*N (r-2)
  let K := 1+2*M+6*|c|+K1+K2
  have hL : 0 ≤ L := grushin_factorial_loss_sum_nonneg (zero_le_one.trans hA) r N hN
  have hX : 0 ≤ X := mul_nonneg (inv_nonneg.mpr he.le) (hN _)
  have hY : 0 ≤ Y := mul_nonneg (sq_nonneg _) (hN _)
  have hi : 1 ≤ e⁻¹ := (one_le_inv₀ he).2 he1
  have hNX : N (r-1) ≤ X := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (hN (r-1))
  have hMX := mul_le_mul_of_nonneg_left hNX hM
  have hcomm := grushin_principal_potential_absorption hA hM c r hr N hN
  have hKQ : Q ≤ K*Q := by
    have h : 1 ≤ K := by dsimp [K]; have := abs_nonneg c; linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h hQ
  have hKL : (M+6*|c|)*L ≤ K*L :=
    mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hL
  have hKX : (M+K1)*X ≤ K*X :=
    mul_le_mul_of_nonneg_right (by dsimp [K]; have := abs_nonneg c; linarith) hX
  have hKY : K2*Y ≤ K*Y :=
    mul_le_mul_of_nonneg_right (by dsimp [K]; have := abs_nonneg c; linarith) hY
  have hinside : Q + M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
        ((j+1).factorial : ℝ)*N (r-(j+1))) +
      6*|c| *(r : ℝ)*N (r-1)+3*|c| *((r*(r-1) : ℕ) : ℝ)*N (r-2)+
      M*N (r-1)+K1*e⁻¹*N (r-1)+K2*(e⁻¹)^2*N (r-2) ≤ K*(Q+X+Y+L) := by
    change _ ≤ (M+6*|c|)*L at hcomm
    change M*N (r-1) ≤ M*X at hMX
    dsimp [X,Y] at hKX hKY ⊢
    nlinarith
  calc
    _ ≤ C0*(K*(Q+X+Y+L)) := mul_le_mul_of_nonneg_left hinside hC0
    _ = (C0*K)*(Q+X+Y+L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right 1 (C0*K))
      (by positivity : 0 ≤ Q+X+Y+L)

theorem grushin_fixed_gap_recurrence_of_localized_bounds
    (N : ℕ → ℝ → ℝ) {ρ A C0 M K1 K2 F : ℝ} (c : ℝ)
    (hρ1 : ρ ≤ 1) (hA : 1 ≤ A) (hC0 : 0 ≤ C0)
    (hM : 0 ≤ M) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hF : 0 ≤ F)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hloc : ∀ r : ℕ, 9 ≤ r → ∀ s e : ℝ, 0 ≤ s → 0 < e → s+e ≤ ρ →
      N r (s+e) ≤ C0*(F*A^r*(r.factorial : ℝ) +
        M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
          ((j+1).factorial : ℝ)*N (r-(j+1)) s) +
        6*|c| *(r : ℝ)*N (r-1) s+3*|c| *((r*(r-1) : ℕ) : ℝ)*N (r-2) s+
        M*N (r-1) s+K1*e⁻¹*N (r-1) s+K2*(e⁻¹)^2*N (r-2) s)) :
    GrushinScalarFixedGapRecurrence N ρ (grushinLocalizedCoefficient C0 M c K1 K2) A F := by
  intro r hr s e hs he hse
  exact (hloc r hr s e hs he hse).trans
    (grushin_localized_scalar_absorption hA hC0 hM hK1 hK2 he (by linarith)
      (by have hA0 := zero_le_one.trans hA; positivity) c r (by omega)
      (fun q => N q s) (fun q => hN q s hs (by linarith)))

end TheoremT.Continuum
