import GrushinScalarFixedGapBound_v1
import GrushinShiftedPowerFactorial_v1

/-! Exact R25 conversion after the order shift k+11 used by R24.
The raw fixed-gap recurrence is retained. The final comparison to a norm
family is explicit and is not a proof of an actual Sobolev embedding. -/
noncomputable section
namespace TheoremT.Continuum

theorem grushin_scalar_shifted_factorial_bound (N : ℕ → ℝ → ℝ)
    {ρ C A F H0 : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hH0 : 0 ≤ H0)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hbase : ∀ q, q ≤ 8 → ∀ s, 0 ≤ s → s ≤ ρ → N q s ≤ H0)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F) (k : ℕ) :
    let B := 2*C*A
    let S := F+H0
    let D := 2*B/ρ
    N (k+11) ρ ≤ (2*B*D^11*(3:ℝ)^12*(12:ℝ)^11)*S*
      (D*6144)^k*(k.factorial : ℝ) := by
  let B := 2*C*A
  let S := F+H0
  let D := 2*B/ρ
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := add_nonneg hF hH0
  have hD : 0 ≤ D := div_nonneg (mul_nonneg (by norm_num) hB) hρ.le
  have hs := grushin_scalar_fixed_gap_bound N hρ hρ1 hC hA hF hH0
    hN hmono hbase hrec (k+11)
  have hnorm : 2*B*((((k+11 : ℕ) : ℝ))+1)/ρ = D*((k : ℝ)+12) := by
    dsimp [D]
    push_cast
    ring
  change N (k+11) ρ ≤ (2*B*D^11*(3:ℝ)^12*(12:ℝ)^11)*S*
    (D*6144)^k*(k.factorial : ℝ)
  calc
    N (k+11) ρ ≤ 2*B*S*(D*((k : ℝ)+12))^(k+11) := by
      change N (k+11) ρ ≤ 2*B*S*(2*B*((((k+11 : ℕ) : ℝ))+1)/ρ)^(k+11) at hs
      simpa only [hnorm] using hs
    _ = (2*B*S*D^(k+11))*((k : ℝ)+12)^(k+11) := by rw [mul_pow]; ring
    _ ≤ (2*B*S*D^(k+11))*
        ((3:ℝ)^12*(12:ℝ)^11*(6144:ℝ)^k*(k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (grushin_shifted_power_factorial_bound k)
        (by positivity)
    _ = (2*B*D^11*(3:ℝ)^12*(12:ℝ)^11)*S*(D*6144)^k*(k.factorial : ℝ) := by
      rw [pow_add,mul_pow]
      ring

theorem grushin_scalar_embedding_factorial_bound (N : ℕ → ℝ → ℝ) (W : ℕ → ℝ)
    {ρ C A F H0 Ebox : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hH0 : 0 ≤ H0) (hE : 0 ≤ Ebox)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hbase : ∀ q, q ≤ 8 → ∀ s, 0 ≤ s → s ≤ ρ → N q s ≤ H0)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F)
    (hshift : ∀ k, W k ≤ Ebox*N (k+11) ρ) (k : ℕ) :
    let B := 2*C*A
    let S := F+H0
    let Cstar := 2*B*Ebox*(2*B/ρ)^11*(3:ℝ)^12*(12:ℝ)^11
    let Astar := (2*B/ρ)*6144
    W k ≤ Cstar*S*Astar^k*(k.factorial : ℝ) := by
  have hb := grushin_scalar_shifted_factorial_bound N hρ hρ1 hC hA hF hH0
    hN hmono hbase hrec k
  apply (hshift k).trans
  convert mul_le_mul_of_nonneg_left hb hE using 1 <;> ring

theorem grushin_norm_family_factorial_bound {X G : Type*} [Norm G]
    (N : ℕ → ℝ → ℝ) (J : ℕ → X → G) (K : Set X)
    {ρ C A F H0 Ebox : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hH0 : 0 ≤ H0) (hE : 0 ≤ Ebox)
    (hN : ∀ q s, 0 ≤ s → s ≤ ρ → 0 ≤ N q s)
    (hmono : ∀ q s t, 0 ≤ s → s ≤ t → t ≤ ρ → N q t ≤ N q s)
    (hbase : ∀ q, q ≤ 8 → ∀ s, 0 ≤ s → s ≤ ρ → N q s ≤ H0)
    (hrec : GrushinScalarFixedGapRecurrence N ρ C A F)
    (hshift : ∀ k x, x ∈ K → ‖J k x‖ ≤ Ebox*N (k+11) ρ) :
    let B := 2*C*A
    let S := F+H0
    let Cstar := 2*B*Ebox*(2*B/ρ)^11*(3:ℝ)^12*(12:ℝ)^11
    let Astar := (2*B/ρ)*6144
    ∀ k x, x ∈ K → ‖J k x‖ ≤ Cstar*S*Astar^k*(k.factorial : ℝ) := by
  dsimp only
  intro k x hx
  exact grushin_scalar_embedding_factorial_bound N (fun q => ‖J q x‖)
    hρ hρ1 hC hA hF hH0 hE hN hmono hbase hrec (fun q => hshift q x hx) k

#print axioms grushin_scalar_shifted_factorial_bound
#print axioms grushin_scalar_embedding_factorial_bound
#print axioms grushin_norm_family_factorial_bound
end TheoremT.Continuum
