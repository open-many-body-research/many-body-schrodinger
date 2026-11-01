import ExponentialL2Tail_v1

/-! The actual exterior H²-star norm, including all ordered mixed derivatives,
and its exponential bound from weighted component L² membership. Physical
applications supply actual WeakPartial witnesses for the components. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def weakH2ExteriorNorm {N : ℕ} (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (r : ℝ) : ℝ := Real.sqrt (‖exteriorL2 r f‖^2+
      (∑ k, ‖exteriorL2 r (d k)‖^2)+(∑ k, ∑ l, ‖exteriorL2 r (e k l)‖^2))

theorem exponential_H2_tail_of_weighted_components {N : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (hdw : ∀ k, MemLp (fun x => Real.exp (a*‖x‖) • d k x) 2 volume)
    (hew : ∀ k l, MemLp (fun x => Real.exp (a*‖x‖) • e k l x) 2 volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C := by
  let U := hw.toLp (fun x => Real.exp (a*‖x‖) • f x)
  let D (k : Coordinate N) := (hdw k).toLp (fun x => Real.exp (a*‖x‖) • d k x)
  let F (k l : Coordinate N) := (hew k l).toLp (fun x => Real.exp (a*‖x‖) • e k l x)
  let S := ‖U‖^2+(∑ k, ‖D k‖^2)+(∑ k, ∑ l, ‖F k l‖^2)
  refine ⟨Real.sqrt S,Real.sqrt_nonneg _,fun r => ?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (exponential_L2_tail_bound ha f hw r) 2
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (exponential_L2_tail_bound ha (d k) (hdw k) r) 2)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun l _ =>
      pow_le_pow_left₀ (norm_nonneg _) (exponential_L2_tail_bound ha (e k l) (hew k l) r) 2))
  simp only [mul_pow,← Finset.mul_sum] at h0 h1 h2
  have h : ‖exteriorL2 r f‖^2+(∑ k, ‖exteriorL2 r (d k)‖^2)+
      (∑ k, ∑ l, ‖exteriorL2 r (e k l)‖^2) ≤ (Real.exp (-a*r))^2*S := by
    dsimp [S,U,D,F] at h0 h1 h2 ⊢
    nlinarith
  apply (Real.sqrt_le_sqrt h).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (Real.exp_pos _)]

#print axioms exponential_H2_tail_of_weighted_components
end TheoremT.Continuum
