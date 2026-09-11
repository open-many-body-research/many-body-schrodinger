import AtomicSobolevExponent_v1

/-! Convert an actual quadratic gradient bound into an actual critical Lq
norm bound. This is a conditional transfer lemma; eigenfunction applications
must supply their gradient estimate from the physical weak equation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum

theorem weakH1_sobolev_of_gradient_bound {N : ℕ} (hN : 0 < N) {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    {B : ℝ} (hB : 0 ≤ B) (hb : (∑ k, ‖d k‖^2) ≤ B*‖f‖^2) :
    eLpNorm f (atomicSobolevExponent N) volume ≤ ENNReal.ofReal
      ((configurationSobolevConstant N : ℝ)*Real.sqrt ((3*N : ℝ)*B)*‖f‖) := by
  have hc : (∑ k, ‖d k‖)^2 ≤ (3*N : ℝ)*∑ k, ‖d k‖^2 := by
    simpa [Coordinate,Nat.mul_comm,mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Coordinate N => (1 : ℝ))
        (fun k => ‖d k‖)
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (3*N : ℝ) by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ (3*N : ℝ)*B by positivity)
  have hn : 0 ≤ Real.sqrt ((3*N : ℝ)*B)*‖f‖ := by positivity
  have hn' : 0 ≤ ∑ k, ‖d k‖ := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hsum : (∑ k, ‖d k‖) ≤ Real.sqrt ((3*N : ℝ)*B)*‖f‖ := by nlinarith
  apply (atomic_weakH1_sobolev hN d hd).2.trans
  apply ENNReal.ofReal_le_ofReal
  have ht := mul_le_mul_of_nonneg_left hsum (NNReal.coe_nonneg (configurationSobolevConstant N))
  simpa only [mul_assoc] using ht

#print axioms weakH1_sobolev_of_gradient_bound
end TheoremT.Continuum
