import WeakH1Sobolev_v1

/-! The actual critical H1 exponent 2(3N)/(3N-2), for every N >= 1. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace TheoremT.Continuum

def atomicSobolevExponent (N : ℕ) : ℝ≥0 := 2*(3*N)/(3*N-2)

theorem configuration_finrank (N : ℕ) : Module.finrank ℝ (Configuration N) = 3*N := by
  simp [Configuration,Coordinate,finrank_euclideanSpace,Nat.mul_comm]

theorem atomicSobolevExponent_inv {N : ℕ} (hN : 0 < N) :
    (atomicSobolevExponent N : ℝ)⁻¹ = (2 : ℝ)⁻¹ -
      (Module.finrank ℝ (Configuration N) : ℝ)⁻¹ := by
  have hn : (1 : ℝ≥0) ≤ N := by exact_mod_cast hN
  have hn' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : (2 : ℝ≥0) ≤ 3*N := by nlinarith
  rw [configuration_finrank]
  simp only [atomicSobolevExponent,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_ofNat,
    NNReal.coe_natCast,NNReal.coe_sub hd,Nat.cast_mul,Nat.cast_ofNat]
  field_simp
  <;> ring

theorem atomic_weakH1_sobolev {N : ℕ} (hN : 0 < N) {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp f (atomicSobolevExponent N) volume ∧
      eLpNorm f (atomicSobolevExponent N) volume ≤ ENNReal.ofReal
        ((configurationSobolevConstant N : ℝ) * ∑ k, ‖d k‖) := by
  have hn : 0 < Module.finrank ℝ (Configuration N) := by
    rw [configuration_finrank]; omega
  exact ⟨weakH1_sobolev_memLp d hd hn (atomicSobolevExponent_inv hN),
    weakH1_sobolev_bound d hd hn (atomicSobolevExponent_inv hN)⟩

theorem twoElectron_weakH1_L3 {f : SpatialL2 2}
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp f 3 volume := by
  have he : atomicSobolevExponent 2 = 3 := by
    apply NNReal.coe_injective
    apply inv_injective
    convert atomicSobolevExponent_inv (by norm_num : 0 < 2) using 1 <;>
      norm_num [configuration_finrank]
  simpa only [he,ENNReal.coe_ofNat] using
    (atomic_weakH1_sobolev (by norm_num : 0 < 2) d hd).1

#print axioms atomicSobolevExponent_inv
#print axioms atomic_weakH1_sobolev
#print axioms twoElectron_weakH1_L3
end TheoremT.Continuum
