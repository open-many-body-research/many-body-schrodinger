import GrushinLocalCommutatorIntegral_v1
import KSHoleIntegralLimit_v1
import NuclearKSCompactIntegral_v1

/-! A continuous-input codimension-four removability theorem; only local bounds on the input are used.
The hypothesis is the weak equation only for tests supported away from the
transverse zero set; the conclusion allows tests crossing that set.
No physical weak KS pullback is asserted here. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem nuclear_KS_continuous_Grushin_removability {N : ℕ} (i : Fin N)
    {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → SpectatorConfiguration i)
    {B : NuclearKSSpace i → ℝ} (hB : Continuous B)
    {u f : NuclearKSSpace i → ℂ} (hu : Continuous u) (hf : Continuous f)
    (Ω : Set (NuclearKSSpace i))
    (hweak : ∀ ψ : NuclearKSSpace i → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω \ {q | q.1=0} →
      (∫ q, (splitGrushin c v B ψ q : ℂ)*u q) = ∫ q, (ψ q : ℂ)*f q)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    (∫ q, (splitGrushin c v B φ q : ℂ)*u q) = ∫ q, (φ q : ℂ)*f q := by
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδ1 (n : ℕ) : δ n ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hd : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hQ := splitGrushin_continuous c v hB hφ
  have hcQ := splitGrushin_compact c v B hc
  have hI := nuclear_KS_real_test_mul_integrable i hQ hcQ hu
  have hJ := nuclear_KS_real_test_mul_integrable i hφ.continuous hc hf
  have hL := nuclear_KS_hole_integral_tendsto i hI hδ hd
  have hR := nuclear_KS_hole_integral_tendsto i hJ hδ hd
  have hD := nuclear_KS_continuous_commutator_integral_tendsto_zero i hφ hc hu hδ hδ1 hd
  have he (n : ℕ) :
      (∫ q, (ksHole (δ n) q.1 : ℂ)*((splitGrushin c v B φ q : ℂ)*u q))+
      (∫ q, (ksHoleCommutator (δ n) φ q : ℂ)*u q) =
      ∫ q, (ksHole (δ n) q.1 : ℂ)*((φ q : ℂ)*f q) := by
    let ψ : NuclearKSSpace i → ℝ := fun q => ksHole (δ n) q.1*φ q
    have hh : ContDiff ℝ ∞ (fun q : NuclearKSSpace i => ksHole (δ n) q.1) :=
      (ksHole_contDiff (δ n)).comp contDiff_fst
    have hψ : ContDiff ℝ ∞ ψ := hh.mul hφ
    have hcψ : HasCompactSupport ψ := hc.mul_left
    have hsψ : tsupport ψ ⊆ Ω \ {q | q.1=0} := by
      intro q hq
      refine ⟨hs (tsupport_mul_subset_right hq),?_⟩
      have ha := ksHole_test_tsupport_away i (hδ n) φ hq
      change δ n ≤ ‖q.1‖ at ha
      intro hz
      change q.1=0 at hz
      simp only [hz,norm_zero] at ha
      exact (not_le_of_gt (hδ n)) ha
    have hw := hweak ψ hψ hcψ hsψ
    have hLI : Integrable (fun q => (ksHole (δ n) q.1 : ℂ)*((splitGrushin c v B φ q : ℂ)*u q)) volume := by
      have ht := nuclear_KS_real_test_mul_integrable i (hh.continuous.mul hQ) hcQ.mul_left hu
      simpa only [Pi.mul_apply,Complex.ofReal_mul,mul_assoc] using ht
    have hDI := nuclear_KS_real_test_mul_integrable i
      (ksHoleCommutator_continuous (δ n) hφ) (ksHoleCommutator_compact (δ n) hc) hu
    rw [← integral_add hLI hDI]
    calc
      _ = ∫ q, (splitGrushin c v B ψ q : ℂ)*u q := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun q => by
          dsimp [ψ]
          rw [splitGrushin_hole_product (δ n) c v B hφ q]
          push_cast
          ring)
      _ = ∫ q, (ψ q : ℂ)*f q := hw
      _ = _ := by simp only [ψ,Complex.ofReal_mul,mul_assoc]
  have hLR := (hL.add hD).congr' (Eventually.of_forall he)
  simpa only [add_zero] using tendsto_nhds_unique hLR hR

#print axioms nuclear_KS_continuous_Grushin_removability
end TheoremT.Continuum
