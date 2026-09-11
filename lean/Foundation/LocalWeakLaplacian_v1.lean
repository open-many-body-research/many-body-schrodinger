import ConfigurationLocalDominated_v1

/-! Actual local distributional Laplacian, including the integrability required
for testing and for finite linear combinations. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def realTestLaplacian {N : ℕ} (φ : Configuration N → ℝ) (x : Configuration N) : ℝ :=
  ∑ k : Coordinate N, fderiv ℝ (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k)

theorem realTestLaplacian_continuous {N : ℕ} {φ : Configuration N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : Continuous (realTestLaplacian φ) := by
  apply continuous_finset_sum
  intro k _
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (coordinateVector k)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const

theorem realTestLaplacian_compact {N : ℕ} {φ : Configuration N → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (realTestLaplacian φ) := by
  have he : realTestLaplacian φ = ∑ k : Coordinate N,
      (fun x => fderiv ℝ (fun y => fderiv ℝ φ y (coordinateVector k)) x (coordinateVector k)) := by
    funext x
    simp [realTestLaplacian]
  rw [he]
  exact HasCompactSupport.finset_sum (fun k _ =>
    (hc.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector k))

def LocalWeakLaplacian {N : ℕ} (f g : Configuration N → ℝ) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable g volume ∧
    ∀ φ : Configuration N → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x*g x) = ∫ x, realTestLaplacian φ x*f x

theorem LocalWeakLaplacian.zero (N : ℕ) :
    LocalWeakLaplacian (fun _ : Configuration N => (0:ℝ)) (fun _ => 0) := by
  refine ⟨continuous_const.locallyIntegrable,continuous_const.locallyIntegrable,?_⟩
  intro φ hφ hc
  simp

theorem LocalWeakLaplacian.add {N : ℕ} {f g u v : Configuration N → ℝ}
    (hfg : LocalWeakLaplacian f g) (huv : LocalWeakLaplacian u v) :
    LocalWeakLaplacian (fun x => f x+u x) (fun x => g x+v x) := by
  refine ⟨hfg.1.add huv.1,hfg.2.1.add huv.2.1,?_⟩
  intro φ hφ hc
  have ig : Integrable (fun x => φ x*g x) := by
    simpa only [smul_eq_mul] using hfg.2.1.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have iv : Integrable (fun x => φ x*v x) := by
    simpa only [smul_eq_mul] using huv.2.1.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have iF : Integrable (fun x => realTestLaplacian φ x*f x) := by
    simpa only [smul_eq_mul] using hfg.1.integrable_smul_left_of_hasCompactSupport
      (realTestLaplacian_continuous hφ) (realTestLaplacian_compact hc)
  have iu : Integrable (fun x => realTestLaplacian φ x*u x) := by
    simpa only [smul_eq_mul] using huv.1.integrable_smul_left_of_hasCompactSupport
      (realTestLaplacian_continuous hφ) (realTestLaplacian_compact hc)
  simp_rw [mul_add]
  rw [integral_add ig iv,integral_add iF iu,hfg.2.2 φ hφ hc,huv.2.2 φ hφ hc]

theorem LocalWeakLaplacian.smul {N : ℕ} {f g : Configuration N → ℝ}
    (hfg : LocalWeakLaplacian f g) (c : ℝ) :
    LocalWeakLaplacian (fun x => c*f x) (fun x => c*g x) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Pi.smul_def,smul_eq_mul] using hfg.1.smul c
  · simpa only [Pi.smul_def,smul_eq_mul] using hfg.2.1.smul c
  · intro φ hφ hc
    simp_rw [← mul_assoc, mul_comm (φ _) c, mul_comm (realTestLaplacian φ _) c,mul_assoc]
    rw [integral_const_mul,integral_const_mul,hfg.2.2 φ hφ hc]

theorem LocalWeakLaplacian.finset_sum {N : ℕ} {ι : Type*} (s : Finset ι)
    {f g : ι → Configuration N → ℝ} (h : ∀ i ∈ s, LocalWeakLaplacian (f i) (g i)) :
    LocalWeakLaplacian (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocalWeakLaplacian.zero N
  | @insert i s hi ih =>
    have ha := (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using ha

#print axioms LocalWeakLaplacian.finset_sum
end TheoremT.Continuum
