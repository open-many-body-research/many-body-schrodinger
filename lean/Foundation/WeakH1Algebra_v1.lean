import BoundedSmoothMultiplier_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem HasH1.add {N : ℕ} {f g : SpatialL2 N} (hf : HasH1 f) (hg : HasH1 g) :
    HasH1 (f+g) := by
  obtain ⟨d,hd⟩ := hf
  obtain ⟨e,he⟩ := hg
  exact ⟨fun k => d k+e k,fun k => weakPartial_add (hd k) (he k)⟩

theorem HasH1.smul {N : ℕ} {f : SpatialL2 N} (hf : HasH1 f) (c : ℂ) :
    HasH1 (c • f) := by
  obtain ⟨d,hd⟩ := hf
  exact ⟨fun k => c • d k,fun k => weakPartial_smul c (hd k)⟩

theorem hasH1_zero (N : ℕ) : HasH1 (0 : SpatialL2 N) :=
  ⟨fun _ => 0,weakPartial_zero⟩

theorem hasH1_finset_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → SpatialL2 N)
    (hf : ∀ j ∈ s, HasH1 (f j)) : HasH1 (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasH1_zero N
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).add (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

theorem HasH1.compact_product_rep {N : ℕ} {f : SpatialL2 N} (hf : HasH1 f)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ g : SpatialL2 N, HasH1 g ∧ g =ᵐ[volume] (fun x => χ x • f x) := by
  have hm : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hc volume
  have hdm (k : Coordinate N) : MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume :=
    ((hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      (hc.fderiv_apply ℝ (coordinateVector k)) volume
  exact ⟨boundedRealMul χ hm f,hf.mul_bounded_smooth χ hχ hm hdm,boundedRealMul_ae χ hm f⟩

#print axioms HasH1.compact_product_rep
end TheoremT.Continuum
