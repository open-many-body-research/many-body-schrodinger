import GenericMollifierSequence_v1

/-! Finite ordered coordinate words commute with the actual smooth mollifier
of a genuine global weak L2 jet. The domain is any finite-dimensional real
inner-product space. No local extension, support, PDE, or representative
regularity hypothesis is inferred. All words use actual nested fderiv. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.GenericMollifier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}

def complexDirectionalWordDeriv (dirs : ι → E) (u : E → ℂ) :
    List ι → E → ℂ
  | [] => u
  | i :: w => fun x => fderiv ℝ (complexDirectionalWordDeriv dirs u w) x (dirs i)

theorem complexDirectionalWordDeriv_contDiff (dirs : ι → E)
    {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (w : List ι) :
    ContDiff ℝ ∞ (complexDirectionalWordDeriv dirs u w) := by
  induction w with
  | nil => exact hu
  | cons i w ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem mollify_word_commute (dirs : ι → E)
    (D : List ι → Lp ℂ 2 (volume : Measure E)) {m : ℕ}
    (hD : ∀ w i, w.length < m → WeakL2Directional (D w) (D (i :: w)) (dirs i))
    (η : E → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (w : List ι) (hw : w.length ≤ m) :
    complexDirectionalWordDeriv dirs (mollify η (D [])) w = mollify η (D w) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hwm : w.length < m := by simp only [List.length_cons] at hw; omega
    simp only [complexDirectionalWordDeriv]
    rw [ih hwm.le]
    funext x
    exact mollify_derivative (hD w i hwm) η hη hcη x

theorem mollifyLp_word_ae (dirs : ι → E)
    (D : List ι → Lp ℂ 2 (volume : Measure E)) {m : ℕ}
    (hD : ∀ w i, w.length < m → WeakL2Directional (D w) (D (i :: w)) (dirs i))
    (n : ℕ) (w : List ι) (hw : w.length ≤ m) :
    (mollifyLp n (D w) : E → ℂ) =ᵐ[volume]
      complexDirectionalWordDeriv dirs (mollify (mollifierKernel n) (D [])) w := by
  rw [mollify_word_commute dirs D hD _ (mollifierKernel_contDiff n)
    (mollifierKernel_hasCompactSupport n) w hw]
  exact mollifyLp_ae n (D w)

theorem weak_word_mollification (dirs : ι → E)
    (D : List ι → Lp ℂ 2 (volume : Measure E)) {m : ℕ}
    (hD : ∀ w i, w.length < m → WeakL2Directional (D w) (D (i :: w)) (dirs i)) :
    (∀ n, ContDiff ℝ ∞ (mollify (mollifierKernel n) (D []))) ∧
    (∀ n w, w.length ≤ m →
      ContDiff ℝ ∞ (complexDirectionalWordDeriv dirs
        (mollify (mollifierKernel n) (D [])) w)) ∧
    (∀ n w, w.length ≤ m → (mollifyLp n (D w) : E → ℂ) =ᵐ[volume]
      complexDirectionalWordDeriv dirs (mollify (mollifierKernel n) (D [])) w) ∧
    (∀ w, w.length ≤ m → Tendsto (fun n => mollifyLp n (D w)) atTop (𝓝 (D w))) ∧
    (∀ n w, w.length ≤ m → ‖mollifyLp n (D w)‖ ≤ ‖D w‖) := by
  have hs (n : ℕ) : ContDiff ℝ ∞ (mollify (mollifierKernel n) (D [])) :=
    mollify_contDiff _ (mollifierKernel_contDiff n) (mollifierKernel_hasCompactSupport n) _
  exact ⟨hs, (fun n w _ => complexDirectionalWordDeriv_contDiff dirs (hs n) w),
    (fun n w hw => mollifyLp_word_ae dirs D hD n w hw),
    (fun w _ => mollifyLp_tendsto (D w)), (fun n w _ => mollifyLp_norm_le n (D w))⟩

end TheoremT.Continuum.GenericMollifier
