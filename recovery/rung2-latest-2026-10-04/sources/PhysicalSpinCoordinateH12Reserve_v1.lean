import PhysicalCoordinateMultiIndexWeakH12_v1

/-! Genuine physical H12 data for all four spin components. The aggregate
is the sum of squared integrals over four spins and 50388 multiindices,
with actual compact-test derivative identities for every member. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem ProductCoordinateWeakHk.mono_budget
    {κ : Type} [Fintype κ] [DecidableEq κ]
    {Ω : Set (Space κ)} {f : Space κ → ℂ} {m : ℕ} {W C : ℝ}
    (hf : ProductCoordinateWeakHk Ω f m W) (hWC : W ≤ C) :
    ProductCoordinateWeakHk Ω f m C := by
  obtain ⟨D,h0,hD,hweak⟩ := hf
  exact ⟨D,h0,fun w hw => ⟨(hD w hw).1,(hD w hw).2.trans hWC⟩,hweak⟩

def SpinPhysicalH12Reserve (i : Fin 2) (Ω : Set (NuclearKSSpace i))
    (f : SpinConfiguration 2 → NuclearKSSpace i → ℂ) (W : ℝ) : Prop :=
  (∀ σ, ProductCoordinateWeakHk Ω (f σ) 12 W) ∧
  ∃ V : SpinConfiguration 2 → boundedMultiIndex 7 12 → NuclearKSSpace i → ℂ,
    (∀ σ, V σ h12ZeroMultiIndex = f σ) ∧
    (∀ σ alpha, RegionL2Budget (V σ alpha) Ω W) ∧
    (∑ σ, physicalH12RegionL2Sum i (V σ) Ω) ≤ 201552 * W ∧
    ∀ σ alpha (φ : NuclearKSSpace i → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ Ω →
      Integrable (fun p => φ p • V σ alpha p) ∧
      Integrable (fun p => productCoordinateTestWord
        (h12PhysicalCoordinateWord i alpha) φ p • f σ p) ∧
      (∫ p, φ p • V σ alpha p) = ((-1 : ℝ)^(∑ k, alpha.val k)) •
        (∫ p, productCoordinateTestWord (h12PhysicalCoordinateWord i alpha) φ p • f σ p)

theorem spinPhysicalH12Reserve_of_coordinate (i : Fin 2)
    {Ω : Set (NuclearKSSpace i)} {f : SpinConfiguration 2 → NuclearKSSpace i → ℂ} {W : ℝ}
    (hf : ∀ σ, ProductCoordinateWeakHk Ω (f σ) 12 W) :
    SpinPhysicalH12Reserve i Ω f W := by
  classical
  choose V h0 hB hS hT using
    (fun σ => physical_coordinateWeakHk_multiIndex_extraction i (hf σ))
  refine ⟨hf,V,h0,hB,?_,hT⟩
  calc
    (∑ σ, physicalH12RegionL2Sum i (V σ) Ω) ≤ ∑ _σ : SpinConfiguration 2, 50388 * W :=
      Finset.sum_le_sum (fun σ _ => hS σ)
    _ = 201552 * W := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin]
      norm_num
      ring

end TheoremT.Continuum.WeakGrushin
