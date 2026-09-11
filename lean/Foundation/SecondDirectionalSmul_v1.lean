import CompactCutoffDirectionalJets_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem second_directional_smul {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => η z • u z) y v) x w =
      (fderiv ℝ (fun y => fderiv ℝ η y v) x w) • u x +
      (fderiv ℝ η x v) • fderiv ℝ u x w +
      (fderiv ℝ η x w) • fderiv ℝ u x v +
      η x • fderiv ℝ (fun y => fderiv ℝ u y v) x w := by
  have hηd : ContDiff ℝ ∞ (fun y => fderiv ℝ η y v) :=
    (hη.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hud : ContDiff ℝ ∞ (fun y => fderiv ℝ u y v) :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have he : (fun y => fderiv ℝ (fun z => η z • u z) y v) =
      (fun y => (fderiv ℝ η y v) • u y + η y • fderiv ℝ u y v) := by
    funext y; exact cutoff_directional_product hη hu y v
  rw [he]
  have ha := (hηd.smul hu).differentiable (by simp)
  have hb := (hη.smul hud).differentiable (by simp)
  simp only [Pi.smul_def'] at ha hb
  have hs := fderiv_add (ha x) (hb x)
  simp only [Pi.add_def] at hs
  rw [hs,ContinuousLinearMap.add_apply]
  rw [cutoff_directional_product hηd hu,cutoff_directional_product hη hud]
  abel

theorem second_same_directional_smul {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x v : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => η z • u z) y v) x v =
      (fderiv ℝ (fun y => fderiv ℝ η y v) x v) • u x +
      (2*fderiv ℝ η x v) • fderiv ℝ u x v +
      η x • fderiv ℝ (fun y => fderiv ℝ u y v) x v := by
  rw [second_directional_smul hη hu]
  rw [two_mul,add_smul]
  abel

#print axioms second_directional_smul
#print axioms second_same_directional_smul
end TheoremT.Continuum
