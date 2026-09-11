import KSLaplacianCompositionAt_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

def ksProductMap (q : KSSpace × S) : Position × S := (ksMap q.1,q.2)

theorem ksProductMap_contDiff : ContDiff ℝ ∞ (ksProductMap (S := S)) :=
  (ksMap_contDiff.comp contDiff_fst).prodMk contDiff_snd

theorem ksProductMap_first (q v : KSSpace × S) :
    fderiv ℝ ksProductMap q v=(fderiv ℝ ksMap q.1 v.1,v.2) := by
  have hh := ((ksMap_contDiff.differentiable (by simp) q.1).hasFDerivAt.comp q
    hasFDerivAt_fst).prodMk (hasFDerivAt_snd (p := q))
  change HasFDerivAt ksProductMap _ q at hh
  rw [hh.fderiv]
  rfl

theorem ksProductMap_second (q v w : KSSpace × S) :
    fderiv ℝ (fun z => fderiv ℝ ksProductMap z v) q w =
      (fderiv ℝ (fun y => fderiv ℝ ksMap y v.1) q.1 w.1,0) := by
  have he : (fun z : KSSpace × S => fderiv ℝ ksProductMap z v)=
      (fun z => (fderiv ℝ ksMap z.1 v.1,v.2)) := funext (fun z => ksProductMap_first z v)
  rw [he]
  have hd : Differentiable ℝ (fun y => fderiv ℝ ksMap y v.1) :=
    (((ksMap_contDiff.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp))
  have hh := ((hd q.1).hasFDerivAt.comp q hasFDerivAt_fst).prodMk
    (hasFDerivAt_const v.2 q)
  change HasFDerivAt (fun z : KSSpace × S => (fderiv ℝ ksMap z.1 v.1,v.2)) _ q at hh
  rw [hh.fderiv]
  rfl

#print axioms ksProductMap_first
#print axioms ksProductMap_second
end TheoremT.Continuum
