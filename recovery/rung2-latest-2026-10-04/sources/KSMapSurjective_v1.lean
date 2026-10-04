import KSMapGeometry_v1

noncomputable section
namespace TheoremT.Continuum

theorem ksMap_surjective : Function.Surjective ksMap := by
  intro x
  have hr : 0 ≤ ‖x‖ := norm_nonneg x
  have hs : ‖x‖^2=x 0^2+x 1^2+x 2^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
    ring
  have hc : 0 ≤ ‖x‖+x 2 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  by_cases hp : 0 < ‖x‖+x 2
  · let a : ℝ := Real.sqrt ((‖x‖+x 2)/2)
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a^2=(‖x‖+x 2)/2 := Real.sq_sqrt (by positivity)
    have hsq : x 0^2+x 1^2=4*a^2*(a^2-x 2) := by rw [ha2]; nlinarith [hs]
    refine ⟨WithLp.toLp 2 ![a,0,x 0/(2*a),-x 1/(2*a)],?_⟩
    ext i
    fin_cases i
    · change 2*(a*(x 0/(2*a))+0*(-x 1/(2*a)))=x 0
      field_simp <;> ring
    · change 2*(0*(x 0/(2*a))-a*(-x 1/(2*a)))=x 1
      field_simp <;> ring
    · change a^2+0^2-(x 0/(2*a))^2-(-x 1/(2*a))^2=x 2
      field_simp
      nlinarith [hsq]
  · have hc0 : ‖x‖+x 2=0 := le_antisymm (le_of_not_gt hp) hc
    have h0 : x 0=0 := by nlinarith [hs,sq_nonneg (x 1)]
    have h1 : x 1=0 := by nlinarith [hs,sq_nonneg (x 0)]
    refine ⟨WithLp.toLp 2 ![0,0,Real.sqrt ‖x‖,0],?_⟩
    ext i
    fin_cases i
    · change 2*(0*Real.sqrt ‖x‖+0*0)=x 0
      simp [h0]
    · change 2*(0*Real.sqrt ‖x‖-0*0)=x 1
      simp [h1]
    · change (0:ℝ)^2+0^2-(Real.sqrt ‖x‖)^2-0^2=x 2
      rw [Real.sq_sqrt hr]
      nlinarith

theorem ksMap_exists_preimage_with_norm (x : Position) :
    ∃ y : KSSpace, ksMap y=x ∧ ‖y‖^2=‖x‖ := by
  obtain ⟨y,hy⟩ := ksMap_surjective x
  exact ⟨y,hy,(ksMap_norm y).symm.trans (congrArg norm hy)⟩

#print axioms ksMap_surjective
#print axioms ksMap_exists_preimage_with_norm
end TheoremT.Continuum
