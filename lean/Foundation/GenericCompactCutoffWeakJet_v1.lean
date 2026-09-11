import GenericBoundedSmoothMultiplier_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem genericBoundedRealMul_second_weakDirectional
    {f dk dl e : Lp ℂ 2 (volume : Measure E)} {k l : E}
    (hl : WeakL2Directional f dl l) (he : WeakL2Directional dk e l)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hm : MemLp χ (⊤ : ENNReal) volume)
    (hk : MemLp (fun x => fderiv ℝ χ x k) (⊤ : ENNReal) volume)
    (hd : MemLp (fun x => fderiv ℝ χ x l) (⊤ : ENNReal) volume)
    (hkl : MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ χ y k) x l) (⊤ : ENNReal) volume) :
    WeakL2Directional
      (genericBoundedRealMul χ hm dk+genericBoundedRealMul (fun x => fderiv ℝ χ x k) hk f)
      ((genericBoundedRealMul χ hm e+genericBoundedRealMul (fun x => fderiv ℝ χ x l) hd dk)+
        (genericBoundedRealMul (fun x => fderiv ℝ χ x k) hk dl+
          genericBoundedRealMul (fun x => fderiv ℝ
            (fun y => fderiv ℝ χ y k) x l) hkl f)) l := by
  have hc : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x k) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  exact weakL2Directional_add (weakL2Directional_genericBoundedRealMul he χ hχ hm hd)
    (weakL2Directional_genericBoundedRealMul hl _ hc hk hkl)

theorem generic_compact_cutoff_weak_jet
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {f : Lp ℂ 2 (volume : Measure E)} {d : E → Lp ℂ 2 (volume : Measure E)}
    {e : E → E → Lp ℂ 2 (volume : Measure E)}
    (hd : ∀ k, WeakL2Directional f (d k) k) (he : ∀ k l, WeakL2Directional (d k) (e k l) l) :
    ∃ u : Lp ℂ 2 (volume : Measure E), ∃ a : E → Lp ℂ 2 (volume : Measure E),
      ∃ b : E → E → Lp ℂ 2 (volume : Measure E),
        (∀ k, WeakL2Directional u (a k) k) ∧ (∀ k l, WeakL2Directional (a k) (b k l) l) ∧
        u =ᵐ[volume] (fun x => χ x • f x) ∧
        (∀ k, a k =ᵐ[volume] (fun x => χ x • d k x+fderiv ℝ χ x k • f x)) ∧
        (∀ k l, b k l =ᵐ[volume] (fun x =>
          (χ x • e k l x+fderiv ℝ χ x l • d k x)+
          (fderiv ℝ χ x k • d l x+
            fderiv ℝ (fun y => fderiv ℝ χ y k) x l • f x))) := by
  have h₀ : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hc volume
  have hcD (k : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x k) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hD (k : E) : MemLp (fun x => fderiv ℝ χ x k) ⊤ volume :=
    (hcD k).continuous.memLp_top_of_hasCompactSupport (hc.fderiv_apply ℝ k) volume
  have hE (k l : E) : MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ χ y k) x l) ⊤ volume :=
    (((hcD k).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      ((hc.fderiv_apply ℝ k).fderiv_apply ℝ l) volume
  let U := genericBoundedRealMul χ h₀
  let D (k : E) := genericBoundedRealMul (fun x => fderiv ℝ χ x k) (hD k)
  let M2 (k l : E) := genericBoundedRealMul (fun x => fderiv ℝ
    (fun y => fderiv ℝ χ y k) x l) (hE k l)
  let a (k : E) := U (d k)+D k f
  let b (k l : E) := (U (e k l)+D l (d k))+(D k (d l)+M2 k l f)
  refine ⟨U f,a,b,?_,?_,genericBoundedRealMul_ae _ h₀ f,?_,?_⟩
  · intro k
    exact weakL2Directional_genericBoundedRealMul (hd k) χ hχ h₀ (hD k)
  · intro k l
    exact genericBoundedRealMul_second_weakDirectional (hd l) (he k l) χ hχ h₀ (hD k) (hD l) (hE k l)
  · intro k
    filter_upwards [Lp.coeFn_add (U (d k)) (D k f),genericBoundedRealMul_ae _ h₀ (d k),
      genericBoundedRealMul_ae _ (hD k) f] with x hx hux hdx
    change (U (d k)+D k f) x = _
    rw [hx]
    change U (d k) x+D k f x = _
    rw [hux,hdx]
  · intro k l
    filter_upwards [Lp.coeFn_add (U (e k l)+D l (d k)) (D k (d l)+M2 k l f),
      Lp.coeFn_add (U (e k l)) (D l (d k)),Lp.coeFn_add (D k (d l)) (M2 k l f),
      genericBoundedRealMul_ae _ h₀ (e k l),genericBoundedRealMul_ae _ (hD l) (d k),
      genericBoundedRealMul_ae _ (hD k) (d l),genericBoundedRealMul_ae _ (hE k l) f] with x hx hx1 hx2 hu hd1 hd2 hh
    change ((U (e k l)+D l (d k))+(D k (d l)+M2 k l f)) x = _
    rw [hx]
    change (U (e k l)+D l (d k)) x+(D k (d l)+M2 k l f) x = _
    rw [hx1,hx2]
    change (U (e k l) x+D l (d k) x)+(D k (d l) x+M2 k l f x) = _
    rw [hu,hd1,hd2,hh]


#print axioms genericBoundedRealMul_second_weakDirectional
#print axioms generic_compact_cutoff_weak_jet
end TheoremT.Continuum
