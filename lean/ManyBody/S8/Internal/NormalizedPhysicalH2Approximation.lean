import ManyBody.S8.CoulombCompactHamiltonianResidual

/-! Normalizing actual physical H2 approximants, with explicit control of every
component and of the genuine graph Rayleigh energy. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

/-- A conservative explicit threshold in the existential tail constant. -/
def physicalCompactNormalizationRadius (a C : ℝ) : ℝ := max 1 (2*C/a)

def physicalNormalizationScalar (F : SpatialL2 2) : ℂ := ((‖F‖⁻¹ : ℝ) : ℂ)

theorem physicalCompactNormalizationRadius_half {a C R : ℝ} (ha : 0<a)
    (hR : physicalCompactNormalizationRadius a C≤R) :
    1≤R ∧ Real.exp (-a*R)*C≤1/2 := by
  have hr1 : 1≤R := (le_max_left _ _).trans hR
  have hr2 : 2*C/a≤R := (le_max_right _ _).trans hR
  have hc : 2*C≤a*R := by
    have := (div_le_iff₀ ha).mp hr2
    nlinarith
  have hx := Real.add_one_le_exp (a*R)
  have hm := mul_le_mul_of_nonneg_right (show 2*C≤Real.exp (a*R) by linarith)
    (Real.exp_pos (-a*R)).le
  have he : Real.exp (a*R)*Real.exp (-a*R)=1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at hm
  exact ⟨hr1,by nlinarith⟩

theorem physical_normalization_scalar_bounds {F f : SpatialL2 2} {δ : ℝ}
    (hf : ‖f‖=1) (hδ : ‖F-f‖≤δ) (hhalf : δ≤1/2) :
    1/2≤‖F‖ ∧ ‖physicalNormalizationScalar F‖≤2 ∧
      ‖physicalNormalizationScalar F-1‖≤2*δ ∧
      ‖physicalNormalizationScalar F • F‖=1 := by
  have hdist : |‖F‖-1|≤δ := by
    simpa only [hf] using (abs_norm_sub_norm_le F f).trans hδ
  have hlow : 1/2≤‖F‖ := by have := (abs_le.mp hdist).1; linarith
  have hpos : 0<‖F‖ := by linarith
  have hi : 0≤‖F‖⁻¹ := inv_nonneg.mpr hpos.le
  have hib : ‖F‖⁻¹≤2 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
  have hn : ‖physicalNormalizationScalar F‖=‖F‖⁻¹ := by
    simp only [physicalNormalizationScalar,Complex.norm_real,norm_inv,norm_norm]
  have hscalar : ‖physicalNormalizationScalar F-1‖=|‖F‖⁻¹-1| := by
    change ‖((‖F‖⁻¹ : ℝ) : ℂ)-(1:ℂ)‖=|‖F‖⁻¹-1|
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hid : ‖F‖⁻¹-1=(1-‖F‖)*‖F‖⁻¹ := by field_simp
  have ha1 : |1-‖F‖|≤δ := by simpa only [abs_sub_comm] using hdist
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have hsmall : |‖F‖⁻¹-1|≤2*δ := by
    rw [hid,abs_mul,abs_of_nonneg hi]
    have := mul_le_mul ha1 hib hi hδ0
    nlinarith
  refine ⟨hlow,hn ▸ hib,hscalar ▸ hsmall,?_⟩
  rw [norm_smul,hn,inv_mul_cancel₀ (ne_of_gt hpos)]

theorem physical_normalized_component_defect_le {c : ℂ} {v w : SpatialL2 2}
    {δ T : ℝ} (hc : ‖c‖≤2) (hc1 : ‖c-1‖≤2*δ)
    (hδ : 0≤δ) (hv : ‖v-w‖≤δ) (hw : ‖w‖≤T) :
    ‖c • v-w‖≤2*δ*(1+T) := by
  have hid : c • v-w=c • (v-w)+(c-1) • w := by
    rw [smul_sub,sub_smul,one_smul]
    abel
  rw [hid]
  calc _≤‖c • (v-w)‖+‖(c-1) • w‖ := norm_add_le _ _
       _=‖c‖*‖v-w‖+‖c-1‖*‖w‖ := by rw [norm_smul,norm_smul]
       _≤2*δ+(2*δ)*T := add_le_add
         (mul_le_mul hc hv (norm_nonneg _) (by norm_num))
         (mul_le_mul hc1 hw (norm_nonneg _) (by positivity))
       _=2*δ*(1+T) := by ring

theorem physicalH2ComponentNorm_first_le (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (k : Coordinate 2) : ‖d k‖≤physicalH2ComponentNorm f d e := by
  calc ‖d k‖≤Real.sqrt (∑ j,‖d j‖^2) := Real.le_sqrt_of_sq_le
         (Finset.single_le_sum (fun j _ => sq_nonneg ‖d j‖) (Finset.mem_univ k))
       _≤physicalH2ComponentNorm f d e := (physicalH2ComponentNorm_bounds f d e).2.1

theorem physicalH2ComponentNorm_le_common (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (T : ℝ) (hT : 0≤T) (h0 : ‖f‖≤T)
    (h1 : ∀ k, ‖d k‖≤T) (h2 : ∀ k l, ‖e k l‖≤T) :
    physicalH2ComponentNorm f d e≤7*T := by
  have hs0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hs1 := Finset.sum_le_sum (s:=Finset.univ)
    (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (h1 k) 2)
  have hs2 := Finset.sum_le_sum (s:=Finset.univ) (fun k _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun l _ => pow_le_pow_left₀ (norm_nonneg _) (h2 k l) 2))
  have hcard : Fintype.card (Coordinate 2)=6 := by simp [Coordinate]
  simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at hs1 hs2
  norm_num only [Nat.cast_ofNat] at hs1 hs2
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · change ‖f‖^2+(∑ k,‖d k‖^2)+(∑ k,∑ l,‖e k l‖^2)≤_
    nlinarith [sq_nonneg T]

theorem physical_normalized_H2_defect_le {F f : SpatialL2 2}
    (D d : Coordinate 2 → SpatialL2 2) (A e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    {δ : ℝ} (hf : ‖f‖=1)
    (hb : physicalH2ComponentNorm (F-f) (fun k => D k-d k) (fun k l => A k l-e k l)≤δ)
    (hhalf : δ≤1/2) :
    physicalH2ComponentNorm (physicalNormalizationScalar F • F-f)
      (fun k => physicalNormalizationScalar F • D k-d k)
      (fun k l => physicalNormalizationScalar F • A k l-e k l)≤
      14*(1+physicalH2ComponentNorm f d e)*δ := by
  have hd0 := (physicalH2ComponentNorm_bounds (F-f) (fun k => D k-d k)
    (fun k l => A k l-e k l)).1.trans hb
  obtain ⟨_,hc,hc1,_⟩ := physical_normalization_scalar_bounds hf hd0 hhalf
  have hδ : 0≤δ := (Real.sqrt_nonneg _).trans hb
  let T := physicalH2ComponentNorm f d e
  have hT : 0≤T := Real.sqrt_nonneg _
  have h0 := physical_normalized_component_defect_le hc hc1 hδ hd0
    (physicalH2ComponentNorm_bounds f d e).1
  have h1 (k : Coordinate 2) :
      ‖physicalNormalizationScalar F • D k-d k‖≤2*δ*(1+T) :=
    physical_normalized_component_defect_le hc hc1 hδ
      ((physicalH2ComponentNorm_first_le (F-f) (fun k => D k-d k)
        (fun k l => A k l-e k l) k).trans hb)
      (physicalH2ComponentNorm_first_le f d e k)
  have h2 (k l : Coordinate 2) :
      ‖physicalNormalizationScalar F • A k l-e k l‖≤2*δ*(1+T) :=
    physical_normalized_component_defect_le hc hc1 hδ
      (((physicalH2ComponentNorm_bounds (F-f) (fun k => D k-d k)
        (fun k l => A k l-e k l)).2.2 k l).trans hb)
      ((physicalH2ComponentNorm_bounds f d e).2.2 k l)
  have hfull := physicalH2ComponentNorm_le_common
    (physicalNormalizationScalar F • F-f)
    (fun k => physicalNormalizationScalar F • D k-d k)
    (fun k l => physicalNormalizationScalar F • A k l-e k l)
    (2*δ*(1+T)) (by positivity) h0 h1 h2
  calc _≤7*(2*δ*(1+T)) := hfull
       _=14*(1+physicalH2ComponentNorm f d e)*δ := by dsimp [T]; ring

theorem normalized_physical_graph_rayleigh_error {f h : SpatialL2 2} {E : ℝ}
    (hf : ‖f‖=1) : |(inner ℂ f h).re-E|≤‖h-(E:ℂ) • f‖ := by
  have hid : (inner ℂ f (h-(E:ℂ) • f)).re=(inner ℂ f h).re-E := by
    rw [inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hf]
    simp
  rw [← hid]
  calc _≤‖inner ℂ f (h-(E:ℂ) • f)‖ := Complex.abs_re_le_norm _
       _≤‖f‖*‖h-(E:ℂ) • f‖ := norm_inner_le_norm _ _
       _=‖h-(E:ℂ) • f‖ := by rw [hf,one_mul]

#print axioms physicalCompactNormalizationRadius_half
#print axioms physical_normalized_H2_defect_le
#print axioms normalized_physical_graph_rayleigh_error
end ManyBody.S8