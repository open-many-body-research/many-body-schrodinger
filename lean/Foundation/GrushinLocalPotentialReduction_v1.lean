import GrushinLocalPotentialL2_v1
import GrushinLocalL2Neighborhood_v1

/-! Zeroth-order potential reduction for the actual weak Grushin operator.
The coefficient is continuous only on the test region, and both input functions
are merely locally L2 there. Every test integral is proved integrable. No global
L2 bound on B*f, differentiation of B, or commutation with mollification is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

omit [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T] in
theorem splitGrushin_potential_smul (c : ℝ) (v : κ → T)
    (B φ : KSSpace × T → ℝ) (f : KSSpace × T → ℂ) (p : KSSpace × T) :
    splitGrushin c v B φ p • f p =
      splitGrushin c v (fun _ => 0) φ p • f p + φ p • (B p • f p) := by
  have hp : splitGrushin c v B φ p =
      splitGrushin c v (fun _ => 0) φ p + φ p * B p := by
    simp only [splitGrushin, zero_mul, add_zero]
    ring
  rw [hp, add_smul, mul_smul]

theorem grushin_local_potential_test_integrable
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    {Ω : Set (KSSpace × T)} {B : KSSpace × T → ℝ}
    (hB : ContinuousOn B Ω) (f g : KSSpace × T → ℂ)
    (hf : ProductLocallyL2On f Ω) (hg : ProductLocallyL2On g Ω)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    Integrable (fun p => splitGrushin c b B φ p • f p) ∧
      Integrable (fun p => splitGrushin c b (fun _ => 0) φ p • f p) ∧
      Integrable (fun p => φ p • g p) ∧
      Integrable (fun p => φ p • (B p • f p)) ∧
      Integrable (fun p => φ p • (g p - B p • f p)) := by
  have hbf := product_locallyL2On_smul_of_continuousOn hB hf
  have hbase := grushin_local_l2_test_integrable c b f g hf hg hφ hcφ hsφ
  have hpot := product_locallyL2_compact_smul_integrable
    (fun p => B p • f p) hbf hφ.continuous hcφ hsφ
  have hfull : Integrable (fun p => splitGrushin c b B φ p • f p) := by
    apply (hbase.1.add hpot).congr
    exact Filter.Eventually.of_forall (fun p => (splitGrushin_potential_smul c b B φ f p).symm)
  have hsub : Integrable (fun p => φ p • (g p - B p • f p)) := by
    apply (hbase.2.sub hpot).congr
    exact Filter.Eventually.of_forall (fun p => (smul_sub (φ p) (g p) (B p • f p)).symm)
  exact ⟨hfull, hbase.1, hbase.2, hpot, hsub⟩

theorem grushin_local_potential_test_iff
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    {Ω : Set (KSSpace × T)} {B : KSSpace × T → ℝ}
    (hB : ContinuousOn B Ω) (f g : KSSpace × T → ℂ)
    (hf : ProductLocallyL2On f Ω) (hg : ProductLocallyL2On g Ω)
    {φ : KSSpace × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    ((∫ p, splitGrushin c b B φ p • f p) = ∫ p, φ p • g p) ↔
      ((∫ p, splitGrushin c b (fun _ => 0) φ p • f p) =
        ∫ p, φ p • (g p - B p • f p)) := by
  obtain ⟨_, hi, hgtest, hpot, _⟩ :=
    grushin_local_potential_test_integrable c b hB f g hf hg hφ hcφ hsφ
  have hleft : (∫ p, splitGrushin c b B φ p • f p) =
      (∫ p, splitGrushin c b (fun _ => 0) φ p • f p) +
        ∫ p, φ p • (B p • f p) := by
    calc
      _ = ∫ p, splitGrushin c b (fun _ => 0) φ p • f p + φ p • (B p • f p) :=
        integral_congr_ae (Filter.Eventually.of_forall (splitGrushin_potential_smul c b B φ f))
      _ = _ := integral_add hi hpot
  have hright : (∫ p, φ p • (g p - B p • f p)) =
      (∫ p, φ p • g p) - ∫ p, φ p • (B p • f p) := by
    simp_rw [smul_sub]
    exact integral_sub hgtest hpot
  rw [hleft, hright]
  exact eq_sub_iff_add_eq.symm

theorem grushin_local_potential_reduction_iff
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    {Ω : Set (KSSpace × T)} {B : KSSpace × T → ℝ}
    (hB : ContinuousOn B Ω) (f g : KSSpace × T → ℂ)
    (hf : ProductLocallyL2On f Ω) (hg : ProductLocallyL2On g Ω) :
    (∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b B φ p • f p) = ∫ p, φ p • g p) ↔
    (∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • f p) =
        ∫ p, φ p • (g p - B p • f p)) := by
  constructor
  · intro h φ hφ hcφ hsφ
    exact (grushin_local_potential_test_iff c b hB f g hf hg hφ hcφ hsφ).mp
      (h φ hφ hcφ hsφ)
  · intro h φ hφ hcφ hsφ
    exact (grushin_local_potential_test_iff c b hB f g hf hg hφ hcφ hsφ).mpr
      (h φ hφ hcφ hsφ)

theorem grushin_local_potential_reduction
    (c : ℝ) (b : OrthonormalBasis κ ℝ T)
    {Ω : Set (KSSpace × T)} {B : KSSpace × T → ℝ}
    (hB : ContinuousOn B Ω) (f g : KSSpace × T → ℂ)
    (hf : ProductLocallyL2On f Ω) (hg : ProductLocallyL2On g Ω)
    (h : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b B φ p • f p) = ∫ p, φ p • g p) :
    ProductLocallyL2On (fun p => g p - B p • f p) Ω ∧
      (∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c b (fun _ => 0) φ p • f p) =
          ∫ p, φ p • (g p - B p • f p)) :=
  ⟨product_locallyL2On_sub_smul hB hf hg,
    (grushin_local_potential_reduction_iff c b hB f g hf hg).mp h⟩

#print axioms grushin_local_potential_test_integrable
#print axioms grushin_local_potential_reduction_iff
#print axioms grushin_local_potential_reduction
end TheoremT.Continuum
