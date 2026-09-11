import GraphAssembly_v2

/-! Linearity for the genuine distributional H2 domain. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem test_integrable {N : ℕ} (f : SpatialL2 N) {φ : Configuration N → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x • f x) :=
  ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    hφ hc

theorem integral_test_add {N : ℕ} (f g : SpatialL2 N) {φ : Configuration N → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x • (f + g) x) = (∫ x, φ x • f x) + (∫ x, φ x • g x) := by
  calc
    _ = ∫ x, φ x • f x + φ x • g x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with x hx
      simp only [hx, Pi.add_apply, smul_add]
    _ = _ := integral_add (test_integrable f hφ hc) (test_integrable g hφ hc)

theorem integral_test_smul {N : ℕ} (c : ℂ) (f : SpatialL2 N)
    (φ : Configuration N → ℝ) :
    (∫ x, φ x • (c • f) x) = c • (∫ x, φ x • f x) := by
  calc
    _ = ∫ x, c • (φ x • f x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with x hx
      rw [hx]
      exact smul_comm (φ x) c (f x)
    _ = _ := integral_smul c _

theorem weakPartial_zero {N : ℕ} (k : Coordinate N) :
    WeakPartial (0 : SpatialL2 N) 0 k := by
  intro φ hφ hc
  simp

theorem weakPartial_add {N : ℕ} {f g df dg : SpatialL2 N} {k : Coordinate N}
    (hf : WeakPartial f df k) (hg : WeakPartial g dg k) :
    WeakPartial (f + g) (df + dg) k := by
  intro φ hφ hc
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [integral_test_add df dg hφ.continuous hc,
    integral_test_add f g hdφ (hc.fderiv_apply ℝ (coordinateVector k)), hf φ hφ hc, hg φ hφ hc]
  abel

theorem weakPartial_smul {N : ℕ} (c : ℂ) {f df : SpatialL2 N} {k : Coordinate N}
    (hf : WeakPartial f df k) : WeakPartial (c • f) (c • df) k := by
  intro φ hφ hc
  rw [integral_test_smul, integral_test_smul, hf φ hφ hc, smul_neg]

theorem hasH2_zero (N : ℕ) : HasH2 (0 : SpatialL2 N) := by
  exact ⟨fun _ => 0, weakPartial_zero, fun _ l => ⟨0, weakPartial_zero l⟩⟩

theorem HasH2.add {N : ℕ} {f g : SpatialL2 N} (hf : HasH2 f) (hg : HasH2 g) :
    HasH2 (f + g) := by
  obtain ⟨df, hf, hdf⟩ := hf
  obtain ⟨dg, hg, hdg⟩ := hg
  refine ⟨fun k => df k + dg k, fun k => weakPartial_add (hf k) (hg k), ?_⟩
  intro k l
  obtain ⟨ef, hef⟩ := hdf k l
  obtain ⟨eg, heg⟩ := hdg k l
  exact ⟨ef + eg, weakPartial_add hef heg⟩

theorem HasH2.smul {N : ℕ} (c : ℂ) {f : SpatialL2 N} (hf : HasH2 f) :
    HasH2 (c • f) := by
  obtain ⟨df, hf, hdf⟩ := hf
  refine ⟨fun k => c • df k, fun k => weakPartial_smul c (hf k), ?_⟩
  intro k l
  obtain ⟨e, he⟩ := hdf k l
  exact ⟨c • e, weakPartial_smul c he⟩

/-- The independently specified weak H2 functions form a genuine submodule. -/
def spatialH2Submodule (N : ℕ) : Submodule ℂ (SpatialL2 N) where
  carrier := {f | HasH2 f}
  zero_mem' := hasH2_zero N
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

/-- Exactly the previously advertised H2 fermionic domain, with its linear structure. -/
def targetDomainSubmodule (N : ℕ) : Submodule ℂ (SpinSpace N) where
  carrier := targetDomain N
  zero_mem' := ⟨(fermionicSubspace N).zero_mem, fun _ => hasH2_zero N⟩
  add_mem' := by
    rintro f g ⟨hf, hf2⟩ ⟨hg, hg2⟩
    exact ⟨(fermionicSubspace N).add_mem hf hg, fun σ => (hf2 σ).add (hg2 σ)⟩
  smul_mem' := by
    rintro c f ⟨hf, hf2⟩
    exact ⟨(fermionicSubspace N).smul_mem c hf, fun σ => (hf2 σ).smul c⟩

theorem targetDomainSubmodule_carrier (N : ℕ) :
    (targetDomainSubmodule N : Set (SpinSpace N)) = targetDomain N := rfl

#print axioms weakPartial_zero
#print axioms weakPartial_add
#print axioms weakPartial_smul
#print axioms HasH2.add
#print axioms HasH2.smul
#print axioms targetDomainSubmodule
#print axioms targetDomainSubmodule_carrier
end TheoremT.Continuum
