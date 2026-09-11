import GrushinSpectatorRegularizedH2_v1
import PartialMollifierUniformWeakEquation_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

theorem partialMollifyLp_local_h2_of_weak_equation
    (c : ℝ) (b : OrthonormalBasis κ ℝ T) (n : ℕ)
    (G h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    {U : Set (KSSpace × T)} (hU : IsOpen U)
    (hP : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • partialMollifyLp n G p) =
        ∫ p, φ p • partialMollifyLp n h p) :
    ProductLocalWeakH2On (partialMollifyLp n G : KSSpace × T → ℂ) U := by
  let J := partialSpectatorJetLp (GenericMollifier.mollifierKernel_contDiff (E := T) n)
    (GenericMollifier.mollifierKernel_hasCompactSupport n) (Lp.memLp G)
  apply grushin_local_h2_of_spectator_second_jets c b (partialMollifyLp n G) (partialMollifyLp n h)
    (fun j => J [b j]) (fun j => J [b j,b j]) _ _ hU hP
  · intro j
    rw [partialMollifyLp_eq_jet_nil]
    exact partialSpectatorJetLp_weak_derivative (GenericMollifier.mollifierKernel_contDiff n)
      (GenericMollifier.mollifierKernel_hasCompactSupport n) (Lp.memLp G) [] (b j)
  · intro j
    exact partialSpectatorJetLp_weak_derivative (GenericMollifier.mollifierKernel_contDiff n)
      (GenericMollifier.mollifierKernel_hasCompactSupport n) (Lp.memLp G) [b j] (b j)

theorem partialMollifyLp_local_h2_and_weak_equation_eventually
    (c : ℝ) (b : OrthonormalBasis κ ℝ T) {Ω C U : Set (KSSpace × T)}
    (hΩ : IsOpen Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω) (hU : IsOpen U) (hUC : U ⊆ C)
    (G h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • G p) = ∫ p, φ p • h p) :
    ∀ᶠ n : ℕ in atTop,
      ProductLocalWeakH2On (partialMollifyLp n G : KSSpace × T → ℂ) U ∧
      ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ p, splitGrushin c b (fun _ => 0) φ p • partialMollifyLp n G p) =
          ∫ p, φ p • partialMollifyLp n h p := by
  filter_upwards [partialMollifyLp_splitGrushin_weak_uniformly_eventually c b hΩ hC hCΩ G h hweak]
    with n hn
  have hP : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • partialMollifyLp n G p) =
        ∫ p, φ p • partialMollifyLp n h p :=
    fun φ hφ hcφ hsφ => hn φ hφ hcφ (hsφ.trans hUC)
  exact ⟨partialMollifyLp_local_h2_of_weak_equation c b n G h hU hP,hP⟩

theorem partialMollifyLp_local_h2_eventually_of_compact_closure
    (c : ℝ) (b : OrthonormalBasis κ ℝ T) {Ω U : Set (KSSpace × T)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hC : IsCompact (closure U)) (hCΩ : closure U ⊆ Ω)
    (G h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • G p) = ∫ p, φ p • h p) :
    ∀ᶠ n : ℕ in atTop, ProductLocalWeakH2On (partialMollifyLp n G : KSSpace × T → ℂ) U := by
  filter_upwards [partialMollifyLp_local_h2_and_weak_equation_eventually c b
    hΩ hC hCΩ hU subset_closure G h hweak] with n hn
  exact hn.1

#print axioms partialMollifyLp_local_h2_of_weak_equation
#print axioms partialMollifyLp_local_h2_and_weak_equation_eventually
#print axioms partialMollifyLp_local_h2_eventually_of_compact_closure
end TheoremT.Continuum
