import ManyBody.S8.Internal.HigherDirectionalRegularity
import ProductCompactCutoffWeakJet_v1

/-!
# Full joint local weak H³ for actual nuclear KS pullbacks

The actual Grushin equation gives joint H² for every genuine first derivative.
Cutoff product rules then assemble all ordered arbitrary-direction third weak
derivatives of the same cutoff.  The scalar and spin wrappers use only the
physical graph and a single physical representative, on every nuclear
coefficient patch.  No third derivatives or differentiated equations are input.
No H¹², uniform derivative budget, or analyticity is asserted here.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- All ordered first, second, and third directional weak L² derivatives of
every compact smooth cutoff of the same raw representative. -/
def ProductLocalWeakH3On (f : Space κ → ℂ) (Ω : Set (Space κ)) : Prop :=
  ∀ χ : Space κ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ e : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ h : Space κ → Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, WeakProductL2Directional U (d v) v) ∧
      (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
      ∀ v w t, WeakProductL2Directional (e v w) (h v w t) t

omit [DecidableEq κ] in
theorem product_local_weakH3_of_first_local_weakH2
    {Ω : Set (Space κ)}
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {b : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (ha : ∀ v, WeakProductL2Directional U (a v) v)
    (hb : ∀ v w, WeakProductL2Directional (a v) (b v w) w)
    (hfirst : ∀ v, ProductLocalWeakH2On (a v : Space κ → ℂ) Ω) :
    ProductLocalWeakH3On (U : Space κ → ℂ) Ω := by
  intro χ hχ hcχ hχΩ
  have hm : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  have hDχ (v : Space κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDm (v : Space κ) : MemLp (fun p => fderiv ℝ χ p v) ⊤ volume :=
    (hDχ v).continuous.memLp_top_of_hasCompactSupport (hcχ.fderiv_apply ℝ v) volume
  let M := productBoundedRealMul χ hm
  let D (v : Space κ) := productBoundedRealMul (fun p => fderiv ℝ χ p v) (hDm v)
  have hs : ∀ v : Space κ,
      ∃ W1 W2 : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ a1 a2 : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ b1 b2 : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
        M (a v) = W1 ∧ D v U = W2 ∧
        (∀ w, WeakProductL2Directional W1 (a1 w) w) ∧
        (∀ w, WeakProductL2Directional W2 (a2 w) w) ∧
        (∀ w t, WeakProductL2Directional (a1 w) (b1 w t) t) ∧
        ∀ w t, WeakProductL2Directional (a2 w) (b2 w t) t := by
    intro v
    obtain ⟨W1, a1, hW1, ha1, hb1⟩ := hfirst v χ hχ hcχ hχΩ
    choose b1 hb1 using hb1
    obtain ⟨W2, a2, b2, ha2, hb2, hW2, _, _⟩ :=
      product_compact_cutoff_weak_jet (hDχ v) (hcχ.fderiv_apply ℝ v) ha hb
    have hM : M (a v) = W1 :=
      Lp.ext ((productBoundedRealMul_ae χ hm (a v)).trans hW1.symm)
    have hD : D v U = W2 := Lp.ext
      ((productBoundedRealMul_ae (fun p => fderiv ℝ χ p v) (hDm v) U).trans hW2.symm)
    exact ⟨W1, W2, a1, a2, b1, b2, hM, hD, ha1, ha2, hb1, hb2⟩
  choose W1 W2 a1 a2 b1 b2 hM hD ha1 ha2 hb1 hb2 using hs
  let d (v : Space κ) := W1 v + W2 v
  let e (v w : Space κ) := a1 v w + a2 v w
  let h (v w t : Space κ) := b1 v w t + b2 v w t
  refine ⟨M U, d, e, h, productBoundedRealMul_ae χ hm U, ?_, ?_, ?_⟩
  · intro v
    have hmul := weak_product_bounded_real_mul (ha v) χ hχ hm (hDm v)
    change WeakProductL2Directional (M U) (M (a v) + D v U) v at hmul
    rw [hM v, hD v] at hmul
    exact hmul
  · intro v w
    exact weak_product_directional_add (ha1 v w) (ha2 v w)
  · intro v w t
    exact weak_product_directional_add (hb1 v w t) (hb2 v w t)

theorem local_homogeneous_grushin_joint_h3
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {b : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (ha : ∀ v, WeakProductL2Directional U (a v) v)
    (hb : ∀ v w, WeakProductL2Directional (a v) (b v w) w)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ProductLocalWeakH3On (U : Space κ → ℂ) Ω :=
  product_local_weakH3_of_first_local_weakH2 ha hb
    (homogeneous_grushin_first_direction_local_h2 hc hΩ hB ha hb hP)

/-- The actual scalar Coulomb graph yields full joint local weak H³ on every
nuclear coefficient patch, including the selected collision. -/
theorem scalar_coulomb_nuclear_KS_local_weakH3 {N : ℕ} (i : Fin N) (Z E : ℝ)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) :
    ProductLocalWeakH3On (g ∘ nuclearKSLift i) (nuclearKSCoefficientPatch i) := by
  intro χ hχ hcχ hχpatch
  obtain ⟨χouter, houter, hcouter, hsouter, V, hV, hχV, hVpatch, houter1⟩ :=
    exists_outer_plateau hcχ (nuclearKSCoefficientPatch_isOpen i) hχpatch
  obtain ⟨U, a, hU, ha, hb⟩ :=
    scalar_coulomb_nuclear_KS_local_weakH2 i Z E hgraph hg hfg
      χouter houter hcouter hsouter
  choose b hb using hb
  have hP := scalar_nuclear_output_on_plateau i Z E hgraph hg hfg hU
    hVpatch (Set.Subset.refl _) houter1
  have hB : ContDiffOn ℝ ∞ (nuclearKSPotential i Z E) V := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt i Z E (hVpatch hp)).contDiffWithinAt
  obtain ⟨W, d, e, h, hW, hd, he, hh⟩ :=
    local_homogeneous_grushin_joint_h3 (by norm_num : (0 : ℝ) < 4) hV hB ha hb hP
      χ hχ hcχ hχV
  refine ⟨W, d, e, h, ?_, hd, he, hh⟩
  filter_upwards [hW, hU] with p hp hu
  rw [hp]
  by_cases ht : p ∈ tsupport χ
  · rw [hu, houter1 p (hχV ht), one_smul]
  · simp only [image_eq_zero_of_notMem_tsupport ht, zero_smul]

/-- One physical representative works for all spin channels and nuclear charts,
before any choice of cutoff or weak derivative witnesses. -/
theorem coulomb_spin_nuclear_KS_local_weakH3 {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {ψ : SpinSpace N} (hgraph : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration N → Configuration N → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
      (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖ ^ 2) ≤
        coulombMoserBoundCoefficient N Z E * ‖ψ‖) ∧
      ∀ σ : SpinConfiguration N, ∀ i : Fin N,
        ProductLocalWeakH3On (u σ ∘ nuclearKSLift i) (nuclearKSCoefficientPatch i) := by
  obtain ⟨u, hu, hue, hperm, hbound⟩ := coulomb_spin_locally_lipschitz_representative hN hgraph
  refine ⟨u, hu, hue, hperm, hbound, ?_⟩
  intro σ i
  have he : (ψ σ : Configuration N → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  exact scalar_coulomb_nuclear_KS_local_weakH3 i Z E (hgraph.2.2 σ) (hu σ).continuous he

#print axioms product_local_weakH3_of_first_local_weakH2
#print axioms local_homogeneous_grushin_joint_h3
#print axioms scalar_coulomb_nuclear_KS_local_weakH3
#print axioms coulomb_spin_nuclear_KS_local_weakH3
end ManyBody.S8

