import ManyBody.S8.Internal.SpectatorBootstrap
import CoulombSpinLocallyLipschitz_v1
import ManyBody.S8.Internal.PhysicalPlateauEquation
import LocalWeakGrushinPlateau_v1
import ProductDiagonalWeakH2Compatible_v1
import WeakGrushinPotentialDerivativeTest_v1

/-!
Genuine joint local weak H2 initialization for actual nuclear KS pullbacks.

A compact smooth multiplier rule constructs coordinate diagonal jets of one
inner cutoff representative. The existing spectator bootstrap supplies the
missing TT diagonals from the actual homogeneous weak equation. The frozen
product Fourier/Laplacian theorem then constructs all arbitrary-direction
ordered second weak L2 derivatives, including mixed derivatives.

The scalar result applies to every existing nuclear coefficient patch and
takes only the physical Hamiltonian graph and its continuous representative.
The spin result chooses one locally Lipschitz physical representative before
all spin components, nuclear charts, and compact cutoffs.

The product has its actual product Lebesgue measure and ordinary product
norm. No product-to-Euclidean isometry is assumed. This is qualitative local
H2 existence; no uniform chart constants, H12 estimate, factorial bound,
analyticity, collision covering, or full Rung 2 is concluded.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The actual bounded real multiplier on product-volume L2 classes. -/
def productBoundedRealMul (B : Space κ → ℝ) (hB : MemLp B ⊤ volume)
    (U : Lp ℂ 2 (volume : Measure (Space κ))) :
    Lp ℂ 2 (volume : Measure (Space κ)) :=
  ((Lp.memLp U).smul hB).toLp (fun p => B p • U p)

omit [DecidableEq κ] in
theorem productBoundedRealMul_ae (B : Space κ → ℝ) (hB : MemLp B ⊤ volume)
    (U : Lp ℂ 2 (volume : Measure (Space κ))) :
    productBoundedRealMul B hB U =ᵐ[volume] (fun p => B p • U p) :=
  MemLp.coeFn_toLp _

omit [DecidableEq κ] in
theorem weak_product_bounded_real_mul
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} {v : Space κ}
    (hd : WeakProductL2Directional U d v)
    (B : Space κ → ℝ) (hB : ContDiff ℝ ∞ B)
    (hm : MemLp B ⊤ volume) (hDm : MemLp (fun p => fderiv ℝ B p v) ⊤ volume) :
    WeakProductL2Directional (productBoundedRealMul B hm U)
      (productBoundedRealMul B hm d +
        productBoundedRealMul (fun p => fderiv ℝ B p v) hDm U) v := by
  intro φ hφ hcφ
  have ht := (weakProduct_directional_local_potential_test hd isOpen_univ
    hB.contDiffOn hφ hcφ (Set.subset_univ _)).2.2
  calc
    _ = ∫ p, φ p • (B p • d p + fderiv ℝ B p v • U p) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add (productBoundedRealMul B hm d)
          (productBoundedRealMul (fun p => fderiv ℝ B p v) hDm U),
        productBoundedRealMul_ae B hm d,
        productBoundedRealMul_ae (fun p => fderiv ℝ B p v) hDm U] with p hp hpd hpU
      rw [hp, Pi.add_apply, hpd, hpU]
    _ = -(∫ p, fderiv ℝ φ p v • (B p • U p)) := ht
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [productBoundedRealMul_ae B hm U] with p hp
      rw [hp]

omit [DecidableEq κ] in
theorem weak_product_directional_add
    {U1 U2 d1 d2 : Lp ℂ 2 (volume : Measure (Space κ))} {v : Space κ}
    (h1 : WeakProductL2Directional U1 d1 v)
    (h2 : WeakProductL2Directional U2 d2 v) :
    WeakProductL2Directional (U1 + U2) (d1 + d2) v := by
  intro φ hφ hcφ
  have hi (G : Lp ℂ 2 (volume : Measure (Space κ)))
      {f : Space κ → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) :
      Integrable (fun p => f p • G p) :=
    ((Lp.memLp G).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hf hcf
  have hDφ : Continuous (fun p => fderiv ℝ φ p v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft : (∫ p, φ p • (d1 + d2) p) =
      (∫ p, φ p • d1 p) + ∫ p, φ p • d2 p := by
    calc
      _ = ∫ p, φ p • d1 p + φ p • d2 p := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add d1 d2] with p hp
        rw [hp, Pi.add_apply, smul_add]
      _ = _ := integral_add (hi d1 hφ.continuous hcφ) (hi d2 hφ.continuous hcφ)
  have hright : (∫ p, fderiv ℝ φ p v • (U1 + U2) p) =
      (∫ p, fderiv ℝ φ p v • U1 p) + ∫ p, fderiv ℝ φ p v • U2 p := by
    calc
      _ = ∫ p, fderiv ℝ φ p v • U1 p + fderiv ℝ φ p v • U2 p := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add U1 U2] with p hp
        rw [hp, Pi.add_apply, smul_add]
      _ = _ := integral_add (hi U1 hDφ (hcφ.fderiv_apply ℝ v))
        (hi U2 hDφ (hcφ.fderiv_apply ℝ v))
  rw [hleft, h1 φ hφ hcφ, h2 φ hφ hcφ, hright]
  abel

/-- Existing YY jets and the true spectator differentiated equation supply
all ordered weak H2 jets of a single inner cutoff. -/
theorem local_homogeneous_grushin_joint_cutoff_h2
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω)
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ))}
    {gt : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ))}
    (hgy : ∀ i, WeakProductL2Directional U (gy i) (yDir i))
    (hgt : ∀ j, WeakProductL2Directional U (gt j) (tDir j))
    (hhyy : ∀ i k, WeakProductL2Directional (gy i) (hyy i k) (yDir k))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ∃ W : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ b : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      W =ᵐ[volume] (fun p => χ p • U p) ∧
      (∀ v, WeakProductL2Directional W (a v) v) ∧
      ∀ v w, WeakProductL2Directional (a v) (b v w) w := by
  have hm : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  have hDχ (v : Space κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDm (v : Space κ) : MemLp (fun p => fderiv ℝ χ p v) ⊤ volume :=
    (hDχ v).continuous.memLp_top_of_hasCompactSupport (hcχ.fderiv_apply ℝ v) volume
  have hDDm (v : Space κ) : MemLp (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p v) ⊤ volume :=
    (((hDχ v).fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      ((hcχ.fderiv_apply ℝ v).fderiv_apply ℝ v) volume
  let M := productBoundedRealMul χ hm
  let D (v : Space κ) := productBoundedRealMul (fun p => fderiv ℝ χ p v) (hDm v)
  let DD (v : Space κ) := productBoundedRealMul
    (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p v) (hDDm v)
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_spectator_cutoff_gain hc hΩ hχ hcχ hχΩ
  have hs : ∀ j : κ,
      ∃ Wj : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ ty : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ tt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ tyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        Wj =ᵐ[volume] (fun p => χ p • gt j p) ∧
        (∀ i, WeakProductL2Directional Wj (ty i) (yDir i)) ∧
        (∀ k, WeakProductL2Directional Wj (tt k) (tDir k)) ∧
        ∀ i k, WeakProductL2Directional (ty i) (tyy i k) (yDir k) := by
    intro j
    obtain ⟨Wj, ty, tt, tyy, hWj, _, _, _, hty, htt, htyy⟩ :=
      hgain B U (gt j) j hB (hgt j) hP
    exact ⟨Wj, ty, tt, tyy, hWj, hty, htt, htyy⟩
  choose Wj ty tt tyy hWj hty htt htyy using hs
  let dY (i : Fin 4) := M (gy i) + D (yDir i) U
  let eY (i : Fin 4) := (M (hyy i i) + D (yDir i) (gy i)) +
    (D (yDir i) (gy i) + DD (yDir i) U)
  let dT (j : κ) := M (gt j) + D (tDir j) U
  let eT (j : κ) := tt j j + (D (tDir j) (gt j) + DD (tDir j) U)
  have hdY : ∀ i, WeakProductL2Directional (M U) (dY i) (yDir i) :=
    fun i => weak_product_bounded_real_mul (hgy i) χ hχ hm (hDm (yDir i))
  have heY : ∀ i, WeakProductL2Directional (dY i) (eY i) (yDir i) := by
    intro i
    exact weak_product_directional_add
      (weak_product_bounded_real_mul (hhyy i i) χ hχ hm (hDm (yDir i)))
      (weak_product_bounded_real_mul (hgy i) _ (hDχ (yDir i)) (hDm (yDir i)) (hDDm (yDir i)))
  have hdT : ∀ j, WeakProductL2Directional (M U) (dT j) (tDir j) :=
    fun j => weak_product_bounded_real_mul (hgt j) χ hχ hm (hDm (tDir j))
  have heT : ∀ j, WeakProductL2Directional (dT j) (eT j) (tDir j) := by
    intro j
    have hMj : M (gt j) = Wj j := Lp.ext ((productBoundedRealMul_ae χ hm (gt j)).trans (hWj j).symm)
    have hdiag : WeakProductL2Directional (M (gt j)) (tt j j) (tDir j) := by
      rw [hMj]
      exact htt j j
    exact weak_product_directional_add hdiag
      (weak_product_bounded_real_mul (hgt j) _ (hDχ (tDir j)) (hDm (tDir j)) (hDDm (tDir j)))
  have hBasisY : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → KSSpace) = oscillatorBasis :=
    funext (EuclideanSpace.basisFun_apply (Fin 4) ℝ)
  have hBasisT : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis :=
    funext (EuclideanSpace.basisFun_apply κ ℝ)
  obtain ⟨a, b, ha, hb, _, _, _, _⟩ :=
    product_weakH2_of_factor_diagonal_jets (EuclideanSpace.basisFun (Fin 4) ℝ)
      (EuclideanSpace.basisFun κ ℝ) dY eY dT eT
      (by simpa only [hBasisY, yDir] using hdY)
      (by simpa only [hBasisY, yDir] using heY)
      (by simpa only [hBasisT, tDir] using hdT)
      (by simpa only [hBasisT, tDir] using heT)
  exact ⟨M U, a, b, productBoundedRealMul_ae χ hm U, ha, hb⟩

#print axioms productBoundedRealMul_ae
#print axioms weak_product_bounded_real_mul
#print axioms weak_product_directional_add
#print axioms local_homogeneous_grushin_joint_cutoff_h2

/-- A fixed continuous physical scalar representative has genuine local weak
H2 in every actual nuclear KS coefficient patch, including the selected nucleus. -/
theorem scalar_coulomb_nuclear_KS_local_weakH2 {N : ℕ} (i : Fin N) (Z E : ℝ)
    {f : SpatialL2 N} (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {g : Configuration N → ℂ} (hg : Continuous g)
    (hfg : (f : Configuration N → ℂ) =ᵐ[volume] g) :
    ProductLocalWeakH2On (g ∘ nuclearKSLift i) (nuclearKSCoefficientPatch i) := by
  intro χ hχ hcχ hχpatch
  obtain ⟨χouter, houter, hcouter, hsouter, V, hV, hχV, hVpatch, houter1⟩ :=
    exists_outer_plateau hcχ (nuclearKSCoefficientPatch_isOpen i) hχpatch
  obtain ⟨K, C, hK, houterK, hKpatch, hC, hinit⟩ :=
    scalar_coulomb_nuclear_KS_one_step i Z E houter hcouter hsouter
  obtain ⟨U, gy, gt, hyy, hU, _, _, _, hgy, hgt, hhyy⟩ := hinit hgraph hg hfg
  have hP := scalar_nuclear_output_on_plateau i Z E hgraph hg hfg hU
    hVpatch (Set.Subset.refl _) houter1
  have hB : ContDiffOn ℝ ∞ (nuclearKSPotential i Z E) V := by
    intro p hp
    exact (nuclearKSPotential_contDiffAt i Z E (hVpatch hp)).contDiffWithinAt
  obtain ⟨W, a, b, hW, ha, hb⟩ := local_homogeneous_grushin_joint_cutoff_h2
    (by norm_num : (0 : ℝ) < 4) hV hB hχ hcχ hχV hgy hgt hhyy hP
  refine ⟨W, a, ?_, ha, fun v w => ⟨b v w, hb v w⟩⟩
  filter_upwards [hW, hU] with p hp hu
  rw [hp]
  by_cases ht : p ∈ tsupport χ
  · rw [hu, houter1 p (hχV ht), one_smul]
    rfl
  · simp only [image_eq_zero_of_notMem_tsupport ht, zero_smul]

/-- One physical spin representative works simultaneously for every nuclear
KS chart and every compact smooth cutoff in its coefficient patch. -/
theorem coulomb_spin_nuclear_KS_local_weakH2 {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {ψ : SpinSpace N} (hgraph : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration N → Configuration N → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
      (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
      (∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖ ^ 2) ≤
        coulombMoserBoundCoefficient N Z E * ‖ψ‖) ∧
      ∀ σ : SpinConfiguration N, ∀ i : Fin N,
        ProductLocalWeakH2On (u σ ∘ nuclearKSLift i) (nuclearKSCoefficientPatch i) := by
  obtain ⟨u, hu, hue, hperm, hbound⟩ := coulomb_spin_locally_lipschitz_representative hN hgraph
  refine ⟨u, hu, hue, hperm, hbound, ?_⟩
  intro σ i
  have he : (ψ σ : Configuration N → ℂ) =ᵐ[volume] u σ := by
    filter_upwards [hue] with x hx
    exact hx σ
  exact scalar_coulomb_nuclear_KS_local_weakH2 i Z E (hgraph.2.2 σ) (hu σ).continuous he

#print axioms scalar_coulomb_nuclear_KS_local_weakH2
#print axioms coulomb_spin_nuclear_KS_local_weakH2

end ManyBody.S8

