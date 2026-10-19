import WeakGrushinRawLocalCutoff_v1
import WeakGrushinMixedMultiIndexEquation_v1

/-! Genuine compact H2 cutoff and actual global principal output for every
available mixed derivative of a raw weak solution. The only PDE premise is the
original zero-order equation. Positive-order equations and cutoff identities
are derived from actual weak coordinate chains. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem mixed_family_local_weakH2
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω) {m : ℕ} {W : ℝ}
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hF : ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m+2 → RegionL2Budget (F α β) Ω W)
    (hY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < m+2 →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < m+2 →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hab : (∑ i,α i)+(∑ j,β j) ≤ m) :
    ProductLocalWeakH2On (F α β) Ω := by
  have hys (i : Fin 4) : (∑ k : Fin 4,((α+Pi.single i 1 : Fin 4 → ℕ) k))+(∑ j,β j) < m+2 := by
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    omega
  have hts (j : Fin 3) : (∑ i,α i)+(∑ k : Fin 3,((β+Pi.single j 1 : Fin 3 → ℕ) k)) < m+2 := by
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    omega
  apply product_local_weakH2_of_diagonal_jets
    (EuclideanSpace.basisFun (Fin 4) ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ) hΩ (F α β)
    (fun i => F (α+Pi.single i 1) β)
    (fun i => F ((α+Pi.single i 1)+Pi.single i 1) β)
    (fun j => F α (β+Pi.single j 1))
    (fun j => F α ((β+Pi.single j 1)+Pi.single j 1)) (hF α β (by omega)).local
  · intro i
    simpa only [yDir,EuclideanSpace.basisFun_apply,oscillatorBasis] using hY α β i (by omega)
  · intro i
    simpa only [yDir,EuclideanSpace.basisFun_apply,oscillatorBasis] using hY _ β i (hys i)
  · intro j
    simpa only [tDir,EuclideanSpace.basisFun_apply,oscillatorBasis] using hT α β j (by omega)
  · intro j
    simpa only [tDir,EuclideanSpace.basisFun_apply,oscillatorBasis] using hT α _ j (hts j)

theorem weak_grushin_mixed_cutoff_equation
    (c : ℝ) {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω) {m : ℕ} {W : ℝ}
    (F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hF : ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m+2 → RegionL2Budget (F α β) Ω W)
    (hY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < m+2 →
      ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < m+2 →
      ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F 0 0 p) = ∫ p,φ p • s p)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hab : (∑ i,α i)+(∑ j,β j) ≤ m)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
    ∃ a : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))), ∃ b : Jet (Fin 3),
      U =ᵐ[volume] (fun p => χ p • F α β p) ∧
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0) ∧
      H =ᵐ[volume] principal c b ∧
      H =ᵐ[volume] (fun p => χ p • (mixedMultiIndexGrushinSource c B F s α β p-B p • F α β p) -
        rawGrushinCutoffError c χ (F α β) (fun i => F (α+Pi.single i 1) β)
          (fun j => F α (β+Pi.single j 1)) p) ∧
      (∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) := by
  obtain ⟨hL,hEq⟩ := weak_grushin_mixed_multiIndex_equations c hΩ hB hs F hF hY hT hP α β hab
  have hb : (fun j => (EuclideanSpace.basisFun (Fin 3) ℝ) j) = oscillatorBasis := by
    funext j; exact EuclideanSpace.basisFun_apply (Fin 3) ℝ j
  obtain ⟨hR,hPr⟩ := grushin_local_potential_reduction c (EuclideanSpace.basisFun (Fin 3) ℝ)
    hB.continuousOn (F α β) (mixedMultiIndexGrushinSource c B F s α β)
    (hF α β (by omega)).local hL (by simpa only [hb] using fun φ hφ hc hs => (hEq φ hφ hc hs).2.2)
  apply raw_local_weakH2_grushin_cutoff c hΩ hχ hcχ hsχ (F α β) _
    (mixed_family_local_weakH2 hΩ F hF hY hT α β hab) hR
    (fun i => F (α+Pi.single i 1) β) (fun j => F α (β+Pi.single j 1))
    (fun i => hY α β i (by omega)) (fun j => hT α β j (by omega))
  simpa only [hb] using hPr

end TheoremT.Continuum.WeakGrushin
