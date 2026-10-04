import WeakFactorialLocalOuterBound_v1
import GrushinFactorialLocalProfile_v1
import CompactWeakFactorialOuterBound_v1

/-! The actual inner local norm of a shifted weak derivative family is
controlled by the global cutoff norm on a plateau. This uses only genuine
weak chains and the actual equality U=eta*F(a,b); no global raw Leibniz
family or inner-norm estimate is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_local_outer_le_plateau_global
    (U : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional U (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {Ω V : Set (Space (Fin 3))} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (F : FactorialRawJetFamily) (a : Fin 4 → ℕ) (b : Fin 3 → ℕ)
    (hFY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < 2 →
      ProductLocalWeakDirectional Ω (F (a+α) (b+β))
        (F ((a+α)+Pi.single i 1) (b+β)) (yDir i))
    (hFT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < 2 →
      ProductLocalWeakDirectional Ω (F (a+α) (b+β))
        (F (a+α) ((b+β)+Pi.single j 1)) (tDir j))
    {η : Space (Fin 3) → ℝ}
    (hU : (U : Space (Fin 3) → ℂ) =ᵐ[volume] (fun p => η p • F a b p))
    (hη : ∀ p ∈ V, η p = 1)
    (W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (hW : FactorialOuterL2Rep
      (fun α β => (weakFactorialJet U d e α β : Space (Fin 3) → ℂ)) W) :
    (∀ q ∈ factorialOuterIndices,
      MemLp (factorialShiftedWeightedField F a b q) 2 (volume.restrict V)) ∧
      factorialLocalOuterNorm F V a b ≤ factorialOuterNorm W := by
  let G := fun α β => F (a+α) (b+β)
  have h0 : ∀ᵐ p ∂volume, p ∈ V → U p = G 0 0 p := by
    filter_upwards [hU] with p hp hin
    simpa only [G,add_zero,hη p hin,one_smul] using hp
  have hY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < 2 →
      ProductLocalWeakDirectional V (G α β) (G (α+Pi.single i 1) β) (yDir i) := by
    intro α β i hab
    simpa only [G,add_assoc] using (hFY α β i hab).mono hVΩ
  have hT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < 2 →
      ProductLocalWeakDirectional V (G α β) (G α (β+Pi.single j 1)) (tDir j) := by
    intro α β j hab
    simpa only [G,add_assoc] using (hFT α β j hab).mono hVΩ
  unfold factorialLocalOuterNorm factorialShiftedWeightedField
  simpa only [G] using
    local_factorial_outer_le_global_weak_representatives U d e hd he hV G h0 hY hT W hW

theorem factorial_local_outer_le_plateau_grushin_output
    {c : ℝ} (hc : 0 < c)
    {U H : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional U (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → U p = 0)
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p)
    (i₀ : Fin 4) {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i₀| ≤ R)
    (S : ℝ) (hS : 1 ≤ S) (hSK : ∀ p ∈ K, ‖p.1‖ ≤ S)
    {Ω V : Set (Space (Fin 3))} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (F : FactorialRawJetFamily) (a : Fin 4 → ℕ) (b : Fin 3 → ℕ)
    (hFY : ∀ α β i, (∑ k,α k)+(∑ j,β j) < 2 →
      ProductLocalWeakDirectional Ω (F (a+α) (b+β))
        (F ((a+α)+Pi.single i 1) (b+β)) (yDir i))
    (hFT : ∀ α β j, (∑ i,α i)+(∑ k,β k) < 2 →
      ProductLocalWeakDirectional Ω (F (a+α) (b+β))
        (F (a+α) ((b+β)+Pi.single j 1)) (tDir j))
    {η : Space (Fin 3) → ℝ}
    (hU : (U : Space (Fin 3) → ℂ) =ᵐ[volume] (fun p => η p • F a b p))
    (hη : ∀ p ∈ V, η p = 1) :
    (∀ q ∈ factorialOuterIndices,
      MemLp (factorialShiftedWeightedField F a b q) 2 (volume.restrict V)) ∧
      factorialLocalOuterNorm F V a b ≤ 498*S^2*(4*R^2+2*R+2+2/c)*‖H‖ := by
  obtain ⟨W,hW,hWn⟩ := compact_weak_factorial_outer_graph_bound hc d e hd he hK hs hP
    i₀ hR hslab S hS hSK
  obtain ⟨hfin,hbound⟩ := factorial_local_outer_le_plateau_global U d e hd he hV hVΩ
    F a b hFY hFT hU hη W hW
  exact ⟨hfin,hbound.trans hWn⟩

end TheoremT.Continuum.WeakGrushin
