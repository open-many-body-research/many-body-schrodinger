import MixedTriangularPotentialStep_v1
import MixedYIterationBudgetSequence_v1

/-! Actual finite Y recovery from the original weak potential equation and
an existing genuine triangular reserve. Each step derives its differentiated
PDE and new weak witnesses. The total derivative reserve m remains fixed,
source/coefficient orders through m-2 suffice, and the region shrinks only
by the supplied actual cutoff stages. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem mixedTriangularState_potential_iterate
    (c : ℝ) (n : ℕ) (Ω V : ℕ → Set (Space κ)) (χ η : ℕ → Space κ → ℝ)
    (M A L D Q : ℕ → ℝ)
    (hGeom : ∀ k, k < n → SpectatorStepGeometry 0 (Ω k) (Ω (k+1)) (V k)
      (χ k) (η k) (M k) (A k) (L k) (D k) (Q k))
    (hO : ∀ k, k < n → IsOpen (Ω (k+1)))
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B (Ω 0))
    {r m : ℕ} (hr : 1 ≤ r) (K0 Q0 H0 Winit : ℝ) (hWinit : 0 ≤ Winit)
    (f : Space κ → ℂ) (S : List (Fin 4) → List κ → Space κ → ℂ)
    (hf : MixedTriangularState (Ω 0) f r m Winit)
    (hS : ∀ a b, a.length+b.length+2 ≤ m → RegionL2Budget (S a b) (Ω 0) H0)
    (hSY : ∀ a b i, a.length+b.length+2 < m →
      ProductLocalWeakDirectional (Ω 0) (S a b) (S (i :: a) b) (yDir i))
    (hST : ∀ b j, b.length+2 < m →
      ProductLocalWeakDirectional (Ω 0) (S [] b) (S [] (j :: b)) (tDir j))
    (hCoeff : ∀ a b, a.length+b.length+2 ≤ m → ∀ p ∈ Ω 0,
      |directionalWordDeriv yDir (spectatorWordDeriv B b) a p| ≤ K0)
    (hQuad : ∀ a, a.length+2 ≤ m → ∀ p ∈ Ω 0,
      |directionalWordDeriv yDir (fun p : Space κ => ‖p.1‖^2) a p| ≤ Q0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • S [] [] p) :
    0 ≤ mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m (Fintype.card κ) Winit n ∧
    MixedTriangularState (Ω n) f (r+2*n) m
      (mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m (Fintype.card κ) Winit n) := by
  let R := mixedYIterationBudgetSeq c M A L D Q K0 Q0 H0 m (Fintype.card κ) Winit
  have hDom : ∀ k, k ≤ n → Ω k ⊆ Ω 0 := by
    intro k
    induction k with
    | zero => intro _; exact Set.Subset.rfl
    | succ k ih =>
      intro hk
      exact (hGeom k (by omega)).domain_subset.trans (ih (by omega))
  have hAll : ∀ k, k ≤ n → 0 ≤ R k ∧ MixedTriangularState (Ω k) f (r+2*k) m (R k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hWinit,?_⟩
      change MixedTriangularState (Ω 0) f (r+2*0) m Winit
      simpa only [Nat.mul_zero,Nat.add_zero] using hf
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      obtain ⟨hR,hState⟩ := ih (by omega)
      have hDi := hDom k (by omega)
      have hn := mixedTriangularState_potential_step c (M k) (A k) (L k) (D k) (Q k)
        K0 Q0 H0 (R k) (hGeom k hkn) (hO k hkn) (hB.mono hDi) (by omega) hR f S hState
        (fun a b hab => (hS a b hab).restrict hDi le_rfl)
        (fun a b i hab => (hSY a b i hab).mono hDi)
        (fun b j hb => (hST b j hb).mono hDi)
        (fun a b hab p hp => hCoeff a b hab p (hDi hp))
        (fun a ha p hp => hQuad a ha p (hDi hp))
        (fun φ hφ hc hs => hP φ hφ hc (hs.trans hDi))
      have hpos := mixedYIterationNext_nonneg c (M k) (A k) (L k) (D k) (Q k)
        K0 Q0 H0 m (Fintype.card κ) (R k) hR
      refine ⟨hpos,?_⟩
      have he : r+2*k+2 = r+2*(k+1) := by omega
      rw [he] at hn
      exact hn
  exact hAll n le_rfl

#print axioms mixedTriangularState_potential_iterate
end TheoremT.Continuum.WeakGrushin
