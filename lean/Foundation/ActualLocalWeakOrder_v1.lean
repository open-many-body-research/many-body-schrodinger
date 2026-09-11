import NestedCutoffDerivative_v1
import CompactSmoothCutoff_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

def HasLocalWeakOrder {N : ℕ} (f : SpatialL2 N) (Ω : Set (Configuration N)) (n : ℕ) : Prop :=
  ∀ (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    tsupport χ ⊆ Ω → HasWeakOrder (cutoffMul χ hχ.continuous hc f) n

theorem HasWeakOrder.localize {N : ℕ} {f : SpatialL2 N} {n : ℕ}
    (hf : HasWeakOrder f n) (Ω : Set (Configuration N)) : HasLocalWeakOrder f Ω n :=
  fun χ hχ hc _ => hf.cutoff χ hχ hc

theorem HasLocalWeakOrder.mono {N : ℕ} {f : SpatialL2 N} {Ω : Set (Configuration N)} {n m : ℕ}
    (hf : HasLocalWeakOrder f Ω n) (hmn : m ≤ n) : HasLocalWeakOrder f Ω m :=
  fun χ hχ hc hs => (hf χ hχ hc hs).mono hmn

theorem HasLocalWeakOrder.weakPartial {N : ℕ} {f d : SpatialL2 N}
    {Ω : Set (Configuration N)} (hΩ : IsOpen Ω) {n : ℕ}
    (hf : HasLocalWeakOrder f Ω (n+1)) {k : Coordinate N} (hd : WeakPartial f d k) :
    HasLocalWeakOrder d Ω n := by
  intro χ hχ hc hs
  obtain ⟨η,hη,hcη,hsη,h1⟩ := compact_exists_smooth_cutoff hc.isCompact hΩ hs
  obtain ⟨a,ha,haO⟩ := hf η hη hcη hsη
  have hh := (haO k).cutoff χ hχ hc
  rw [nested_cutoff_weakPartial_eq hd hχ hc hη hcη h1 (ha k)] at hh
  exact hh

theorem HasLocalWeakOrder.compact_product_rep {N : ℕ} {f : SpatialL2 N}
    {Ω : Set (Configuration N)} {n : ℕ} (hf : HasLocalWeakOrder f Ω n)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω) :
    ∃ g : SpatialL2 N, HasWeakOrder g n ∧ g =ᵐ[volume] (fun x => χ x • f x) :=
  ⟨cutoffMul χ hχ.continuous hc f,hf χ hχ hc hs,cutoffMul_ae χ hχ.continuous hc f⟩

#print axioms HasLocalWeakOrder.weakPartial
end TheoremT.Continuum
