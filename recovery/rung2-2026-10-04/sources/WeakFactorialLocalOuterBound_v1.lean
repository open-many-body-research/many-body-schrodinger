import WeakFactorialLocalFamilyMatch_v1
import LpSubmeasureRepresentativeBound_v1
import GrushinFactorialOuterL2_v1

/-! Restriction of actual global weighted weak-jet representatives controls
the inner local outer norm. Actual local weak-chain uniqueness identifies
all fields before submeasure monotonicity is used. No inner norm bound or
weighted integrability is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem local_factorial_outer_le_global_weak_representatives
    (U : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional U (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {V : Set (Space (Fin 3))} (hV : IsOpen V)
    (G : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (h0 : ∀ᵐ p ∂volume, p ∈ V → U p = G 0 0 p)
    (hY : ∀ a b i, (∑ k,a k)+(∑ j,b j) < 2 →
      ProductLocalWeakDirectional V (G a b) (G (a+Pi.single i 1) b) (yDir i))
    (hT : ∀ a b j, (∑ i,a i)+(∑ k,b k) < 2 →
      ProductLocalWeakDirectional V (G a b) (G a (b+Pi.single j 1)) (tDir j))
    (W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (hW : FactorialOuterL2Rep
      (fun a b => (weakFactorialJet U d e a b : Space (Fin 3) → ℂ)) W) :
    (∀ q ∈ factorialOuterIndices,
      MemLp (fun p => factorialYMonomial q.2.2 p.1 • G q.1 q.2.1 p) 2 (volume.restrict V)) ∧
    (∑ q ∈ factorialOuterIndices,
      (eLpNorm (fun p => factorialYMonomial q.2.2 p.1 • G q.1 q.2.1 p) 2 (volume.restrict V)).toReal) ≤
        factorialOuterNorm W := by
  have hj := weakFactorialJet_ae_local_of_natural_chains U d e hd he hV G h0 hY hT
  have hcomp (q : FactorialOuterIndex) (hq : q ∈ factorialOuterIndices) :
      MemLp (fun p => factorialYMonomial q.2.2 p.1 • G q.1 q.2.1 p) 2 (volume.restrict V) ∧
      (eLpNorm (fun p => factorialYMonomial q.2.2 p.1 • G q.1 q.2.1 p) 2 (volume.restrict V)).toReal ≤ ‖W q‖ := by
    have heq : (W q : Space (Fin 3) → ℂ) =ᵐ[volume.restrict V]
        (fun p => factorialYMonomial q.2.2 p.1 • G q.1 q.2.1 p) := by
      have hl := (ae_restrict_iff' hV.measurableSet).mpr
        (hj q.1 q.2.1 (((factorialOuterIndices_mem q).mp hq).1))
      filter_upwards [(hW q hq).filter_mono ae_restrict_le,hl] with p hp hqeq
      rw [hp,hqeq]
    exact lp_submeasure_representative_bound Measure.restrict_le_self (W q) _ heq
  exact ⟨fun q hq => (hcomp q hq).1,
    Finset.sum_le_sum (fun q hq => (hcomp q hq).2)⟩

end TheoremT.Continuum.WeakGrushin
