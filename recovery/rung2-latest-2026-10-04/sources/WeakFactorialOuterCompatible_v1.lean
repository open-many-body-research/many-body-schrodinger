import WeakGrushinCommonRadialBound_v1
import GrushinFactorialOuterAssembly_v1
import GrushinFactorialOuterCardinality_v1
import GrushinFactorialLowDegreeCases_v1

/-! Full outer norm assembly for an L2 family whose six low-order entries
are identified with genuine weak jets.  The final canonical wrapper
discharges these identities rather than retaining an arbitrary family. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

def CompatibleFactorialWeakJet
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3)) : Prop :=
    D 0 0 = f ∧
    (∀ i : Fin 4, D (Pi.single i 1) 0 = d (yDir i)) ∧
    (∀ j : Fin 3, D 0 (Pi.single j 1) = d (tDir j)) ∧
    (∀ i j : Fin 4, D (Pi.single i 1+Pi.single j 1) 0 = e (yDir i) (yDir j)) ∧
    (∀ (i : Fin 4) (j : Fin 3), D (Pi.single i 1) (Pi.single j 1) = e (yDir i) (tDir j)) ∧
    (∀ i j : Fin 3, D 0 (Pi.single i 1+Pi.single j 1) = e (tDir i) (tDir j))

theorem compatible_factorial_weak_jet_support
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (hD : CompatibleFactorialWeakJet D f d e)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (ho : (∑ i, α i)+(∑ j, β j) ≤ 2) :
    ∀ᵐ p ∂volume, p ∉ K → D α β p = 0 := by
  have hh := compact_weakH2_weighted_jet_memLp d e hd he hK hs
  rcases factorial_outer_derivative_six_cases α β ho with
    ⟨rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩
  · simpa only [hD.1] using hs
  · simpa only [hD.2.1 i] using hh.1 (yDir i)
  · simpa only [hD.2.2.1 j] using hh.1 (tDir j)
  · simpa only [hD.2.2.2.1 i j] using hh.2.1 (yDir i) (yDir j)
  · simpa only [hD.2.2.2.2.1 i j] using hh.2.1 (yDir i) (tDir j)
  · simpa only [hD.2.2.2.2.2 i j] using hh.2.1 (tDir i) (tDir j)

theorem compact_weak_compatible_factorial_outer_bound
    {c : ℝ} (hc : 0 < c)
    {f h : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    (i₀ : Fin 4) {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i₀| ≤ R)
    (S : ℝ) (hS : 1 ≤ S) (hSK : ∀ p ∈ K, ‖p.1‖ ≤ S)
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (hD : CompatibleFactorialWeakJet D f d e) :
    ∃ W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))),
      FactorialOuterL2Rep (fun α β => (D α β : Space (Fin 3) → ℂ)) W ∧
      factorialOuterNorm W ≤ 498*S^2*(factorialGraphCoefficient R c)*‖h‖ := by
  have hcomp := compact_weakH2_common_radial_output_bound hc d e hd he hK hs hP i₀ hR hslab
  have hC : 0 ≤ factorialGraphCoefficient R c :=
    (by norm_num : (0:ℝ) ≤ 2).trans (factorialGraphCoefficient_bounds hR hc).2.2.1
  have hDs := compatible_factorial_weak_jet_support d e hd he hK hs D hD
  have hrad (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (ho : (∑ i, α i)+(∑ j, β j) ≤ 2) :
      (∫ p, ‖(‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • D α β p‖^2) ≤
      (factorialGraphCoefficient R c)^2*‖h‖^2 := by
    rcases factorial_outer_derivative_six_cases α β ho with
      ⟨rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩
    · simpa [factorialOuterRadialOrder,hD.1,← l2_norm_sq_integral] using hcomp.1
    · simpa [factorialOuterRadialOrder,hD.2.1 i] using hcomp.2.1 i
    · simpa [factorialOuterRadialOrder,hD.2.2.1 j] using hcomp.2.2.1 j
    · simpa [factorialOuterRadialOrder,Finset.sum_add_distrib,hD.2.2.2.1 i j] using hcomp.2.2.2.1 i j
    · simpa [factorialOuterRadialOrder,hD.2.2.2.2.1 i j] using hcomp.2.2.2.2.1 i j
    · simpa [factorialOuterRadialOrder,Finset.sum_add_distrib,hD.2.2.2.2.2 i j] using hcomp.2.2.2.2.2 i j
  have hU (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (ho : (∑ i, α i)+(∑ j, β j) ≤ 2) :
      ∃ U : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
        U =ᵐ[volume] (fun p => (‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • D α β p) ∧
        ‖U‖ ≤ factorialGraphCoefficient R c*‖h‖ := by
    have hu := compact_support_weight_memLp hK
      (fun p : Space (Fin 3) => ‖p.1‖^(factorialOuterRadialOrder α β))
      (continuous_fst.norm.pow _) (D α β) (hDs α β ho)
    let U := hu.toLp (fun p => (‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • D α β p)
    refine ⟨U,MemLp.coeFn_toLp hu,?_⟩
    have hn := hrad α β ho
    rw [← actual_l2_toLp_norm_sq_integral hu] at hn
    change ‖U‖^2 ≤ _ at hn
    nlinarith [norm_nonneg U,norm_nonneg h,mul_nonneg hC (norm_nonneg h)]
  obtain ⟨W,hW,hWn⟩ := factorial_outer_L2_assembly
    (fun α β => (D α β : Space (Fin 3) → ℂ))
    S (factorialGraphCoefficient R c*‖h‖) hS
    (fun α β _ => (Lp.memLp (D α β)).aestronglyMeasurable)
    (fun α β ho => by
      filter_upwards [hDs α β ho] with p hp hne
      exact hSK p (by_contra (fun hnot => hne (hp hnot)))) hU
  refine ⟨W,hW,?_⟩
  simpa only [factorialOuterIndices_card,Nat.cast_ofNat,mul_assoc] using hWn

end TheoremT.Continuum.WeakGrushin
