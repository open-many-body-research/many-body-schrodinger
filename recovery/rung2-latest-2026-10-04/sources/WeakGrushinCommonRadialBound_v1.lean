import WeakGrushinRadialOutput_v1
import CompactWeakGrushinSlabGraphBounds_v1
import GrushinFactorialGraphCoefficient_v1

/-! A single explicit coefficient for every actual weak radial component
of coordinate order at most two. The original support slab supplies R;
all derivative and principal estimates are discharged dependencies. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem compact_weakH2_common_radial_output_bound
    {c : ℝ} (hc : 0 < c)
    {f h : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    (i₀ : Fin 4) {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i₀| ≤ R) :
    ‖f‖^2 ≤ (factorialGraphCoefficient R c)^2*‖h‖^2 ∧
    (∀ i : Fin 4, (∫ p, ‖d (yDir i) p‖^2) ≤ (factorialGraphCoefficient R c)^2*‖h‖^2) ∧
    (∀ j : Fin 3, (∫ p, ‖d (tDir j) p‖^2) ≤ (factorialGraphCoefficient R c)^2*‖h‖^2) ∧
    (∀ i j : Fin 4, (∫ p, ‖e (yDir i) (yDir j) p‖^2) ≤ (factorialGraphCoefficient R c)^2*‖h‖^2) ∧
    (∀ (i : Fin 4) (j : Fin 3), (∫ p, ‖‖p.1‖ • e (yDir i) (tDir j) p‖^2) ≤
      (factorialGraphCoefficient R c)^2*‖h‖^2) ∧
    (∀ i j : Fin 3, (∫ p, ‖(‖p.1‖^2) • e (tDir i) (tDir j) p‖^2) ≤
      (factorialGraphCoefficient R c)^2*‖h‖^2) := by
  have hcomp := (compact_weakH2_radial_output_estimates hc.le d e hd he hK hs hP).2
  have hsl := compact_weakH2_slab_graph_bounds_on_compact hc.le d e hd he hK hs hP i₀ hR hslab
  have hinput := hsl.1
  have hY := hsl.2.2
  let C := factorialGraphCoefficient R c
  let E := ‖h‖^2
  have hE : 0 ≤ E := sq_nonneg ‖h‖
  obtain ⟨hC0,hCY,hC2,hcC2⟩ := factorialGraphCoefficient_bounds hR hc
  change 4*R^2 ≤ C at hC0
  change 2*R ≤ C at hCY
  change 2 ≤ C at hC2
  change 2 ≤ c*C at hcC2
  have hC0sq := pow_le_pow_left₀ (by positivity : 0 ≤ 4*R^2) hC0 2
  have hCYsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*R) hCY 2
  have hC2sq : 4 ≤ C^2 := by nlinarith
  have hcC2sq : 4 ≤ c^2*C^2 := by nlinarith [sq_nonneg (c*C-2)]
  have hcCprod : 4 ≤ c*C^2 := by nlinarith [mul_le_mul hcC2 hC2 (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ c*C)]
  have hs0 : ‖f‖^2 ≤ C^2*E :=
    hinput.trans (mul_le_mul_of_nonneg_right hC0sq hE)
  have hsY (i : Fin 4) : (∫ p, ‖d (yDir i) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E := by
    have ht := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 4 => ∫ p, ‖d (yDir i) p‖^2
        ∂(volume : Measure (Space (Fin 3))))
      (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ i)
    exact (ht.trans hY).trans (mul_le_mul_of_nonneg_right (by nlinarith : 4*R^2 ≤ C^2) hE)
  have hsT (j : Fin 3) : (∫ p, ‖d (tDir j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    positive_weighted_square_bound (b := 1) (by positivity : 0 < 16*c) hE (by nlinarith) (by simpa only [one_mul,E] using hcomp.1 j)
  have hsYY (i j : Fin 4) : (∫ p, ‖e (yDir i) (yDir j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    (hcomp.2.1 i j).trans (mul_le_mul_of_nonneg_right (by linarith : (3/2:ℝ) ≤ C^2) hE)
  have hsYT (i : Fin 4) (j : Fin 3) : (∫ p, ‖(‖p.1‖:ℝ) •
      e (yDir i) (tDir j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    positive_weighted_square_bound (b := 3/2) (by positivity : 0 < 2*c) hE (by nlinarith) (hcomp.2.2.1 i j)
  have hsTT (i j : Fin 3) : (∫ p, ‖(‖p.1‖^2:ℝ) •
      e (tDir i) (tDir j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    positive_weighted_square_bound (b := 3/2) (by positivity : 0 < c^2) hE (by nlinarith) (hcomp.2.2.2 i j)
  exact ⟨hs0,hsY,hsT,hsYY,hsYT,hsTT⟩

end TheoremT.Continuum.WeakGrushin
