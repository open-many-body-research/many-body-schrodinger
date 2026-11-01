import SmoothComplexMixedSourceWords_v1
import MixedWordFDeriv_v1
import Mathlib.Analysis.Normed.Group.Bounded

/-! Finite compact bounds for actual mixed words of a smooth complex source.
The operator norm of the iterated Frechet derivative controls each ordered
word with factor one. Compactness supplies a common bound through a fixed
finite order and hence an actual region L2 budget. Both bounds may depend
on the source, compact set, and requested order; no factorial estimate or
uniformity in order, and no algorithm for selecting the bounds, is claimed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem complexDirectionalWordDeriv_eq_iteratedFDeriv {ι : Type}
    (dirs : ι → Space κ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {s : Space κ → ℂ} (hs : ContDiffOn ℝ ∞ s Ω)
    (w : List ι) {p : Space κ} (hp : p ∈ Ω) :
    complexDirectionalWordDeriv dirs s w p =
      iteratedFDeriv ℝ w.length s p (directionalWordDirections dirs w) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have heq : complexDirectionalWordDeriv dirs s w =ᶠ[𝓝 p]
        (fun q => iteratedFDeriv ℝ w.length s q (directionalWordDirections dirs w)) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact ih hq
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length s) p :=
      (hs.contDiffAt (hΩ.mem_nhds hp)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top w.length)
    change fderiv ℝ (complexDirectionalWordDeriv dirs s w) p (dirs i) = _
    rw [heq.fderiv_eq]
    symm
    simpa only [List.length_cons, directionalWordDirections, Fin.cons_zero,
      Fin.tail_cons] using
      (hd.iteratedFDeriv_succ_apply_left'
        (m := Fin.cons (dirs i) (directionalWordDirections dirs w)))

theorem complexDirectionalWordDeriv_norm_le_iteratedFDeriv {ι : Type}
    (dirs : ι → Space κ) (hdirs : ∀ i, ‖dirs i‖ ≤ 1)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (w : List ι) {p : Space κ} (hp : p ∈ Ω) :
    ‖complexDirectionalWordDeriv dirs s w p‖ ≤ ‖iteratedFDeriv ℝ w.length s p‖ := by
  rw [complexDirectionalWordDeriv_eq_iteratedFDeriv dirs hΩ hs w hp]
  have hprod : (∏ i : Fin w.length, ‖directionalWordDirections dirs w i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i _ => directionalWordDirections_norm_le dirs hdirs w i)
  exact ((iteratedFDeriv ℝ w.length s p).le_opNorm
    (directionalWordDirections dirs w)).trans
      (mul_le_of_le_one_right (norm_nonneg _) hprod)

theorem complexCoordinateWordDeriv_of_tWord (s : Space κ → ℂ) (tb : List κ) :
    complexDirectionalWordDeriv productCoordinateDirection s
      (tb.map (Sum.inr : κ → Fin 4 ⊕ κ)) = complexDirectionalWordDeriv tDir s tb := by
  induction tb with
  | nil => rfl
  | cons j tb ih =>
    simp only [List.map_cons, complexDirectionalWordDeriv, productCoordinateDirection, ih]

theorem complexMixedSourceWord_eq_coordinateWord (s : Space κ → ℂ)
    (ya : List (Fin 4)) (tb : List κ) :
    complexMixedSourceWord s ya tb =
      complexDirectionalWordDeriv productCoordinateDirection s
        (ya.map (Sum.inl : Fin 4 → Fin 4 ⊕ κ) ++
          tb.map (Sum.inr : κ → Fin 4 ⊕ κ)) := by
  change complexDirectionalWordDeriv yDir (complexDirectionalWordDeriv tDir s tb) ya = _
  induction ya with
  | nil =>
    simpa only [List.map_nil, List.nil_append, complexDirectionalWordDeriv] using
      (complexCoordinateWordDeriv_of_tWord s tb).symm
  | cons i ya ih =>
    simp only [List.map_cons, List.cons_append, complexDirectionalWordDeriv,
      productCoordinateDirection, ih]

theorem complexMixedSourceWord_norm_le_iteratedFDeriv
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) (ya : List (Fin 4)) (tb : List κ)
    {p : Space κ} (hp : p ∈ Ω) :
    ‖complexMixedSourceWord s ya tb p‖ ≤
      ‖iteratedFDeriv ℝ (ya.length + tb.length) s p‖ := by
  rw [complexMixedSourceWord_eq_coordinateWord]
  have hh := complexDirectionalWordDeriv_norm_le_iteratedFDeriv productCoordinateDirection
    (fun i => (productCoordinateDirection_norm i).le) hΩ hs
    (ya.map (Sum.inl : Fin 4 → Fin 4 ⊕ κ) ++
      tb.map (Sum.inr : κ → Fin 4 ⊕ κ)) hp
  have hlen : (ya.map (Sum.inl : Fin 4 → Fin 4 ⊕ κ) ++
      tb.map (Sum.inr : κ → Fin 4 ⊕ κ)).length = ya.length + tb.length := by simp
  rw [hlen] at hh
  exact hh

theorem mixedWordDeriv_compact_finite_bound
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {K : Set (Space κ)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ya : List (Fin 4), ∀ tb : List κ,
      ya.length + tb.length ≤ m → ∀ p ∈ K,
        |directionalWordDeriv yDir (spectatorWordDeriv B tb) ya p| ≤ M := by
  classical
  have hex (k : Fin (m+1)) :
      ∃ C : ℝ, ∀ p ∈ K, ‖iteratedFDeriv ℝ (k : ℕ) B p‖ ≤ C := by
    have hc : ContinuousOn (iteratedFDeriv ℝ (k : ℕ) B) K := by
      intro p hp
      exact ((hB.contDiffAt (hΩ.mem_nhds (hKΩ hp))).continuousAt_iteratedFDeriv
        (by simp)).continuousWithinAt
    exact hK.exists_bound_of_continuousOn hc
  choose C hC using hex
  let M : ℝ := ∑ k : Fin (m+1), max (C k) 0
  refine ⟨M, Finset.sum_nonneg (fun k _ => le_max_right (C k) 0), ?_⟩
  intro ya tb hlen p hp
  let k : Fin (m+1) := ⟨ya.length + tb.length, by omega⟩
  have hb : ‖iteratedFDeriv ℝ (ya.length + tb.length) B p‖ ≤ C k := hC k p hp
  have hmax : max (C k) 0 ≤ M :=
    Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ k)
  exact ((mixedWordDeriv_abs_le_iteratedFDeriv hΩ hB ya tb (hKΩ hp)).trans hb).trans
    ((le_max_left (C k) 0).trans hmax)

theorem complexMixedSourceWord_compact_finite_bound
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) {K : Set (Space κ)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ya : List (Fin 4), ∀ tb : List κ,
      ya.length + tb.length ≤ m → ∀ p ∈ K, ‖complexMixedSourceWord s ya tb p‖ ≤ M := by
  classical
  have hex (k : Fin (m+1)) :
      ∃ C : ℝ, ∀ p ∈ K, ‖iteratedFDeriv ℝ (k : ℕ) s p‖ ≤ C := by
    have hc : ContinuousOn (iteratedFDeriv ℝ (k : ℕ) s) K := by
      intro p hp
      exact ((hs.contDiffAt (hΩ.mem_nhds (hKΩ hp))).continuousAt_iteratedFDeriv
        (by simp)).continuousWithinAt
    exact hK.exists_bound_of_continuousOn hc
  choose C hC using hex
  let M : ℝ := ∑ k : Fin (m+1), max (C k) 0
  refine ⟨M, Finset.sum_nonneg (fun k _ => le_max_right (C k) 0), ?_⟩
  intro ya tb hlen p hp
  let k : Fin (m+1) := ⟨ya.length + tb.length, by omega⟩
  have hb : ‖iteratedFDeriv ℝ (ya.length + tb.length) s p‖ ≤ C k := hC k p hp
  have hmax : max (C k) 0 ≤ M :=
    Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ k)
  exact ((complexMixedSourceWord_norm_le_iteratedFDeriv hΩ hs ya tb (hKΩ hp)).trans hb).trans
    ((le_max_left (C k) 0).trans hmax)

theorem complexMixedSourceWord_compact_region_budgets
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {s : Space κ → ℂ}
    (hs : ContDiffOn ℝ ∞ s Ω) {K : Set (Space κ)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ ya : List (Fin 4), ∀ tb : List κ,
      ya.length + tb.length ≤ m → RegionL2Budget (complexMixedSourceWord s ya tb) K W := by
  obtain ⟨M, _hM0, hM⟩ := complexMixedSourceWord_compact_finite_bound hΩ hs hK hKΩ m
  let W : ℝ := M^2 * (volume K).toReal
  refine ⟨W, mul_nonneg (sq_nonneg M) ENNReal.toReal_nonneg, ?_⟩
  intro ya tb hlen
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hc := (complexMixedSourceWord_contDiffOn hΩ hs ya tb).continuousOn.mono hKΩ
  have htop : MemLp (complexMixedSourceWord s ya tb) ⊤ (volume.restrict K) := by
    apply memLp_top_of_bound (hc.aestronglyMeasurable hK.measurableSet) M
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact hM ya tb hlen p hp
  have hm : MemLp (complexMixedSourceWord s ya tb) 2 (volume.restrict K) :=
    htop.mono_exponent (by simp)
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∫ _p in K, M^2 := by
      apply integral_mono_ae (hm.integrable_norm_pow (by norm_num)) (integrable_const _)
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (hM ya tb hlen p hp) 2
    _ = W := by simp [W, Measure.real, mul_comm]

end TheoremT.Continuum.WeakGrushin
