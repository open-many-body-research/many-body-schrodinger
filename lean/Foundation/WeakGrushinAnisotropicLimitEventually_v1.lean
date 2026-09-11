import WeakGrushinAnisotropicLimitBounds_v1

/-! An eventual complete jet package suffices for anisotropic strong-L2
closure. No derivative witness is required for the finitely many initial
terms. Tail witness selection is noncomputable mathematical existence and
does not assert an executable approximation procedure. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2_anisotropic_jets_preserve_bounds_eventually
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → Y) (w : κ → T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    {C CY CT CYY : ℝ}
    (hjets : ∀ᶠ n : ℕ in atTop,
      ∃ dy : ι → Lp ℂ 2 (volume : Measure (Y × T)),
      ∃ dt : κ → Lp ℂ 2 (volume : Measure (Y × T)),
      ∃ eyy : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
        (∀ i, WeakProductL2Directional (u n) (dy i) (v i,0)) ∧
        (∀ j, WeakProductL2Directional (u n) (dt j) (0,w j)) ∧
        (∀ i j, WeakProductL2Directional (dy i) (eyy i j) (v j,0)) ∧
        ((∑ i, ‖dy i‖^2) + (∑ j, ‖dt j‖^2) + (∑ i, ∑ j, ‖eyy i j‖^2) ≤ C) ∧
        (∑ i, ‖dy i‖^2) ≤ CY ∧ (∑ j, ‖dt j‖^2) ≤ CT ∧
        (∑ i, ∑ j, ‖eyy i j‖^2) ≤ CYY) :
    ∃ gy : ι → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ hyy : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
      ((∑ i, ‖gy i‖^2) + (∑ j, ‖gt j‖^2) + (∑ i, ∑ j, ‖hyy i j‖^2) ≤ C) ∧
      (∑ i, ‖gy i‖^2) ≤ CY ∧ (∑ j, ‖gt j‖^2) ≤ CT ∧
      (∑ i, ∑ j, ‖hyy i j‖^2) ≤ CYY ∧
      (∀ i, WeakProductL2Directional f (gy i) (v i,0)) ∧
      (∀ j, WeakProductL2Directional f (gt j) (0,w j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (v j,0) := by
  classical
  obtain ⟨n₀,hn₀⟩ := hjets.exists_forall_of_atTop
  have htail (k : ℕ) := hn₀ (k+n₀) (Nat.le_add_left n₀ k)
  choose dy dt eyy hdy hdt heyy hb hbY hbT hbYY using htail
  exact weakProductL2_anisotropic_jets_preserve_bounds v w (fun k => u (k+n₀))
    dy dt eyy f (hf.comp (tendsto_add_atTop_nat n₀)) hdy hdt heyy hb hbY hbT hbYY

#print axioms weakProductL2_anisotropic_jets_preserve_bounds_eventually
end TheoremT.Continuum
