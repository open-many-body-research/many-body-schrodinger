import WeakGrushinAnisotropicLimitProduct_v1
import WeakGrushinAnisotropicLimitUniqueness_v1
import WeakGrushinAnisotropicLimitSecondFamily_v1

/-! Anisotropic strong-L2 closure with simultaneous aggregate bounds.
The hypotheses are estimates on approximating genuine weak jets. Existence
or convergence of limit jets is not assumed. Uniqueness identifies the jets
produced by independently applying the finite-family bounded-limit theorem.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2_anisotropic_jets_preserve_bounds
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → Y) (w : κ → T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (dy : ℕ → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (dt : ℕ → κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (eyy : ℕ → ι → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    (hdy : ∀ n i, WeakProductL2Directional (u n) (dy n i) (v i,0))
    (hdt : ∀ n j, WeakProductL2Directional (u n) (dt n j) (0,w j))
    (heyy : ∀ n i j, WeakProductL2Directional (dy n i) (eyy n i j) (v j,0))
    {C CY CT CYY : ℝ}
    (hb : ∀ n, (∑ i, ‖dy n i‖^2) + (∑ j, ‖dt n j‖^2) +
      (∑ i, ∑ j, ‖eyy n i j‖^2) ≤ C)
    (hbY : ∀ n, (∑ i, ‖dy n i‖^2) ≤ CY)
    (hbT : ∀ n, (∑ j, ‖dt n j‖^2) ≤ CT)
    (hbYY : ∀ n, (∑ i, ∑ j, ‖eyy n i j‖^2) ≤ CYY) :
    ∃ gy : ι → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ hyy : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
      ((∑ i, ‖gy i‖^2) + (∑ j, ‖gt j‖^2) + (∑ i, ∑ j, ‖hyy i j‖^2) ≤ C) ∧
      (∑ i, ‖gy i‖^2) ≤ CY ∧ (∑ j, ‖gt j‖^2) ≤ CT ∧
      (∑ i, ∑ j, ‖hyy i j‖^2) ≤ CYY ∧
      (∀ i, WeakProductL2Directional f (gy i) (v i,0)) ∧
      (∀ j, WeakProductL2Directional f (gt j) (0,w j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (v j,0) := by
  obtain ⟨gy,gt,hyy,hall,hgy,hgt,hhyy⟩ :=
    weakProductL2_anisotropic_jets_of_bounded_strong_approximation
      v w u dy dt eyy f hf hdy hdt heyy hb
  obtain ⟨ay,hay,hayD⟩ := weakProductL2Directional_family_of_bounded_strong_approximation
    (fun i => (v i,(0 : T))) u dy f hf hdy hbY
  have hgyay : gy = ay := funext fun i => weakProductL2Directional_unique (hgy i) (hayD i)
  obtain ⟨aT,hat,hatD⟩ := weakProductL2Directional_family_of_bounded_strong_approximation
    (fun j => ((0 : Y),w j)) u dt f hf hdt hbT
  have hgtat : gt = aT := funext fun j => weakProductL2Directional_unique (hgt j) (hatD j)
  obtain ⟨ayy,hayy,hayyD⟩ := weakProductL2_second_family_of_bounded_strong_approximation
    (fun i => (v i,(0 : T))) u dy eyy f hf hdy heyy gy hgy hbYY
  have hhyyayy : hyy = ayy := funext fun i => funext fun j =>
    weakProductL2Directional_unique (hhyy i j) (hayyD i j)
  refine ⟨gy,gt,hyy,hall,?_,?_,?_,hgy,hgt,hhyy⟩
  · simpa only [hgyay] using hay
  · simpa only [hgtat] using hat
  · simpa only [hhyyayy] using hayy

theorem weakProductL2_anisotropic_jets_of_separate_bounded_strong_approximation
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → Y) (w : κ → T)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Y × T)))
    (dy : ℕ → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (dt : ℕ → κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (eyy : ℕ → ι → ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (hf : Tendsto u atTop (𝓝 f))
    (hdy : ∀ n i, WeakProductL2Directional (u n) (dy n i) (v i,0))
    (hdt : ∀ n j, WeakProductL2Directional (u n) (dt n j) (0,w j))
    (heyy : ∀ n i j, WeakProductL2Directional (dy n i) (eyy n i j) (v j,0))
    {CY CT CYY : ℝ}
    (hbY : ∀ n, (∑ i, ‖dy n i‖^2) ≤ CY)
    (hbT : ∀ n, (∑ j, ‖dt n j‖^2) ≤ CT)
    (hbYY : ∀ n, (∑ i, ∑ j, ‖eyy n i j‖^2) ≤ CYY) :
    ∃ gy : ι → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ hyy : ι → ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∑ i, ‖gy i‖^2) ≤ CY ∧ (∑ j, ‖gt j‖^2) ≤ CT ∧
      (∑ i, ∑ j, ‖hyy i j‖^2) ≤ CYY ∧
      (∀ i, WeakProductL2Directional f (gy i) (v i,0)) ∧
      (∀ j, WeakProductL2Directional f (gt j) (0,w j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (v j,0) := by
  obtain ⟨gy,gt,hyy,_,hY,hT,hYY,hgy,hgt,hhyy⟩ :=
    weakProductL2_anisotropic_jets_preserve_bounds v w u dy dt eyy f hf hdy hdt heyy
      (fun n => add_le_add (add_le_add (hbY n) (hbT n)) (hbYY n)) hbY hbT hbYY
  exact ⟨gy,gt,hyy,hY,hT,hYY,hgy,hgt,hhyy⟩

#print axioms weakProductL2_anisotropic_jets_preserve_bounds
#print axioms weakProductL2_anisotropic_jets_of_separate_bounded_strong_approximation
end TheoremT.Continuum
