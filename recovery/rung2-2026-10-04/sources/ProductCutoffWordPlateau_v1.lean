import ProductDirectionalWordCommutator_v1

/-! Exact local identification of every ordered cutoff word on an open plateau.
No regularity assumption on the raw fields is needed for this algebraic identity. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
variable {ι : Type}

theorem directionalWordDeriv_constant_open
    (dirs : ι → Y × T) {χ : Y × T → ℝ} {U : Set (Y × T)}
    (hU : IsOpen U) {c : ℝ} (hχ : ∀ p ∈ U, χ p = c)
    (w : List ι) : ∀ p ∈ U,
      directionalWordDeriv dirs χ w p = if w = [] then c else 0 := by
  classical
  induction w with
  | nil => simpa only [directionalWordDeriv,ite_true] using hχ
  | cons i w ih =>
    intro p hp
    have he : directionalWordDeriv dirs χ w =ᶠ[𝓝 p]
        (fun _ => if w = [] then c else 0) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact ih q hq
    simp [directionalWordDeriv,he.fderiv_eq]

theorem directionalWordProduct_plateau
    (dirs : ι → Y × T) {χ : Y × T → ℝ} {U : Set (Y × T)}
    (hU : IsOpen U) (hχ : ∀ p ∈ U, χ p = 1)
    (D : List ι → Y × T → ℂ) (w : List ι) {p : Y × T} (hp : p ∈ U) :
    directionalWordProduct dirs χ D w p = D w p := by
  rw [directionalWordProduct_eq_commutator_add]
  have hz : directionalWordCommutator dirs χ D w p = 0 := by
    unfold directionalWordCommutator
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hz
    have hpw := (spectatorWordProperSplits_strict hab).1
    have hne : ab.1 ≠ [] := by intro h; simp only [h,List.length_nil] at hpw; omega
    rw [directionalWordDeriv_constant_open dirs hU hχ ab.1 p hp,if_neg hne,zero_smul]
  rw [hz,hχ p hp,one_smul,zero_add]

theorem directionalWordProduct_plateau_restrict_ae
    (dirs : ι → Y × T) {χ : Y × T → ℝ} {U : Set (Y × T)}
    (hU : IsOpen U) (hχ : ∀ p ∈ U, χ p = 1)
    (D : List ι → Y × T → ℂ) (w : List ι) {K : Set (Y × T)} (hK : K ⊆ U) :
    directionalWordProduct dirs χ D w =ᵐ[volume.restrict K] D w := by
  filter_upwards [(ae_restrict_of_ae_restrict_of_subset hK (ae_restrict_mem hU.measurableSet))] with p hp
  exact directionalWordProduct_plateau dirs hU hχ D w hp

end TheoremT.Continuum
