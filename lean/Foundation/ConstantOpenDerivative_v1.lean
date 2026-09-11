import LocalWeakLaplacian_v1

noncomputable section
open Filter
open scoped Topology
namespace TheoremT.Continuum

theorem fderiv_zero_of_constant_open {N : ℕ} {χ : Configuration N → ℝ}
    {S : Set (Configuration N)} (hS : IsOpen S) {c : ℝ}
    (hχ : ∀ x ∈ S, χ x=c) {x : Configuration N} (hx : x ∈ S) : fderiv ℝ χ x=0 := by
  have he : χ =ᶠ[𝓝 x] (fun _ => c) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact hχ y hy
  simpa using he.fderiv_eq (𝕜 := ℝ)

theorem realTestLaplacian_zero_of_constant_open {N : ℕ} {χ : Configuration N → ℝ}
    {S : Set (Configuration N)} (hS : IsOpen S) {c : ℝ}
    (hχ : ∀ x ∈ S, χ x=c) {x : Configuration N} (hx : x ∈ S) :
    realTestLaplacian χ x=0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hd : ∀ y ∈ S, fderiv ℝ χ y (coordinateVector k)=0 := by
    intro y hy
    rw [fderiv_zero_of_constant_open hS hχ hy]
    rfl
  rw [fderiv_zero_of_constant_open hS hd hx]
  rfl

#print axioms realTestLaplacian_zero_of_constant_open
end TheoremT.Continuum
