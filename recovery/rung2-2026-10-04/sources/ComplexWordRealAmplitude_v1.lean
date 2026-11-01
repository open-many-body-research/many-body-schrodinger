import SmoothComplexMixedSourceWords_v1
import ProductDirectionalWordLeibniz_v1

/-! Literal arbitrary directional words of a locally smooth real coefficient
times a fixed complex amplitude. The equality is asserted on the open domain
of smoothness and requires no coefficient or source norm bounds. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff

namespace TheoremT.Continuum.WeakGrushin

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem complexDirectionalWordDeriv_real_smul_const {ι : Type}
    (dirs : ι → Space κ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {b : Space κ → ℝ} (hb : ContDiffOn ℝ ∞ b Ω) (z : ℂ)
    (w : List ι) {p : Space κ} (hp : p ∈ Ω) :
    complexDirectionalWordDeriv dirs (fun q => b q • z) w p =
      directionalWordDeriv dirs b w p • z := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have heq : complexDirectionalWordDeriv dirs (fun q => b q • z) w =ᶠ[𝓝 p]
        (fun q => directionalWordDeriv dirs b w q • z) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact ih hq
    have hd : DifferentiableAt ℝ (directionalWordDeriv dirs b w) p :=
      ((directionalWordDeriv_contDiffOn dirs hΩ hb w).contDiffAt
        (hΩ.mem_nhds hp)).differentiableAt (by simp)
    change fderiv ℝ (complexDirectionalWordDeriv dirs (fun q => b q • z) w) p (dirs i) =
      fderiv ℝ (directionalWordDeriv dirs b w) p (dirs i) • z
    rw [heq.fderiv_eq, fderiv_smul_const hd z]
    rfl

end TheoremT.Continuum.WeakGrushin
