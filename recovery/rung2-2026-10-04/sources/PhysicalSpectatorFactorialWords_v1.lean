import KSCommonAnnulusFactorialWords_v1

/-! Exact arbitrary coordinate-word pullback from the physical spectator
space to the canonical three-coordinate space. This transports the actual
direction fields, with no change of norm or derivative order. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalSpectatorReindexAt_symm_coordinate (i : Fin 2)
    (j : Fin 4 ⊕ Fin 3) :
    (physicalSpectatorReindexAt i).symm (productCoordinateDirection j) =
      productCoordinateDirection (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm j) := by
  cases j with
  | inl j => exact physicalSpectatorReindexAt_symm_yDir i j
  | inr j => exact physicalSpectatorReindexAt_symm_tDir i j

theorem physicalSpectatorReindexAt_symm_word (i : Fin 2)
    {Ω : Set (NuclearKSSpace i)} (hΩ : IsOpen Ω)
    {b : NuclearKSSpace i → ℝ} (hb : ContDiffOn ℝ ∞ b Ω)
    (w : List (Fin 4 ⊕ Fin 3)) {p : Space (Fin 3)}
    (hp : (physicalSpectatorReindexAt i).symm p ∈ Ω) :
    directionalWordDeriv productCoordinateDirection
      (b ∘ (physicalSpectatorReindexAt i).symm) w p =
    directionalWordDeriv productCoordinateDirection b
      (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm))
      ((physicalSpectatorReindexAt i).symm p) := by
  induction w generalizing p with
  | nil => rfl
  | cons j w ih =>
    have hpre : IsOpen ((physicalSpectatorReindexAt i).symm ⁻¹' Ω) :=
      hΩ.preimage (physicalSpectatorReindexAt i).symm.continuous
    have heq : directionalWordDeriv productCoordinateDirection
        (b ∘ (physicalSpectatorReindexAt i).symm) w =ᶠ[𝓝 p]
        (directionalWordDeriv productCoordinateDirection b
          (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm))) ∘
            (physicalSpectatorReindexAt i).symm := by
      filter_upwards [hpre.mem_nhds hp] with q hq
      exact ih hq
    have hd := (directionalWordDeriv_contDiffOn productCoordinateDirection hΩ hb
      (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm))).contDiffAt
        (hΩ.mem_nhds hp)
    simp only [directionalWordDeriv,List.map_cons]
    rw [heq.fderiv_eq]
    rw [fderiv_comp p (hd.differentiableAt (by simp))
      (physicalSpectatorReindexAt i).symm.toContinuousLinearMap.differentiableAt,
      (physicalSpectatorReindexAt i).symm.hasFDerivAt.fderiv]
    exact congrArg (fun v => fderiv ℝ
      (directionalWordDeriv productCoordinateDirection b
        (w.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm)))
      ((physicalSpectatorReindexAt i).symm p) v)
      (physicalSpectatorReindexAt_symm_coordinate i j)

end TheoremT.Continuum
