import ProductSevenPullbackL2Budget_v1

/-! Auditable endpoints for the preserved compiled pullback-budget proofs.
The approved v7 declaration scanner rejects Lean's valid double-apostrophe
image notation in v1. These fresh endpoints use Set.image and preserve every
mathematical hypothesis and conclusion; the original compiled bytes remain
unchanged, and axiom checks traverse their proofs. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
namespace TheoremT.Continuum
open WeakGrushin

theorem seven_coordinate_restricted_volume (K : Set (Fin 7 → ℝ)) :
    MeasurePreserving sevenToProduct (volume.restrict K)
      (volume.restrict (Set.image sevenToProduct K)) :=
  sevenToProduct_restrict_measurePreserving K

theorem seven_coordinate_integral_image (K : Set (Fin 7 → ℝ))
    (f : Space (Fin 3) → ℝ) :
    (∫ x in K, f (sevenToProduct x)) = ∫ p in Set.image sevenToProduct K, f p :=
  sevenToProduct_integral_restrict_image K f

theorem seven_coordinate_pullback_memLp
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    MemLp (f ∘ sevenToProduct) 2 (volume.restrict K) :=
  sevenToProduct_pullback_memLp hK hf

theorem seven_coordinate_integral_sq_le
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ ∫ p in Ω, ‖f p‖^2 :=
  sevenToProduct_integral_sq_le hK hf

theorem seven_coordinate_sqrt_integral_le_eLpNorm
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    Real.sqrt (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ (eLpNorm f 2 (volume.restrict Ω)).toReal :=
  sevenToProduct_sqrt_integral_le_eLpNorm hK hf

theorem seven_coordinate_regionL2Budget
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ} {W : ℝ}
    (hf : RegionL2Budget f Ω W) :
    MemLp (f ∘ sevenToProduct) 2 (volume.restrict K) ∧
      Real.sqrt (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ Real.sqrt W :=
  sevenToProduct_regionL2Budget hK hf

theorem seven_coordinate_regionL2Budget_sq
    {K : Set (Fin 7 → ℝ)} {Ω : Set (Space (Fin 3))}
    (hK : MapsTo sevenToProduct K Ω) {f : Space (Fin 3) → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hf : RegionL2Budget f Ω (M^2)) :
    Real.sqrt (∫ x in K, ‖f (sevenToProduct x)‖^2) ≤ M :=
  sevenToProduct_regionL2Budget_sq hK hM hf

end TheoremT.Continuum
