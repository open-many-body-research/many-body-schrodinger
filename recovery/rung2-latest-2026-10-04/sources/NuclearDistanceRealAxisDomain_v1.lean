import NuclearDistanceRealAxisConnection_v1
import PhysicalKSAnalyticAxisSlice_v1

/-! Exact translation and domain bounds for the real nuclear representative.
The spatial vectors carry their Euclidean norms. The complex SO(2) input
uses coordinate sup norms, with the spectator center subtracted literally. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def nuclearDistanceRealAxisInput (σ r s u : ℝ) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![ (nuclearDistanceRealSpatial r s u 0 : ℂ),
       (nuclearDistanceRealSpatial r s u 1 : ℂ)],
   ![ (nuclearDistanceRealSpatial r s u 2 : ℂ), ((s - σ : ℝ) : ℂ)])

theorem nuclearDistanceRealSpectator_sub (s σ : ℝ) :
    nuclearDistanceRealSpectator s - nuclearDistanceRealSpectator σ =
      nuclearDistanceRealSpectator (s - σ) := by
  ext i
  fin_cases i <;> simp [nuclearDistanceRealSpectator]

theorem nuclearDistanceRealSpectator_sub_norm (s σ : ℝ) :
    ‖nuclearDistanceRealSpectator s - nuclearDistanceRealSpectator σ‖ = |s - σ| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [nuclearDistanceRealSpectator_sub]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, nuclearDistanceRealSpectator]

theorem nuclearDistanceRealSpectator_add_increment (s σ : ℝ) :
    nuclearDistanceRealSpectator σ + nuclearDistanceRealSpectator (s - σ) =
      nuclearDistanceRealSpectator s := by
  ext i
  fin_cases i <;> simp [nuclearDistanceRealSpectator]

theorem nuclearDistanceRealAxisInput_complex_map (σ r s u : ℝ) :
    physicalKSComplexAxisMap (nuclearDistanceRealAxisInput σ r s u) =
      Sum.elim (fun i => (nuclearDistanceRealSpatial r s u i : ℂ))
        (fun i => ((nuclearDistanceRealSpectator s - nuclearDistanceRealSpectator σ) i : ℂ)) := by
  funext j
  cases j with
  | inl i =>
    fin_cases i <;> simp [physicalKSComplexAxisMap, physicalComplexAxisSlice,
      nuclearDistanceRealAxisInput, nuclearDistanceRealSpatial]
  | inr i =>
    fin_cases i <;> simp [physicalKSComplexAxisMap, physicalComplexAxisSlice,
      nuclearDistanceRealAxisInput, nuclearDistanceRealSpectator]

theorem nuclearDistanceRealAxisInput_spectator (σ r s u : ℝ) :
    (nuclearDistanceRealAxisInput σ r s u).2 =
      ![(nuclearDistanceRealZ r s u : ℂ), ((s - σ : ℝ) : ℂ)] := rfl

theorem nuclearDistanceRealAxisInput_transverse_square {σ r s u : ℝ}
    (hw : 0 ≤ nuclearDistanceRealW r s u) :
    (nuclearDistanceRealAxisInput σ r s u).1 0 ^ 2 +
      (nuclearDistanceRealAxisInput σ r s u).1 1 ^ 2 =
      (nuclearDistanceRealW r s u : ℂ) := by
  change (nuclearDistanceRealSpatial r s u 0 : ℂ)^2 +
    (nuclearDistanceRealSpatial r s u 1 : ℂ)^2 = (nuclearDistanceRealW r s u : ℂ)
  exact_mod_cast nuclearDistanceRealSpatial_transverse_square hw

theorem nuclearDistanceRealAxisInput_domain {σ r s u h : ℝ}
    (hr : 0 ≤ r) (hw : 0 ≤ nuclearDistanceRealW r s u) (hh : 0 < h)
    (hrh : r < h) (hsh : |s - σ| < h) :
    (∀ i, ‖(nuclearDistanceRealAxisInput σ r s u).1 i‖ < h) ∧
      ‖(nuclearDistanceRealAxisInput σ r s u).2‖ < h ∧
      ‖(nuclearDistanceRealAxisInput σ r s u).1 0 ^ 2 +
        (nuclearDistanceRealAxisInput σ r s u).1 1 ^ 2‖ < h^2 := by
  have hx (i : Fin 3) : ‖(nuclearDistanceRealSpatial r s u i : ℂ)‖ < h := by
    have hi := (PiLp.norm_apply_le (nuclearDistanceRealSpatial r s u) i).trans_lt
      ((nuclearDistanceRealSpatial_norm hr hw).trans_lt hrh)
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hi
  constructor
  · intro i
    fin_cases i
    · exact hx 0
    · exact hx 1
  constructor
  · apply (pi_norm_lt_iff hh).mpr
    intro i
    fin_cases i
    · exact hx 2
    · change ‖((s - σ : ℝ) : ℂ)‖ < h
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hsh
  · rw [nuclearDistanceRealAxisInput_transverse_square hw]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    have hwr : nuclearDistanceRealW r s u ≤ r^2 := by
      dsimp only [nuclearDistanceRealW]
      nlinarith [sq_nonneg (nuclearDistanceRealZ r s u)]
    exact hwr.trans_lt ((sq_lt_sq₀ hr hh.le).mpr hrh)

theorem nuclearDistanceRealAxisInput_domain_of_triangle {σ r s u δ h : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hu : 0 ≤ u)
    (hlo : |r - s| ≤ u) (hhi : u ≤ r + s) (hh : 0 < h)
    (hrδ : r < δ) (hsδ : |s - σ| < δ) (hδh : δ ≤ h / 16) :
    (∀ i, ‖(nuclearDistanceRealAxisInput σ r s u).1 i‖ < h) ∧
      ‖(nuclearDistanceRealAxisInput σ r s u).2‖ < h ∧
      ‖(nuclearDistanceRealAxisInput σ r s u).1 0 ^ 2 +
        (nuclearDistanceRealAxisInput σ r s u).1 1 ^ 2‖ < h^2 := by
  exact nuclearDistanceRealAxisInput_domain hr
    (nuclearDistanceRealW_nonneg hr hs hu hlo hhi) hh (by linarith) (by linarith)

end TheoremT.Continuum
