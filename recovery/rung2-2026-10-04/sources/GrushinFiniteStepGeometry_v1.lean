import PhysicalSpectatorH12Geometry_v1

/-! Arbitrarily many actual finite cutoff stages on the seven-coordinate
Grushin space. The regions and cutoffs are fixed before any solution or PDE.
The coefficient used in the cutoff estimates may vary from stage to stage. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

def finiteGrushinRegion (a : Space (Fin 3)) (ry rt δ : ℝ) (k : ℕ) : Set (Space (Fin 3)) :=
  rectangularOpenBox a (ry-2*k*δ) (rt-2*k*δ)

def finiteGrushinMiddle (a : Space (Fin 3)) (ry rt δ : ℝ) (k : ℕ) : Set (Space (Fin 3)) :=
  rectangularOpenBox a (ry-2*k*δ-δ) (rt-2*k*δ-δ)

def finiteGrushinInnerCutoff (a : Space (Fin 3)) (ry rt δ : ℝ) (k : ℕ) :
    Space (Fin 3) → ℝ :=
  h12InnerCutoff a (ry-2*k*δ) (rt-2*k*δ) δ

def finiteGrushinEnergyCutoff (a : Space (Fin 3)) (ry rt δ : ℝ) (k : ℕ) :
    Space (Fin 3) → ℝ :=
  h12EnergyCutoff a (ry-2*k*δ) (rt-2*k*δ) δ

theorem finiteGrushinRegion_isOpen (a : Space (Fin 3)) (ry rt δ : ℝ) (k : ℕ) :
    IsOpen (finiteGrushinRegion a ry rt δ k) := rectangularOpenBox_isOpen a _ _

theorem finiteGrushinRegion_measurableSet (a : Space (Fin 3)) (ry rt δ : ℝ) (k : ℕ) :
    MeasurableSet (finiteGrushinRegion a ry rt δ k) :=
  (finiteGrushinRegion_isOpen a ry rt δ k).measurableSet

theorem finiteGrushinRegion_zero (a : Space (Fin 3)) (ry rt δ : ℝ) :
    finiteGrushinRegion a ry rt δ 0 = rectangularOpenBox a ry rt := by
  simp [finiteGrushinRegion]

theorem finiteGrushinRegion_antitone (a : Space (Fin 3)) (ry rt : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) : Antitone (finiteGrushinRegion a ry rt δ) := by
  intro k l hkl p hp d
  have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hd : 2*(k : ℝ)*δ ≤ 2*(l : ℝ)*δ := by nlinarith
  cases d with
  | inl d => exact (hp (.inl d)).trans_le (sub_le_sub_left hd ry)
  | inr d => exact (hp (.inr d)).trans_le (sub_le_sub_left hd rt)

theorem finiteGrushinRegion_subset_initial (a : Space (Fin 3)) (ry rt : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    finiteGrushinRegion a ry rt δ k ⊆ rectangularOpenBox a ry rt := by
  simpa only [finiteGrushinRegion_zero] using
    finiteGrushinRegion_antitone a ry rt hδ (Nat.zero_le k)

theorem finiteGrushinRegion_contains_closed (a : Space (Fin 3))
    {ry rt δ bY bT : ℝ} (n : ℕ)
    (hy : bY < ry-2*n*δ) (ht : bT < rt-2*n*δ) :
    rectangularClosedBox a bY bT ⊆ finiteGrushinRegion a ry rt δ n :=
  rectangularClosedBox_subset_openBox a hy ht

theorem finite_grushin_step_geometry (a : Space (Fin 3))
    (n : ℕ) {ry rt δ C1 C2 : ℝ} (hδ : 0 < δ)
    (hy : 2*(n : ℝ)*δ ≤ ry) (ht : 2*(n : ℝ)*δ ≤ rt)
    (c : ℕ → ℝ) (hc : ∀ k, k < n → 0 ≤ c k)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∀ k, k < n → SpectatorStepGeometry (c k)
      (finiteGrushinRegion a ry rt δ k) (finiteGrushinRegion a ry rt δ (k+1))
      (finiteGrushinMiddle a ry rt δ k)
      (finiteGrushinInnerCutoff a ry rt δ k) (finiteGrushinEnergyCutoff a ry rt δ k)
      1 (h12CutoffScalarBound (c k) (‖a.1‖+2*ry) C1 C2 δ)
      (h12CutoffWeightBound (c k) (‖a.1‖+2*ry) C1 δ)
      1 (h12CutoffWeightBound (c k) (‖a.1‖+2*ry) C1 δ) := by
  intro k hk
  have hkn : (k : ℝ)+1 ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
  have hky : 2*δ ≤ ry-2*k*δ := by nlinarith
  have hkt : 2*δ ≤ rt-2*k*δ := by nlinarith
  have hS : ‖a.1‖+2*(ry-2*k*δ) ≤ ‖a.1‖+2*ry := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h := h12_spectatorStepGeometry a (hc k hk) hδ hky hkt hC1 hC2 hS
  have heY : ry-2*(↑(k+1) : ℝ)*δ = ry-2*k*δ-2*δ := by push_cast; ring
  have heT : rt-2*(↑(k+1) : ℝ)*δ = rt-2*k*δ-2*δ := by push_cast; ring
  simpa only [finiteGrushinRegion,finiteGrushinMiddle,finiteGrushinInnerCutoff,
    finiteGrushinEnergyCutoff,heY,heT] using h

#print axioms finite_grushin_step_geometry
end TheoremT.Continuum.WeakGrushin
