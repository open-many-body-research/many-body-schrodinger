import ContinuumFoundation_v1
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import HardyWeakCore_v1

/-!
Smooth compact density for the actual continuum L2 space, using the pinned
mathlib theorem rather than postulating a smoothing operation. This is L2
density only: it makes no derivative-norm approximation claim and cannot by
itself extend the Hardy inequality to the actual weak H1 space.

The original Configuration and SpatialL2 definitions are unchanged. Their
source provenance and frozen historical context are recorded in CollisionNull_v2.
-/

noncomputable section
open MeasureTheory Filter
open scoped ContDiff

namespace TheoremT.Continuum

/-- Actual L2 equivalence classes admitting an everywhere smooth compactly
supported complex representative on R^(3N). -/
def smoothCompactClass (N : ℕ) : Set (SpatialL2 N) :=
  {f | ∃ φ : Configuration N → ℂ,
    f =ᵐ[volume] φ ∧ HasCompactSupport φ ∧ ContDiff ℝ ∞ φ}

/-- Smooth compact representatives are dense in the actual continuum L2 norm. -/
theorem smoothCompactClass_dense (N : ℕ) : Dense (smoothCompactClass N) := by
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ENNReal) ≠ ⊤)

/-- Every actual spatial L2 wavefunction has a smooth compact approximation
with a prescribed positive L2 tolerance. This is existence, not an algorithm. -/
theorem exists_smoothCompact_eLp_approx {N : ℕ} (f : SpatialL2 N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Configuration N → ℂ,
      HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧
      MemLp φ 2 (volume : Measure (Configuration N)) ∧
      eLpNorm (fun x => f x - φ x) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨φ, hc, hs, he⟩ := (Lp.memLp f).exist_eLpNorm_sub_le
    (by norm_num : (2 : ENNReal) ≠ ⊤) (by norm_num) hε
  exact ⟨φ, hc, hs, hs.continuous.memLp_of_hasCompactSupport hc, he⟩

theorem exists_smoothCompact_L2_approx {N : ℕ} (f : SpatialL2 N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SpatialL2 N, g ∈ smoothCompactClass N ∧ ‖f - g‖ < ε := by
  obtain ⟨g, hd, hg⟩ := (Metric.dense_iff.mp (smoothCompactClass_dense N)) f ε hε
  exact ⟨g, hg, by simpa only [Metric.mem_ball, dist_comm, dist_eq_norm] using hd⟩

theorem smoothCompactClass_hasH2 {N : ℕ} {f : SpatialL2 N}
    (hf : f ∈ smoothCompactClass N) : HasH2 f := by
  obtain ⟨φ, hfφ, hc, hs⟩ := hf
  have hφ : MemLp φ 2 (volume : Measure (Configuration N)) :=
    hs.continuous.memLp_of_hasCompactSupport hc
  have heq : f = hφ.toLp φ := by
    apply Lp.ext
    exact hfφ.trans hφ.coeFn_toLp.symm
  rw [heq]
  exact compact_c2_hasH2 (hs.of_le (by norm_num)) hc hφ

/-- The actual weak H2 domain is dense in the scalar L2 topology. This asserts
neither H2-norm density of a core nor existence of Coulomb Hamiltonian outputs. -/
theorem weakH2_dense_in_L2 (N : ℕ) : Dense {f : SpatialL2 N | HasH2 f} :=
  (smoothCompactClass_dense N).mono (fun _ hf => smoothCompactClass_hasH2 hf)

theorem weakH1_dense_in_L2 (N : ℕ) : Dense {f : SpatialL2 N | HasH1 f} :=
  (weakH2_dense_in_L2 N).mono (fun _ hf => h2_implies_h1 hf)

def smoothCompactSpinClass (N : ℕ) : Set (SpinSpace N) :=
  {ψ | ∀ σ, ψ σ ∈ smoothCompactClass N}

/-- The finite spin sum also has dense componentwise smooth compact functions.
No intersection-with-fermionic-space density inference is made here. -/
theorem smoothCompactSpinClass_dense (N : ℕ) : Dense (smoothCompactSpinClass N) := by
  have hd : Dense (Set.pi Set.univ (fun _ : SpinConfiguration N => smoothCompactClass N)) :=
    dense_pi Set.univ (fun _ _ => smoothCompactClass_dense N)
  have h := ((PiLp.homeomorph 2 (fun _ : SpinConfiguration N => SpatialL2 N)).isOpenQuotientMap.dense_preimage_iff).mpr hd
  simpa [smoothCompactSpinClass, Set.preimage, PiLp.homeomorph, WithLp.equiv] using h

theorem weakH2_spin_dense_in_L2 (N : ℕ) :
    Dense {ψ : SpinSpace N | ∀ σ, HasH2 (ψ σ)} := by
  apply (smoothCompactSpinClass_dense N).mono
  intro ψ hψ
  change ∀ σ, ψ σ ∈ smoothCompactClass N at hψ
  intro σ
  exact smoothCompactClass_hasH2 (hψ σ)

#print axioms smoothCompactClass_dense
#print axioms exists_smoothCompact_eLp_approx
#print axioms exists_smoothCompact_L2_approx
#print axioms smoothCompactClass_hasH2
#print axioms weakH2_dense_in_L2
#print axioms weakH1_dense_in_L2
#print axioms smoothCompactSpinClass_dense
#print axioms weakH2_spin_dense_in_L2

end TheoremT.Continuum
