import HardySobolevDensity_v1
import CutoffH1Convergence_v2

/-! Compact smooth approximation of the actual weak H¹ graph, without any
second derivative hypothesis on the input. The approximants lie in actual H².
This is mathematical density, not an executable approximation algorithm. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

private theorem exists_two_stage_h1_approximation
    {ι E : Type*} [Finite ι] [NormedAddCommGroup E]
    (A : ℕ → ι → E) (f : ι → E) (B : ℕ → E → E)
    (hA : ∀ i, Tendsto (fun n => A n i) atTop (𝓝 (f i)))
    (hB : ∀ g, Tendsto (fun m => B m g) atTop (𝓝 g))
    {ε : ℝ} (hε : 0 < ε) : ∃ n m, ∀ i, ‖B m (A n i) - f i‖ < ε := by
  have hh : 0 < ε / 2 := half_pos hε
  have ha : ∀ᶠ n in atTop, ∀ i, ‖A n i - f i‖ < ε / 2 := by
    apply eventually_all.2
    intro i
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.1 (hA i) (ε/2) hh)
  obtain ⟨n, hn⟩ := ha.exists
  have hb : ∀ᶠ m in atTop, ∀ i, ‖B m (A n i) - A n i‖ < ε / 2 := by
    apply eventually_all.2
    intro i
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.1 (hB (A n i)) (ε/2) hh)
  obtain ⟨m, hm⟩ := hb.exists
  refine ⟨n, m, fun i => ?_⟩
  calc
    ‖B m (A n i) - f i‖ ≤ ‖B m (A n i) - A n i‖ + ‖A n i - f i‖ :=
      by simpa only [dist_eq_norm] using dist_triangle (B m (A n i)) (A n i) (f i)
    _ < ε := by linarith [hn i, hm i]

theorem weakH1_smooth_compact_graph_approximation {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Configuration N → ℂ, ∃ g : SpatialL2 N,
      ∃ dg : Coordinate N → SpatialL2 N,
      ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      (g : Configuration N → ℂ) =ᵐ[volume] u ∧
      (∀ k, (dg k : Configuration N → ℂ) =ᵐ[volume] smoothPartial u k) ∧
      (∀ k, WeakPartial g (dg k) k) ∧ HasH2 g ∧
      ‖g-f‖ < ε ∧ ∀ k, ‖dg k-d k‖ < ε := by
  let I := Option (Coordinate N)
  let target : I → SpatialL2 N := fun i => match i with
    | none => f
    | some k => d k
  let A : ℕ → I → SpatialL2 N := fun n i => match i with
    | none => cutoffAt n f
    | some k => cutoffDerivativeAt n f (d k) k
  have hA : ∀ i, Tendsto (fun n => A n i) atTop (𝓝 (target i)) := by
    intro i
    rcases i with _ | k
    · exact cutoffAt_tendsto f
    · exact cutoffDerivativeAt_tendsto f (d k) k
  obtain ⟨n,m,ha⟩ := exists_two_stage_h1_approximation A target
    (fun m g => mollifyLp m g) hA (fun g => mollifyLp_tendsto g) hε
  let u := mollify (mollifierKernel N m) (cutoffAt n f)
  let g := mollifyLp m (cutoffAt n f)
  let dg := fun k => mollifyLp m (cutoffDerivativeAt n f (d k) k)
  have hdc (k : Coordinate N) :
      WeakPartial (cutoffAt n f) (cutoffDerivativeAt n f (d k) k) k :=
    cutoffDerivativeAt_weakPartial (hd k) n
  have hu := mollifyKernel_cutoff_contDiff_compact n m f
  have hgu : (g : Configuration N → ℂ) =ᵐ[volume] u :=
    mollifyLp_ae m (cutoffAt n f)
  have hm : MemLp u 2 volume := hu.1.continuous.memLp_of_hasCompactSupport hu.2
  have hmg : hm.toLp u = g := Lp.ext (hm.coeFn_toLp.trans hgu.symm)
  have hH2 : HasH2 g := by
    rw [← hmg]
    exact compact_c2_hasH2 (hu.1.of_le (by simp)) hu.2 hm
  refine ⟨u,g,dg,hu.1,hu.2,hgu,?_,?_,hH2,?_,?_⟩
  · intro k
    exact mollifyLp_partial_ae (hdc k) m
  · intro k
    exact mollifyLp_weakPartial (hdc k) m
  · exact ha none
  · intro k
    exact ha (some k)

set_option pp.proofs false in
#print weakH1_smooth_compact_graph_approximation
#print axioms weakH1_smooth_compact_graph_approximation

end TheoremT.Continuum
