import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
open Filter
open scoped ContDiff Topology BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finiteDim_open_exists_smooth_cutoff_at {Ω : Set (E)}
    (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∀ y ∈ Metric.ball x r, χ y=1 := by
  obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp hΩ x hx
  let b : ContDiffBump x := ⟨ε/4,ε/2,by positivity,by linarith⟩
  refine ⟨ε/4,by positivity,b,b.contDiff,b.hasCompactSupport,?_,?_⟩
  · intro y hy
    apply hs
    have hy' : y ∈ Metric.closedBall x b.rOut := by simpa only [b.tsupport_eq] using hy
    change dist y x ≤ ε/2 at hy'
    exact lt_of_le_of_lt hy' (by linarith)
  · intro y hy
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)


theorem finiteDim_compact_exists_smooth_cutoff {K Ω : Set (E)}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKO : K ⊆ Ω) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ω ∧ ∀ x ∈ K, η =ᶠ[𝓝 x] fun _ => 1 := by
  classical
  have hx (x : K) := finiteDim_open_exists_smooth_cutoff_at hΩ (hKO x.property)
  choose r hr b hb hc hs h1 using hx
  obtain ⟨s,hcover⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : E) (r x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa using hr ⟨x,hx⟩⟩)
  let η : E → ℝ := fun y => 1-∏ x ∈ s,(1-b x y)
  have hη : ContDiff ℝ ∞ η :=
    contDiff_const.sub (contDiff_prod (fun x _ => contDiff_const.sub (hb x)))
  have hsupport : tsupport η ⊆ ⋃ x ∈ s, tsupport (b x) := by
    apply closure_minimal _ (isClosed_biUnion_finset (fun x _ => isClosed_tsupport _))
    intro y hy
    by_contra hn
    have hz (x : K) (hx : x ∈ s) : b x y=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,h⟩⟩))
    have hp : (∏ x ∈ s,(1-b x y))=1 := Finset.prod_eq_one (fun x hx => by rw [hz x hx];ring)
    exact hy (by simp only [η,hp,sub_self])
  have hcompact : IsCompact (⋃ x ∈ s, tsupport (b x)) :=
    s.isCompact_biUnion (fun x _ => (hc x).isCompact)
  refine ⟨η,hη,hcompact.of_isClosed_subset (isClosed_tsupport _) hsupport,?_,?_⟩
  · intro y hy
    obtain ⟨x,hx,hy⟩ := Set.mem_iUnion₂.mp (hsupport hy)
    exact hs x hy
  · intro y hy
    obtain ⟨x,hxs,hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
    filter_upwards [Metric.isOpen_ball.mem_nhds hyx] with z hz
    have hp : (∏ j ∈ s,(1-b j z))=0 := Finset.prod_eq_zero hxs (by rw [h1 x z hz];ring)
    simp only [η,hp,sub_zero]


#print axioms finiteDim_compact_exists_smooth_cutoff
end TheoremT.Continuum
