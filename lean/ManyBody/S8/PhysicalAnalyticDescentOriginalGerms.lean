import ManyBody.S8.Internal.PhysicalAnalyticDescentGermBridge
import ManyBody.S8.CoulombSpinPhysicalOriginalNormFactorial
import ManyBody.S8.Internal.PhysicalCollisionCoordinateScaling
import ManyBody.S8.Internal.PhysicalCollisionGermRescaling
/-! Original physical A-plus-distance-B germs, compatible across positive scales.

The same graph-derived full-spin representative has fixed original-norm
pointwise data at all scales up to1/4. Its literal recovered A/B descents
restrict through actual Euclidean physical coordinates, then the exact
positive-scale identity returns them to the original wavefunction.
The original A is u(0)+epsilon*A_scaled(p/epsilon), while original B is
B_scaled(p/epsilon). Both exact reconstruction and separate real analytic
germ/jet compatibility at the same selected collision point are proved.

The nuclear/pair coordinate maps are genuine compositions of the original
physical maps; the pair convention here is the restored coefficient-1 lift.
Compatibility concerns one fixed selected physical coordinate map. No
transition between different collision types or simultaneous-collision
coverage, effective coefficients, global approximation, or solver is claimed.
-/
noncomputable section
open Filter
open scoped Topology NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

theorem physical_descent_literal_unscaled_collision_germ
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    {f : Space (Fin 3) → ℂ} {ε M A F0 W : ℝ} {t0 tScaled : Position}
    (hε : 0<ε) (hA : 1≤A)
    (hdata : PhysicalKSBoxAnalyticDescentData f
      (fun X T => originScaledDifference g ε (C (X,T))) t0 M A F0 W)
    (hT : ‖tScaled-t0‖ < physicalDescentNeighborhoodRadius M A) :
    AnalyticAt ℝ (physicalRescaledCollisionA ε (g 0) (physicalDescentAReal f t0))
      (0,ε • tScaled) ∧
    AnalyticAt ℝ (physicalRescaledCollisionB ε (physicalDescentBReal f t0))
      (0,ε • tScaled) ∧
    (fun p => physicalRescaledCollisionA ε (g 0) (physicalDescentAReal f t0) p+
      ‖p.1‖ • physicalRescaledCollisionB ε (physicalDescentBReal f t0) p)
      =ᶠ[𝓝 ((0:Position),ε • tScaled)] (fun p => g (C p)) := by
  obtain ⟨ha,hb,heq⟩ := physical_descent_literal_collision_germ hdata hA hT
  have hfun : (fun p : Position × Position => originScaledDifference g ε (C p)) =
      (fun p => (g (C (ε • p))-g (C 0))/(ε:ℂ)) := by
    funext p
    exact originScaledDifference_comp_physical_coordinates g C ε p
  change (fun p => physicalDescentAReal f t0 p+‖p.1‖ • physicalDescentBReal f t0 p)
    =ᶠ[𝓝 ((0:Position),tScaled)] (fun p => originScaledDifference g ε (C p)) at heq
  rw [hfun] at heq
  have hh := physical_collision_germ_rescale (v := fun p => g (C p)) hε ha hb heq
  simpa only [map_zero] using hh

theorem physical_descent_original_overlap_germ_unique
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    {f₀ f₁ : Space (Fin 3) → ℂ} {ε₀ ε₁ M0 A0 F0 W0 M1 A1 F1 W1 : ℝ}
    {t0 t1 tStar : Position}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hA0 : 1≤A0) (hA1 : 1≤A1)
    (hdata0 : PhysicalKSBoxAnalyticDescentData f₀
      (fun X T => originScaledDifference g ε₀ (C (X,T))) t0 M0 A0 F0 W0)
    (hdata1 : PhysicalKSBoxAnalyticDescentData f₁
      (fun X T => originScaledDifference g ε₁ (C (X,T))) t1 M1 A1 F1 W1)
    (hT0 : ‖ε₀⁻¹ • tStar-t0‖ < physicalDescentNeighborhoodRadius M0 A0)
    (hT1 : ‖ε₁⁻¹ • tStar-t1‖ < physicalDescentNeighborhoodRadius M1 A1) :
    (physicalRescaledCollisionA ε₀ (g 0) (physicalDescentAReal f₀ t0)
      =ᶠ[𝓝 ((0:Position),tStar)]
        physicalRescaledCollisionA ε₁ (g 0) (physicalDescentAReal f₁ t1)) ∧
    (physicalRescaledCollisionB ε₀ (physicalDescentBReal f₀ t0)
      =ᶠ[𝓝 ((0:Position),tStar)]
        physicalRescaledCollisionB ε₁ (physicalDescentBReal f₁ t1)) := by
  obtain ⟨ha0,hb0,he0⟩ := physical_descent_literal_unscaled_collision_germ
    g C hε₀ hA0 hdata0 hT0
  obtain ⟨ha1,hb1,he1⟩ := physical_descent_literal_unscaled_collision_germ
    g C hε₁ hA1 hdata1 hT1
  have h0 : ε₀ • (ε₀⁻¹ • tStar)=tStar := by simp [smul_smul,hε₀.ne']
  have h1 : ε₁ • (ε₁⁻¹ • tStar)=tStar := by simp [smul_smul,hε₁.ne']
  rw [h0] at ha0 hb0 he0
  rw [h1] at ha1 hb1 he1
  exact analytic_distance_decomposition_germ_unique tStar ha0 ha1 hb0 hb1
    (he0.trans he1.symm)

def PhysicalOriginalCollisionGerms
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    (f : ℝ → Space (Fin 3) → ℂ) (M A η : ℝ) : Prop :=
  (∀ ε : ℝ, 0<ε → ε≤η → ∀ t0 : Position, ‖t0‖=1 → ∀ tScaled : Position,
    ‖tScaled-t0‖ < physicalDescentNeighborhoodRadius M A →
    AnalyticAt ℝ (physicalRescaledCollisionA ε (g 0) (physicalDescentAReal (f ε) t0))
      (0,ε • tScaled) ∧
    AnalyticAt ℝ (physicalRescaledCollisionB ε (physicalDescentBReal (f ε) t0))
      (0,ε • tScaled) ∧
    (fun p => physicalRescaledCollisionA ε (g 0) (physicalDescentAReal (f ε) t0) p+
      ‖p.1‖ • physicalRescaledCollisionB ε (physicalDescentBReal (f ε) t0) p)
      =ᶠ[𝓝 ((0:Position),ε • tScaled)] (fun p => g (C p))) ∧
  (∀ ε₀ ε₁ : ℝ, 0<ε₀ → ε₀≤η → 0<ε₁ → ε₁≤η →
    ∀ t0 t1 : Position, ‖t0‖=1 → ‖t1‖=1 → ∀ tStar : Position,
    ‖ε₀⁻¹ • tStar-t0‖ < physicalDescentNeighborhoodRadius M A →
    ‖ε₁⁻¹ • tStar-t1‖ < physicalDescentNeighborhoodRadius M A →
    (physicalRescaledCollisionA ε₀ (g 0) (physicalDescentAReal (f ε₀) t0)
      =ᶠ[𝓝 ((0:Position),tStar)]
        physicalRescaledCollisionA ε₁ (g 0) (physicalDescentAReal (f ε₁) t1)) ∧
    (physicalRescaledCollisionB ε₀ (physicalDescentBReal (f ε₀) t0)
      =ᶠ[𝓝 ((0:Position),tStar)]
        physicalRescaledCollisionB ε₁ (physicalDescentBReal (f ε₁) t1)))

theorem physical_original_collision_germs_of_descent
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    (f : ℝ → Space (Fin 3) → ℂ) {M A F0 W η : ℝ} (hA : 1≤A)
    (hdata : ∀ ε : ℝ, 0<ε → ε≤η → ∀ t0 : Position, ‖t0‖=1 →
      PhysicalKSBoxAnalyticDescentData (f ε)
        (fun X T => originScaledDifference g ε (C (X,T))) t0 M A F0 W) :
    PhysicalOriginalCollisionGerms g C f M A η := by
  constructor
  · intro ε hε hlim t0 ht0 tScaled hT
    exact physical_descent_literal_unscaled_collision_germ g C hε hA
      (hdata ε hε hlim t0 ht0) hT
  · intro ε₀ ε₁ hε₀ hlim₀ hε₁ hlim₁ t0 t1 ht0 ht1 tStar hT0 hT1
    exact physical_descent_original_overlap_germ_unique g C hε₀ hε₁ hA hA
      (hdata ε₀ hε₀ hlim₀ t0 ht0) (hdata ε₁ hε₁ hlim₁ t1 ht1) hT0 hT1

theorem nuclear_physical_original_collision_germs
    (g : Configuration 2 → ℂ) (i : Fin 2) {M A F0 W η : ℝ} (hA : 1≤A) (hF0 : 0≤F0)
    (hdata : ∀ ε : ℝ, 0<ε → ε≤η → ∀ t0 : Position, ‖t0‖=1 →
      PhysicalKSBoxPointwiseData
        ((originScaledDifference g ε ∘ nuclearKSLift i) ∘
          (physicalSpectatorReindexAt i).symm) t0 M A F0 W) :
    PhysicalOriginalCollisionGerms g (originalNuclearPhysicalCoordinatesCLM i)
      (fun ε => (originScaledDifference g ε ∘ nuclearKSLift i) ∘
        (physicalSpectatorReindexAt i).symm) M A η := by
  apply physical_original_collision_germs_of_descent g (originalNuclearPhysicalCoordinatesCLM i) _ hA
  intro ε hε hlim t0 ht0
  exact nuclearKSPhysicalAnalyticDescent_data (originScaledDifference g ε) i
    (hdata ε hε hlim t0 ht0) hA hF0

theorem pair_physical_original_collision_germs
    (g : Configuration 2 → ℂ) {M A F0 W η : ℝ} (hA : 1≤A) (hF0 : 0≤F0)
    (hdata : ∀ ε : ℝ, 0<ε → ε≤η → ∀ t0 : Position, ‖t0‖=1 →
      PhysicalKSBoxPointwiseData
        ((originScaledDifference g ε ∘ TheoremT.Continuum.pairKSLift) ∘
          (physicalSpectatorReindexAt (0:Fin 2)).symm) t0 M A F0 W) :
    PhysicalOriginalCollisionGerms g originalPairPhysicalCoordinatesCLM
      (fun ε => (originScaledDifference g ε ∘ TheoremT.Continuum.pairKSLift) ∘
        (physicalSpectatorReindexAt (0:Fin 2)).symm) M A η := by
  apply physical_original_collision_germs_of_descent g originalPairPhysicalCoordinatesCLM _ hA
  intro ε hε hlim t0 ht0
  exact pairKSPhysicalAnalyticDescent_data (originScaledDifference g ε)
    (hdata ε hε hlim t0 ht0) hA hF0

#print axioms physical_descent_literal_unscaled_collision_germ
#print axioms physical_descent_original_overlap_germ_unique
#print axioms physical_original_collision_germs_of_descent
#print axioms nuclear_physical_original_collision_germs
#print axioms pair_physical_original_collision_germs

theorem coulomb_spin_physical_original_norm_collision_germs (Z E : ℝ) :
    ∃ M A : ℝ, ∃ C_L : ℝ≥0, ∃ Csrc CH12 : ℝ,
      1≤M ∧ 1≤A ∧ 0≤Csrc ∧ 0≤CH12 ∧
      ∀ ψ : SpinSpace 2, hamiltonianGraph 2 Z ψ ((E:ℂ) • ψ) →
      ∃ u : SpinConfiguration 2 → Configuration 2 → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ σ, LipschitzOnWith (C_L * ‖ψ‖₊) (u σ) (Metric.ball 0 1)) ∧
        (∀ᵐ x ∂MeasureTheory.volume, ∀ σ, ψ σ x=u σ x) ∧
        (∀ π : Equiv.Perm (Fin 2), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration 2, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient 2 Z E*‖ψ‖) ∧
        ∀ σ : SpinConfiguration 2,
          (∀ i : Fin 2, PhysicalOriginalCollisionGerms (u σ)
            (originalNuclearPhysicalCoordinatesCLM i)
            (fun ε => (originScaledDifference (u σ) ε ∘ nuclearKSLift i) ∘
              (physicalSpectatorReindexAt i).symm) M A (1/4)) ∧
          PhysicalOriginalCollisionGerms (u σ) originalPairPhysicalCoordinatesCLM
            (fun ε => (originScaledDifference (u σ) ε ∘ TheoremT.Continuum.pairKSLift) ∘
              (physicalSpectatorReindexAt (0:Fin 2)).symm) M A (1/4) := by
  obtain ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,hgain⟩ :=
    coulomb_spin_physical_original_norm_pointwise Z E
  refine ⟨M,A,C_L,Csrc,CH12,hM,hA,hsrc,hH12,?_⟩
  intro ψ hgraph
  obtain ⟨u,hu,hLip,hAE,hperm,hbound,hN,hP⟩ := hgain ψ hgraph
  have hF0 : 0≤Csrc*‖ψ‖ := mul_nonneg hsrc (norm_nonneg ψ)
  refine ⟨u,hu,hLip,hAE,hperm,hbound,?_⟩
  intro σ
  constructor
  · intro i
    apply nuclear_physical_original_collision_germs (u σ) i hA hF0
    intro ε hε hlim t0 ht0
    exact hN ε hε hlim σ i t0 ht0
  · apply pair_physical_original_collision_germs (u σ) hA hF0
    intro ε hε hlim t0 ht0
    exact hP ε hε hlim σ t0 ht0

#print axioms coulomb_spin_physical_original_norm_collision_germs

theorem physical_descent_original_overlap_jets_unique
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    {f₀ f₁ : Space (Fin 3) → ℂ} {ε₀ ε₁ M0 A0 F0 W0 M1 A1 F1 W1 : ℝ}
    {t0 t1 tStar : Position}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hA0 : 1≤A0) (hA1 : 1≤A1)
    (hdata0 : PhysicalKSBoxAnalyticDescentData f₀
      (fun X T => originScaledDifference g ε₀ (C (X,T))) t0 M0 A0 F0 W0)
    (hdata1 : PhysicalKSBoxAnalyticDescentData f₁
      (fun X T => originScaledDifference g ε₁ (C (X,T))) t1 M1 A1 F1 W1)
    (hT0 : ‖ε₀⁻¹ • tStar-t0‖ < physicalDescentNeighborhoodRadius M0 A0)
    (hT1 : ‖ε₁⁻¹ • tStar-t1‖ < physicalDescentNeighborhoodRadius M1 A1) (n : ℕ) :
    iteratedFDeriv ℝ n (physicalRescaledCollisionA ε₀ (g 0) (physicalDescentAReal f₀ t0)) (0,tStar) =
      iteratedFDeriv ℝ n (physicalRescaledCollisionA ε₁ (g 0) (physicalDescentAReal f₁ t1)) (0,tStar) ∧
    iteratedFDeriv ℝ n (physicalRescaledCollisionB ε₀ (physicalDescentBReal f₀ t0)) (0,tStar) =
      iteratedFDeriv ℝ n (physicalRescaledCollisionB ε₁ (physicalDescentBReal f₁ t1)) (0,tStar) := by
  obtain ⟨hA,hB⟩ := physical_descent_original_overlap_germ_unique
    g C hε₀ hε₁ hA0 hA1 hdata0 hdata1 hT0 hT1
  exact ⟨(hA.iteratedFDeriv ℝ n).eq_of_nhds,(hB.iteratedFDeriv ℝ n).eq_of_nhds⟩

#print axioms physical_descent_original_overlap_jets_unique
end ManyBody.S8