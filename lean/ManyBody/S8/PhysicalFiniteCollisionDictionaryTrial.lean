import ManyBody.S8.PhysicalFiniteCollisionDictionary
import ManyBody.S8.Internal.PhysicalFiniteDictionaryTrial

/-! Genuine H2 and scalar Coulomb graph membership of the literal finite
weighted collision dictionary trial. The same original cutoff state precedes
every precision. Trial classes are obtained by subtracting the already-derived
actual weak H2 errors, and the original scalar graph is linear. All comparison
rates refer to that cutoff state and its graph output. No normalization,
global ground approximation or eigenvalue residual is asserted here. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalFiniteCollisionDictionaryTrialData (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (M A R Z E : ℝ) : Prop :=
  ∃n : ℕ,∃cs : Fin n → PhysicalAdmissibleCollisionChart R,
    ∃ρ : Fin n → Configuration 2 → ℝ,
      (∀i,ContDiff ℝ ∞ (ρ i)) ∧ (∀i,HasCompactSupport (ρ i)) ∧
      (∀i,tsupport (ρ i)⊆physicalAdmissibleCollisionPatch M A R (cs i)) ∧
      (∀i x,0≤ρ i x ∧ ρ i x≤1) ∧ (∀x∈tsupport χ,(∑i,ρ i x)=1) ∧
      ∃ms : Fin n → ℕ,∃m : ℕ,∃C : ℝ,1≤C ∧ (∀i,ms i≤m) ∧
      ∃U : SpatialL2 2,∃a : Coordinate 2 → SpatialL2 2,
      ∃b : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃HU : SpatialL2 2,
        U=ᵐ[volume] (fun x => χ x • u x) ∧
        (∀k,WeakPartial U (a k) k) ∧ (∀k l,WeakPartial (a k) (b k l) l) ∧
        HasH2 U ∧ scalarHamiltonianGraph 2 Z U HU ∧ ∀p : ℕ,
        (∀i,(physicalDyadicDistanceSupport
          (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
          (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p).card≤
            (physicalDyadicDistanceOrder m p)^3) ∧
        (∀i,∀α∈physicalDyadicDistanceSupport
          (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
          (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p,
          (∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p ∧
            ∀j : Fin 3,α j<physicalDyadicDistanceOrder m p) ∧
        HasCompactSupport (physicalFiniteCollisionDictionary u χ cs ρ ms p) ∧
        tsupport (physicalFiniteCollisionDictionary u χ cs ρ ms p)⊆tsupport χ ∧
        ∃T : SpatialL2 2,∃dt : Coordinate 2 → SpatialL2 2,
        ∃et : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃HT : SpatialL2 2,
          T=ᵐ[volume] physicalFiniteCollisionDictionary u χ cs ρ ms p ∧
          (∀k,WeakPartial T (dt k) k) ∧ (∀k l,WeakPartial (dt k) (et k l) l) ∧
          HasH2 T ∧ scalarHamiltonianGraph 2 Z T HT ∧
          ‖U-T‖≤(1/2:ℝ)^p*C ∧ (∀k,‖a k-dt k‖≤(1/2:ℝ)^p*C) ∧
          (∀k l,‖b k l-et k l‖≤(1/2:ℝ)^p*C) ∧
          physicalH2ComponentNorm (U-T) (fun k => a k-dt k)
            (fun k l => b k l-et k l)≤(1/2:ℝ)^p*C ∧
          ‖HU-HT‖≤(3+2*(2*|Z|+1))*((1/2:ℝ)^p*C) ∧
          ‖(HU-(E:ℂ) • U)-(HT-(E:ℂ) • T)‖≤
            physicalDistanceGraphCoefficient Z E*((1/2:ℝ)^p*C)

theorem actual_physical_finite_collision_dictionary_trial
    {f : SpatialL2 2} {u : Configuration 2 → ℂ} (hH2 : HasH2 f)
    (hAE : (f : Configuration 2 → ℂ)=ᵐ[volume] u)
    {χ : Configuration 2 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {M A R : ℝ} (Z E : ℝ) (hdata : PhysicalFiniteCollisionDictionaryData u χ M A R) :
    PhysicalFiniteCollisionDictionaryTrialData u χ M A R Z E := by
  obtain ⟨n,cs,ρ,hρ,hcρ,hsρ,hbρ,hpsum,ms,m,C,hC,hms,hp⟩ := hdata
  obtain ⟨U,a,b,HU,hU,ha,hb,hU2,hHU⟩ := physical_compact_cutoff_actual_H2_graph hH2 hAE hχ hc Z
  refine ⟨n,cs,ρ,hρ,hcρ,hsρ,hbρ,hpsum,ms,m,C,hC,hms,U,a,b,HU,hU,ha,hb,hU2,hHU,?_⟩
  intro p
  obtain ⟨hs,hdeg,F,d,e,hF,hd,he,_hF2,h0,h1,h2,hN⟩ := hp p
  have hident : physicalFiniteCollisionDictionary u χ cs ρ ms p=
      (fun x => χ x • ∑i,ρ i x • (physicalDyadicDistancePolynomial
        (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
        (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p
        (physicalCollisionChartDistances (cs i).1 x):ℂ)) := by
    funext x
    simp only [physicalFiniteCollisionDictionary,Finset.smul_sum,mul_smul]
  refine ⟨hs,hdeg,?_,?_,?_⟩
  · rw [hident]
    exact hc.smul_right
  · rw [hident]
    exact tsupport_smul_subset_left _ _
  · exact physical_actual_H2_graph_trial_of_error (E:=E) hU hF ha hb hd he hHU h0 h1 h2 hN

theorem physical_finite_collision_dictionary_trial_actual_error_small
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {M A R Z E : ℝ}
    (hdata : PhysicalFiniteCollisionDictionaryTrialData u χ M A R Z E) :
    ∃n : ℕ,∃cs : Fin n → PhysicalAdmissibleCollisionChart R,
    ∃ρ : Fin n → Configuration 2 → ℝ,∃ms : Fin n → ℕ,
    ∃U : SpatialL2 2,∃a : Coordinate 2 → SpatialL2 2,
    ∃b : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃HU : SpatialL2 2,
      U=ᵐ[volume] (fun x => χ x • u x) ∧
      (∀k,WeakPartial U (a k) k) ∧ (∀k l,WeakPartial (a k) (b k l) l) ∧
      HasH2 U ∧ scalarHamiltonianGraph 2 Z U HU ∧
      ∀η : ℝ,0<η → ∀p0 : ℕ,∃p : ℕ,
      ∃T : SpatialL2 2,∃dt : Coordinate 2 → SpatialL2 2,
      ∃et : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃HT : SpatialL2 2,
        p0≤p ∧ HasCompactSupport (physicalFiniteCollisionDictionary u χ cs ρ ms p) ∧
        tsupport (physicalFiniteCollisionDictionary u χ cs ρ ms p)⊆tsupport χ ∧
        T=ᵐ[volume] physicalFiniteCollisionDictionary u χ cs ρ ms p ∧
        (∀k,WeakPartial T (dt k) k) ∧ (∀k l,WeakPartial (dt k) (et k l) l) ∧
        HasH2 T ∧ scalarHamiltonianGraph 2 Z T HT ∧
        physicalH2ComponentNorm (U-T) (fun k => a k-dt k)
          (fun k l => b k l-et k l)+‖HU-HT‖+
          ‖(HU-(E:ℂ) • U)-(HT-(E:ℂ) • T)‖<η := by
  obtain ⟨n,cs,ρ,_hρ,_hcρ,_hsρ,_hbρ,_hpsum,ms,_m,C,hC,_hms,
    U,a,b,HU,hU,ha,hb,hU2,hHU,hp⟩ := hdata
  refine ⟨n,cs,ρ,ms,U,a,b,HU,hU,ha,hb,hU2,hHU,?_⟩
  intro η hη p0
  let K := physicalDistanceGraphCoefficient Z E
  have hlim : Tendsto (fun p : ℕ => (1+2*K)*((1/2:ℝ)^p*C)) atTop (𝓝 0) := by
    convert ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
      (by norm_num : (1/2:ℝ)<1)).mul_const C).const_mul (1+2*K) using 1
    simp
  obtain ⟨p,hp0,hpη⟩ := ((eventually_ge_atTop p0).and
    (hlim.eventually (gt_mem_nhds hη))).exists
  obtain ⟨_hs,_hdeg,hcompact,hsupport,T,dt,et,HT,hT,hd,he,hT2,hHT,
    _h0,_h1,_h2,hN,hGraph,hShift⟩ := hp p
  let τ := (1/2:ℝ)^p*C
  have hτ : 0≤τ := by dsimp [τ]; have : 0≤C := le_trans (by norm_num) hC; positivity
  have hK : 3+2*(2*|Z|+1)≤K := by
    dsimp [K,physicalDistanceGraphCoefficient]
    exact le_add_of_nonneg_right (abs_nonneg E)
  have hGraph' : ‖HU-HT‖≤K*τ := hGraph.trans (mul_le_mul_of_nonneg_right hK hτ)
  have hsum : physicalH2ComponentNorm (U-T) (fun k => a k-dt k)
      (fun k l => b k l-et k l)+‖HU-HT‖+
      ‖(HU-(E:ℂ) • U)-(HT-(E:ℂ) • T)‖≤(1+2*K)*τ := by
    change physicalH2ComponentNorm (U-T) (fun k => a k-dt k)
      (fun k l => b k l-et k l)≤τ at hN
    change ‖(HU-(E:ℂ) • U)-(HT-(E:ℂ) • T)‖≤K*τ at hShift
    nlinarith
  exact ⟨p,T,dt,et,HT,hp0,hcompact,hsupport,hT,hd,he,hT2,hHT,hsum.trans_lt hpη⟩

#print axioms physical_finite_collision_dictionary_trial_actual_error_small
def PhysicalGroundFiniteCollisionDictionaryTrialData (u : Configuration 2 → ℂ)
    (M A R Z E : ℝ) : Prop :=
  ∀χ : Configuration 2 → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
    (∀x∈tsupport χ,∃c : PhysicalAdmissibleCollisionChart R,
      x∈physicalAdmissibleCollisionPatch M A R c) →
    PhysicalFiniteCollisionDictionaryTrialData u χ M A R Z E

#print axioms actual_physical_finite_collision_dictionary_trial
theorem twoElectron_scalar_ground_finite_collision_dictionary_trial
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        ‖f‖ = 1 ∧ HasH2 f ∧
        scalarHamiltonianGraph 2 Z f
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
        spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
        (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
          TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
        (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
          (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
        LocallyLipschitz u ∧ (f : Configuration 2 → ℂ) =ᵐ[volume] u ∧
        (∀ x, ‖u x‖ ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
        (∀ x, (u x).im = 0) ∧
        (∀ x, u (permuteSpace twoElectronSwap x) = u x) ∧
        (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
          u (configurationRotation 2 Q x) = u x) ∧
        0 < L ∧ 0 < R ∧ LipschitzOnWith L u (ball 0 R) ∧
        0 ≤ M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume ∧
        0 ≤ (((L : ℝ)^2+‖u 0‖^2)*C_H) ∧
        (∃ d : Coordinate 2 → SpatialL2 2,
          ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
          (∀ k, WeakPartial f (d k) k) ∧
          (∀ k l, WeakPartial (d k) (e k l) l) ∧
          ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
              weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxInvariantAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference u ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ t0 : Position, ‖t0‖ = 1 →
            PhysicalKSBoxEvenInvariantAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference u ε (pairKSPhysicalCoordinates X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        0 < physicalKSAnalyticAxisRadius M A ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) → ∀ i : Fin 2,
          PhysicalKSAxisAnalyticDescentData
            ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
              (physicalSpectatorReindexAt i).symm)
            (WithLp.toLp 2 ![0,0,1]) M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖u 0‖^2)*C_H) (physicalKSAnalyticAxisRadius M A)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          PhysicalKSAxisAnalyticDescentData
            ((originScaledDifference u ε ∘ pairKSLift) ∘
              (physicalSpectatorReindexAt (0 : Fin 2)).symm)
            (WithLp.toLp 2 ![0,0,1]) M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖u 0‖^2)*C_H) (physicalKSAnalyticAxisRadius M A)) ∧
        0<pairAmbientDistanceRadius 1 M A ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientPhysicalAnalyticData (originScaledDifference u ε) 1 M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PhysicalPairAmbientReconstruction u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        0<nuclearAmbientRetainedRadius M A ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
            (nuclearAmbientNormalizedBound M A
              (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
          NuclearAmbientDistanceDerivativeData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A) ∧
          PairRealAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearRealAmbientDistanceDerivativeData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearAmbientDistanceTaylorData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) ∧
          NuclearAmbientProfileRealityData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceTaylorData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A) ∧
          PairAmbientProfileRealityData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearRationalDistanceC2ApproximationData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairRationalDistanceC2ApproximationData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearDyadicDistanceTaylorData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairDyadicDistanceTaylorData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearBoundedDyadicDistanceDictionaryData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairBoundedDyadicDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearDyadicRationalDistanceDictionaryData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairDyadicRationalDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ,0<ε → ε≤min 1 (R/4) →
          PhysicalGroundDistanceDyadicH2Data u ε M A) ∧
        (∀ ε : ℝ,0<ε → ε≤min 1 (R/4) →
          PhysicalGroundIndexOneDistanceDyadicH2Data u ε M A) ∧
        PhysicalGroundFiniteCollisionDictionaryData u M A R ∧
        PhysicalGroundFiniteCollisionDictionaryTrialData u M A R Z (variationalGroundEnergy 2 Z).toReal := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hActual,hIndexOne,hFinite⟩ :=
      twoElectron_scalar_ground_finite_collision_dictionary Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hActual,hIndexOne,hFinite,?_⟩
  intro χ hχ hc hcover
  exact actual_physical_finite_collision_dictionary_trial hH2 hAE hχ hc Z
    (variationalGroundEnergy 2 Z).toReal (hFinite χ hχ hc hcover)

#print axioms twoElectron_scalar_ground_finite_collision_dictionary_trial
end ManyBody.S8
