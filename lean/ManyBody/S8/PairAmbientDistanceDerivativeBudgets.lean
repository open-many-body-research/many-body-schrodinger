import ManyBody.S8.PairDistanceAnalyticReconstruction
import ManyBody.S8.Internal.HolomorphicBallDerivativeBounds
import Mathlib.Tactic
/-! Actual factorial budgets for literal complex pair distance derivatives.

The input data contain the actual normalized pair ambient reconstruction,
not derivative estimates. Bounded holomorphic full distance polydiscs and the
genuine Cauchy operator-norm theorem give all natural derivative orders on
the half polydisc. Subtracting the actual u(0) before estimating removes that
constant at positive orders. The original first profile and full function
carry epsilon*(epsilon^-1)^n; the second carries (epsilon^-1)^n.

Every ordered coordinate word is the actual complex iterated Frechet
derivative applied to coordinate unit vectors in Fin 3 -> Complex. Its
coordinate order may repeat arbitrarily. The ambient space has the actual
Pi maximum norm; no Euclidean norm identification is used.

The principal endpoint assumes only Z>=2, preserves the same normalized
ground graph and physical representative from the original-unscaled pair
reconstruction, and discharges all input analytic/bounded-domain data.
These are derivatives of literal distance profiles, not derivatives in
electron Cartesian coordinates.
-/

set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open scoped ContDiff NNReal BigOperators Topology
open MeasureTheory Metric
namespace ManyBody.S8

theorem holomorphic_constant_add_half_ball_bound
    {f : (Fin 3 → ℂ) → ℂ} {a x : Fin 3 → ℂ} {R C : ℝ} (c : ℂ)
    (hR : 0<R) (hC : 0≤C) (hx : ‖x-a‖<R/2)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hb : ∀ y ∈ ball a R, ‖f y‖≤C)
    (n : ℕ) :
    ‖iteratedFDeriv ℂ n (fun q => c+f q) x‖≤
      (if n=0 then ‖c‖ else 0)+C*(2*Real.exp 1/R)^n*(n.factorial:ℝ) := by
  have hxmem : x∈ball a R := by rw [mem_ball,dist_eq_norm]; linarith
  obtain rfl | hn := eq_or_ne n 0
  · simp only [norm_iteratedFDeriv_zero,ite_true,pow_zero,Nat.factorial_zero,
      Nat.cast_one,mul_one]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) (hb x hxmem))
  have he : iteratedFDeriv ℂ n (fun q => c+f q) x=iteratedFDeriv ℂ n f x := by
    change iteratedFDeriv ℂ n ((fun _ => c)+f) x=_
    rw [iteratedFDeriv_add_apply contDiffAt_const ((hf x hxmem).contDiffAt.of_le le_top)]
    simp only [iteratedFDeriv_const_of_ne hn,Pi.zero_apply,zero_add]
  rw [he,ite_eq_right hn,zero_add]
  exact holomorphic_iteratedFDeriv_half_ball_bound hR hC hx hf hb n

def pairOriginalDistanceCenter (ε : ℝ) : Fin 3 → ℂ := ![(ε:ℂ),(ε:ℂ),0]

theorem pair_original_distance_ball_iff {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (q : Fin 3 → ℂ) :
    q∈ball (pairOriginalDistanceCenter ε) (ε*δ) ↔
      ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ := by
  rw [mem_ball,dist_eq_norm,pi_norm_lt_iff (mul_pos hε hδ)]
  constructor
  · intro h
    exact ⟨by simpa [pairOriginalDistanceCenter] using h 0,
      by simpa [pairOriginalDistanceCenter] using h 1,
      by simpa [pairOriginalDistanceCenter] using h 2⟩
  · rintro ⟨h0,h1,h2⟩ j
    fin_cases j
    · simpa [pairOriginalDistanceCenter] using h0
    · simpa [pairOriginalDistanceCenter] using h1
    · simpa [pairOriginalDistanceCenter] using h2

theorem pair_distance_inverse_scale_mem {ε δ : ℝ} (hε : 0<ε)
    (q : Fin 3 → ℂ)
    (hr : ‖q 0-(ε:ℂ)‖<ε*δ) (hs : ‖q 1-(ε:ℂ)‖<ε*δ)
    (ht : ‖q 2‖<ε*δ) :
    ‖((ε:ℂ)⁻¹ • q) 0-1‖<δ ∧
    ‖((ε:ℂ)⁻¹ • q) 1-1‖<δ ∧ ‖((ε:ℂ)⁻¹ • q) 2‖<δ := by
  have hc : (ε:ℂ)≠0 := by exact_mod_cast hε.ne'
  have hnorm : ‖(ε:ℂ)⁻¹‖=ε⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have h0 : ((ε:ℂ)⁻¹ • q) 0-1=(ε:ℂ)⁻¹*(q 0-(ε:ℂ)) := by
    change (ε:ℂ)⁻¹*q 0-1=(ε:ℂ)⁻¹*(q 0-(ε:ℂ))
    field_simp [hc]
  have h1 : ((ε:ℂ)⁻¹ • q) 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ)) := by
    change (ε:ℂ)⁻¹*q 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ))
    field_simp [hc]
  refine ⟨?_,?_,?_⟩
  · rw [h0,norm_mul,hnorm]; exact (inv_mul_lt_iff₀ hε).mpr hr
  · rw [h1,norm_mul,hnorm]; exact (inv_mul_lt_iff₀ hε).mpr hs
  · change ‖(ε:ℂ)⁻¹*q 2‖<δ
    rw [norm_mul,hnorm]; exact (inv_mul_lt_iff₀ hε).mpr ht

def pairOriginalCenteredA (u : Configuration 2 → ℂ) (ε : ℝ) (q : Fin 3 → ℂ) : ℂ :=
  (ε:ℂ)*pairAmbientPhysicalA (originScaledDifference u ε) 1 ((ε:ℂ)⁻¹ • q)

def pairOriginalCenteredFunction (u : Configuration 2 → ℂ) (ε : ℝ) (q : Fin 3 → ℂ) : ℂ :=
  pairOriginalCenteredA u ε q+q 2*pairOriginalAmbientB u ε q

def PairAmbientDistanceDerivativeData (u : Configuration 2 → ℂ)
    (ε M A F0 W δ : ℝ) : Prop :=
  ∀ q : Fin 3 → ℂ, ‖q-pairOriginalDistanceCenter ε‖<ε*δ/2 → ∀ n : ℕ,
    ‖iteratedFDeriv ℂ n (pairOriginalAmbientA u ε) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℂ n (pairOriginalAmbientB u ε) q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℂ n (pairOriginalAmbientFunction u ε) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        pairAmbientNormalizedBound M A F0 W δ*(2*Real.exp 1/δ)^n*(n.factorial:ℝ)

theorem pair_ambient_distance_derivative_data
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hdata : PairAmbientPhysicalAnalyticData (originScaledDifference u ε) 1 M A F0 W δ) :
    PairAmbientDistanceDerivativeData u ε M A F0 W δ := by
  have hrec := pair_original_ambient_positive_rescaling u hε hδ hdata
  have hanA : AnalyticOnNhd ℂ (pairOriginalCenteredA u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) := by
    intro q hq
    have hdom := (pair_original_distance_ball_iff hε hδ q).mp hq
    have hh : AnalyticAt ℂ (fun p => pairOriginalAmbientA u ε p-u 0) q :=
      (hrec.1 q hdom).sub analyticAt_const
    have he : (fun p => pairOriginalAmbientA u ε p-u 0)=pairOriginalCenteredA u ε := by
      funext p; dsimp [pairOriginalAmbientA,pairOriginalCenteredA]; ring
    rwa [he] at hh
  have hanB : AnalyticOnNhd ℂ (pairOriginalAmbientB u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have hanH : AnalyticOnNhd ℂ (pairOriginalCenteredFunction u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) := by
    intro q hq
    have hcoord : AnalyticAt ℂ (fun p : Fin 3 → ℂ => p 2) q :=
      (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
    exact (hanA q hq).add (hcoord.mul (hanB q hq))
  have hb (q : Fin 3 → ℂ) (hq : q∈ball (pairOriginalDistanceCenter ε) (ε*δ)) :
      ‖pairOriginalCenteredA u ε q‖≤ε*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
      ‖pairOriginalAmbientB u ε q‖≤
        (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
      ‖pairOriginalCenteredFunction u ε q‖≤ε*pairAmbientNormalizedBound M A F0 W δ := by
    obtain ⟨hr,hs,ht⟩ := (pair_original_distance_ball_iff hε hδ q).mp hq
    obtain ⟨hr',hs',ht'⟩ := pair_distance_inverse_scale_mem hε q hr hs ht
    obtain ⟨hbA,hbB⟩ := hdata.2.2.1 _ hr' hs' ht'
    have hAn : ‖pairOriginalCenteredA u ε q‖≤ε*(16*physicalKSPointwiseAmplitude M A F0 W) := by
      dsimp [pairOriginalCenteredA]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
      exact mul_le_mul_of_nonneg_left hbA hε.le
    refine ⟨hAn,hbB,?_⟩
    calc
      _≤‖pairOriginalCenteredA u ε q‖+‖q 2*pairOriginalAmbientB u ε q‖ := norm_add_le _ _
      _=‖pairOriginalCenteredA u ε q‖+‖q 2‖*‖pairOriginalAmbientB u ε q‖ := by rw [norm_mul]
      _≤ε*(16*physicalKSPointwiseAmplitude M A F0 W)+ε*δ*
          ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) :=
        add_le_add hAn (mul_le_mul ht.le hbB (norm_nonneg _) (mul_pos hε hδ).le)
      _=_ := by dsimp [pairAmbientNormalizedBound]; ring
  have hcenter : pairOriginalDistanceCenter ε∈ball (pairOriginalDistanceCenter ε) (ε*δ) :=
    mem_ball_self (mul_pos hε hδ)
  have hCA : 0≤ε*(16*physicalKSPointwiseAmplitude M A F0 W) :=
    (norm_nonneg _).trans (hb _ hcenter).1
  have hCB : 0≤(32*(7*physicalKSPointwiseRate M A)^2)*
      (16*physicalKSPointwiseAmplitude M A F0 W) := (norm_nonneg _).trans (hb _ hcenter).2.1
  have hCH : 0≤ε*pairAmbientNormalizedBound M A F0 W δ :=
    (norm_nonneg _).trans (hb _ hcenter).2.2
  intro q hq n
  have hA := holomorphic_constant_add_half_ball_bound (u 0) (mul_pos hε hδ) hCA hq hanA
    (fun p hp => (hb p hp).1) n
  have hB := holomorphic_iteratedFDeriv_half_ball_bound (mul_pos hε hδ) hCB hq hanB
    (fun p hp => (hb p hp).2.1) n
  have hH := holomorphic_constant_add_half_ball_bound (u 0) (mul_pos hε hδ) hCH hq hanH
    (fun p hp => (hb p hp).2.2) n
  have hfunA : (fun p => u 0+pairOriginalCenteredA u ε p)=pairOriginalAmbientA u ε := rfl
  have hfunH : (fun p => u 0+pairOriginalCenteredFunction u ε p)=pairOriginalAmbientFunction u ε := by
    funext p; dsimp [pairOriginalCenteredFunction,pairOriginalCenteredA,
      pairOriginalAmbientFunction,pairOriginalAmbientA]; ring
  rw [hfunA] at hA
  rw [hfunH] at hH
  have hrate : 2*Real.exp 1/(ε*δ)=ε⁻¹*(2*Real.exp 1/δ) := by field_simp
  rw [hrate,mul_pow] at hA hB hH
  refine ⟨?_,?_,?_⟩
  · convert hA using 1; ring
  · convert hB using 1; ring
  · convert hH using 1; ring

#print axioms holomorphic_constant_add_half_ball_bound
#print axioms pair_ambient_distance_derivative_data

def ambientDistanceWordDerivative (f : (Fin 3 → ℂ) → ℂ)
    {n : ℕ} (w : Fin n → Fin 3) (q : Fin 3 → ℂ) : ℂ :=
  iteratedFDeriv ℂ n f q (fun j => Pi.single (w j) 1)

theorem ambientDistanceWordDerivative_norm_le
    (f : (Fin 3 → ℂ) → ℂ) {n : ℕ} (w : Fin n → Fin 3) (q : Fin 3 → ℂ) :
    ‖ambientDistanceWordDerivative f w q‖≤‖iteratedFDeriv ℂ n f q‖ := by
  have hunit (j : Fin n) : ‖(Pi.single (w j) 1 : Fin 3 → ℂ)‖=1 := by rw [Pi.norm_single,norm_one]
  have hh := (iteratedFDeriv ℂ n f q).le_opNorm (fun j => Pi.single (w j) 1)
  simpa only [ambientDistanceWordDerivative,hunit,Finset.prod_const_one,mul_one] using hh

theorem pair_ambient_distance_coordinate_word_budgets
    {u : Configuration 2 → ℂ} {ε M A F0 W δ : ℝ}
    (hdata : PairAmbientDistanceDerivativeData u ε M A F0 W δ)
    (q : Fin 3 → ℂ) (hq : ‖q-pairOriginalDistanceCenter ε‖<ε*δ/2)
    {n : ℕ} (w : Fin n → Fin 3) :
    ‖ambientDistanceWordDerivative (pairOriginalAmbientA u ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖ambientDistanceWordDerivative (pairOriginalAmbientB u ε) w q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖ambientDistanceWordDerivative (pairOriginalAmbientFunction u ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        pairAmbientNormalizedBound M A F0 W δ*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) :=
  ⟨(ambientDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).1,
    (ambientDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.1,
    (ambientDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.2⟩

#print axioms pair_ambient_distance_coordinate_word_budgets

theorem twoElectron_scalar_ground_pair_ambient_distance_derivative_budgets
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
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδ,hambient,hrec⟩ :=
      twoElectron_scalar_ground_pair_ambient_distance_reconstruction Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδ,hambient,hrec,?_⟩
  intro ε hε hlim
  exact pair_ambient_distance_derivative_data u hε hδ (hambient ε hε hlim)

#print axioms twoElectron_scalar_ground_pair_ambient_distance_derivative_budgets

end ManyBody.S8
