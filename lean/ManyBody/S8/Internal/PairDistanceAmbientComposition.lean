import PairDistancePolynomialBounds_v1
import PairDistanceRealAlgebra_v1
import PhysicalKSAxisAnalyticDescent_v1
import TwoElectronScalarGroundAxisAnalyticDescent_v1
import PhysicalKSCoordinatesRotation_v1
import ManyBody.S8.Internal.PhysicalDistanceConfigurationOrbit
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic
/-! Actual pair-distance ambient composition and physical reconstruction.

For ambient complex distances q=(r,s,u), the literal principal square-root
branch is tau=sqrt((r^2+s^2)/2-u^2/4). The actual axis coordinates are
z=(r^2-s^2)/(2*tau), w=u^2-z^2 and spectator increment tau-sigma.
The polynomial estimates prove positive real part and keep this branch
holomorphic on a full complex polydisc. They give tau deviation<=3*delta,
|z|<=5*delta and |w|<=26*delta^2; these are derived inequalities.

The real canonical configuration uses the recovered original pair coordinates
center plus/minus half the separation, with principal coefficient 1.
Its three physical distances are proved exactly. The genuine SO(2)-descended
A/B series and physical KS identity reconstruct its physical value; the
degenerate-safe two-reflection orbit theorem extends this to every actual
configuration with those distances.

The final theorem constructs the actual normalized scalar Coulomb ground
state for Z>=2 and one common physical representative. It retains the full
original graph/spectrum/decay/descent conclusions and derives one positive
explicit ambient-distance radius for every admissible physical scale.
No transformed derivative, arbitrary square-root branch, assumed physical
distance identity or assumed analytic data is a premise of that endpoint.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators Topology
namespace ManyBody.S8
open TheoremT.Continuum

def pairAmbientCenterPolynomial (q : Fin 3 → ℂ) : ℂ :=
  (q 0^2+q 1^2)/2-q 2^2/4
def pairAmbientTau (q : Fin 3 → ℂ) : ℂ :=
  Complex.sqrt (pairAmbientCenterPolynomial q)
def pairAmbientAxisZ (q : Fin 3 → ℂ) : ℂ :=
  (q 0^2-q 1^2)/(2*pairAmbientTau q)
def pairAmbientAxisW (q : Fin 3 → ℂ) : ℂ :=
  q 2^2-pairAmbientAxisZ q^2
def pairAmbientDistanceInput (σ : ℝ) (q : Fin 3 → ℂ) : ℂ × (Fin 2 → ℂ) :=
  (pairAmbientAxisW q,![pairAmbientAxisZ q,pairAmbientTau q-(σ:ℂ)])

theorem pairAmbientTau_sq (q : Fin 3 → ℂ) :
    pairAmbientTau q^2=pairAmbientCenterPolynomial q := by
  exact Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ)≠0)

theorem pairAmbientTau_re_nonneg (q : Fin 3 → ℂ) : 0≤(pairAmbientTau q).re := by
  dsimp [pairAmbientTau,Complex.sqrt]
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem pairAmbientCenterPolynomial_analyticAt (q : Fin 3 → ℂ) :
    AnalyticAt ℂ pairAmbientCenterPolynomial q := by
  have h0 := (ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  have h1 := (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  have h2 := (ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  exact (((h0.pow 2).add (h1.pow 2)).mul analyticAt_const).sub
    ((h2.pow 2).mul analyticAt_const)

theorem pairAmbientCenterPolynomial_re_pos {σ δ : ℝ} (hσ : 0<σ) (hδ : 0≤δ)
    (hsmall : δ≤σ/16) (q : Fin 3 → ℂ)
    (hr : ‖q 0-(σ:ℂ)‖≤δ) (hs : ‖q 1-(σ:ℂ)‖≤δ) (hu : ‖q 2‖≤δ) :
    0<(pairAmbientCenterPolynomial q).re := by
  have hb := pair_distance_center_polynomial_bound hσ hδ hsmall hr hs hu
  have ha := Complex.abs_re_le_norm (pairAmbientCenterPolynomial q-(σ:ℂ)^2)
  have he : (pairAmbientCenterPolynomial q-(σ:ℂ)^2).re =
      (pairAmbientCenterPolynomial q).re-σ^2 := by simp [pow_two]
  rw [he] at ha
  have hn := neg_abs_le ((pairAmbientCenterPolynomial q).re-σ^2)
  have hm := mul_le_mul_of_nonneg_left hsmall hσ.le
  change ‖pairAmbientCenterPolynomial q-(σ:ℂ)^2‖≤3*σ*δ at hb
  nlinarith [sq_pos_of_pos hσ]

theorem pairAmbientTau_analyticAt (q : Fin 3 → ℂ)
    (hq : 0<(pairAmbientCenterPolynomial q).re) :
    AnalyticAt ℂ pairAmbientTau q := by
  exact (pairAmbientCenterPolynomial_analyticAt q).cpow analyticAt_const (Or.inl hq)

theorem pairAmbientTau_deviation_bound {σ δ : ℝ} (hσ : 0<σ) (hδ : 0≤δ)
    (hsmall : δ≤σ/16) (q : Fin 3 → ℂ)
    (hr : ‖q 0-(σ:ℂ)‖≤δ) (hs : ‖q 1-(σ:ℂ)‖≤δ) (hu : ‖q 2‖≤δ) :
    ‖pairAmbientTau q-(σ:ℂ)‖≤3*δ := by
  have hb := pair_distance_center_polynomial_bound hσ hδ hsmall hr hs hu
  change ‖pairAmbientCenterPolynomial q-(σ:ℂ)^2‖≤3*σ*δ at hb
  have hsumnorm : σ≤‖pairAmbientTau q+(σ:ℂ)‖ := by
    have hre := pairAmbientTau_re_nonneg q
    have hh := Complex.re_le_norm (pairAmbientTau q+(σ:ℂ))
    simp only [Complex.add_re,Complex.ofReal_re] at hh
    linarith
  have he : (pairAmbientTau q-(σ:ℂ))*(pairAmbientTau q+(σ:ℂ)) =
      pairAmbientCenterPolynomial q-(σ:ℂ)^2 := by
    rw [←pairAmbientTau_sq q]
    ring
  have hn : ‖pairAmbientTau q-(σ:ℂ)‖*‖pairAmbientTau q+(σ:ℂ)‖ =
      ‖pairAmbientCenterPolynomial q-(σ:ℂ)^2‖ := by rw [←norm_mul,he]
  have hm := mul_le_mul_of_nonneg_left hsumnorm (norm_nonneg (pairAmbientTau q-(σ:ℂ)))
  nlinarith

theorem pairAmbientDistanceInput_bounds {σ δ : ℝ} (hσ : 0<σ) (hδ : 0≤δ)
    (hsmall : δ≤σ/16) (q : Fin 3 → ℂ)
    (hr : ‖q 0-(σ:ℂ)‖≤δ) (hs : ‖q 1-(σ:ℂ)‖≤δ) (hu : ‖q 2‖≤δ) :
    0<(pairAmbientCenterPolynomial q).re ∧ σ/2≤‖pairAmbientTau q‖ ∧
      ‖pairAmbientTau q-(σ:ℂ)‖≤3*δ ∧
      ‖pairAmbientAxisZ q‖≤5*δ ∧ ‖pairAmbientAxisW q‖≤26*δ^2 := by
  have hd := pairAmbientTau_deviation_bound hσ hδ hsmall q hr hs hu
  have hl : σ/2≤‖pairAmbientTau q‖ := by
    have hh := norm_sub_norm_le (σ:ℂ) (pairAmbientTau q)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ,norm_sub_rev] at hh
    linarith
  have hz := pair_distance_axis_quotient_bound hσ hδ hsmall hr hs hl
  have hw := pair_distance_transverse_polynomial_bound hδ hu hz
  exact ⟨pairAmbientCenterPolynomial_re_pos hσ hδ hsmall q hr hs hu,hl,hd,hz,hw⟩

theorem pairAmbientDistanceInput_analyticAt (σ : ℝ) (q : Fin 3 → ℂ)
    (hP : 0<(pairAmbientCenterPolynomial q).re) (hτ : pairAmbientTau q≠0) :
    AnalyticAt ℂ (pairAmbientDistanceInput σ) q := by
  have h0 := (ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  have h1 := (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  have h2 := (ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  have ht := pairAmbientTau_analyticAt q hP
  have hz : AnalyticAt ℂ pairAmbientAxisZ q :=
    ((h0.pow 2).sub (h1.pow 2)).div (analyticAt_const.mul ht) (mul_ne_zero (by norm_num) hτ)
  have hw : AnalyticAt ℂ pairAmbientAxisW q := (h2.pow 2).sub (hz.pow 2)
  apply hw.prod
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hz
  · exact ht.sub analyticAt_const

theorem pairAmbientDistanceInput_domain {σ δ h : ℝ} (hσ : 0<σ) (hh : 0<h)
    (hδσ : δ≤σ/16) (hδh : δ≤h/8) (q : Fin 3 → ℂ)
    (hr : ‖q 0-(σ:ℂ)‖<δ) (hs : ‖q 1-(σ:ℂ)‖<δ) (hu : ‖q 2‖<δ) :
    0<(pairAmbientCenterPolynomial q).re ∧ pairAmbientTau q≠0 ∧
      ‖(pairAmbientDistanceInput σ q).1‖<h^2 ∧
      ‖(pairAmbientDistanceInput σ q).2‖<h := by
  have hδ : 0≤δ := (norm_nonneg _).trans hr.le
  obtain ⟨hP,ht,hd,hz,hw⟩ := pairAmbientDistanceInput_bounds hσ hδ hδσ q hr.le hs.le hu.le
  have hne : pairAmbientTau q≠0 := norm_ne_zero_iff.mp (by linarith : ‖pairAmbientTau q‖≠0)
  have hsq : δ^2≤(h/8)^2 := (sq_le_sq₀ hδ (by positivity)).mpr hδh
  refine ⟨hP,hne,hw.trans_lt (by nlinarith [sq_pos_of_pos hh]),?_⟩
  apply (pi_norm_lt_iff hh).mpr
  intro i
  fin_cases i
  · exact hz.trans_lt (by linarith)
  · exact hd.trans_lt (by linarith)

theorem pair_ambient_distance_composition_on_polydisc
    {G : (ℂ × (Fin 2 → ℂ)) → ℂ} {σ δ h M : ℝ}
    (hσ : 0<σ) (hh : 0<h) (hδσ : δ≤σ/16) (hδh : δ≤h/8)
    (hG : AnalyticOnNhd ℂ G {z | ‖z.1‖<h^2 ∧ ‖z.2‖<h})
    (hbound : ∀ w s, ‖w‖<h^2 → ‖s‖<h → ‖G (w,s)‖≤M) :
    AnalyticOnNhd ℂ (G ∘ pairAmbientDistanceInput σ)
      {q | ‖q 0-(σ:ℂ)‖<δ ∧ ‖q 1-(σ:ℂ)‖<δ ∧ ‖q 2‖<δ} ∧
    ∀ q, ‖q 0-(σ:ℂ)‖<δ → ‖q 1-(σ:ℂ)‖<δ → ‖q 2‖<δ →
      ‖G (pairAmbientDistanceInput σ q)‖≤M := by
  constructor
  · intro q hq
    obtain ⟨hP,hne,hw,hs⟩ := pairAmbientDistanceInput_domain hσ hh hδσ hδh q hq.1 hq.2.1 hq.2.2
    exact AnalyticAt.comp (f := pairAmbientDistanceInput σ) (g := G)
      (hG _ ⟨hw,hs⟩) (pairAmbientDistanceInput_analyticAt σ q hP hne)
  · intro q hr hs hu
    obtain ⟨hP,hne,hw,hs⟩ := pairAmbientDistanceInput_domain hσ hh hδσ hδh q hr hs hu
    exact hbound _ _ hw hs


def pairAmbientRealCenterPolynomial (q : Fin 3 → ℝ) : ℝ :=
  (q 0^2+q 1^2)/2-q 2^2/4
def pairAmbientRealTau (q : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (pairAmbientRealCenterPolynomial q)
def pairAmbientRealAxisZ (q : Fin 3 → ℝ) : ℝ :=
  (q 0^2-q 1^2)/(2*pairAmbientRealTau q)
def pairAmbientRealAxisW (q : Fin 3 → ℝ) : ℝ :=
  q 2^2-pairAmbientRealAxisZ q^2
def pairAmbientCanonicalX (q : Fin 3 → ℝ) : Position :=
  WithLp.toLp 2 ![Real.sqrt (pairAmbientRealAxisW q),0,pairAmbientRealAxisZ q]
def pairAmbientCanonicalT (q : Fin 3 → ℝ) : Position :=
  WithLp.toLp 2 ![0,0,pairAmbientRealTau q]
def pairAmbientCanonicalConfiguration (q : Fin 3 → ℝ) : Configuration 2 :=
  pairKSPhysicalCoordinates (pairAmbientCanonicalX q) (pairAmbientCanonicalT q)

theorem pairAmbientCenterPolynomial_ofReal (q : Fin 3 → ℝ) :
    pairAmbientCenterPolynomial (fun i => (q i : ℂ)) =
      (pairAmbientRealCenterPolynomial q : ℂ) := by
  simp [pairAmbientCenterPolynomial,pairAmbientRealCenterPolynomial]

theorem pairAmbientTau_ofReal (q : Fin 3 → ℝ)
    (hP : 0≤pairAmbientRealCenterPolynomial q) :
    pairAmbientTau (fun i => (q i : ℂ)) = (pairAmbientRealTau q : ℂ) := by
  rw [pairAmbientTau,pairAmbientCenterPolynomial_ofReal]
  simp [Complex.sqrt_eq_real_add_ite,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hP,pairAmbientRealTau]

theorem pairAmbientAxisZ_ofReal (q : Fin 3 → ℝ)
    (hP : 0≤pairAmbientRealCenterPolynomial q) :
    pairAmbientAxisZ (fun i => (q i : ℂ)) = (pairAmbientRealAxisZ q : ℂ) := by
  simp [pairAmbientAxisZ,pairAmbientRealAxisZ,pairAmbientTau_ofReal q hP]

theorem pairAmbientAxisW_ofReal (q : Fin 3 → ℝ)
    (hP : 0≤pairAmbientRealCenterPolynomial q) :
    pairAmbientAxisW (fun i => (q i : ℂ)) = (pairAmbientRealAxisW q : ℂ) := by
  simp [pairAmbientAxisW,pairAmbientRealAxisW,pairAmbientAxisZ_ofReal q hP]

theorem pairAmbientRealCenterPolynomial_pos {σ δ : ℝ} (hσ : 0<σ) (hδ : 0≤δ)
    (hsmall : δ≤σ/16) (q : Fin 3 → ℝ)
    (hr : |q 0-σ|≤δ) (hs : |q 1-σ|≤δ) (hu : |q 2|≤δ) :
    0<pairAmbientRealCenterPolynomial q := by
  have hrC : ‖(q 0:ℂ)-(σ:ℂ)‖≤δ := by simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hr
  have hsC : ‖(q 1:ℂ)-(σ:ℂ)‖≤δ := by simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hs
  have huC : ‖(q 2:ℂ)‖≤δ := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hu
  have hp := pairAmbientCenterPolynomial_re_pos hσ hδ hsmall
    (fun i => (q i : ℂ)) hrC hsC huC
  rwa [pairAmbientCenterPolynomial_ofReal,Complex.ofReal_re] at hp

theorem pairAmbientRealAxisW_nonneg (q : Fin 3 → ℝ)
    (hr : 0≤q 0) (hs : 0≤q 1) (hu : 0≤q 2)
    (hlow : |q 0-q 1|≤q 2) (hhigh : q 2≤q 0+q 1)
    (hP : 0<pairAmbientRealCenterPolynomial q) :
    0≤pairAmbientRealAxisW q := by
  exact pair_distance_real_transverse_nonneg hr hs hu hlow hhigh
    (Real.sqrt_pos.mpr hP) (Real.sq_sqrt hP.le)

theorem pairAmbientCanonicalX_norm (q : Fin 3 → ℝ)
    (hu : 0≤q 2) (hw : 0≤pairAmbientRealAxisW q) :
    ‖pairAmbientCanonicalX q‖=q 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) hu).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pairAmbientCanonicalX,Fin.sum_univ_three]
  rw [Real.sq_sqrt hw]
  dsimp [pairAmbientRealAxisW]
  ring

theorem pairAmbientCanonical_distances (q : Fin 3 → ℝ)
    (hr : 0≤q 0) (hs : 0≤q 1) (hu : 0≤q 2)
    (hlow : |q 0-q 1|≤q 2) (hhigh : q 2≤q 0+q 1)
    (hP : 0<pairAmbientRealCenterPolynomial q) :
    ‖position (pairAmbientCanonicalConfiguration q) 0‖=q 0 ∧
      ‖position (pairAmbientCanonicalConfiguration q) 1‖=q 1 ∧
      ‖position (pairAmbientCanonicalConfiguration q) 0-
        position (pairAmbientCanonicalConfiguration q) 1‖=q 2 := by
  have hτ : 0<pairAmbientRealTau q := Real.sqrt_pos.mpr hP
  have hτsq : pairAmbientRealTau q^2=pairAmbientRealCenterPolynomial q := Real.sq_sqrt hP.le
  have hw := pairAmbientRealAxisW_nonneg q hr hs hu hlow hhigh hP
  have hrec := pair_distance_real_reconstruction hτ.ne' hτsq
  change pairAmbientRealAxisW q/4+(pairAmbientRealTau q+pairAmbientRealAxisZ q/2)^2=q 0^2 ∧
    pairAmbientRealAxisW q/4+(pairAmbientRealTau q-pairAmbientRealAxisZ q/2)^2=q 1^2 ∧
    pairAmbientRealAxisW q+pairAmbientRealAxisZ q^2=q 2^2 at hrec
  have h0 : ‖position (pairAmbientCanonicalConfiguration q) 0‖^2=q 0^2 := by
    rw [pairAmbientCanonicalConfiguration,position_pairKSPhysicalCoordinates_zero,
      EuclideanSpace.real_norm_sq_eq]
    simp [pairAmbientCanonicalX,pairAmbientCanonicalT,Fin.sum_univ_three,PiLp.smul_apply]
    nlinarith [Real.sq_sqrt hw,hrec.1]
  have h1 : ‖position (pairAmbientCanonicalConfiguration q) 1‖^2=q 1^2 := by
    rw [pairAmbientCanonicalConfiguration,position_pairKSPhysicalCoordinates_one,
      EuclideanSpace.real_norm_sq_eq]
    simp [pairAmbientCanonicalX,pairAmbientCanonicalT,Fin.sum_univ_three,PiLp.smul_apply]
    nlinarith [Real.sq_sqrt hw,hrec.2.1]
  have hdiff : position (pairAmbientCanonicalConfiguration q) 0-
      position (pairAmbientCanonicalConfiguration q) 1=pairAmbientCanonicalX q := by
    rw [pairAmbientCanonicalConfiguration,position_pairKSPhysicalCoordinates_zero,
      position_pairKSPhysicalCoordinates_one]
    module
  exact ⟨(sq_eq_sq₀ (norm_nonneg _) hr).mp h0,
    (sq_eq_sq₀ (norm_nonneg _) hs).mp h1,
    by rw [hdiff]; exact pairAmbientCanonicalX_norm q hu hw⟩


def pairAmbientAxisCenter (σ : ℝ) : Position := WithLp.toLp 2 ![0,0,σ]
def pairAmbientCanonicalAxisArgument (σ : ℝ) (q : Fin 3 → ℝ) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![(Real.sqrt (pairAmbientRealAxisW q):ℂ),0],
    ![(pairAmbientRealAxisZ q:ℂ),(pairAmbientRealTau q-σ:ℂ)])

def pairAmbientPhysicalTaylorRadius (M A : ℝ) : ℝ :=
  min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹

def pairAmbientPhysicalLift (g : Configuration 2 → ℂ) :
    TheoremT.Continuum.WeakGrushin.Space (Fin 3) → ℂ :=
  ((g ∘ TheoremT.Continuum.pairKSLift) ∘ (physicalSpectatorReindexAt (0:Fin 2)).symm)

def pairAmbientPhysicalA (g : Configuration 2 → ℂ) (σ : ℝ) : (Fin 3 → ℂ) → ℂ :=
  physicalKSAxisDescendedA (pairAmbientPhysicalLift g) (pairAmbientAxisCenter σ) ∘
    pairAmbientDistanceInput σ
def pairAmbientPhysicalB (g : Configuration 2 → ℂ) (σ : ℝ) : (Fin 3 → ℂ) → ℂ :=
  physicalKSAxisDescendedB (pairAmbientPhysicalLift g) (pairAmbientAxisCenter σ) ∘
    pairAmbientDistanceInput σ

theorem pairAmbientCanonicalT_sub_norm (σ : ℝ) (q : Fin 3 → ℝ) :
    ‖pairAmbientCanonicalT q-pairAmbientAxisCenter σ‖=
      |pairAmbientRealTau q-σ| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq,pairAmbientCanonicalT,pairAmbientAxisCenter,
    Fin.sum_univ_three]

theorem pairAmbientCanonicalAxisArgument_map (σ : ℝ) (q : Fin 3 → ℝ) :
    physicalKSComplexAxisMap (pairAmbientCanonicalAxisArgument σ q) =
      Sum.elim (fun i => (pairAmbientCanonicalX q i:ℂ))
        (fun i => ((pairAmbientCanonicalT q-pairAmbientAxisCenter σ) i:ℂ)) := by
  funext j
  cases j with
  | inl i => fin_cases i <;> simp [physicalKSComplexAxisMap,physicalComplexAxisSlice,
      pairAmbientCanonicalAxisArgument,pairAmbientCanonicalX]
  | inr i => fin_cases i <;> simp [physicalKSComplexAxisMap,physicalComplexAxisSlice,
      pairAmbientCanonicalAxisArgument,pairAmbientCanonicalT,pairAmbientAxisCenter]

theorem pairAmbientCanonicalAxisArgument_input (σ : ℝ) (q : Fin 3 → ℝ)
    (hP : 0≤pairAmbientRealCenterPolynomial q) (hw : 0≤pairAmbientRealAxisW q) :
    ((pairAmbientCanonicalAxisArgument σ q).1 0^2+
        (pairAmbientCanonicalAxisArgument σ q).1 1^2,
      (pairAmbientCanonicalAxisArgument σ q).2) =
      pairAmbientDistanceInput σ (fun i => (q i:ℂ)) := by
  apply Prod.ext
  · simp [pairAmbientCanonicalAxisArgument,pairAmbientDistanceInput,
      pairAmbientAxisW_ofReal q hP,←Complex.ofReal_pow,Real.sq_sqrt hw]
  · ext i
    fin_cases i <;> simp [pairAmbientCanonicalAxisArgument,pairAmbientDistanceInput,
      pairAmbientAxisZ_ofReal q hP,pairAmbientTau_ofReal q hP]

theorem pairAmbientCanonical_identity
    (g : Configuration 2 → ℂ) {σ δ M A F0 W h : ℝ}
    (hσ : 0<σ) (hh : 0<h) (hδσ : δ≤σ/16) (hδh : δ≤h/8)
    (hδX : δ≤min ((pairAmbientPhysicalTaylorRadius M A)^2)
      (32*(7*physicalKSPointwiseRate M A)^2)⁻¹)
    (hδT : δ≤pairAmbientPhysicalTaylorRadius M A/4)
    (hpoint : PhysicalKSBoxPointwiseData (pairAmbientPhysicalLift g)
      (pairAmbientAxisCenter σ) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hrotation : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      g (configurationRotation 2 Q x)=g x)
    (hradius : h≤physicalKSAnalyticAxisRadius M A)
    (q : Fin 3 → ℝ) (hr : 0≤q 0) (hs : 0≤q 1) (hu : 0≤q 2)
    (hlow : |q 0-q 1|≤q 2) (hhigh : q 2≤q 0+q 1)
    (hqr : |q 0-σ|<δ) (hqs : |q 1-σ|<δ) (hqu : q 2<δ) :
    g (pairAmbientCanonicalConfiguration q) =
      pairAmbientPhysicalA g σ (fun i => (q i:ℂ))+
        (q 2:ℂ)*pairAmbientPhysicalB g σ (fun i => (q i:ℂ)) := by
  have hδ : 0≤δ := (abs_nonneg _).trans hqr.le
  have hqabs : |q 2|<δ := by rwa [abs_of_nonneg hu]
  have hrC : ‖(q 0:ℂ)-(σ:ℂ)‖<δ := by
    simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hqr
  have hsC : ‖(q 1:ℂ)-(σ:ℂ)‖<δ := by
    simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hqs
  have huC : ‖(q 2:ℂ)‖<δ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hqabs
  have hP := pairAmbientRealCenterPolynomial_pos hσ hδ hδσ q hqr.le hqs.le hqabs.le
  have hw := pairAmbientRealAxisW_nonneg q hr hs hu hlow hhigh hP
  have hinput := pairAmbientCanonicalAxisArgument_input σ q hP.le hw
  obtain ⟨_,_,hW,hS⟩ := pairAmbientDistanceInput_domain hσ hh hδσ hδh
    (fun i => (q i:ℂ)) hrC hsC huC
  have hWreal : pairAmbientRealAxisW q<h^2 := by
    change ‖pairAmbientAxisW (fun i => (q i:ℂ))‖<h^2 at hW
    simpa only [pairAmbientAxisW_ofReal q hP.le,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hw] using hW
  have hx : ∀ i : Fin 2, ‖(pairAmbientCanonicalAxisArgument σ q).1 i‖<h := by
    intro i
    fin_cases i
    · have hsqrt : Real.sqrt (pairAmbientRealAxisW q)<h := by
        nlinarith [Real.sq_sqrt hw,Real.sqrt_nonneg (pairAmbientRealAxisW q)]
      simpa [pairAmbientCanonicalAxisArgument,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt
    · simpa [pairAmbientCanonicalAxisArgument] using hh
  have hsaxis : ‖(pairAmbientCanonicalAxisArgument σ q).2‖<h := by
    rw [←hinput] at hS
    exact hS
  have hwaxis : ‖(pairAmbientCanonicalAxisArgument σ q).1 0^2+
      (pairAmbientCanonicalAxisArgument σ q).1 1^2‖<h^2 := by
    rw [←hinput] at hW
    exact hW
  have haxis := pairKSPhysicalAxisAnalyticDescent_data g hpoint hA hF0 hrotation hh hradius
  have haxisA := haxis.1.2.2 (pairAmbientCanonicalAxisArgument σ q) hx hsaxis hwaxis
  have haxisB := haxis.2.2.2 (pairAmbientCanonicalAxisArgument σ q) hx hsaxis hwaxis
  dsimp only at haxisA haxisB
  rw [pairAmbientCanonicalAxisArgument_map,hinput] at haxisA haxisB
  have hbox := pairKSPhysicalAnalyticDescent_data g hpoint hA hF0
  obtain ⟨r,hpos,he,hphysical⟩ := hbox.2.2.2
  have hnorm := pairAmbientCanonicalX_norm q hu hw
  have hX : ‖pairAmbientCanonicalX q‖<min ((r:ℝ)^2)
      (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ := by
    rw [hnorm,he]
    exact hqu.trans_le hδX
  have hd := pairAmbientTau_deviation_bound hσ hδ hδσ (fun i => (q i:ℂ))
    hrC.le hsC.le huC.le
  have hdreal : |pairAmbientRealTau q-σ|≤3*δ := by
    simpa only [pairAmbientTau_ofReal q hP.le,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs] using hd
  have hT : ‖pairAmbientCanonicalT q-pairAmbientAxisCenter σ‖<(r:ℝ) := by
    rw [pairAmbientCanonicalT_sub_norm]
    have hrpos : 0<pairAmbientPhysicalTaylorRadius M A := by
      change 0<min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹
      have hrate := physicalKSPointwiseRate_pos (M:=M) hA
      positivity
    rw [he]
    change |pairAmbientRealTau q-σ|<pairAmbientPhysicalTaylorRadius M A
    linarith
  have hid := hphysical (pairAmbientCanonicalX q)
    (pairAmbientCanonicalT q-pairAmbientAxisCenter σ) hX hT
  have hcenter : pairAmbientAxisCenter σ+
      (pairAmbientCanonicalT q-pairAmbientAxisCenter σ)=pairAmbientCanonicalT q := by abel
  rw [hcenter] at hid
  simp only [pairAmbientAxisCenter] at haxisA haxisB hid
  rw [haxisA,haxisB,hnorm] at hid
  exact hid


def pairAmbientDistanceRadius (σ M A : ℝ) : ℝ :=
  min (σ/16) (min (physicalKSAnalyticAxisRadius M A/8)
    (min (min ((pairAmbientPhysicalTaylorRadius M A)^2)
      (32*(7*physicalKSPointwiseRate M A)^2)⁻¹)
      (pairAmbientPhysicalTaylorRadius M A/4)))

theorem pairAmbientDistanceRadius_pos {σ M A : ℝ} (hσ : 0<σ) (hA : 1≤A) :
    0<pairAmbientDistanceRadius σ M A := by
  have hrate := physicalKSPointwiseRate_pos (M:=M) hA
  have haxis := physicalKSAnalyticAxisRadius_pos (M:=M) hA
  have hR : 0<pairAmbientPhysicalTaylorRadius M A := by
    dsimp [pairAmbientPhysicalTaylorRadius]
    positivity
  dsimp [pairAmbientDistanceRadius]
  positivity

theorem pairAmbientDistanceRadius_le (σ M A : ℝ) :
    pairAmbientDistanceRadius σ M A≤σ/16 ∧
      pairAmbientDistanceRadius σ M A≤physicalKSAnalyticAxisRadius M A/8 ∧
      pairAmbientDistanceRadius σ M A≤min ((pairAmbientPhysicalTaylorRadius M A)^2)
        (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ ∧
      pairAmbientDistanceRadius σ M A≤pairAmbientPhysicalTaylorRadius M A/4 := by
  dsimp [pairAmbientDistanceRadius]
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

def pairAmbientPhysicalDistances (x : Configuration 2) : Fin 3 → ℝ :=
  ![‖position x 0‖,‖position x 1‖,‖position x 0-position x 1‖]

def PairAmbientPhysicalAnalyticData (g : Configuration 2 → ℂ)
    (σ M A F0 W δ : ℝ) : Prop :=
  AnalyticOnNhd ℂ (pairAmbientPhysicalA g σ)
    {q | ‖q 0-(σ:ℂ)‖<δ ∧ ‖q 1-(σ:ℂ)‖<δ ∧ ‖q 2‖<δ} ∧
  AnalyticOnNhd ℂ (pairAmbientPhysicalB g σ)
    {q | ‖q 0-(σ:ℂ)‖<δ ∧ ‖q 1-(σ:ℂ)‖<δ ∧ ‖q 2‖<δ} ∧
  (∀ q : Fin 3 → ℂ, ‖q 0-(σ:ℂ)‖<δ → ‖q 1-(σ:ℂ)‖<δ → ‖q 2‖<δ →
    ‖pairAmbientPhysicalA g σ q‖≤16*physicalKSPointwiseAmplitude M A F0 W ∧
    ‖pairAmbientPhysicalB g σ q‖≤
      (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) ∧
  (∀ x : Configuration 2, |‖position x 0‖-σ|<δ → |‖position x 1‖-σ|<δ →
    ‖position x 0-position x 1‖<δ →
    g x=pairAmbientPhysicalA g σ (fun i => (pairAmbientPhysicalDistances x i:ℂ))+
      (‖position x 0-position x 1‖:ℂ)*
        pairAmbientPhysicalB g σ (fun i => (pairAmbientPhysicalDistances x i:ℂ)))

theorem pairAmbientPhysicalAnalytic_data
    (g : Configuration 2 → ℂ) {σ M A F0 W : ℝ} (hσ : 0<σ)
    (hpoint : PhysicalKSBoxPointwiseData (pairAmbientPhysicalLift g)
      (pairAmbientAxisCenter σ) M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0)
    (hrotation : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      g (configurationRotation 2 Q x)=g x) :
    PairAmbientPhysicalAnalyticData g σ M A F0 W (pairAmbientDistanceRadius σ M A) := by
  have hh := physicalKSAnalyticAxisRadius_pos (M:=M) hA
  obtain ⟨hδσ,hδh,hδX,hδT⟩ := pairAmbientDistanceRadius_le σ M A
  have haxis := pairKSPhysicalAxisAnalyticDescent_data g hpoint hA hF0 hrotation hh le_rfl
  have hcompA := pair_ambient_distance_composition_on_polydisc
    hσ hh hδσ hδh haxis.1.1 haxis.1.2.1
  have hcompB := pair_ambient_distance_composition_on_polydisc
    hσ hh hδσ hδh haxis.2.1 haxis.2.2.1
  refine ⟨hcompA.1,hcompB.1,?_,?_⟩
  · intro q hr hs hu
    exact ⟨hcompA.2 q hr hs hu,hcompB.2 q hr hs hu⟩
  · intro x hxr hxs hxu
    let q : Fin 3 → ℝ := pairAmbientPhysicalDistances x
    have hr : 0≤q 0 := norm_nonneg _
    have hs : 0≤q 1 := norm_nonneg _
    have hu : 0≤q 2 := norm_nonneg _
    have hlow : |q 0-q 1|≤q 2 := abs_norm_sub_norm_le _ _
    have hhigh : q 2≤q 0+q 1 := norm_sub_le _ _
    have hqr : |q 0-σ|<pairAmbientDistanceRadius σ M A := hxr
    have hqs : |q 1-σ|<pairAmbientDistanceRadius σ M A := hxs
    have hqu : q 2<pairAmbientDistanceRadius σ M A := hxu
    have hδ := (abs_nonneg _).trans hqr.le
    have hqabs : |q 2|<pairAmbientDistanceRadius σ M A := by rwa [abs_of_nonneg hu]
    have hP := pairAmbientRealCenterPolynomial_pos hσ hδ hδσ q hqr.le hqs.le hqabs.le
    obtain ⟨h0,h1,hsep⟩ := pairAmbientCanonical_distances q hr hs hu hlow hhigh hP
    have hv := rotation_invariant_eq_of_physical_distances g hrotation x
      (pairAmbientCanonicalConfiguration q) h0.symm h1.symm hsep.symm
    have hid := pairAmbientCanonical_identity g hσ hh hδσ hδh hδX hδT
      hpoint hA hF0 hrotation le_rfl q hr hs hu hlow hhigh hqr hqs hqu
    exact hv.trans hid


theorem twoElectron_scalar_ground_pair_ambient_analytic_descent
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
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,haxispos,hNA,hPA⟩ :=
      twoElectron_scalar_ground_axis_analytic_descent_with_H2_decay Z hZ
  have ht : ‖pairAmbientAxisCenter 1‖=1 := by
    have hs : ‖pairAmbientAxisCenter 1‖^2=1 := by
      simp [pairAmbientAxisCenter,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    nlinarith [norm_nonneg (pairAmbientAxisCenter 1)]
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,pairAmbientDistanceRadius_pos (M:=M) (by norm_num) hA,?_⟩
  intro ε hε hlim
  have hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      originScaledDifference u ε (configurationRotation 2 Q x)=originScaledDifference u ε x :=
    fun Q x => originScaledDifference_configurationRotation u Q (hrotation Q) ε x
  exact pairAmbientPhysicalAnalytic_data (originScaledDifference u ε) (by norm_num)
    (hP ε hε hlim _ ht).1.1.1.1 hA hF0 hg

#print axioms twoElectron_scalar_ground_pair_ambient_analytic_descent

#print axioms pairAmbientDistanceRadius_pos
#print axioms pairAmbientPhysicalAnalytic_data
#print axioms pairAmbientCanonical_identity
#print axioms pairAmbientCanonical_distances
#print axioms pairAmbientDistanceInput_domain
#print axioms pair_ambient_distance_composition_on_polydisc
end ManyBody.S8

