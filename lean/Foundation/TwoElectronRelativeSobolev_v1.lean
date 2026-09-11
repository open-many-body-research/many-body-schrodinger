import TwoElectronRelativeCoordinates_v1
import HardyH1ScalarDensity_v2
import HardyH1ClosedGraph_v1

/-! Weak H1 covariance under the actual center/relative isometry. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def twoElectronRelativeSign (i : Fin 2) : ℝ := if i = 0 then 1 else -1

theorem twoElectronRelative_basis (k : Coordinate 2) :
    twoElectronRelativeEquiv (coordinateVector k) =
      (Real.sqrt 2)⁻¹ • (coordinateVector (0,k.2) +
        twoElectronRelativeSign k.1 • coordinateVector (1,k.2)) := by
  apply (WithLp.ext_iff 2).mpr
  funext ⟨j,l⟩
  rcases k with ⟨i,k⟩
  fin_cases i <;> fin_cases j <;>
    simp [twoElectronRelativeEquiv,twoElectronHadamardLinear,twoElectronRelativeSign,
      coordinateVector,div_eq_mul_inv] <;> ring

def twoElectronRelativePull : SpatialL2 2 →ₗᵢ[ℂ] SpatialL2 2 :=
  Lp.compMeasurePreservingₗᵢ ℂ twoElectronRelativeEquiv
    twoElectronRelativeEquiv_measurePreserving

theorem twoElectronRelativePull_ae (f : SpatialL2 2) :
    twoElectronRelativePull f =ᵐ[volume] f ∘ twoElectronRelativeEquiv :=
  Lp.coeFn_compMeasurePreserving f twoElectronRelativeEquiv_measurePreserving

def twoElectronRelativeGradient (d : Coordinate 2 → SpatialL2 2) (k : Coordinate 2) : SpatialL2 2 :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (twoElectronRelativePull (d (0,k.2)) +
    (twoElectronRelativeSign k.1 : ℂ) • twoElectronRelativePull (d (1,k.2)))

theorem twoElectronRelative_smoothPartial {u : Configuration 2 → ℂ}
    (hu : ContDiff ℝ 1 u) (k : Coordinate 2) (x : Configuration 2) :
    smoothPartial (u ∘ twoElectronRelativeEquiv) k x =
      ((Real.sqrt 2)⁻¹ : ℂ) * (smoothPartial u (0,k.2) (twoElectronRelativeEquiv x) +
        (twoElectronRelativeSign k.1 : ℂ) * smoothPartial u (1,k.2) (twoElectronRelativeEquiv x)) := by
  have h := ((hu.differentiable (by norm_num) (twoElectronRelativeEquiv x)).hasFDerivAt).comp x
    twoElectronRelativeEquiv.toContinuousLinearEquiv.hasFDerivAt
  rw [smoothPartial,h.fderiv]
  change fderiv ℝ u (twoElectronRelativeEquiv x) (twoElectronRelativeEquiv (coordinateVector k)) = _
  rw [twoElectronRelative_basis,map_smul,map_add,map_smul]
  simp only [smoothPartial,Complex.real_smul,smul_eq_mul,Complex.ofReal_inv]

theorem twoElectronRelativeGradient_ae (d : Coordinate 2 → SpatialL2 2)
    (du : Coordinate 2 → Configuration 2 → ℂ) (hd : ∀ k, d k =ᵐ[volume] du k)
    (k : Coordinate 2) :
    twoElectronRelativeGradient d k =ᵐ[volume] fun x =>
      ((Real.sqrt 2)⁻¹ : ℂ) * (du (0,k.2) (twoElectronRelativeEquiv x) +
        (twoElectronRelativeSign k.1 : ℂ) * du (1,k.2) (twoElectronRelativeEquiv x)) := by
  have h0 := twoElectronRelativeEquiv_measurePreserving.quasiMeasurePreserving.ae (hd (0,k.2))
  have h1 := twoElectronRelativeEquiv_measurePreserving.quasiMeasurePreserving.ae (hd (1,k.2))
  filter_upwards [Lp.coeFn_smul ((Real.sqrt 2)⁻¹ : ℂ)
      (twoElectronRelativePull (d (0,k.2)) + (twoElectronRelativeSign k.1 : ℂ) • twoElectronRelativePull (d (1,k.2))),
    Lp.coeFn_add (twoElectronRelativePull (d (0,k.2)))
      ((twoElectronRelativeSign k.1 : ℂ) • twoElectronRelativePull (d (1,k.2))),
    Lp.coeFn_smul (twoElectronRelativeSign k.1 : ℂ) (twoElectronRelativePull (d (1,k.2))),
    twoElectronRelativePull_ae (d (0,k.2)),twoElectronRelativePull_ae (d (1,k.2)),h0,h1]
    with x hc ha hs hp0 hp1 h0 h1
  dsimp only [twoElectronRelativeGradient]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply] at *
  rw [hc,ha,hs,hp0,hp1,h0,h1]

theorem twoElectronRelative_smooth_weak (u : Configuration 2 → ℂ)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (hf : f =ᵐ[volume] u) (hd : ∀ k, d k =ᵐ[volume] smoothPartial u k) (k : Coordinate 2) :
    WeakPartial (twoElectronRelativePull f) (twoElectronRelativeGradient d k) k := by
  let v := u ∘ twoElectronRelativeEquiv
  have hv : ContDiff ℝ ∞ v := hu.comp twoElectronRelativeEquiv.toContinuousLinearEquiv.contDiff
  have hvc : HasCompactSupport v := hc.comp_homeomorph twoElectronRelativeEquiv.toHomeomorph
  have hm : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  have hdm : MemLp (smoothPartial v k) 2 volume :=
    (smoothPartial_contDiff hv k).continuous.memLp_of_hasCompactSupport (smoothPartial_compact hvc k)
  have hfv : twoElectronRelativePull f = hm.toLp v := by
    apply Lp.ext
    exact ((twoElectronRelativePull_ae f).trans
      (twoElectronRelativeEquiv_measurePreserving.quasiMeasurePreserving.ae hf)).trans hm.coeFn_toLp.symm
  have hdv : twoElectronRelativeGradient d k = hdm.toLp (smoothPartial v k) := by
    apply Lp.ext
    filter_upwards [twoElectronRelativeGradient_ae d (smoothPartial u) hd k,hdm.coeFn_toLp] with x hx hy
    rw [hx,hy]
    exact (twoElectronRelative_smoothPartial (hu.of_le (by norm_num)) k x).symm
  rw [hfv,hdv]
  exact classicalDerivative_to_WeakPartial (hv.of_le (by norm_num)) k hm hdm

theorem twoElectronRelative_weakPartial (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial f (d k) k) (k : Coordinate 2) :
    WeakPartial (twoElectronRelativePull f) (twoElectronRelativeGradient d k) k := by
  obtain ⟨u,g,dg,hu,hc,hgu,hdgu,hdg,hH2,hg,hdd⟩ := weakH1_smooth_compact_graph_sequence d hd
  have hfg := twoElectronRelativePull.continuous.continuousAt.tendsto.comp hg
  have hd0 := twoElectronRelativePull.continuous.continuousAt.tendsto.comp (hdd (0,k.2))
  have hd1 := twoElectronRelativePull.continuous.continuousAt.tendsto.comp (hdd (1,k.2))
  have hddg : Tendsto (fun n => twoElectronRelativeGradient (dg n) k) atTop
      (𝓝 (twoElectronRelativeGradient d k)) :=
    (hd0.add (hd1.const_smul (twoElectronRelativeSign k.1 : ℂ))).const_smul ((Real.sqrt 2)⁻¹ : ℂ)
  exact WeakPartial.of_tendsto
    (fun n => twoElectronRelative_smooth_weak (u n) (hu n) (hc n) (g n) (dg n) (hgu n) (hdgu n) k)
    hfg hddg

#print axioms twoElectronRelative_basis
#print axioms twoElectronRelative_smoothPartial
#print axioms twoElectronRelative_weakPartial
end TheoremT.Continuum
