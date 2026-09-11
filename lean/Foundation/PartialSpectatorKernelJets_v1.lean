import PartialSpectatorSmoothKernel_v1

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T F : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T] {ν : Measure T} [IsAddHaarMeasure ν]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def spectatorKernelJet (K : T → ℝ) : List T → T → ℝ
  | [] => K
  | v::vs => fun t => fderiv ℝ (spectatorKernelJet K vs) t v

def spectatorFiberJet (G : Y × T → F) : List T → Y × T → F
  | [] => G
  | v::vs => spectatorFiberDirectional (spectatorFiberJet G vs) v

theorem spectatorKernelJet_contDiff {K : T → ℝ} (hK : ContDiff ℝ ∞ K) (vs : List T) :
    ContDiff ℝ ∞ (spectatorKernelJet K vs) := by
  induction vs with
  | nil => exact hK
  | cons v vs ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectatorKernelJet_hasCompactSupport {K : T → ℝ} (hcK : HasCompactSupport K) (vs : List T) :
    HasCompactSupport (spectatorKernelJet K vs) := by
  induction vs with
  | nil => exact hcK
  | cons v vs ih => exact ih.fderiv_apply ℝ v

theorem partialSpectatorConvolution_fiber_jet_of_slice
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (y : Y) (hy : MemLp (fun t => G (y,t)) 2 ν) (vs : List T) (t : T) :
    spectatorFiberJet (partialSpectatorConvolution (ν := ν) K G) vs (y,t) =
      partialSpectatorConvolution (ν := ν) (spectatorKernelJet K vs) G (y,t) := by
  induction vs generalizing t with
  | nil => rfl
  | cons v vs ih =>
    have he : (fun q => spectatorFiberJet (partialSpectatorConvolution (ν := ν) K G) vs (y,q)) =
        (fun q => partialSpectatorConvolution (ν := ν) (spectatorKernelJet K vs) G (y,q)) := funext ih
    change fderiv ℝ (fun q => spectatorFiberJet (partialSpectatorConvolution (ν := ν) K G) vs (y,q)) t v = _
    rw [he]
    exact partialSpectatorConvolution_fiber_derivative_of_slice
      (spectatorKernelJet_contDiff hK vs) (spectatorKernelJet_hasCompactSupport hcK vs) y hy v t

theorem partialSpectatorConvolution_fiber_jet_ae
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG2 : MemLp G 2 (μ.prod ν)) (vs : List T) :
    spectatorFiberJet (partialSpectatorConvolution (ν := ν) K G) vs =ᵐ[μ.prod ν]
      partialSpectatorConvolution (ν := ν) (spectatorKernelJet K vs) G := by
  filter_upwards [(quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae
    (memLp_two_product_slices_ae hG2)] with p hp
  exact partialSpectatorConvolution_fiber_jet_of_slice hK hcK p.1 hp vs p.2

theorem partialSpectatorConvolution_fiber_jet_memLp
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG2 : MemLp G 2 (μ.prod ν)) (vs : List T) :
    MemLp (spectatorFiberJet (partialSpectatorConvolution (ν := ν) K G) vs) 2 (μ.prod ν) := by
  have hi := (spectatorKernelJet_contDiff hK vs).continuous.integrable_of_hasCompactSupport
    (μ := ν) (spectatorKernelJet_hasCompactSupport hcK vs)
  exact (partialSpectatorConvolution_ae_memLp_two hi hG2).ae_eq
    (partialSpectatorConvolution_fiber_jet_ae hK hcK hG2 vs).symm

theorem partialSpectatorConvolution_fiber_jet_integral_sq_le
    {K : T → ℝ} {G : Y × T → F} (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K)
    (hG2 : MemLp G 2 (μ.prod ν)) (vs : List T) :
    (∫ p, ‖spectatorFiberJet (partialSpectatorConvolution (ν := ν) K G) vs p‖^2 ∂μ.prod ν) ≤
      (∫ s, ‖spectatorKernelJet K vs s‖ ∂ν)^2 * (∫ p, ‖G p‖^2 ∂μ.prod ν) := by
  have hi := (spectatorKernelJet_contDiff hK vs).continuous.integrable_of_hasCompactSupport
    (μ := ν) (spectatorKernelJet_hasCompactSupport hcK vs)
  have he := integral_congr_ae ((partialSpectatorConvolution_fiber_jet_ae hK hcK hG2 vs).fun_comp
    (fun z : F => ‖z‖^2))
  simp only [Function.comp_apply] at he
  rw [he]
  exact partialSpectatorConvolution_ae_integral_sq_le hi hG2

#print axioms spectatorKernelJet
#print axioms spectatorFiberJet
#print axioms spectatorKernelJet_contDiff
#print axioms spectatorKernelJet_hasCompactSupport
#print axioms partialSpectatorConvolution_fiber_jet_of_slice
#print axioms partialSpectatorConvolution_fiber_jet_ae
#print axioms partialSpectatorConvolution_fiber_jet_memLp
#print axioms partialSpectatorConvolution_fiber_jet_integral_sq_le
end TheoremT.Continuum
