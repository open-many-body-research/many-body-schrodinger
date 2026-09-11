import TwoElectronSliceNuclearIdentities_v1

/-! Integrate an explicit one-electron H1 form inequality over actual two-electron slices.
No slicing or component-energy inequality is assumed. The one-electron comparison is a premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def twoElectronScalarComponentEnergy (Z : ℝ) (i : Fin 2) (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) : ℝ :=
  (1 / 2 : ℝ) * (∑ k : Fin 3, ‖d (i,k)‖ ^ 2) -
    Z * ∫ q, ‖F q‖ ^ 2 / ‖position q i‖

theorem twoElectronFirstSlice_gradient_integrable (d : Coordinate 2 → SpatialL2 2) :
    Integrable (fun y => ∑ k : Fin 3, ‖twoElectronFirstSlice (d (0,k)) y‖ ^ 2) volume :=
  integrable_finsetSum _ (fun k _ => twoElectronFirstSlice_norm_sq_integrable (d (0,k)))

theorem twoElectronSecondSlice_gradient_integrable (d : Coordinate 2 → SpatialL2 2) :
    Integrable (fun x => ∑ k : Fin 3, ‖twoElectronSecondSlice (d (1,k)) x‖ ^ 2) volume :=
  integrable_finsetSum _ (fun k _ => twoElectronSecondSlice_norm_sq_integrable (d (1,k)))

theorem twoElectronFirstSlice_gradient_integral (d : Coordinate 2 → SpatialL2 2) :
    (∫ y, ∑ k : Fin 3, ‖twoElectronFirstSlice (d (0,k)) y‖ ^ 2) =
      ∑ k : Fin 3, ‖d (0,k)‖ ^ 2 := by
  rw [integral_finsetSum _ (fun k _ => twoElectronFirstSlice_norm_sq_integrable (d (0,k)))]
  simp_rw [twoElectronFirstSlice_norm_sq_integral]

theorem twoElectronSecondSlice_gradient_integral (d : Coordinate 2 → SpatialL2 2) :
    (∫ x, ∑ k : Fin 3, ‖twoElectronSecondSlice (d (1,k)) x‖ ^ 2) =
      ∑ k : Fin 3, ‖d (1,k)‖ ^ 2 := by
  rw [integral_finsetSum _ (fun k _ => twoElectronSecondSlice_norm_sq_integrable (d (1,k)))]
  simp_rw [twoElectronSecondSlice_norm_sq_integral]

theorem twoElectron_first_component_of_oneElectron_bound
    (φ : SpatialL2 1) (hφ : ‖φ‖=1) (Z β C : ℝ)
    (hone : ∀ (f : SpatialL2 1) (d : Coordinate 1 → SpatialL2 1),
      (∀ k, WeakPartial f (d k) k) →
      β * ‖f‖ ^ 2 ≤ (1 / 2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖ ^ 2) -
        Z * (∫ x, ‖f x‖ ^ 2 / ‖x‖) + C * ‖inner ℂ φ f‖ ^ 2)
    (F : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial F (d k) k) :
    β * ‖F‖ ^ 2 ≤ twoElectronScalarComponentEnergy Z 0 F d +
      C * ‖twoElectronProjectFirst φ F‖ ^ 2 := by
  have hg := (twoElectronFirstSlice_gradient_integrable d).const_mul (1 / 2 : ℝ)
  have hn := (twoElectronFirstSlice_nuclear_integrable F d hd).const_mul Z
  have ha := (twoElectronFirstSlice_amplitude_sq_integrable φ F).const_mul C
  have hgn : Integrable (fun y : Configuration 1 =>
      (1/2 : ℝ) * (∑ k : Fin 3, ‖twoElectronFirstSlice (d (0,k)) y‖^2) -
        Z * twoElectronFirstSlice_nuclear F y) volume := hg.sub hn
  have hp : ∀ᵐ y ∂volume,
      β * ‖twoElectronFirstSlice F y‖ ^ 2 ≤
        (1 / 2 : ℝ) * (∑ k : Fin 3, ‖twoElectronFirstSlice (d (0,k)) y‖ ^ 2) -
          Z * twoElectronFirstSlice_nuclear F y + C * ‖inner ℂ φ (twoElectronFirstSlice F y)‖ ^ 2 := by
    filter_upwards [twoElectronFirstSlice_weakPartial_ae F d hd] with y hy
    have hw : ∀ k : Coordinate 1,
        WeakPartial (twoElectronFirstSlice F y) (twoElectronFirstSlice (d (0,k.2)) y) k := by
      rintro ⟨i,k⟩
      fin_cases i
      exact hy k
    have h := hone (twoElectronFirstSlice F y) (fun k => twoElectronFirstSlice (d (0,k.2)) y) hw
    simpa [Fintype.sum_prod_type,twoElectronFirstSlice_nuclear] using h
  have h := integral_mono_ae ((twoElectronFirstSlice_norm_sq_integrable F).const_mul β)
    (hgn.add ha) hp
  dsimp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_const_mul,integral_add hgn ha,integral_sub hg hn,
    integral_const_mul,integral_const_mul,integral_const_mul,
    twoElectronFirstSlice_norm_sq_integral,twoElectronFirstSlice_gradient_integral,
    twoElectronFirstSlice_nuclear_integral F d hd,
    twoElectronFirstSlice_amplitude_sq_integral φ hφ F] at h
  exact h

theorem twoElectron_second_component_of_oneElectron_bound
    (φ : SpatialL2 1) (hφ : ‖φ‖=1) (Z β C : ℝ)
    (hone : ∀ (f : SpatialL2 1) (d : Coordinate 1 → SpatialL2 1),
      (∀ k, WeakPartial f (d k) k) →
      β * ‖f‖ ^ 2 ≤ (1 / 2 : ℝ) * (∑ k : Coordinate 1, ‖d k‖ ^ 2) -
        Z * (∫ x, ‖f x‖ ^ 2 / ‖x‖) + C * ‖inner ℂ φ f‖ ^ 2)
    (F : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial F (d k) k) :
    β * ‖F‖ ^ 2 ≤ twoElectronScalarComponentEnergy Z 1 F d +
      C * ‖twoElectronProjectSecond φ F‖ ^ 2 := by
  have hg := (twoElectronSecondSlice_gradient_integrable d).const_mul (1 / 2 : ℝ)
  have hn := (twoElectronSecondSlice_nuclear_integrable F d hd).const_mul Z
  have ha := (twoElectronSecondSlice_amplitude_sq_integrable φ F).const_mul C
  have hgn : Integrable (fun x : Configuration 1 =>
      (1/2 : ℝ) * (∑ k : Fin 3, ‖twoElectronSecondSlice (d (1,k)) x‖^2) -
        Z * twoElectronSecondSlice_nuclear F x) volume := hg.sub hn
  have hp : ∀ᵐ x ∂volume,
      β * ‖twoElectronSecondSlice F x‖ ^ 2 ≤
        (1 / 2 : ℝ) * (∑ k : Fin 3, ‖twoElectronSecondSlice (d (1,k)) x‖ ^ 2) -
          Z * twoElectronSecondSlice_nuclear F x + C * ‖inner ℂ φ (twoElectronSecondSlice F x)‖ ^ 2 := by
    filter_upwards [twoElectronSecondSlice_weakPartial_ae F d hd] with x hx
    have hw : ∀ k : Coordinate 1,
        WeakPartial (twoElectronSecondSlice F x) (twoElectronSecondSlice (d (1,k.2)) x) k := by
      rintro ⟨i,k⟩
      fin_cases i
      exact hx k
    have h := hone (twoElectronSecondSlice F x) (fun k => twoElectronSecondSlice (d (1,k.2)) x) hw
    simpa [Fintype.sum_prod_type,twoElectronSecondSlice_nuclear] using h
  have h := integral_mono_ae ((twoElectronSecondSlice_norm_sq_integrable F).const_mul β)
    (hgn.add ha) hp
  dsimp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_const_mul,integral_add hgn ha,integral_sub hg hn,
    integral_const_mul,integral_const_mul,integral_const_mul,
    twoElectronSecondSlice_norm_sq_integral,twoElectronSecondSlice_gradient_integral,
    twoElectronSecondSlice_nuclear_integral F d hd,
    twoElectronSecondSlice_amplitude_sq_integral φ hφ F] at h
  exact h

#print axioms twoElectron_first_component_of_oneElectron_bound
#print axioms twoElectron_second_component_of_oneElectron_bound
end TheoremT.Continuum
