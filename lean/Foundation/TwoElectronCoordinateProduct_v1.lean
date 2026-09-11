import ConfigurationSlicing_v2

/-!
Actual two-electron coordinates, product Lebesgue measure, and L2 pullback.
This is new post-freeze work. Historical comparison source:
`THEOREM_T_FREEZE_2026-09-09_212604/formal/AtomicTwoElectron.lean`,
SHA-256 `3134f576bab8d922ddc71b64ae1fabd1fa34a46692fcf8422478754576476516`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`.
No assertion about the frozen source is changed by this construction.
-/

noncomputable section
open MeasureTheory Filter

namespace TheoremT.Continuum

/-- The two physical electron indices become two copies of the one-electron index. -/
def twoElectronCoordinateSplit : Coordinate 2 ≃ Coordinate 1 ⊕ Coordinate 1 :=
  (Equiv.prodCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm
    (Equiv.refl (Fin 3))).trans (Equiv.sumProdDistrib (Fin 1) (Fin 1) (Fin 3))

/-- The product with the Euclidean sum norm is isometric to the actual configuration. -/
def twoElectronConfigurationSplit :
    Configuration 2 ≃ₗᵢ[ℝ] WithLp 2 (Configuration 1 × Configuration 1) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ twoElectronCoordinateSplit).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Coordinate 1 ⊕ Coordinate 1 => ℝ))

/-- The ordinary product has the same topology, and carries product Lebesgue measure. -/
def twoElectronConfigurationProduct :
    Configuration 2 ≃L[ℝ] Configuration 1 × Configuration 1 :=
  twoElectronConfigurationSplit.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Configuration 1) (Configuration 1))

@[simp] theorem twoElectronConfigurationProduct_fst_apply
    (x : Configuration 2) (k : Fin 3) :
    (twoElectronConfigurationProduct x).1 (0, k) = x (0, k) := rfl

@[simp] theorem twoElectronConfigurationProduct_snd_apply
    (x : Configuration 2) (k : Fin 3) :
    (twoElectronConfigurationProduct x).2 (0, k) = x (1, k) := rfl

@[simp] theorem twoElectronConfigurationProduct_fst_position
    (x : Configuration 2) :
    position (twoElectronConfigurationProduct x).1 0 = position x 0 := rfl

@[simp] theorem twoElectronConfigurationProduct_snd_position
    (x : Configuration 2) :
    position (twoElectronConfigurationProduct x).2 0 = position x 1 := rfl

theorem twoElectronConfigurationSplit_measurePreserving :
    MeasurePreserving twoElectronConfigurationSplit :=
  twoElectronConfigurationSplit.measurePreserving

theorem twoElectronConfigurationProduct_measurePreserving :
    MeasurePreserving twoElectronConfigurationProduct volume
      ((volume : Measure (Configuration 1)).prod volume) :=
  (WithLp.volume_preserving_ofLp (Configuration 1) (Configuration 1)).comp
    twoElectronConfigurationSplit.measurePreserving

theorem twoElectronConfigurationProduct_symm_measurePreserving :
    MeasurePreserving twoElectronConfigurationProduct.symm
      ((volume : Measure (Configuration 1)).prod volume) volume :=
  twoElectronConfigurationSplit.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp (Configuration 1) (Configuration 1))

@[simp] theorem twoElectronConfigurationProduct_symm_first
    (x y : Configuration 1) (k : Fin 3) :
    twoElectronConfigurationProduct.symm (x, y) (0, k) = x (0, k) := by
  rw [← twoElectronConfigurationProduct_fst_apply]
  simp

@[simp] theorem twoElectronConfigurationProduct_symm_second
    (x y : Configuration 1) (k : Fin 3) :
    twoElectronConfigurationProduct.symm (x, y) (1, k) = y (0, k) := by
  rw [← twoElectronConfigurationProduct_snd_apply]
  simp

/-- L2 on the Cartesian product with its actual product Lebesgue measure. -/
abbrev TwoElectronProductL2 := Lp ℂ 2
  ((volume : Measure (Configuration 1)).prod (volume : Measure (Configuration 1)))

/-- Pull product functions back to the actual two-electron configuration. -/
def twoElectronL2Pullback : TwoElectronProductL2 →ₗᵢ[ℂ] SpatialL2 2 :=
  Lp.compMeasurePreservingₗᵢ ℂ twoElectronConfigurationProduct
    twoElectronConfigurationProduct_measurePreserving

/-- Write an actual two-electron L2 class in ordinary product coordinates. -/
def twoElectronL2ToProduct : SpatialL2 2 →ₗᵢ[ℂ] TwoElectronProductL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ twoElectronConfigurationProduct.symm
    twoElectronConfigurationProduct_symm_measurePreserving

theorem twoElectronL2Pullback_ae (f : TwoElectronProductL2) :
    twoElectronL2Pullback f =ᵐ[volume] f ∘ twoElectronConfigurationProduct :=
  Lp.coeFn_compMeasurePreserving f twoElectronConfigurationProduct_measurePreserving

theorem twoElectronL2ToProduct_ae (f : SpatialL2 2) :
    twoElectronL2ToProduct f =ᵐ[(volume : Measure (Configuration 1)).prod volume]
      f ∘ twoElectronConfigurationProduct.symm :=
  Lp.coeFn_compMeasurePreserving f twoElectronConfigurationProduct_symm_measurePreserving

@[simp] theorem twoElectronL2Pullback_toProduct (f : SpatialL2 2) :
    twoElectronL2Pullback (twoElectronL2ToProduct f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (twoElectronConfigurationProduct.symm ∘ twoElectronConfigurationProduct) = id :=
    funext twoElectronConfigurationProduct.symm_apply_apply
  simp only [h, Lp.compMeasurePreserving_id_apply]

@[simp] theorem twoElectronL2ToProduct_pullback (f : TwoElectronProductL2) :
    twoElectronL2ToProduct (twoElectronL2Pullback f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (twoElectronConfigurationProduct ∘ twoElectronConfigurationProduct.symm) = id :=
    funext twoElectronConfigurationProduct.apply_symm_apply
  simp only [h, Lp.compMeasurePreserving_id_apply]

/-- The actual two-electron spatial Hilbert space is unitarily represented in product coordinates. -/
def twoElectronL2ProductEquiv : SpatialL2 2 ≃ₗᵢ[ℂ] TwoElectronProductL2 :=
  { twoElectronL2ToProduct with
    invFun := twoElectronL2Pullback
    left_inv := twoElectronL2Pullback_toProduct
    right_inv := twoElectronL2ToProduct_pullback }

#print axioms twoElectronConfigurationProduct_fst_apply
#print axioms twoElectronConfigurationProduct_snd_apply
#print axioms twoElectronConfigurationProduct_measurePreserving
#print axioms twoElectronConfigurationProduct_symm_measurePreserving
#print axioms twoElectronL2ProductEquiv
#print axioms twoElectronL2Pullback_ae
#print axioms twoElectronL2ToProduct_ae

end TheoremT.Continuum
