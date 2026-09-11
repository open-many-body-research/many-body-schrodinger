import ProductDiagonalWeakH2_v1
import WeakGrushinAnisotropicLimitUniqueness_v1

/-! The recovered full weak H2 jets agree with every supplied coordinate first
and diagonal second derivative. Uniqueness is proved for actual weak product
jets, so this is compatibility of concrete L2 classes, not of formal labels. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
variable {Y T ι κ : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
  [Fintype ι] [Fintype κ]

theorem product_weakH2_compatible_with_coordinate_diagonal_jets
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    (d e : ι ⊕ κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (hd : ∀ i, WeakProductL2Directional f (d i) (productBasisDirection bY bT i))
    (he : ∀ i, WeakProductL2Directional (d i) (e i) (productBasisDirection bY bT i)) :
    ∃ a : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ b : (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional f (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      (∀ i, a (productBasisDirection bY bT i) = d i) ∧
      ∀ i, b (productBasisDirection bY bT i) (productBasisDirection bY bT i) = e i := by
  obtain ⟨a,b,ha,hb⟩ := product_weakH2_of_coordinate_diagonal_jets bY bT d e hd he
  refine ⟨a,b,ha,hb,?_,?_⟩
  · intro i
    exact weakProductL2Directional_unique (ha _) (hd i)
  · intro i
    exact weakProductL2SecondDirectional_unique (ha _) (hd i) (hb _ _) (he i)

theorem product_weakH2_of_factor_diagonal_jets
    (bY : OrthonormalBasis ι ℝ Y) (bT : OrthonormalBasis κ ℝ T)
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    (dY eY : ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (dT eT : κ → Lp ℂ 2 (volume : Measure (Y × T)))
    (hdY : ∀ i, WeakProductL2Directional f (dY i) (bY i,0))
    (heY : ∀ i, WeakProductL2Directional (dY i) (eY i) (bY i,0))
    (hdT : ∀ j, WeakProductL2Directional f (dT j) (0,bT j))
    (heT : ∀ j, WeakProductL2Directional (dT j) (eT j) (0,bT j)) :
    ∃ a : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
    ∃ b : (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ v, WeakProductL2Directional f (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      (∀ i, a (bY i,0) = dY i) ∧ (∀ j, a (0,bT j) = dT j) ∧
      (∀ i, b (bY i,0) (bY i,0) = eY i) ∧ ∀ j, b (0,bT j) (0,bT j) = eT j := by
  have hd : ∀ i, WeakProductL2Directional f ((Sum.elim dY dT) i) (productBasisDirection bY bT i) := by
    intro i
    cases i with
    | inl i => exact hdY i
    | inr j => exact hdT j
  have he : ∀ i, WeakProductL2Directional ((Sum.elim dY dT) i) ((Sum.elim eY eT) i)
      (productBasisDirection bY bT i) := by
    intro i
    cases i with
    | inl i => exact heY i
    | inr j => exact heT j
  obtain ⟨a,b,ha,hb,hda,heb⟩ := product_weakH2_compatible_with_coordinate_diagonal_jets
    bY bT (Sum.elim dY dT) (Sum.elim eY eT) hd he
  exact ⟨a,b,ha,hb,(fun i => hda (.inl i)),(fun j => hda (.inr j)),
    (fun i => heb (.inl i)),(fun j => heb (.inr j))⟩

end TheoremT.Continuum
