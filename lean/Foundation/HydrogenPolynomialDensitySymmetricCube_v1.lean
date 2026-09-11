import HydrogenPolynomialDensityTensorC1_v1
import Mathlib.Algebra.MvPolynomial.Monad

/-! Affine transport of the verified tensor C1 approximation to [-1,1]^3.
This cube contains the actual radius-one sphere, including its coordinate poles. -/
noncomputable section
namespace TheoremT.HydrogenPolynomialDensity

def fromUnitCube3 (y : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => 2 * y i - 1
def toUnitCube3 (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => (x i + 1) / 2

theorem fromUnitCube3_toUnitCube3 (x : Fin 3 → ℝ) :
    fromUnitCube3 (toUnitCube3 x) = x := by ext i; simp [fromUnitCube3, toUnitCube3]; ring

theorem fromUnitCube3_update (x : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    fromUnitCube3 (Function.update x i t) = Function.update (fromUnitCube3 x) i (2 * t - 1) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [fromUnitCube3]
  · simp [fromUnitCube3, Function.update_of_ne hj]

theorem toUnitCube3_update (x : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    toUnitCube3 (Function.update x i t) = Function.update (toUnitCube3 x) i ((t + 1) / 2) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [toUnitCube3]
  · simp [toUnitCube3, Function.update_of_ne hj]

theorem toUnitCube3_mem {x : Fin 3 → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    inUnitCube (toUnitCube3 x) := by
  intro i
  obtain ⟨hl, hu⟩ := abs_le.mp (hx i)
  constructor <;> dsimp [toUnitCube3] <;> linarith

def symmetricCubePolynomial3 (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.bind₁ (fun i =>
    (MvPolynomial.X i + 1) * MvPolynomial.C (1 / 2 : ℝ)) p

theorem symmetricCubePolynomial3_eval (p : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (symmetricCubePolynomial3 p) =
      MvPolynomial.eval (toUnitCube3 x) p := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x
    (MvPolynomial.bind₁ _ p) = MvPolynomial.eval₂Hom (RingHom.id ℝ) (toUnitCube3 x) p
  rw [MvPolynomial.eval₂Hom_bind₁]
  have he : (fun i : Fin 3 => MvPolynomial.eval₂Hom (RingHom.id ℝ) x
      ((MvPolynomial.X i + 1) * MvPolynomial.C (1 / 2 : ℝ))) = toUnitCube3 x := by
    funext i
    simp [toUnitCube3, div_eq_mul_inv]
  rw [he]

theorem fromUnitCube3_hasDerivAt {f : (Fin 3 → ℝ) → ℝ}
    {g : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hfg : ∀ i y, HasDerivAt (fun t => f (Function.update y i t)) (g i y) (y i))
    (i : Fin 3) (y : Fin 3 → ℝ) :
    HasDerivAt (fun t => f (fromUnitCube3 (Function.update y i t)))
      (2 * g i (fromUnitCube3 y)) (y i) := by
  have hlin := ((hasDerivAt_id (y i)).const_mul 2).sub_const 1
  have hd := (hfg i (fromUnitCube3 y)).comp (y i) hlin
  simpa only [fromUnitCube3_update, fromUnitCube3, Function.comp_def, id_eq,
    one_mul, mul_comm] using hd

theorem symmetricCube_tensor_hasDerivAt (n : ℕ) (i : Fin 3)
    (F : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update x i t)
      (symmetricCubePolynomial3 (tensorBernsteinPolynomial3 (n + 1) F)))
      (tensorBernsteinDerivative3 n i F (toUnitCube3 x) / 2) (x i) := by
  have hlin := ((hasDerivAt_id (x i)).add_const 1).div_const 2
  have hd := (tensorBernsteinPolynomial3_hasDerivAt n i F (toUnitCube3 x)).comp (x i) hlin
  simp_rw [symmetricCubePolynomial3_eval, toUnitCube3_update]
  simpa only [toUnitCube3, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using hd

/-- Every actual globally C1 function admits one real multivariate polynomial
uniformly approximating its value and first derivatives on [-1,1]^3. -/
theorem exists_mvPolynomial3_C1_near_symmetricCube {f : (Fin 3 → ℝ) → ℝ}
    {g : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hfc : Continuous f) (hgc : ∀ i, Continuous (g i))
    (hfg : ∀ i y, HasDerivAt (fun t => f (Function.update y i t)) (g i y) (y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      (∀ x, (∀ i, |x i| ≤ 1) → |MvPolynomial.eval x p - f x| < ε) ∧
      (∀ i x, (∀ j, |x j| ≤ 1) →
        |deriv (fun t => MvPolynomial.eval (Function.update x i t) p) (x i) - g i x| < ε) := by
  let F : (Fin 3 → ℝ) → ℝ := fun y => f (fromUnitCube3 y)
  let G : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i y => 2 * g i (fromUnitCube3 y)
  have hF : Continuous F := hfc.comp (by unfold fromUnitCube3; fun_prop)
  have hG : ∀ i, Continuous (G i) := fun i =>
    continuous_const.mul ((hgc i).comp (by unfold fromUnitCube3; fun_prop))
  obtain ⟨n, hn⟩ := tensorBernsteinPolynomial3_C1_uniform hF hG
    (fromUnitCube3_hasDerivAt hfg) hε
  obtain ⟨hv, hd⟩ := hn n le_rfl
  refine ⟨symmetricCubePolynomial3 (tensorBernsteinPolynomial3 (n + 1) F), ?_, ?_⟩
  · intro x hx
    have hvx := hv (toUnitCube3 x) (toUnitCube3_mem hx)
    simpa only [symmetricCubePolynomial3_eval, F, fromUnitCube3_toUnitCube3] using hvx
  · intro i x hx
    have hdx := hd i (toUnitCube3 x) (toUnitCube3_mem hx)
    rw [tensorBernsteinPolynomial3_deriv] at hdx
    simp only [G, fromUnitCube3_toUnitCube3] at hdx
    rw [(symmetricCube_tensor_hasDerivAt n i F x).deriv]
    have heq : tensorBernsteinDerivative3 n i F (toUnitCube3 x) / 2 - g i x =
        (tensorBernsteinDerivative3 n i F (toUnitCube3 x) - 2 * g i x) / 2 := by ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.exists_mvPolynomial3_C1_near_symmetricCube
