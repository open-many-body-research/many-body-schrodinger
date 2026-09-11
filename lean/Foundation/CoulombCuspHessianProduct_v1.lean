import CoulombCuspDerivativeBounds_v1

/-! The uniform cusp Hessian bound multiplied by every actual weak H1
function is L2. This uses the physical Hardy inequalities and requires no
prior essential boundedness of the input function. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem cuspHessianBound_mul_memLp {N : ℕ} (Z : ℝ) (v w : Configuration N)
    {f : SpatialL2 N} (hf : HasH1 f) :
    MemLp (fun x => cuspHessianBound N Z v w x*‖f x‖) 2 volume := by
  obtain ⟨d,hd⟩ := hf
  have hn (i : Fin N) : MemLp (fun x =>
      (2*‖electronPositionCLM i v‖*‖electronPositionCLM i w‖/‖position x i‖)*‖f x‖) 2 volume := by
    have h := (weak_nuclear_memLp_two_and_bound i f d hd).1.norm.const_mul
      (2*‖electronPositionCLM i v‖*‖electronPositionCLM i w‖)
    apply h.ae_eq
    filter_upwards with x
    simp only [norm_div,Complex.norm_real,norm_norm]
    ring
  have hp (i j : Fin N) (hij : i<j) : MemLp (fun x =>
      (2*‖pairDifferenceCLM i j v‖*‖pairDifferenceCLM i j w‖/‖position x i-position x j‖)*‖f x‖) 2 volume := by
    have h := (weak_pair_memLp_two_and_bound i j (ne_of_lt hij) f d hd).1.norm.const_mul
      (2*‖pairDifferenceCLM i j v‖*‖pairDifferenceCLM i j w‖)
    apply h.ae_eq
    filter_upwards with x
    simp only [norm_div,Complex.norm_real,norm_norm]
    ring
  have hn' := (memLp_finsetSum Finset.univ (fun i _ => hn i)).const_mul |Z|
  have hp' := (memLp_finsetSum Finset.univ (fun i _ =>
    memLp_finsetSum (Finset.univ.filter (fun j : Fin N => i<j))
      (fun j hj => hp i j (Finset.mem_filter.mp hj).2))).const_mul (1/2:ℝ)
  have h := hn'.add hp'
  apply h.ae_eq
  filter_upwards with x
  simp only [Pi.add_apply,cuspHessianBound,add_mul,mul_assoc,Finset.sum_mul]

#print axioms cuspHessianBound_mul_memLp
end TheoremT.Continuum
