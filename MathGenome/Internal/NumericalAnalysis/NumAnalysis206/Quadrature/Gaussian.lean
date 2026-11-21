import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.Gaussian
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.Lagrange
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.OrthogonalRoots
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.AdaptiveOptimality

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace NumAnalysis206.Quadrature

/-- W58's constructive weight formula, valid on unbounded support. -/
def gaussianWeight {n : ℕ} (μ : Measure ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Specs.gaussianWeightValue μ x i

/-- Integrating the Lagrange expansion gives exactness below the node count. -/
lemma integral_eq_sum_cardinal (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hn : 1 ≤ n) (hm : FiniteMoment μ (2 * n))
    (x : Fin n → ℝ) (hx : Function.Injective x)
    (p : ℝ[X]) (hp : p.degree < n) :
    (∫ t : ℝ, p.eval t ∂μ) = ∑ i, gaussianWeight μ x i * p.eval (x i) := by
  classical
  have hx' : Set.InjOn x (Finset.univ : Finset (Fin n)) := hx.injOn
  have hrepr : p = Lagrange.interpolate Finset.univ x (fun i => p.eval (x i)) :=
    (Lagrange.eq_interpolate_iff _ hx').mp ⟨by simpa using hp, by simp⟩
  have hcard (i : Fin n) :
      (NumAnalysis206.Approximation.cardinal Finset.univ x i).natDegree ≤ n - 1 := by
    exact natDegree_le_of_degree_le (by
      simpa using NumAnalysis206.Approximation.cardinal_degree Finset.univ x hx' i
        (Finset.mem_univ i))
  have hint (i : Fin n) : Integrable (fun t : ℝ =>
      p.eval (x i) * (NumAnalysis206.Approximation.cardinal Finset.univ x i).eval t) μ :=
    (polynomial_integrable μ n hm _ ((hcard i).trans (by omega))).const_mul _
  conv_lhs => rw [hrepr]
  change (∫ t : ℝ, (∑ i : Fin n, C (p.eval (x i)) *
    NumAnalysis206.Approximation.cardinal Finset.univ x i).eval t ∂μ) = _
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  exact mul_comm _ _

theorem gaussian_exactness : Specs.gaussianExactness := by
  intro μ _ n hn hm π hπ x hx hroot p hp
  let s := p /ₘ π
  let r := p %ₘ π
  have hπd : π.degree = n := by rw [degree_eq_natDegree hπ.1.ne_zero, hπ.2.1]
  have hr : r.degree < n := by simpa only [hπd] using degree_modByMonic_lt p hπ.1
  have hsn : s.natDegree < n := by
    dsimp [s]
    rw [natDegree_divByMonic p hπ.1, hπ.2.1]
    omega
  have hs : s.degree < n := degree_le_natDegree.trans_lt (by exact_mod_cast hsn)
  have hrn : r.natDegree < n := by
    by_cases hz : r = 0
    · simp [hz]; omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr hr
  have hdecomp : p = r + π * s := (modByMonic_add_div p π).symm
  have hi₁ : Integrable (fun t => r.eval t) μ :=
    polynomial_integrable μ n hm r (by omega)
  have hi₂ : Integrable (fun t => π.eval t * s.eval t) μ :=
    polynomial_products μ n hm π s (by rw [hπ.2.1]; omega)
  have hInt : (∫ t, p.eval t ∂μ) = ∫ t, r.eval t ∂μ := by
    conv_lhs => rw [hdecomp]
    simp only [eval_add, eval_mul]
    rw [integral_add hi₁ hi₂, hπ.2.2 s hs, add_zero]
  have hval (i : Fin n) : p.eval (x i) = r.eval (x i) := by
    rw [hdecomp, eval_add, eval_mul, (hroot i).eq_zero, zero_mul, add_zero]
  rw [hInt]
  change _ = ∑ i, gaussianWeight μ x i * p.eval (x i)
  simp_rw [hval]
  exact integral_eq_sum_cardinal μ n hn hm x hx r hr

/-- Every Gaussian weight is the positive squared norm of its cardinal polynomial. -/
theorem gaussian_weights : Specs.gaussianWeights := by
  classical
  intro μ _ n hn hm hG π hπ x hx hroot i
  let ℓ := NumAnalysis206.Approximation.cardinal Finset.univ x i
  have hx' : Set.InjOn x (Finset.univ : Finset (Fin n)) := hx.injOn
  have hd : ℓ.natDegree ≤ n - 1 := by
    exact natDegree_le_of_degree_le (by
      simpa [ℓ] using NumAnalysis206.Approximation.cardinal_degree Finset.univ x hx' i
        (Finset.mem_univ i))
  have heval (j : Fin n) : ℓ.eval (x j) = if i = j then 1 else 0 :=
    NumAnalysis206.Approximation.cardinal_eval Finset.univ x hx' i (Finset.mem_univ i)
      j (Finset.mem_univ j)
  have hℓ0 : ℓ ≠ 0 := by
    intro hz
    have hself := heval i
    simp [hz] at hself
  have he := gaussian_exactness μ n hn hm π hπ x hx hroot (ℓ ^ 2) (by
    calc
      (ℓ ^ 2).natDegree ≤ 2 * ℓ.natDegree := natDegree_pow_le
      _ ≤ 2 * n - 1 := by omega)
  have hw : gaussianWeight μ x i = ∫ t : ℝ, (ℓ.eval t)^2 ∂μ := by
    simpa only [gaussianWeight, eval_pow, heval, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using he.symm
  change gaussianWeight μ x i = _ ∧ 0 < gaussianWeight μ x i
  refine ⟨hw, ?_⟩
  rw [hw]
  exact polynomial_square_positive μ n hm hG ℓ hℓ0 (by omega)

/-- Gaussian quadrature for every finite positive Borel measure with the stated
finite moment and nondegeneracy; the complete W58 interface. -/
theorem gaussian_quadrature : Specs.gaussianQuadrature := by
  intro μ _ n hn hm
  refine ⟨gram_support μ n hm, ?_⟩
  intro hG
  obtain ⟨π, hπ, huniq⟩ := orthogonal_polynomial_exists_unique μ n hn hm hG
  obtain ⟨x, hx, hprod, hroots, hsimple, hloc⟩ := orthogonal_roots μ n hn hm hG π hπ
  have hroot (i : Fin n) : π.IsRoot (x i) := (hroots (x i)).mpr ⟨i, rfl⟩
  exact ⟨π, hπ, huniq, x, hx, hprod, hroots, hsimple, hloc,
    gaussian_weights μ n hn hm hG π hπ x hx hroot,
    gaussian_exactness μ n hn hm π hπ x hx hroot,
    adaptive_optimality μ n hn hm hG⟩

end NumAnalysis206.Quadrature
