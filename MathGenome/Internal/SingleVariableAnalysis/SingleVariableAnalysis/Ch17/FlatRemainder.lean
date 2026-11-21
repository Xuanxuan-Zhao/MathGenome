import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.FlatDecay
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.CoefficientUnique
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.FlatRemainder

/-!
K03.17.flat_remainder: the flat exponential and zero have identical all-orders
power expansions, although they differ at every nonzero point. The exact
function, decay estimate and positivity come from Ch06.FlatDecay. Coefficient
uniqueness is applied only after verifying the power scale on the nontrivial
punctured approach. This uses neither smoothness nor analyticity.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology BigOperators

/-- The two-sided power family is an asymptotic scale on the punctured approach. -/
theorem powerScale_at_zero :
    IsScalarAsymptoticScale (𝓝[≠] (0 : ℝ)) (fun j x => x ^ j) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro j
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_ne_zero j hx
  · intro j
    apply (scalarLittleO_iff_isLittleO _ _ _).mpr
    exact (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (Nat.lt_succ_self j)).mono
      nhdsWithin_le_nhds

/-- Every natural index includes order zero, and the limit is two-sided. -/
theorem flatRemainder_littleO_everyPower :
    ∀ m : ℕ, ScalarLittleO (𝓝[≠] (0 : ℝ)) flatExponential (fun x => |x| ^ m) := by
  intro m ε hε
  exact (flatExponential_littleO_everyPower m ε hε).filter_mono nhdsWithin_le_nhds

theorem flatRemainder_pos : ∀ x : ℝ, x ≠ 0 → 0 < flatExponential x :=
  flatExponential_pos

/-- Both functions have the all-orders expansion with the same zero coefficients. -/
theorem flatRemainder_commonZeroExpansion :
    HasScalarAsymptoticExpansion (𝓝[≠] (0 : ℝ))
        (fun j x => x ^ j) (fun _ => 0) flatExponential ∧
      HasScalarAsymptoticExpansion (𝓝[≠] (0 : ℝ))
        (fun j x => x ^ j) (fun _ => 0) (fun _ => 0) := by
  constructor
  · intro m
    change ScalarLittleO (𝓝[≠] (0 : ℝ))
      (fun x => flatExponential x - ∑ j ∈ Finset.range (m + 1), (0 : ℝ) * x ^ j)
      (fun x => x ^ m)
    simpa only [zero_mul, Finset.sum_const_zero, sub_zero, ScalarLittleO,
      Real.norm_eq_abs, abs_pow, abs_abs] using flatRemainder_littleO_everyPower m
  · intro m ε hε
    apply Eventually.of_forall
    intro x
    simp only [AsymptoticPartialSum, zero_mul, Finset.sum_const_zero, sub_zero,
      norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

/-- In the fixed power scale these zero coefficients are the only possible ones
for either function. This is coefficient uniqueness, not function uniqueness. -/
theorem flatRemainder_coefficientsExactlyZero (a : ℕ → ℝ) :
    (HasScalarAsymptoticExpansion (𝓝[≠] (0 : ℝ))
        (fun j x => x ^ j) a flatExponential ↔ a = fun _ => 0) ∧
    (HasScalarAsymptoticExpansion (𝓝[≠] (0 : ℝ))
        (fun j x => x ^ j) a (fun _ => 0) ↔ a = fun _ => 0) := by
  have hf := flatRemainder_commonZeroExpansion.1
  have hz := flatRemainder_commonZeroExpansion.2
  constructor
  · constructor
    · intro ha
      exact asymptoticExpansion_coefficients_unique _ _ a (fun _ => 0)
        flatExponential powerScale_at_zero ha hf
    · intro ha
      simpa only [ha] using hf
  · constructor
    · intro ha
      exact asymptoticExpansion_coefficients_unique _ _ a (fun _ => 0)
        (fun _ => 0) powerScale_at_zero ha hz
    · intro ha
      simpa only [ha] using hz

/-- They differ at every point of each punctured neighborhood, and each such
neighborhood contains a witness (so the assertion is nonvacuous). -/
theorem flatRemainder_differsEveryPuncturedNeighborhood (δ : ℝ) (hδ : 0 < δ) :
    (∀ x : ℝ, 0 < |x| → |x| < δ → flatExponential x ≠ 0) ∧
      ∃ x : ℝ, 0 < |x| ∧ |x| < δ ∧ flatExponential x ≠ 0 := by
  have hne : ∀ x : ℝ, 0 < |x| → flatExponential x ≠ 0 :=
    fun x hx => ne_of_gt (flatRemainder_pos x (abs_pos.mp hx))
  refine ⟨fun x hx _ => hne x hx, δ / 2, ?_, ?_, ?_⟩
  · rw [abs_of_pos (half_pos hδ)]
    exact half_pos hδ
  · rw [abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  · exact ne_of_gt (flatRemainder_pos _ (ne_of_gt (half_pos hδ)))

end SingleVariableAnalysis
