import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.StoneComplex
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.StoneReal

/-!
Complex Stone–Weierstrass on compact real sets, K03.16.stone_complex.
Conjugation supplies both real-valued components. Their real subalgebra
separates points, so the upstream real theorem approximates each component.
Adding the real approximation to i times the imaginary approximation gives
the required complex approximation. The closure statements follow from this
arbitrary uniform accuracy. This is the component argument in the manuscript.
-/
noncomputable section
namespace SingleVariableAnalysis

open scoped Topology
open Specs.SingleVariableAnalysis.Ch16.StoneComplex

/-- The real unital algebra of real-valued elements of a complex algebra. -/
def complexRealSubalgebra : realSubalgebraType := realSubalgebraValue

theorem complex_realSubalgebra_membership : realSubalgebraMembership := by
  intro K A g
  rfl

theorem complex_realSubalgebra_representation : realSubalgebraRepresentation := by
  intro K A f
  constructor
  · rintro ⟨hf, him⟩
    have heq : realLift K (realPart K f) = f := by
      ext x
      apply Complex.ext
      · rfl
      · exact (him x).symm
    exact ⟨realPart K f, by change realLift K (realPart K f) ∈ A; rw [heq]; exact hf,
      heq⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hg, fun x => rfl⟩

theorem complex_conjugation_apply : conjugationApply := by
  intro K u x
  rfl

theorem complex_component_formulas : componentFormulas := by
  intro K u
  constructor
  · ext x
    change ((u x).re : ℂ) = (2 : ℂ)⁻¹ * (u x + star (u x))
    simpa only [div_eq_mul_inv, mul_comm, starRingEnd_apply] using Complex.re_eq_add_conj (u x)
  · ext x
    change ((u x).im : ℂ) = (2 * Complex.I)⁻¹ * (u x - star (u x))
    simpa only [div_eq_mul_inv, mul_comm, starRingEnd_apply] using Complex.im_eq_sub_conj (u x)

theorem complex_real_components_mem : componentsMem := by
  intro K A hconj u hu
  constructor
  · change realLift K (realPart K u) ∈ A
    rw [(complex_component_formulas K u).1]
    exact A.smul_mem (A.add_mem hu (hconj u hu)) _
  · change realLift K (imagPart K u) ∈ A
    rw [(complex_component_formulas K u).2]
    exact A.smul_mem (A.sub_mem hu (hconj u hu)) _

theorem complex_component_separation : componentSeparation := by
  intro K u x y hxy
  by_contra h
  push Not at h
  exact hxy (Complex.ext h.1 h.2)

theorem complex_realSubalgebra_separates : realSubalgebraSeparates := by
  intro K A hconj hsep x y hxy
  obtain ⟨u, hu, hune⟩ := hsep x y hxy
  obtain ⟨hre, him⟩ := complex_real_components_mem K A hconj u hu
  rcases complex_component_separation K u x y hune with h | h
  · exact ⟨realPart K u, hre, h⟩
  · exact ⟨imagPart K u, him, h⟩

/-- Inclusion of real maps preserves the uniform norm, including on empty K. -/
theorem norm_realLift {K : Set ℝ} [CompactSpace K] (g : C(K, ℝ)) :
    ‖realLift K g‖ = ‖g‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
    intro x
    change ‖(g x : ℂ)‖ ≤ ‖g‖
    simpa only [Complex.norm_real] using g.norm_coe_le_norm x
  · apply (ContinuousMap.norm_le _ (norm_nonneg (realLift K g))).mpr
    intro x
    have hx : ‖(g x : ℂ)‖ ≤ ‖realLift K g‖ := (realLift K g).norm_coe_le_norm x
    simpa only [Complex.norm_real] using hx

theorem complex_stone_weierstrass_uniform_approximation : uniformApproximation := by
  intro K _ A hconj hsep f ε hε
  have hB := complex_realSubalgebra_separates K A hconj hsep
  obtain ⟨u, hu, hfu⟩ := real_stone_weierstrass_uniform_approximation
    K (realSubalgebraValue K A) hB (realPart K f) (ε / 2) (by positivity)
  obtain ⟨v, hv, hfv⟩ := real_stone_weierstrass_uniform_approximation
    K (realSubalgebraValue K A) hB (imagPart K f) (ε / 2) (by positivity)
  refine ⟨realLift K u + Complex.I • realLift K v,
    A.add_mem hu (A.smul_mem hv _), ?_⟩
  have hdecomp : f - (realLift K u + Complex.I • realLift K v) =
      realLift K (realPart K f - u) + Complex.I • realLift K (imagPart K f - v) := by
    ext x
    change f x - ((u x : ℂ) + Complex.I * (v x : ℂ)) =
      (((f x).re - u x : ℝ) : ℂ) + Complex.I * (((f x).im - v x : ℝ) : ℂ)
    apply Complex.ext <;> simp
  rw [hdecomp]
  calc
    _ ≤ ‖realLift K (realPart K f - u)‖ +
        ‖Complex.I • realLift K (imagPart K f - v)‖ := norm_add_le _ _
    _ = ‖realPart K f - u‖ + ‖imagPart K f - v‖ := by
      rw [norm_smul, Complex.norm_I, one_mul, norm_realLift, norm_realLift]
    _ < ε / 2 + ε / 2 := add_lt_add hfu hfv
    _ = ε := by ring

theorem complex_stone_weierstrass_pointwise_approximation : pointwiseApproximation := by
  intro K _ A hconj hsep f ε hε
  obtain ⟨g, hg, hfg⟩ :=
    complex_stone_weierstrass_uniform_approximation K A hconj hsep f ε hε
  exact ⟨g, hg, fun x => ((f - g).norm_coe_le_norm x).trans_lt hfg⟩

theorem complex_stone_weierstrass_uniform_closure : uniformClosureEqUniv := by
  intro K _ A hconj hsep
  apply Set.eq_univ_of_forall
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ :=
    complex_stone_weierstrass_uniform_approximation K A hconj hsep f ε hε
  exact ⟨g, hg, by simpa only [dist_eq_norm] using hfg⟩

theorem complex_stone_weierstrass_closure : closureEqTop := by
  intro K _ A hconj hsep
  apply SetLike.coe_injective
  rw [A.topologicalClosure_coe, complex_stone_weierstrass_uniform_closure K A hconj hsep]
  rfl

end SingleVariableAnalysis
