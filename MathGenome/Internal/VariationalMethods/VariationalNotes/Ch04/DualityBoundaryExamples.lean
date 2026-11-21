import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.DualityBoundaryExamples
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.ConvexProgramModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Classical
open Set Filter
open VariationalNotes.Ch04.BoundaryExamplesSpecs
namespace VariationalNotes.Ch04.BoundaryExamples

theorem square_primal_solution : BoundaryExamplesSpecs.square_primal_solution := by
  have hf : squareFeasible = {0} := by
    ext x
    simp only [squareFeasible, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro h
      nlinarith [sq_nonneg x]
    · rintro rfl
      norm_num
  refine ⟨hf, ?_, ?_⟩
  · apply le_antisymm
    · exact (iInf_le _ (⟨0, by simp [squareFeasible]⟩ : squareFeasible)).trans_eq (by simp)
    · apply le_iInf
      intro x
      have hx : x.val = 0 := by simpa [hf] using x.property
      simp [hx]
  · intro x hx y hy
    have hx0 : x = 0 := by simpa [hf] using hx
    have hy0 : y = 0 := by simpa [hf] using hy
    simp [hx0, hy0]

theorem square_convex_data : BoundaryExamplesSpecs.square_convex_data := by
  exact ⟨(LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn convex_univ, (show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow⟩

theorem square_dual_positive : BoundaryExamplesSpecs.square_dual_positive := by
  intro lam hlam
  have hmin (x : ℝ) : -1 / (4 * lam) ≤ squareLagrangian lam x := by
    unfold squareLagrangian
    apply (div_le_iff₀ (by positivity : 0 < 4 * lam)).2
    nlinarith [sq_nonneg (2 * lam * x + 1)]
  have heq : squareLagrangian lam (-1 / (2 * lam)) = -1 / (4 * lam) := by
    unfold squareLagrangian
    field_simp
    ring
  apply le_antisymm
  · exact (iInf_le _ (-1 / (2 * lam))).trans_eq (congrArg (fun r : ℝ => (r : EReal)) heq)
  · exact le_iInf (fun x => EReal.coe_le_coe (hmin x))

theorem square_dual_zero : BoundaryExamplesSpecs.square_dual_zero := by
  apply (EReal.eq_bot_iff_forall_lt _).2
  intro y
  apply lt_of_le_of_lt (iInf_le _ (y - 1))
  change ((squareLagrangian 0 (y - 1) : ℝ) : EReal) < (y : EReal)
  apply EReal.coe_lt_coe_iff.2
  simp only [squareLagrangian, zero_mul, add_zero]
  linarith

theorem square_dual_value : BoundaryExamplesSpecs.square_dual_value := by
  apply le_antisymm
  · apply iSup_le
    intro lam
    apply (iInf_le _ 0).trans_eq
    simp [squareLagrangian]
  · by_contra h
    have hneg : squareDual < (0 : EReal) := lt_of_not_ge h
    obtain ⟨r, hr, hr0⟩ := EReal.lt_iff_exists_real_btwn.mp hneg
    have hrneg : r < 0 := by exact_mod_cast hr0
    let lam : ℝ := -1 / (4 * r)
    have hlam : 0 < lam := div_pos_of_neg_of_neg (by norm_num) (by linarith)
    have heq : -1 / (4 * lam) = r := by
      dsimp [lam]
      field_simp
    have hle : (r : EReal) ≤ squareDual := by
      have hq := square_dual_positive lam hlam
      rw [heq] at hq
      exact hq.symm.le.trans (le_iSup (fun l : {l : ℝ // 0 ≤ l} => squareDualFunction l.val) ⟨lam, hlam.le⟩)
    exact (not_lt_of_ge hle) hr

theorem square_dual_not_attained : BoundaryExamplesSpecs.square_dual_not_attained := by
  intro lam hlam
  rw [square_dual_value]
  rcases eq_or_lt_of_le hlam with h | h
  · rw [← h, square_dual_zero]
    exact EReal.bot_lt_coe 0
  · rw [square_dual_positive lam h]
    apply EReal.coe_lt_coe_iff.2
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

private theorem positiveDomain_convex : Convex ℝ positiveDomain := by
  intro p hp q hq a b ha hb hab
  change 0 < a * p.2 + b * q.2
  change 0 < p.2 at hp
  change 0 < q.2 at hq
  by_cases h : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [h, hb1] using hq
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) hp) (mul_nonneg hb hq.le)

private theorem perspectiveConstraint_convex :
    ConvexOn ℝ positiveDomain perspectiveConstraint := by
  refine ⟨positiveDomain_convex, ?_⟩
  intro p hp q hq a b ha hb hab
  have hp0 : 0 < p.2 := hp
  have hq0 : 0 < q.2 := hq
  have hm : 0 < a * p.2 + b * q.2 :=
    positiveDomain_convex hp hq ha hb hab
  change (a * p.1 + b * q.1) ^ 2 / (a * p.2 + b * q.2) ≤
    a * (p.1 ^ 2 / p.2) + b * (q.1 ^ 2 / q.2)
  apply (div_le_iff₀ hm).2
  have hid :
      (a * (p.1 ^ 2 / p.2) + b * (q.1 ^ 2 / q.2)) * (a * p.2 + b * q.2) -
        (a * p.1 + b * q.1) ^ 2 =
      a * b / (p.2 * q.2) * (q.2 * p.1 - p.2 * q.1) ^ 2 := by
    field_simp
    ring
  have hn : 0 ≤ a * b / (p.2 * q.2) * (q.2 * p.1 - p.2 * q.1) ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg ha hb) (mul_pos hp0 hq0).le) (sq_nonneg _)
  linarith

theorem perspective_convex_data : BoundaryExamplesSpecs.perspective_convex_data := by
  refine ⟨positiveDomain_convex, ⟨positiveDomain_convex, ?_⟩, perspectiveConstraint_convex⟩
  intro p hp q hq a b ha hb hab
  have h := convexOn_exp.2 (mem_univ (-p.1)) (mem_univ (-q.1)) ha hb hab
  change Real.exp (-(a * p.1 + b * q.1)) ≤
    a * Real.exp (-p.1) + b * Real.exp (-q.1)
  convert h using 1
  congr 1
  simp only [smul_eq_mul]
  ring

theorem perspective_primal_solution : BoundaryExamplesSpecs.perspective_primal_solution := by
  have hf (z : ℝ × ℝ) : z ∈ perspectiveFeasible ↔ z.1 = 0 ∧ 0 < z.2 := by
    change (0 < z.2 ∧ z.1 ^ 2 / z.2 ≤ 0) ↔ _
    constructor
    · rintro ⟨hy, hxy⟩
      have hx : z.1 ^ 2 ≤ 0 := by
        simpa using (div_le_iff₀ hy).1 hxy
      exact ⟨by nlinarith [sq_nonneg z.1], hy⟩
    · rintro ⟨hx, hy⟩
      simp [hx, hy]
  have hval (z : ℝ × ℝ) (hz : z ∈ perspectiveFeasible) : exponentialObjective z = 1 := by
    simp [exponentialObjective, (hf z).1 hz |>.1]
  refine ⟨hf, ?_, hval, ?_⟩
  · apply le_antisymm
    · exact (iInf_le _ (⟨(0, 1), (hf _).2 ⟨rfl, by norm_num⟩⟩ : perspectiveFeasible)).trans_eq (by simp [exponentialObjective])
    · apply le_iInf
      intro z
      simp [hval z z.property]
  · intro z hz w hw
    rw [hval z hz, hval w hw]

private theorem perspective_curve_formula (lam t : ℝ) (ht : t ≠ 0) :
    perspectiveLagrangian lam (t, t ^ 3) = Real.exp (-t) + lam * t⁻¹ := by
  dsimp [perspectiveLagrangian, exponentialObjective, perspectiveConstraint]
  congr 1
  field_simp

theorem perspective_curve_limit : BoundaryExamplesSpecs.perspective_curve_limit := by
  intro lam
  have h : Tendsto (fun t : ℝ => Real.exp (-t) + lam * t⁻¹) atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.add
      (tendsto_inv_atTop_zero.const_mul lam)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (perspective_curve_formula lam t ht.ne').symm

theorem perspective_dual_function : BoundaryExamplesSpecs.perspective_dual_function := by
  intro lam hlam
  apply le_antisymm
  · by_contra h
    have hpos : (0 : EReal) < perspectiveDualFunction lam := lt_of_not_ge h
    obtain ⟨r, hr0, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hpos
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    have hev : ∀ᶠ t : ℝ in atTop, perspectiveLagrangian lam (t, t ^ 3) < r :=
      (tendsto_order.1 (perspective_curve_limit lam)).2 r hrpos
    obtain ⟨t, ht, htr⟩ := ( (eventually_gt_atTop (0 : ℝ)).and hev).exists
    have hz : (t, t ^ 3) ∈ positiveDomain := by
      change 0 < t ^ 3
      positivity
    have hle : perspectiveDualFunction lam ≤
        (perspectiveLagrangian lam (t, t ^ 3) : EReal) :=
      iInf_le _ (⟨(t, t ^ 3), hz⟩ : positiveDomain)
    exact (not_lt_of_ge (hle.trans (EReal.coe_le_coe htr.le))) hr
  · apply le_iInf
    intro z
    apply EReal.coe_nonneg.2
    exact add_nonneg (Real.exp_pos _).le
      (mul_nonneg hlam (div_nonneg (sq_nonneg _) z.property.le))

theorem perspective_dual_value_attained : BoundaryExamplesSpecs.perspective_dual_value_attained := by
  have hdual : perspectiveDual = 0 := by
    apply le_antisymm
    · apply iSup_le
      intro lam
      exact (perspective_dual_function lam lam.property).le
    · have h := le_iSup (fun l : {l : ℝ // 0 ≤ l} => perspectiveDualFunction l.val)
        (⟨0, le_refl 0⟩ : {l : ℝ // 0 ≤ l})
      simpa only [perspectiveDual, perspective_dual_function 0 (le_refl 0)] using h
  refine ⟨hdual, ?_, ?_⟩
  · intro lam hlam
    rw [perspective_dual_function lam hlam, hdual]
  · rw [perspective_primal_solution.2.1, hdual, sub_zero]

/-- Passing from real convex data on a convex domain to the manuscript's
extended epigraph definition introduces no regularity or closedness assumption. -/
private theorem convex_extension {X : Type*} [AddCommGroup X] [Module ℝ X]
    {D : Set X} {f : X → ℝ} (h : ConvexOn ℝ D f) :
    VariationalNotes.ConvexAnalysis.Specs.IsConvex
      (fun x => if x ∈ D then (f x : WithTop ℝ) else ⊤) := by
  classical
  apply (VariationalNotes.ConvexAnalysis.convex_iff_twoPoint _).2
  intro x y r s hr hs a b ha hb hab
  have hx : x ∈ D := by
    by_contra hn
    simp [hn] at hr
  have hy : y ∈ D := by
    by_contra hn
    simp [hn] at hs
  have hr' : f x = r := by simpa [hx] using hr
  have hs' : f y = s := by simpa [hy] using hs
  rw [ite_eq_left (h.1 hx hy ha hb hab)]
  exact WithTop.coe_le_coe.mpr (by simpa [hr', hs', smul_eq_mul] using h.2 hx hy ha hb hab)

theorem square_extended_data : BoundaryExamplesSpecs.square_extended_data := by
  have hf := convex_extension square_convex_data.1
  have hg := convex_extension square_convex_data.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change VariationalNotes.ConvexAnalysis.Specs.IsConvex (fun x : ℝ => (x : WithTop ℝ))
    simpa only [mem_univ, ite_true] using hf
  · change VariationalNotes.ConvexAnalysis.Specs.IsConvex (fun x : ℝ => ((x ^ 2 : ℝ) : WithTop ℝ))
    simpa only [mem_univ, ite_true] using hg
  · ext x
    simp [VariationalNotes.ConvexAnalysis.Specs.effectiveDomain, squareObjectiveExtended]
  · ext x
    simp [VariationalNotes.ConvexAnalysis.Specs.effectiveDomain, squareConstraintExtended]

theorem perspective_extended_data : BoundaryExamplesSpecs.perspective_extended_data := by
  refine ⟨convex_extension perspective_convex_data.2.1,
    convex_extension perspective_convex_data.2.2, ?_, ?_⟩
  · ext z
    by_cases hz : z ∈ positiveDomain <;>
      simp [VariationalNotes.ConvexAnalysis.Specs.effectiveDomain,
        exponentialObjectiveExtended, hz]
  · ext z
    by_cases hz : z ∈ positiveDomain <;>
      simp [VariationalNotes.ConvexAnalysis.Specs.effectiveDomain,
        perspectiveConstraintExtended, hz]

end VariationalNotes.Ch04.BoundaryExamples
