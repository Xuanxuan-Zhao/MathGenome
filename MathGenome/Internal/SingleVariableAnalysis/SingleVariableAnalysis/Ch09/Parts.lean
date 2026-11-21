import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Product
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
Integration by parts for the proper Riemann integral (K03.09.parts).
The proof uses the product rule, Darboux product integrability, finite
linearity, and the upstream Newton–Leibniz theorem. Endpoint derivative
extensions are unrestricted there. The private continuity lemma supplies
integrability directly by uniform continuity and the Darboux criterion.
-/
namespace SingleVariableAnalysis.Riemann
open Set
open scoped BigOperators

private theorem parts_continuous_real_integrable {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) : RealIntegrable f a b := by
  have hb : BoundedOnInterval f a b :=
    ⟨(isCompact_Icc.image_of_continuousOn hc).bddBelow,
      (isCompact_Icc.image_of_continuousOn hc).bddAbove⟩
  apply (realIntegrable_iff_small_gap f hab hb).mpr
  intro ε hε
  let η := ε / (b - a + 1)
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) η hη
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  have hosc (i : Fin P.n) : cellSupremum f P hb i - cellInfimum f P hb i ≤ η := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    have hxy : |x - y| < δ := by
      have hbound : |x - y| ≤ cellLength P i := by
        apply abs_le.mpr
        change _ ≤ x - y ∧ x - y ≤ _
        change _ ≤ x ∧ x ≤ _ at hx
        change _ ≤ y ∧ y ≤ _ at hy
        dsimp [cellLength, Specs.SingleVariableAnalysis.Ch08.Partitions.lengthValue]
        constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      exact hbound.trans_lt ((cellLength_le_mesh P i).trans_lt hP)
    have hdiff : |f x - f y| < η := by
      simpa only [Real.dist_eq] using huc x (cell_subset_interval P i hx)
        y (cell_subset_interval P i hy) (by simpa only [Real.dist_eq] using hxy)
    exact (le_abs_self _).trans hdiff.le
  refine ⟨P, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hosc i) (cell_positive P i).le
  rw [sum_cell_oscillation, ← Finset.mul_sum, sum_cellLength] at hsum
  refine hsum.trans_lt ?_
  have he : η * (b - a + 1) = ε := div_mul_cancel₀ _ (by positivity)
  nlinarith

private theorem parts_continuous_complex_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) : ComplexIntegrable f a b :=
  ⟨parts_continuous_real_integrable hab (Complex.continuous_re.comp_continuousOn hc),
    parts_continuous_real_integrable hab (Complex.continuous_im.comp_continuousOn hc)⟩

theorem real_parts : Specs.SingleVariableAnalysis.Ch09.Parts.realParts := by
  intro u v du dv a b hab hu hv hdu hdv hdui hdvi
  have h₁ := real_product (parts_continuous_real_integrable hab hu) hdvi
  have h₂ := real_product hdui (parts_continuous_real_integrable hab hv)
  obtain ⟨hs, he⟩ := real_add_value h₂ h₁
  have hftc := real_ftc_second (fun x => u x * v x)
    (fun x => du x * v x + u x * dv x) a b hab (hu.mul hv)
    (fun x hx => (hdu x hx).mul (hdv x hx)) hs
  change realIntegral _ hs = u b * v b - u a * v a at hftc
  have hsum := he.symm.trans hftc
  exact ⟨h₁, h₂, eq_sub_of_add_eq (by simpa only [add_comm] using hsum)⟩

theorem complex_parts : Specs.SingleVariableAnalysis.Ch09.Parts.complexParts := by
  intro u v du dv a b hab hu hv hdu hdv hdui hdvi
  have h₁ := complex_product (parts_continuous_complex_integrable hab hu) hdvi
  have h₂ := complex_product hdui (parts_continuous_complex_integrable hab hv)
  obtain ⟨hs, he⟩ := complex_add_value h₂ h₁
  have hftc := complex_ftc_second (fun x => u x * v x)
    (fun x => du x * v x + u x * dv x) a b hab (hu.mul hv)
    (fun x hx => (hdu x hx).mul (hdv x hx)) hs
  refine ⟨h₁, h₂, ?_⟩
  change complexIntegral _ hs = u b * v b - u a * v a at hftc
  exact eq_sub_of_add_eq (by simpa only [add_comm] using he.symm.trans hftc)

theorem real_parts_oriented : Specs.SingleVariableAnalysis.Ch09.Parts.realPartsOriented := by
  intro u v du dv a b hu hv hdu hdv hdui hdvi
  obtain ⟨h₁, h₂, he⟩ := real_parts u v du dv (min a b) (max a b)
    (min_le_max) hu hv hdu hdv hdui hdvi
  refine ⟨h₁, h₂, ?_⟩
  by_cases hab : a ≤ b
  · simpa only [hab, ite_true, one_mul, min_eq_left hab, max_eq_right hab] using he
  · have hba := le_of_not_ge hab
    have he' : -realIntegral _ h₁ =
        u (min a b) * v (min a b) - u (max a b) * v (max a b) - -realIntegral _ h₂ := by
      change realIntegral _ h₁ = _ at he
      rw [he]
      ring
    simpa only [hab, ite_false, neg_one_mul, min_eq_right hba, max_eq_left hba] using he'

theorem complex_parts_oriented : Specs.SingleVariableAnalysis.Ch09.Parts.complexPartsOriented := by
  intro u v du dv a b hu hv hdu hdv hdui hdvi
  obtain ⟨h₁, h₂, he⟩ := complex_parts u v du dv (min a b) (max a b)
    (min_le_max) hu hv hdu hdv hdui hdvi
  refine ⟨h₁, h₂, ?_⟩
  by_cases hab : a ≤ b
  · simpa only [hab, ite_true, one_mul, min_eq_left hab, max_eq_right hab] using he
  · have hba := le_of_not_ge hab
    have he' : -complexIntegral _ h₁ =
        u (min a b) * v (min a b) - u (max a b) * v (max a b) - -complexIntegral _ h₂ := by
      change complexIntegral _ h₁ = _ at he
      rw [he]
      ring
    simpa only [hab, ite_false, neg_one_mul, min_eq_right hba, max_eq_left hba] using he'

private theorem parts_c1_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ContinuousOn (derivWithin f (Icc a b)) (Icc a b) ∧
      ∀ x ∈ Ioo a b, HasDerivAt f (derivWithin f (Icc a b) x) x := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · exact ⟨hf.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl,
      fun x hx => (hf.differentiableOn_one x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)⟩
  · exact ⟨by simp only [Icc_self]; exact continuousOn_singleton _ _,
      by simp only [Ioo_self, mem_empty_iff_false, false_implies, implies_true]⟩

theorem real_parts_c1 : Specs.SingleVariableAnalysis.Ch09.Parts.realPartsC1 := by
  intro u v a b hu hv
  obtain ⟨huc, hud⟩ := parts_c1_derivative min_le_max hu
  obtain ⟨hvc, hvd⟩ := parts_c1_derivative min_le_max hv
  have hui := parts_continuous_real_integrable min_le_max huc
  have hvi := parts_continuous_real_integrable min_le_max hvc
  exact ⟨hui, hvi, real_parts_oriented u v _ _ a b hu.continuousOn hv.continuousOn
    hud hvd hui hvi⟩

theorem complex_parts_c1 : Specs.SingleVariableAnalysis.Ch09.Parts.complexPartsC1 := by
  intro u v a b hu hv
  obtain ⟨huc, hud⟩ := parts_c1_derivative min_le_max hu
  obtain ⟨hvc, hvd⟩ := parts_c1_derivative min_le_max hv
  have hui := parts_continuous_complex_integrable min_le_max huc
  have hvi := parts_continuous_complex_integrable min_le_max hvc
  exact ⟨hui, hvi, complex_parts_oriented u v _ _ a b hu.continuousOn hv.continuousOn
    hud hvd hui hvi⟩

end SingleVariableAnalysis.Riemann
