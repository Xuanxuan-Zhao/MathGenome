import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsDensity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.C1Variation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsExistence

/-! A smooth real integrator has its continuous derivative as density.
All estimates concern the project's actual strict partitions, arbitrary closed
cell tags, and proper Riemann integral, with no measure-integral replacement. -/
namespace SingleVariableAnalysis.Stieltjes
open Riemann Set
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch15.RsDensity (derivativeModulus)
namespace Density

lemma modulus_set_nonempty {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    (g : ℝ → ℝ) :
    {z : ℝ | ∃ x ∈ Icc a b, ∃ y ∈ Icc a b,
      |x-y| ≤ r ∧ z = ‖g x-g y‖}.Nonempty :=
  ⟨0, a, left_mem_Icc.mpr hab, a, left_mem_Icc.mpr hab,
    by simpa using hr, by simp⟩

lemma modulus_set_bddAbove {a b r : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    BddAbove {z : ℝ | ∃ x ∈ Icc a b, ∃ y ∈ Icc a b,
      |x-y| ≤ r ∧ z = ‖g x-g y‖} := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hg.norm
  refine ⟨2 * M, ?_⟩
  rintro z ⟨x, hx, y, hy, _, rfl⟩
  have hx' := hM (Set.mem_image_of_mem _ hx)
  have hy' := hM (Set.mem_image_of_mem _ hy)
  exact (norm_sub_le _ _).trans (by linarith)

lemma norm_sub_le_modulus {a b r x y : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : |x-y| ≤ r) : ‖g x-g y‖ ≤ derivativeModulus a b g r :=
  le_csSup (modulus_set_bddAbove hg) ⟨x, hx, y, hy, hxy, rfl⟩

lemma modulus_nonneg {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) : 0 ≤ derivativeModulus a b g r := by
  simpa using norm_sub_le_modulus hg (left_mem_Icc.mpr hab)
    (left_mem_Icc.mpr hab) (by simpa using hr : |a-a| ≤ r)

end Density

theorem derivative_modulus_vanishes :
    Specs.SingleVariableAnalysis.Ch15.RsDensity.modulusVanishes := by
  intro a b hab g hg ε hε
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) (ε/2) (half_pos hε)
  refine ⟨δ, hδ, fun r hr hrd => ⟨Density.modulus_nonneg hab hr hg, ?_⟩⟩
  have hle : derivativeModulus a b g r ≤ ε/2 := by
    apply csSup_le (Density.modulus_set_nonempty hab hr g)
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    have h := hc x hx y hy (by simpa only [Real.dist_eq] using hxy.trans_lt hrd)
    simpa only [dist_eq_norm] using h.le
  linarith

/-- Sum the cell chord errors after multiplying by each integrand tag value. -/
theorem smooth_mesh_comparison :
    Specs.SingleVariableAnalysis.Ch15.RsDensity.meshComparison := by
  intro E _ _ a b hab f α g hf hd hg P t
  classical
  let M := Specs.SingleVariableAnalysis.Ch15.RsExistence.supNorm a b f
  let w := derivativeModulus a b g (mesh P)
  have hM (x : ℝ) (hx : x ∈ Icc a b) : ‖f x‖ ≤ M :=
    le_csSup (isCompact_Icc.bddAbove_image hf.norm) (mem_image_of_mem _ hx)
  have hw : 0 ≤ w := Density.modulus_nonneg hab (mesh_nonneg P) hg
  have herr (i : Fin P.n) :
      ‖α (P.point i.succ) - α (P.point i.castSucc) - cellLength P i * g (t i)‖ ≤
        w * cellLength P i := by
    apply BV.chord_error_le hd P i (t i)
    intro x hx
    apply Density.norm_sub_le_modulus hg (cell_subset_interval P i hx)
      (tag_mem_interval P t i)
    exact (BV.cell_dist_le_length P i hx (t i).property).trans (cellLength_le_mesh P i)
  have he : taggedSum P t f α - Riemann.taggedSum P t (fun x => g x • f x) =
      ∑ i : Fin P.n,
        (α (P.point i.succ) - α (P.point i.castSucc) - cellLength P i * g (t i)) •
          f (t i) := by
    simp only [taggedSum, S.sumValue, Riemann.taggedSum, Riemann.S.sumValue,
      ← mul_smul, ← Finset.sum_sub_distrib, sub_smul]
  rw [he]
  calc
    _ ≤ ∑ i : Fin P.n,
        ‖α (P.point i.succ) - α (P.point i.castSucc) - cellLength P i * g (t i)‖ *
          ‖f (t i)‖ := by
      simpa only [norm_smul] using norm_sum_le Finset.univ
        (fun i : Fin P.n =>
          (α (P.point i.succ) - α (P.point i.castSucc) - cellLength P i * g (t i)) •
            f (t i))
    _ ≤ ∑ i : Fin P.n, (w * cellLength P i) * M := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (herr i) (hM _ (tag_mem_interval P t i)) (norm_nonneg _)
        (mul_nonneg hw (cell_positive P i).le)
    _ = M * w * (b-a) := by
      rw [← sum_cellLength P, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A smooth integrator is BV with no assumption on its derivative's sign. -/
lemma boundedVariation_of_c1 {a b : ℝ} (hab : a ≤ b) {α g : ℝ → ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt α (g x) (Icc a b) x)
    (hg : ContinuousOn g (Icc a b)) : BV.HasBoundedVariation α a b := by
  obtain ⟨hn, hv⟩ := BV.c1_variation α g a b hab hd hg
  change Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue α a b < ⊤
  rw [hv]
  exact ENNReal.ofReal_lt_top

private lemma triangle {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x-z‖ ≤ ‖x-y‖ + ‖y-z‖ := by
  simpa only [sub_add_sub_cancel] using norm_add_le (x-y) (y-z)

/-- The quantitative comparison identifies any two of the mesh limits. -/
lemma smooth_limits_equal {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → E) (α g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt α (g x) (Icc a b) x)
    (hg : ContinuousOn g (Icc a b)) {I J : E}
    (hI : Specs.SingleVariableAnalysis.Ch15.RsExistence.meshLimit a b f α I)
    (hJ : FineTaggedLimit (fun x => g x • f x) a b J) : I = J := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let M := Specs.SingleVariableAnalysis.Ch15.RsExistence.supNorm a b f
  have hM : 0 ≤ M := (norm_nonneg (f a)).trans
    (le_csSup (isCompact_Icc.bddAbove_image hf.norm)
      (mem_image_of_mem _ (left_mem_Icc.mpr hab)))
  let C := M * (b-a)
  have hC : 0 ≤ C := mul_nonneg hM (sub_nonneg.mpr hab)
  let η := ε / (4 * (C+1))
  have hden : 0 < 4 * (C+1) := by positivity
  have hη : 0 < η := div_pos hε hden
  have hsmall : η * C < ε/2 := by
    have he : η * (4 * (C+1)) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
    nlinarith
  obtain ⟨δg, hδg, hmod⟩ := derivative_modulus_vanishes a b hab g hg η hη
  obtain ⟨δI, hδI, hIc⟩ := hI (ε/4) (by positivity)
  obtain ⟨δJ, hδJ, hJc⟩ := hJ (ε/4) (by positivity)
  obtain ⟨P, hP⟩ := exists_fine_partition hab (min δg (min δI δJ))
    (lt_min hδg (lt_min hδI hδJ))
  obtain ⟨t⟩ := tags_exist P
  have hPg := hP.trans_le (min_le_left _ _)
  have hPI := hP.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hPJ := hP.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have h₁ := hIc P hPI t
  have h₂ := hJc P t hPJ
  have hmod' := (hmod (mesh P) (mesh_nonneg P) hPg).2
  have hcomp := smooth_mesh_comparison a b hab f α g hf hd hg P t
  have herr : ‖taggedSum P t f α - Riemann.taggedSum P t (fun x => g x • f x)‖ < ε/2 := by
    have hle : M * derivativeModulus a b g (mesh P) * (b-a) ≤ η * C := by
      calc
        _ = derivativeModulus a b g (mesh P) * C := by dsimp [C]; ring
        _ ≤ η * C := mul_le_mul_of_nonneg_right hmod'.le hC
    exact hcomp.trans_lt (hle.trans_lt hsmall)
  have ht₁ := triangle I (taggedSum P t f α) J
  have ht₂ := triangle (taggedSum P t f α)
    (Riemann.taggedSum P t (fun x => g x • f x)) J
  rw [norm_sub_rev I (taggedSum P t f α)] at ht₁
  linarith

/-- The real density formula, with existence of the ordinary proper integral. -/
theorem real_smooth_integrator :
    Specs.SingleVariableAnalysis.Ch15.RsDensity.realDensity := by
  intro a b hab f α g hf hd hg
  let h := BV.continuousOn_realIntegrable hab (hf.mul hg)
  obtain ⟨I, hI, _, hmesh⟩ := continuous_bv_integral hab f α hf
    (boundedVariation_of_c1 hab hd hg)
  have hlim := (real_tagged_equivalence (fun x => f x * g x) hab
    (RealIntegrable.bounded h) (realIntegral _ h)).mp ⟨h, rfl⟩
  have he : I = realIntegral (fun x => f x * g x) h :=
    smooth_limits_equal hab f α g hf hd hg hmesh (by
      intro ε hε
      obtain ⟨δ, hδ, hc⟩ := hlim ε hε
      refine ⟨δ, hδ, fun P t hP => ?_⟩
      have hc' := hc P t hP
      have heq : Riemann.taggedSum P t (fun x => g x • f x) =
          ∑ i : Fin P.n, cellLength P i * (f (t i) * g (t i)) := by
        apply Finset.sum_congr rfl
        intro i _
        change cellLength P i * (g (t i) * f (t i)) = _
        rw [mul_comm (g (t i)) (f (t i))]
      change ‖Riemann.taggedSum P t (fun x => g x • f x) - _‖ < ε
      rw [heq]
      simp only [Specs.SingleVariableAnalysis.Ch08.Partitions.sumValue, smul_eq_mul] at hc'
      convert hc' using 1)
  rw [he] at hI hmesh
  exact ⟨h, hI, hmesh⟩

/-- Complex values use real scalar increments of the same real integrator. -/
theorem complex_smooth_integrator :
    Specs.SingleVariableAnalysis.Ch15.RsDensity.complexDensity := by
  intro a b hab f α g hf hd hg
  let p : ℝ → ℂ := fun x => f x * (g x : ℂ)
  have hp : ContinuousOn p (Icc a b) :=
    hf.mul (Complex.continuous_ofReal.comp_continuousOn hg)
  have h : ComplexIntegrable p a b :=
    ⟨BV.continuousOn_realIntegrable hab (Complex.continuous_re.comp_continuousOn hp),
      BV.continuousOn_realIntegrable hab (Complex.continuous_im.comp_continuousOn hp)⟩
  obtain ⟨I, hI, _, hmesh⟩ := continuous_bv_integral hab f α hf
    (boundedVariation_of_c1 hab hd hg)
  have hb : ∃ M : ℝ, ∀ x ∈ Icc a b, ‖p x‖ ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hp.norm
    exact ⟨M, fun x hx => hM (mem_image_of_mem _ hx)⟩
  have hlim := (complex_tagged_equivalence p hab hb (complexIntegral p h)).mp ⟨h, rfl⟩
  have he : I = complexIntegral p h :=
    smooth_limits_equal hab f α g hf hd hg hmesh (by
      simpa only [p, Complex.real_smul, mul_comm] using hlim)
  rw [he] at hI hmesh
  exact ⟨h, hI, hmesh⟩

end SingleVariableAnalysis.Stieltjes
