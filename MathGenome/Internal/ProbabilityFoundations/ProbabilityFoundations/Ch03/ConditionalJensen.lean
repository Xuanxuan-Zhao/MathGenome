import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalJensen
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.BasicConditionalIdentities
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous

/-! Conditional Jensen, paper.tex 939–984. We represent the extended
expectation in `EReal` as the difference of the two canonical nonnegative
conditional expectations. One affine minorant controls the negative part.
Conditional comparison with integrable lower bounds and a countable affine
supremum give the inequality on a single almost-sure event.
-/

open MeasureTheory Function Set Filter
open scoped ENNReal

namespace ProbabilityFoundations.Ch03

universe u

noncomputable def extendedConditionalExpectation :
    ∀ {Ω : Type u} (_G : MeasurableSpace Ω) [F : MeasurableSpace Ω],
      Measure[F] Ω → (Ω → ℝ) → (Ω → EReal) :=
  fun {_Ω} G _F P Y ω =>
    (condLExp G P (fun ω => ENNReal.ofReal (Y ω)) ω : EReal) -
      (condLExp G P (fun ω => ENNReal.ofReal (-Y ω)) ω : EReal)

theorem finite_convex_continuous (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    Continuous φ ∧ Measurable φ := by
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  exact ⟨hc, hc.measurable⟩

theorem convex_negative_part_integrable {Ω : Type u} [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (φ : ℝ → ℝ)
    (hX : Integrable X P) (hφ : ConvexOn ℝ univ φ) :
    Integrable (fun ω => max (-(φ (X ω))) 0) P := by
  have hc := (finite_convex_continuous φ hφ).1
  obtain ⟨a, b, hab⟩ := hφ.exists_affine_le_real isClosed_univ
    (lowerSemicontinuousOn_univ_iff.mpr hc.lowerSemicontinuous)
  have hi : Integrable (fun ω => a * X ω + b) P :=
    (hX.const_mul a).add (integrable_const b)
  apply hi.neg_part.mono'
    (((continuous_neg.comp hc).max continuous_const).comp_aestronglyMeasurable hX.1)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le_max (neg_le_neg (hab (X ω) (mem_univ _))) le_rfl

private lemma condLExp_ofReal_positive_part {Ω : Type u} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] (P : Measure[F] Ω) (Y : Ω → ℝ)
    (hY : Integrable (fun ω => max (Y ω) 0) P) :
    condLExp G P (fun ω => ENNReal.ofReal (Y ω)) =ᵐ[P]
      (fun ω => ENNReal.ofReal (condExp G P (fun ω => max (Y ω) 0) ω)) := by
  simpa using
    (condLExp_ofReal G hY (ae_of_all _ (fun ω => le_max_right (Y ω) 0)))

private lemma negative_conditional_finite {Ω : Type u} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] (P : Measure[F] Ω) (Y : Ω → ℝ)
    (hY : Integrable (fun ω => max (-Y ω) 0) P) :
    ∀ᵐ ω ∂P, condLExp G P (fun ω => ENNReal.ofReal (-Y ω)) ω < ∞ := by
  filter_upwards [condLExp_ofReal_positive_part G P (fun ω => -Y ω) hY] with ω hω
  rw [hω]
  exact ENNReal.ofReal_lt_top

theorem convex_negative_conditional_finite {Ω : Type u} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] (P : Measure[F] Ω) [IsProbabilityMeasure P] (_hGF : G ≤ F)
    (X : Ω → ℝ) (φ : ℝ → ℝ) (hX : Integrable X P) (hφ : ConvexOn ℝ univ φ) :
    ∀ᵐ ω ∂P, condLExp G P (fun ω => ENNReal.ofReal (-(φ (X ω)))) ω < ∞ :=
  negative_conditional_finite G P _ (convex_negative_part_integrable P X φ hX hφ)

private lemma real_parts_sub (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with hx | hx
  · simp [hx, neg_nonpos.mpr hx]
  · simp [hx, neg_nonneg.mpr hx]

theorem extendedConditionalExpectation_integrable {Ω : Type u} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] (P : Measure[F] Ω) [IsProbabilityMeasure P] (_hGF : G ≤ F)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    extendedConditionalExpectation G P Y =ᵐ[P]
      (fun ω => ((condExp G P Y ω : ℝ) : EReal)) := by
  have hs := condExp_sub hY.pos_part hY.neg_part G
  have heq : (fun ω => max (Y ω) 0 - max (-Y ω) 0) = Y :=
    funext (fun ω => real_parts_sub (Y ω))
  change condExp G P (fun ω => max (Y ω) 0 - max (-Y ω) 0) =ᵐ[P] _ at hs
  rw [heq] at hs
  filter_upwards [condLExp_ofReal_positive_part G P Y hY.pos_part,
    condLExp_ofReal_positive_part G P (fun ω => -Y ω) hY.neg_part, hs,
    condExp_nonneg (m := G) (μ := P) (ae_of_all _ (fun ω => le_max_right (Y ω) 0)),
    condExp_nonneg (m := G) (μ := P) (ae_of_all _ (fun ω => le_max_right (-Y ω) 0))]
    with ω hp hn hs hpos hneg
  simp only [extendedConditionalExpectation, hp, hn]
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal]
  simp only [Pi.zero_apply] at hpos hneg
  rw [max_eq_left hpos, max_eq_left hneg]
  exact (EReal.coe_sub _ _).symm.trans (congrArg (fun x : ℝ => (x : EReal)) hs.symm)

private lemma ennreal_parts_order {x y : ℝ} (hxy : x ≤ y) :
    ENNReal.ofReal x + ENNReal.ofReal (-y) ≤
      ENNReal.ofReal y + ENNReal.ofReal (-x) := by
  have hm : max x 0 + max (-y) 0 ≤ max y 0 + max (-x) 0 := by
    have hx := real_parts_sub x
    have hy := real_parts_sub y
    linarith
  have hp (a b : ℝ) : ENNReal.ofReal a + ENNReal.ofReal b =
      ENNReal.ofReal (max a 0 + max b 0) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    simp
  rw [hp, hp]
  exact ENNReal.ofReal_le_ofReal hm

private lemma ereal_parts_order (a b c d : ℝ≥0∞)
    (hb : b ≠ ∞) (hc : c ≠ ∞) (hd : d ≠ ∞) (h : c + b ≤ a + d) :
    (c : EReal) - (d : EReal) ≤ (a : EReal) - (b : EReal) := by
  by_cases ha : a = ∞
  · subst a
    rw [EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hb, EReal.top_sub_coe]
    exact le_top
  · have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ha, hd⟩) h
    rw [ENNReal.toReal_add hc hb, ENNReal.toReal_add ha hd] at hr
    rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb,
      ← EReal.coe_ennreal_toReal hc, ← EReal.coe_ennreal_toReal hd,
      ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

/-- Conditional comparison with an integrable lower bound, retaining a possibly
infinite positive conditional integral on the right. -/
theorem conditional_integrable_lower_bound {Ω : Type u} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] (P : Measure[F] Ω) [IsProbabilityMeasure P] (hGF : G ≤ F)
    (Z Y : Ω → ℝ) (hZ : Integrable Z P) (hYm : AEStronglyMeasurable Y P)
    (hYn : Integrable (fun ω => max (-Y ω) 0) P) (hZY : Z ≤ᵐ[P] Y) :
    ∀ᵐ ω ∂P, ((condExp G P Z ω : ℝ) : EReal) ≤
      extendedConditionalExpectation G P Y ω := by
  have hparts : (fun ω => ENNReal.ofReal (Z ω) + ENNReal.ofReal (-Y ω)) ≤ᵐ[P]
      (fun ω => ENNReal.ofReal (Y ω) + ENNReal.ofReal (-Z ω)) := by
    filter_upwards [hZY] with ω hω using ennreal_parts_order hω
  have hmono := condLExp_mono (mΩ := G) hparts
  have hl := condLExp_add_left (mΩ := G) (fun ω => ENNReal.ofReal (-Y ω))
    hZ.1.aemeasurable.ennreal_ofReal
  have hr := condLExp_add_left (mΩ := G) (fun ω => ENNReal.ofReal (-Z ω))
    hYm.aemeasurable.ennreal_ofReal
  have hzp : ∀ᵐ ω ∂P, condLExp G P (fun ω => ENNReal.ofReal (Z ω)) ω ≠ ∞ := by
    filter_upwards [condLExp_ofReal_positive_part G P Z hZ.pos_part] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  filter_upwards [hmono, hl, hr, hzp, negative_conditional_finite G P Z hZ.neg_part,
    negative_conditional_finite G P Y hYn,
    extendedConditionalExpectation_integrable G P hGF Z hZ] with ω hm hl hr hp hn hYn hZeq
  simp only [Pi.add_apply] at hl hr
  change condLExp G P (fun ω => ENNReal.ofReal (Z ω) + ENNReal.ofReal (-Y ω)) ω = _ at hl
  change condLExp G P (fun ω => ENNReal.ofReal (Y ω) + ENNReal.ofReal (-Z ω)) ω = _ at hr
  rw [hl, hr] at hm
  rw [← hZeq]
  exact ereal_parts_order _ _ _ _ hYn.ne hp hn.ne hm

/-- Conditional Jensen for every finite convex function on the whole real line.
Only `X` is assumed integrable; the right side may equal positive infinity. -/
theorem conditional_jensen {Ω : Type u} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] (P : Measure[F] Ω) [IsProbabilityMeasure P] (hGF : G ≤ F)
    (X : Ω → ℝ) (φ : ℝ → ℝ) (hX : Integrable X P) (hφ : ConvexOn ℝ univ φ) :
    ∀ᵐ ω ∂P, (φ (condExp G P X ω) : EReal) ≤
      extendedConditionalExpectation G P (fun ω => φ (X ω)) ω := by
  have hc := (finite_convex_continuous φ hφ).1
  have hYn := convex_negative_part_integrable P X φ hX hφ
  obtain ⟨L, c, hle, hsup⟩ := hφ.real_univ_sSup_of_nat_affine_eq hc.lowerSemicontinuous
  have hp : ∀ᵐ ω ∂P, ∀ i : ℕ,
      ((L i (condExp G P X ω) + c i : ℝ) : EReal) ≤
        extendedConditionalExpectation G P (fun ω => φ (X ω)) ω := by
    apply ae_all_iff.mpr
    intro i
    have hlin := (L i).comp_condExp_add_const_comm hGF hX (c i)
    have hbound := conditional_integrable_lower_bound G P hGF
      (fun ω => L i (X ω) + c i) (fun ω => φ (X ω))
      (((L i).integrable_comp hX).add (integrable_const (c i)))
      (hc.comp_aestronglyMeasurable hX.1) hYn
      (ae_of_all _ (fun ω => hle i (X ω)))
    filter_upwards [hlin, hbound] with ω hlin hbound
    exact hlin ▸ hbound
  filter_upwards [hp] with ω hω
  by_cases ht : extendedConditionalExpectation G P (fun ω => φ (X ω)) ω = ⊤
  · rw [ht]
    exact le_top
  · have hb : extendedConditionalExpectation G P (fun ω => φ (X ω)) ω ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hω 0)
    generalize hz : extendedConditionalExpectation G P (fun ω => φ (X ω)) ω = z at *
    lift z to ℝ using ⟨ht, hb⟩
    apply EReal.coe_le_coe_iff.mpr
    have hsup' : (⨆ i, L i (condExp G P X ω) + c i) = φ (condExp G P X ω) := by
      simpa using congrFun hsup (condExp G P X ω)
    rw [← hsup']
    exact ciSup_le (fun i => EReal.coe_le_coe_iff.mp (hω i))

end ProbabilityFoundations.Ch03
