import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import Mathlib.Topology.Order.Compact

/-!
# Continuity of proper Riemann integral families

K03.14.proper_continuity. The proof uses the existing Darboux integral,
linearity and its norm estimate. Compact uniform continuity supplies the
rectangle specialization. All domain topologies are the induced topologies,
so the assertions include endpoints and degenerate intervals.
-/
namespace SingleVariableAnalysis.ParameterIntegral
open scoped Topology BigOperators
open Riemann
namespace C
export Specs.SingleVariableAnalysis.Ch14.ProperContinuity (sectionError realFamily complexFamily)
end C

/-- Linearity for a difference, retaining integrability of both inputs. -/
theorem real_difference_value {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) :
    ∃ hd : RealIntegrable (fun x => f x - g x) a b,
      realIntegral _ hd = realIntegral f hf - realIntegral g hg := by
  obtain ⟨hn, hvn⟩ := real_mul_value hg (-1)
  obtain ⟨hd, hvd⟩ := real_add_value hf hn
  simp only [neg_one_mul] at hd hvd hvn
  simp only [sub_eq_add_neg]
  exact ⟨hd, by rw [hvd, hvn]⟩

theorem complex_difference_value {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) :
    ∃ hd : ComplexIntegrable (fun x => f x - g x) a b,
      complexIntegral _ hd = complexIntegral f hf - complexIntegral g hg := by
  obtain ⟨hn, hvn⟩ := complex_mul_value hg (-1)
  obtain ⟨hd, hvd⟩ := complex_add_value hf hn
  simp only [neg_one_mul] at hd hvd hvn
  simp only [sub_eq_add_neg]
  exact ⟨hd, by rw [hvd, hvn]⟩

/-- The ambient section representatives give precisely the subtype error range. -/
theorem section_error_image {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → E)
    (g : T → ℝ → E) (hg : ∀ t (x : Set.Icc a b), g t x = f x t)
    (t t₀ : T) :
    (fun x => ‖g t x - g t₀ x‖) '' Set.Icc a b =
      Set.range (fun x : Set.Icc a b => ‖f x t - f x t₀‖) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by dsimp only; rw [hg t ⟨x, hx⟩, hg t₀ ⟨x, hx⟩]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, by dsimp only; rw [hg t x, hg t₀ x]⟩

theorem real_difference_bound :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.realDifferenceBound := by
  intro a b T f t t₀ ht h₀
  obtain ⟨hd, hv⟩ := real_difference_value ht h₀
  obtain ⟨hn, hnorm, hbound⟩ := real_norm_estimate _ hd
  change ‖realIntegral _ ht - realIntegral _ h₀‖ ≤ _
  rw [← hv]
  apply hnorm.trans
  simpa only [C.sectionError, section_error_image f (parameterSection .real f)
    (fun t x => section_on_interval .real f t x) t t₀] using hbound

theorem complex_difference_bound :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.complexDifferenceBound := by
  intro a b T f t t₀ ht h₀
  obtain ⟨hd, hv⟩ := complex_difference_value ht h₀
  obtain ⟨hn, hnorm, hbound⟩ := complex_norm_estimate _ hd
  change ‖complexIntegral _ ht - complexIntegral _ h₀‖ ≤ _
  rw [← hv]
  apply hnorm.trans
  simpa only [C.sectionError, section_error_image f (parameterSection .complex f)
    (fun t x => section_on_interval .complex f t x) t t₀] using hbound

/-- A vanishing scalar majorant proves continuity in any normed target. -/
theorem continuousAt_of_eventual_error_bound {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] {F : X → E} {e : X → ℝ} {t₀ : X} (L : ℝ)
    (he : Filter.Tendsto e (𝓝 t₀) (𝓝 0))
    (hb : ∀ᶠ t in 𝓝 t₀, ‖F t - F t₀‖ ≤ L * e t) : ContinuousAt F t₀ := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hb
  simpa only [mul_zero] using he.const_mul L

theorem real_local_continuity :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.realLocalContinuity := by
  intro a b T f t₀ h₀ _hnear hlim
  have hsub := hlim.comp (continuous_subtype_val.continuousAt (x :=
    (⟨t₀, h₀⟩ : properParameters .real f))).tendsto
  apply continuousAt_of_eventual_error_bound (b - a) hsub
  exact Filter.Eventually.of_forall (fun t => real_difference_bound f t.val t₀ t.property h₀)

theorem real_relative_continuity :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.realRelativeContinuity := by
  intro a b T f t₀ h₀ hnear hlim F hF
  apply continuousAt_of_eventual_error_bound (b - a) hlim
  filter_upwards [hnear] with t ht
  rw [hF t ht, hF t₀ h₀]
  exact real_difference_bound f t t₀ ht h₀

theorem complex_local_continuity :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.complexLocalContinuity := by
  intro a b T f t₀ h₀ _hnear hlim
  have hsub := hlim.comp (continuous_subtype_val.continuousAt (x :=
    (⟨t₀, h₀⟩ : properParameters .complex f))).tendsto
  apply continuousAt_of_eventual_error_bound (b - a) hsub
  exact Filter.Eventually.of_forall (fun t => complex_difference_bound f t.val t₀ t.property h₀)

theorem complex_relative_continuity :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.complexRelativeContinuity := by
  intro a b T f t₀ h₀ hnear hlim F hF
  apply continuousAt_of_eventual_error_bound (b - a) hlim
  filter_upwards [hnear] with t ht
  rw [hF t ht, hF t₀ h₀]
  exact complex_difference_bound f t t₀ ht h₀

/-- Compact uniform continuity gives small Darboux gaps directly.
This helper supplies the continuous sections used below; no measure integral
or unproved bridge from it is involved. -/
theorem real_integrable_of_continuousOn {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b)) : RealIntegrable g a b := by
  have hb : BoundedOnInterval g a b :=
    ⟨isCompact_Icc.bddBelow_image hg, isCompact_Icc.bddAbove_image hg⟩
  apply (realIntegrable_iff_small_gap g hab hb).mpr
  intro ε hε
  let η := ε / (b - a + 1)
  have hlen : 0 < b - a + 1 := by linarith
  have hη : 0 < η := div_pos hε hlen
  have hηeq : η * (b - a + 1) = ε := div_mul_cancel₀ ε hlen.ne'
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  have hosc (i : Fin P.n) :
      cellSupremum g P hb i - cellInfimum g P hb i ≤ η := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    have hd : dist x y < δ := by
      rw [Real.dist_eq]
      have hl := cellLength_le_mesh P i
      change P.point i.succ - P.point i.castSucc ≤ mesh P at hl
      exact abs_lt.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2],
        by linarith [hx.1, hx.2, hy.1, hy.2]⟩
    exact (le_abs_self _).trans (by
      simpa only [Real.dist_eq] using (hc x (cell_subset_interval P i hx)
        y (cell_subset_interval P i hy) hd).le)
  refine ⟨P, ?_⟩
  calc
    upperSum g P hb - lowerSum g P hb =
        ∑ i : Fin P.n, (cellSupremum g P hb i - cellInfimum g P hb i) *
          cellLength P i := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ i : Fin P.n, η * cellLength P i := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hosc i) (cell_positive P i).le)
    _ = η * (b - a) := by rw [← Finset.mul_sum, sum_cellLength]
    _ < ε := by nlinarith

/-- A continuous interval-subtype section has a continuous ambient representative
on the interval; no regularity of its zero extension outside the interval is used. -/
theorem continuousOn_of_section_agreement {E : Type*} [TopologicalSpace E]
    {a b : ℝ} {g : ℝ → E} {v : Set.Icc a b → E}
    (hv : Continuous v) (heq : ∀ x : Set.Icc a b, g x = v x) :
    ContinuousOn g (Set.Icc a b) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hv.congr (fun x => (heq x).symm)

/-- Uniform continuity on a compact rectangle makes the actual supremum of
section differences tend to zero, uniformly over the spatial interval. -/
theorem rectangle_section_error_tendsto {E : Type*} [NormedAddCommGroup E]
    {a b c d : ℝ} (hab : a ≤ b)
    {f : Set.Icc a b → Set.Icc c d → E}
    (hf : Continuous (Function.uncurry f)) (t₀ : Set.Icc c d) :
    Filter.Tendsto (fun t => C.sectionError f t t₀) (𝓝 t₀) (𝓝 0) := by
  have hu := CompactSpace.uniformContinuous_of_continuous hf
  let x₀ : Set.Icc a b := ⟨a, le_rfl, hab⟩
  apply Metric.tendsto_nhds_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hd (x : Set.Icc a b) : ‖f x t - f x t₀‖ < ε / 2 := by
    have hdist : dist (x, t) (x, t₀) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using ht
    simpa only [Function.uncurry_apply_pair, dist_eq_norm] using hc hdist
  have hb : BddAbove (Set.range (fun x : Set.Icc a b => ‖f x t - f x t₀‖)) :=
    ⟨ε / 2, by rintro r ⟨x, rfl⟩; exact (hd x).le⟩
  have hlo : 0 ≤ C.sectionError f t t₀ :=
    (norm_nonneg _).trans (le_csSup hb ⟨x₀, rfl⟩)
  have hhi : C.sectionError f t t₀ ≤ ε / 2 := by
    change sSup (Set.range (fun x : Set.Icc a b => ‖f x t - f x t₀‖)) ≤ ε / 2
    apply csSup_le (s := Set.range (fun x : Set.Icc a b => ‖f x t - f x t₀‖))
      ⟨_, ⟨x₀, rfl⟩⟩
    rintro r ⟨x, rfl⟩
    exact (hd x).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  exact hhi.trans_lt (half_lt_self hε)

theorem real_rectangle_continuity :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.realRectangleContinuity := by
  intro a b c d hab _hcd f hf
  have hs (t : Set.Icc c d) : SectionIntegrable .real f t := by
    apply real_integrable_of_continuousOn hab
    apply continuousOn_of_section_agreement
      (hf.comp (continuous_id.prodMk continuous_const))
    exact fun x => section_on_interval .real f t x
  refine ⟨hs, continuous_iff_continuousAt.mpr (fun t₀ => ?_)⟩
  apply real_relative_continuity f t₀ (hs t₀)
    (Filter.Eventually.of_forall hs) (rectangle_section_error_tendsto hab hf t₀)
  exact fun _ _ => rfl

theorem complex_rectangle_continuity :
    Specs.SingleVariableAnalysis.Ch14.ProperContinuity.complexRectangleContinuity := by
  intro a b c d hab _hcd f hf
  have hs (t : Set.Icc c d) : SectionIntegrable .complex f t := by
    have hv : Continuous (fun x => f x t) :=
      hf.comp (continuous_id.prodMk continuous_const)
    constructor
    · apply real_integrable_of_continuousOn hab
      apply continuousOn_of_section_agreement (Complex.continuous_re.comp hv)
      exact fun x => congrArg Complex.re (section_on_interval .complex f t x)
    · apply real_integrable_of_continuousOn hab
      apply continuousOn_of_section_agreement (Complex.continuous_im.comp hv)
      exact fun x => congrArg Complex.im (section_on_interval .complex f t x)
  refine ⟨hs, continuous_iff_continuousAt.mpr (fun t₀ => ?_)⟩
  apply complex_relative_continuity f t₀ (hs t₀)
    (Filter.Eventually.of_forall hs) (rectangle_section_error_tendsto hab hf t₀)
  exact fun _ _ => rfl

end SingleVariableAnalysis.ParameterIntegral
