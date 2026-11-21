import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcFtc
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcStieltjesEquivalence
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcPrimitive

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace D11.Ch12.AcFtc

/-- Equality on the closed interval transfers the primitive's derivative at
each interior point. In particular, every representing density is the same
classical derivative almost everywhere. -/
lemma representation_derivative {K : Type*} [RCLike K]
    (F f : ℝ → K) {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Icc a b))
    (hr : ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, f t) :
    (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (f x) x) ∧
      f =ᵐ[volume.restrict (Icc a b)] deriv F := by
  have hd := AcPrimitive.primitive_derivative f (F a) hab hf
  have hF : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (f x) x := by
    filter_upwards [hd] with x hx hxi
    apply (hx hxi).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
    exact hr y (Ioo_subset_Icc_self hy)
  refine ⟨hF, ?_⟩
  rw [Filter.EventuallyEq, ← restrict_Ioo_eq_restrict_Icc,
    ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hF] with x hx hxi
  exact (hx hxi).deriv.symm

/-- The reverse implication tests exactly the original finite disjoint-interval
condition. Values outside the compact interval play no role. -/
lemma ac_of_representation {K : Type*} [RCLike K]
    (F f : ℝ → K) {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Icc a b))
    (hr : ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, f t) :
    AbsolutelyContinuousOnInterval F a b := by
  have h := AcPrimitive.primitive_ac f (F a) hab hf
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n u v huv hends hdis hlength
  have hbound := hh n u v huv hends hdis hlength
  calc
    (∑ j, ‖F (v j) - F (u j)‖) =
        ∑ j, ‖Specs.D11.Ch12.AcPrimitive.primitive_value f (F a) a (v j) -
          Specs.D11.Ch12.AcPrimitive.primitive_value f (F a) a (u j)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hr _ (hends j).1, hr _ (hends j).2]
      rfl
    _ < ε := hbound

/-- Assemble the three equivalences from compact AC reconstruction and the
primitive theorem. Reconstruction is supplied by the acyclic Stieltjes/RN
argument, rather than a general BV differentiation assumption. -/
lemma ftc_of_reconstruction {K : Type*} [RCLike K]
    (hreconstruct : ∀ (F : ℝ → K) {a b : ℝ}, a < b →
      AbsolutelyContinuousOnInterval F a b →
      IntegrableOn (deriv F) (Icc a b) ∧
      (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (deriv F x) x) ∧
      ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, deriv F t) :
    Specs.D11.Ch12.AcFtc.ftc_statement K := by
  intro F a b hab
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hAC
    obtain ⟨hi, _, hr⟩ := hreconstruct F hab hAC
    exact ⟨deriv F, hi, hr⟩
  · rintro ⟨f, hf, hr⟩
    exact ac_of_representation F f hab hf hr
  · intro hAC
    obtain ⟨hi, hd, hr⟩ := hreconstruct F hab hAC
    exact ⟨hd, hi, hr⟩
  · rintro ⟨_, hi, hr⟩
    exact ac_of_representation F (deriv F) hab hi hr
  · intro f hf hr
    have heq := (representation_derivative F f hab hf hr).2
    refine ⟨heq, ?_⟩
    intro g hg hgr
    exact heq.trans (representation_derivative F g hab hg hgr).2.symm

theorem ftc_real : Specs.D11.Ch12.AcFtc.ftc_real := by
  apply ftc_of_reconstruction
  intro F a b hab hAC
  exact ((AcStieltjesEquivalence.compact_real F hab).2 hAC).2

theorem ftc_complex : Specs.D11.Ch12.AcFtc.ftc_complex := by
  apply ftc_of_reconstruction
  intro F a b hab hAC
  exact ((AcStieltjesEquivalence.compact_complex F hab).2 hAC).2

theorem derivative_representative : Specs.D11.Ch12.AcFtc.derivative_representative := by
  intro K _ _ _ F
  exact ⟨measurable_deriv F, fun _ hx => deriv_zero_of_not_differentiableAt hx⟩

end D11.Ch12.AcFtc
