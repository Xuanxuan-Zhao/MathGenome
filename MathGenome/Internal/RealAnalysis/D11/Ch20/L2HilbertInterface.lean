import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.L2HilbertInterface
import MathGenome.Internal.RealAnalysis.D11.Ch10.Completeness
import MathGenome.Internal.RealAnalysis.D11.Ch10.CauchySchwarz
import Mathlib.MeasureTheory.Function.L2Space

/-! Ordinary L² is Hilbert for arbitrary positive measures.

The norm and vector operations are the accepted quotient construction. We pull
back the native L² inner product along its proved linear isometry. The paper's
first-slot convention is the reverse of Lean's convention; the representative
identity proves precisely the integral of f times conjugate g. Completeness is
the accepted ordinary-quotient completeness theorem. All formulas retain
ordinary measurable representatives, even when the measure is incomplete.
-/
open MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace D11.Ch20.L2HilbertInterface
open Specs.D11.Ch10.QuotientConstruction
open D11.Ch10.QuotientConstruction

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Hilbert structure compatible with the already constructed quotient norm. -/
instance quotientInnerProductSpace (μ : Measure X) :
    InnerProductSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ 2) where
  inner f g := inner 𝕜 (nativeLinearIsometryEquiv μ 2 f)
    (nativeLinearIsometryEquiv μ 2 g)
  norm_sq_eq_re_inner f := by
    rw [← (nativeLinearIsometryEquiv μ 2).norm_map f]
    exact norm_sq_eq_re_inner _
  conj_inner_symm f g := inner_conj_symm _ _
  add_left f g h := by
    change inner 𝕜 (nativeLinearIsometryEquiv μ 2 (f + g)) _ = _
    rw [map_add, inner_add_left]
  smul_left f g c := by
    change inner 𝕜 (nativeLinearIsometryEquiv μ 2 (c • f)) _ = _
    rw [map_smul, inner_smul_left]

/-- Every ordinary raw pair has an absolutely integrable first-slot product,
and the quotient pairing is its scalar integral. -/
theorem inner_classOf (μ : Measure X) (f g : Raw (𝕜 := 𝕜) μ 2) :
    ∃ h : Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ
        (fun x => f.val x * conj (g.val x)),
      inner 𝕜 (classOf g) (classOf f) =
        Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value μ
          (fun x => f.val x * conj (g.val x)) h := by
  have hf : f.val ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ 2 := by
    exact (raw_finite μ 2 (by norm_num) f.val).mp (by simpa using f.property)
  have hg : g.val ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ 2 := by
    exact (raw_finite μ 2 (by norm_num) g.val).mp (by simpa using g.property)
  obtain ⟨hi, _⟩ := D11.Ch10.CauchySchwarz.integral_bound μ f.val g.val hf hg
  refine ⟨hi, ?_⟩
  change (∫ x, inner 𝕜 (g.property.2.toLp g.val x)
    (f.property.2.toLp f.val x) ∂μ) = ∫ x, f.val x * conj (g.val x) ∂μ
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp f.property.2, MemLp.coeFn_toLp g.property.2]
    with x hfx hgx
  simp only [hfx, hgx, RCLike.inner_apply]

/-- The source proposition, including its first-slot convention and full measure range. -/
theorem l2_hilbert : Specs.D11.Ch20.L2HilbertInterface.l2_hilbert := by
  intro X 𝕜 _ _ _ _ μ
  refine ⟨quotientNormedAddCommGroup μ 2, quotientInnerProductSpace μ,
    nativeLinearIsometryEquiv μ 2, nativeLinearIsometryEquiv_classOf μ 2,
    norm_classOf μ 2, D11.Ch10.Completeness.quotientCompleteSpace μ 2,
    inner_classOf μ, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    exact inner_add_right _ _ _
  · intro c f g
    exact inner_smul_right _ _ _
  · intro f g
    exact (inner_conj_symm _ _).symm
  · intro f
    exact ⟨inner_self_eq_norm_sq_to_K _, inner_self_eq_zero⟩
  · intro f g
    exact (norm_inner_le_norm g f).trans_eq (mul_comm _ _)

end D11.Ch20.L2HilbertInterface
