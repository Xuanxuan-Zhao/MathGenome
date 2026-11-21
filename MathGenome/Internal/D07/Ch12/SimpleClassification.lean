import MathGenome.Internal.Specs.D07.Ch12.SimpleClassification
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Classification of simple extensions, including the evaluation formulas and
uniqueness stated in paper.tex:3623–3629. The library's algebraic equivalence
is the quotient evaluation lift; its transcendental equivalence extends the
injective polynomial evaluation map to fraction fields.
-/

universe u v

namespace D07.Ch12.SimpleClassification

open Polynomial
open Specs.D07.Ch12.SimpleClassification

theorem algebraicClassification : AlgebraicClassification.{u, v} := by
  intro K L _ _ _ α hα
  let e := IntermediateField.adjoinRootEquivAdjoin K hα.isIntegral
  have hx : e (AdjoinRoot.root (minpoly K α)) =
      IntermediateField.AdjoinSimple.gen K α :=
    IntermediateField.adjoinRootEquivAdjoin_apply_root K hα.isIntegral
  refine ⟨e, hx, ?_, ?_⟩
  · intro p
    have hev : e.toAlgHom.comp (AdjoinRoot.mkₐ (minpoly K α)) =
        aeval (IntermediateField.AdjoinSimple.gen K α) := by
      apply Polynomial.algHom_ext
      simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AdjoinRoot.coe_mkₐ,
        AdjoinRoot.mk_X, aeval_X] using hx
    calc
      (e (AdjoinRoot.mk (minpoly K α) p) : L) =
          (aeval (IntermediateField.AdjoinSimple.gen K α) p : L) :=
        congrArg (fun y : IntermediateField.adjoin K {α} => (y : L))
          (AlgHom.congr_fun hev p)
      _ = aeval α p :=
        (aeval_algebraMap_apply L (IntermediateField.AdjoinSimple.gen K α) p).symm
  · intro e' he'
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext (he'.trans hx.symm)

theorem transcendentalClassification : TranscendentalClassification.{u, v} := by
  intro K L _ _ _ α hα
  let e := RatFunc.algEquivOfTranscendental α hα
  have hx : e RatFunc.X = IntermediateField.AdjoinSimple.gen K α :=
    Subtype.ext (RatFunc.algEquivOfTranscendental_X α hα)
  refine ⟨e, hx, ?_, ?_⟩
  · intro p q _
    simp only [map_div₀, RatFunc.algEquivOfTranscendental_algebraMap, e]
    exact congrArg₂ (· / ·)
      (aeval_algebraMap_apply L (IntermediateField.AdjoinSimple.gen K α) p).symm
      (aeval_algebraMap_apply L (IntermediateField.AdjoinSimple.gen K α) q).symm
  · intro e' he'
    apply AlgEquiv.coe_toAlgHom_injective
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    exact he'.trans hx.symm

end D07.Ch12.SimpleClassification
