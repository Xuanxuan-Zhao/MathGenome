import MathGenome.Internal.Specs.D07.Ch12.AdjoinRoot
import MathGenome.Internal.D07.Ch08.FieldEmbedding
import MathGenome.Internal.D07.Ch11.IrreducibleQuotient

/-! Adjoining a root by the abstract quotient K[X]/(f), K07.12.adjoin_root. -/

universe u

namespace D07.Ch12.AdjoinRoot

open Polynomial
open Specs.D07.Ch12.AdjoinRoot

theorem quotient_isField : QuotientIsField.{u} := by
  intro K _ f hf
  exact (Ch11.IrreducibleQuotient.quotientFieldIffIrreducible
    K f hf.natDegree_pos).mpr hf

theorem constant_embedding : ConstantEmbedding.{u} := by
  intro K _ f hf
  let : Nontrivial (Polynomial K ⧸ Ideal.span {f}) :=
    (quotient_isField K f hf).nontrivial
  exact ⟨Ch08.FieldEmbedding.unital_injective K _
    ((Ideal.Quotient.mk (Ideal.span {f})).comp C), rfl⟩

theorem root_equation : RootEquation.{u} := by
  intro K _ f _
  exact Ch11.IrreducibleQuotient.quotientRootEquation K f

end D07.Ch12.AdjoinRoot
