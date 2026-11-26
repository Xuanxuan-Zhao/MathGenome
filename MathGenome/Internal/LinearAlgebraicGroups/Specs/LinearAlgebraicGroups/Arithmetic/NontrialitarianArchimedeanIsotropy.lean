import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianArchimedeanIsotropy

open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (LocalPoints)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open CharacterDescent (Cocharacter)
open IntegralModels (MatrixRealization)
open NontrialitarianSpinModels (DescendedQuadraticPair EquivariantSpinTrivialization
  IsOrthogonal SpinModel)
open OppositeRadicals (IsNoncentral)
open SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open Unipotent (baseChangedAlgebraicGroup)

/-- A noncompact archimedean factor of a nontrialitarian spin model admits a
noncentral cocharacter over the completion. A complex factor is noncompact. -/
def ArchimedeanIsotropy : Prop :=
  ∀ {k L I : Type u} [Field k] [hK : NumberField k]
    [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (G : AffineAlgebraicGroup k), IsAbsolutelyAlmostSimple G →
    ∀ (C : EquivariantSpinTrivialization (K := L) (I := I) G)
      (Q : DescendedQuadraticPair C.action), SpinModel G Q →
    4 ≤ Fintype.card I → IsOrthogonal (toDivisionInvolution Q.involution) →
    ∀ (D : GlobalFieldData.{u, u} k), D = .number hK →
    ∀ (i : MatrixRealization G) (w : D.InfinitePlace),
      (¬ CompactSpace (LocalPoints D i (.inr w)) →
        ∃ c : Cocharacter (baseChangedAlgebraicGroup (D.Completion (.inr w)) G).val,
          IsNoncentral c) ∧
      (∀ e : D.Completion (.inr w) ≃+* ℂ, IsHomeomorph e →
        ¬ CompactSpace (LocalPoints D i (.inr w)))

end LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianArchimedeanIsotropy
