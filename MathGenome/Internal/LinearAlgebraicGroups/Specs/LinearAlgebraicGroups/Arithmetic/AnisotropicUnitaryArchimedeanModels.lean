import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitaryArchimedeanModels

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (LocalPoints)
open _root_.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation (Contracted)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open IntegralModels (MatrixRealization)
open OuterTypeAModels (RepresentsUnitary)
open ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- At an infinite place, the completed special unitary group is compact and
connected, or the cocharacter radical points and the contracted elements each
generate a dense subgroup in the topology of the chosen closed realization. -/
def ArchimedeanLocalModels : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    Module.finrank K E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A), 3 ≤ degree E A →
    ∀ (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
      RepresentsUnitary hA b s G →
      ∀ (i : MatrixRealization G) [NumberField K], D = .number inferInstance →
      ∀ w : D.InfinitePlace,
        (CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w))) ∨
        (Dense (Subgroup.closure (localPointSet D i (.inr w)
          (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
          Set (LocalPoints D i (.inr w))) ∧
         Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
          Set (LocalPoints D i (.inr w))))

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitaryArchimedeanModels
