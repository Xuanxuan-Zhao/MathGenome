import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitaryFiniteModels

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (LocalPoints)
open _root_.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation (Contracted)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open IntegralModels (MatrixRealization)
open LocalQuotientMixing (MixingCases)
open OuterTypeAModels (RepresentsUnitary)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- Outside a finite set of places where the quadratic centre embeds in the
completion, the local group belongs to the mixing cases and its contracted
elements generate a dense subgroup in the topology of the given realization. -/
def FiniteLocalModels : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    Module.finrank K E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A), 3 ≤ degree E A →
    ∀ (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
      RepresentsUnitary hA b s G →
      ∀ i : MatrixRealization G,
        ∃ B : Finset D.FinitePlace,
          (∀ w ∈ B, Nonempty (E →ₐ[K] D.Completion (Sum.inl w))) ∧
          ∀ w : D.FinitePlace, w ∉ B →
            MixingCases (baseChangedAlgebraicGroup (D.Completion (Sum.inl w)) G) ∧
            Dense (Subgroup.closure {x : LocalPoints D i (Sum.inl w) | Contracted x} :
              Set (LocalPoints D i (Sum.inl w)))

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitaryFiniteModels
