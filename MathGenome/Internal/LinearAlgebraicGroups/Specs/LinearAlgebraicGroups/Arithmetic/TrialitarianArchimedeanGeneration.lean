import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms

set_option autoImplicit false

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianArchimedeanGeneration

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (LocalPoints)
open _root_.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation (Contracted)
open GeometricRadicals (IsSemisimple)
open IntegralModels (MatrixRealization)
open ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open TrialitarianLocalForms (IsTrialitarian)
open Unipotent (baseChangedAlgebraicGroup)

/-- The archimedean inputs for adelic isolation and approximation for a
globally trialitarian group, in the original matrix point topology. -/
def ArchimedeanInputs : Prop :=
  ∀ {K : Type u} [Field K] [hK : NumberField K] (D : GlobalFieldData.{u, u} K),
    D = .number hK →
    ∀ (G : AffineAlgebraicGroup K), IsSemisimple G → GeometricallySimplyConnected G →
      IsTrialitarian G →
      ∀ (i : MatrixRealization G) (w : D.InfinitePlace),
        (¬ CompactSpace (LocalPoints D i (.inr w)) →
          Dense (Subgroup.closure (localPointSet D i (.inr w)
            (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
              Set (LocalPoints D i (.inr w))) ∧
          Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
            Set (LocalPoints D i (.inr w)))) ∧
        (CompactSpace (LocalPoints D i (.inr w)) →
          ConnectedSpace (LocalPoints D i (.inr w)))

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianArchimedeanGeneration
