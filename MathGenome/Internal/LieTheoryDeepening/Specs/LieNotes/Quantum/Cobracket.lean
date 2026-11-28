import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.RootCobracket
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.DualJacobi

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.Cobracket

open ClassicalLimit (ClassicalReduction)
open Completion (HopfMaps Level Uh CompletedSquare)
open MatrixSpecialization (Classical Sl3)
open RootCobracket (Restriction exteriorEmbedding)
open SkewReduction (DividedSkew specialize specializeSquare completedFlip)
open Specs.LieNotes.Coboundary (isLieBialgebraCobracketValue tensorCycleValue)

universe u

/-- The skew coproduct of the completed quantization induces the specified Lie
bialgebra cobracket, with its divided value on every lift. -/
def CobracketProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (d : ∀ N : Level, Coproduct.TruncatedData k N)
      (s : ∀ N : Level, Hopf.TruncatedData k N (d N)) (D : HopfMaps k),
      Completion.ProjectsTo D d s ∧ Completion.HopfIdentities D ∧
      Completion.ContinuousHopfMaps D ∧
      ∃ (r : ClassicalReduction D) (b : DividedSkew r) (q : Restriction b),
        isLieBialgebraCobracketValue q.delta ∧
        (∀ x : Classical k,
          let t := TensorProduct.map b.skew LinearMap.id (b.skew x)
          t + tensorCycleValue t + tensorCycleValue (tensorCycleValue t) = 0) ∧
        ∀ (x : Sl3 k) (X : Uh k),
          specialize r X = UniversalEnvelopingAlgebra.ι k x →
          ∃! Z : CompletedSquare k,
            (PowerSeries.X : PowerSeries k) • Z = D.comul X - completedFlip (D.comul X) ∧
            specializeSquare r Z = exteriorEmbedding (q.delta x)

end Specs.LieNotes.Quantum.Cobracket
