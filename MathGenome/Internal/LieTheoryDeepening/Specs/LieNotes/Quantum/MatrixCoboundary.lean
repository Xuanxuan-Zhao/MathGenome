import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.RootCobracket

noncomputable section

namespace Specs.LieNotes.Quantum.MatrixCoboundary

open Specs.LieNotes.Coboundary (wedge₂Value coboundaryValue
  isLieBialgebraCobracketValue)
open MatrixSpecialization (Sl3 matrixE matrixF matrixUnit)
open ClassicalLimit (ClassicalReduction)
open Completion (HopfMaps Level Uh CompletedSquare)
open RootCobracket (Restriction exteriorEmbedding)
open SkewReduction (DividedSkew specialize specializeSquare completedFlip)

universe u

def StandardTensorType :=
  ∀ (k : Type u) [Field k], ⋀[k]^2 (Sl3 k)

/-- The bivector in the matrix model, with the sign for
`(Δ - Δᵒᵖ) / h`. -/
def standardTensor (k : Type u) [Field k] : ⋀[k]^2 (Sl3 k) :=
  -wedge₂Value (matrixE k 0) (matrixF k 0) -
    wedge₂Value (matrixE k 1) (matrixF k 1) -
    wedge₂Value (matrixUnit k 0 2 (by decide)) (matrixUnit k 2 0 (by decide))

/-- Any restriction of the divided skew coproduct as in UQ08 is the
diagonal adjoint action on the specified tensor. -/
def RestrictionCoboundaryProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] {D : HopfMaps k}
    {r : ClassicalReduction D} {b : DividedSkew r} (q : Restriction b),
    q.delta = coboundaryValue (standardTensor k)

/-- The coboundary identity holds for the first-order Lie bialgebra
cobracket of the completed quantization, on every lift. -/
def MatrixCoboundaryProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (d : ∀ N : Level, Coproduct.TruncatedData k N)
      (s : ∀ N : Level, Hopf.TruncatedData k N (d N)) (D : HopfMaps k),
      Completion.ProjectsTo D d s ∧ Completion.HopfIdentities D ∧
      Completion.ContinuousHopfMaps D ∧
      ∃ (r : ClassicalReduction D) (b : DividedSkew r) (q : Restriction b),
        q.delta = coboundaryValue (standardTensor k) ∧
        isLieBialgebraCobracketValue q.delta ∧
        ∀ (x : Sl3 k) (X : Uh k),
          specialize r X = UniversalEnvelopingAlgebra.ι k x →
          ∃! Z : CompletedSquare k,
            (PowerSeries.X : PowerSeries k) • Z = D.comul X - completedFlip (D.comul X) ∧
            specializeSquare r Z = exteriorEmbedding (coboundaryValue (standardTensor k) x)

end Specs.LieNotes.Quantum.MatrixCoboundary
