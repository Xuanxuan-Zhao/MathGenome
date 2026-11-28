import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SkewReduction
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Basic

noncomputable section

namespace Specs.LieNotes.Quantum.RootCobracket

open ClassicalLimit (ClassicalReduction)
open Completion (HopfMaps Level)
open MatrixSpecialization (Sl3 matrixE matrixF matrixH)
open SkewReduction (ClassicalSquare DividedSkew)
open Specs.LieNotes.Coboundary (alternatingTensorValue isCobracketCocycleValue wedge₂Value)

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k]

/-- The Lie exterior square in the ordinary enveloping tensor square, with
`a ∧ b` represented by `ι(a) ⊗ ι(b) - ι(b) ⊗ ι(a)`. -/
def exteriorEmbedding : ⋀[k]^2 (Sl3 k) →ₗ[k] ClassicalSquare k :=
  let ι : Sl3 k →ₗ[k] MatrixSpecialization.Classical k :=
    (UniversalEnvelopingAlgebra.ι k).toLinearMap
  (TensorProduct.map ι ι).comp alternatingTensorValue

/-- The Cartan, simple-root, and nonsimple-root values in the matrix model. -/
structure RootValues (δ : Sl3 k →ₗ[k] ⋀[k]^2 (Sl3 k)) : Prop where
  cartan (i : Presentation.Root) : δ (matrixH k i) = 0
  simplePositive (i : Presentation.Root) :
    δ (matrixE k i) = wedge₂Value (matrixH k i) (matrixE k i)
  simpleNegative (i : Presentation.Root) :
    δ (matrixF k i) = wedge₂Value (matrixH k i) (matrixF k i)
  positive : δ ⁅matrixE k 0, matrixE k 1⁆ =
    wedge₂Value (matrixH k 0 + matrixH k 1) ⁅matrixE k 0, matrixE k 1⁆ +
      (2 : k) • wedge₂Value (matrixE k 0) (matrixE k 1)
  negative : δ ⁅matrixF k 0, matrixF k 1⁆ =
    wedge₂Value (matrixH k 0 + matrixH k 1) ⁅matrixF k 0, matrixF k 1⁆ -
      (2 : k) • wedge₂Value (matrixF k 0) (matrixF k 1)

variable [CharZero k] {D : HopfMaps k} {r : ClassicalReduction D}

/-- The restriction of the actual divided skew map to the Lie algebra. -/
def FactorsThrough (b : DividedSkew r) (δ : Sl3 k →ₗ[k] ⋀[k]^2 (Sl3 k)) : Prop :=
  ∀ x : Sl3 k, exteriorEmbedding (δ x) = b.skew (UniversalEnvelopingAlgebra.ι k x)

/-- This factorization is unique and satisfies the exterior adjoint cocycle condition. -/
structure Restriction (b : DividedSkew r) where
  delta : Sl3 k →ₗ[k] ⋀[k]^2 (Sl3 k)
  embedding_injective : Function.Injective (exteriorEmbedding (k := k))
  factors : FactorsThrough b delta
  unique (δ' : Sl3 k →ₗ[k] ⋀[k]^2 (Sl3 k)) (hδ' : FactorsThrough b δ') : δ' = delta
  values : RootValues delta
  cocycle : isCobracketCocycleValue delta

/-- The first-order root values and the resulting Lie algebra cocycle on the
actual matrix specialization of the completed quantum enveloping algebra. -/
def RootCobracketProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (d : ∀ N : Level, Coproduct.TruncatedData k N)
      (s : ∀ N : Level, Hopf.TruncatedData k N (d N)) (D : HopfMaps k),
      Completion.ProjectsTo D d s ∧ Completion.HopfIdentities D ∧
      Completion.ContinuousHopfMaps D ∧
      ∃ (r : ClassicalReduction D) (b : DividedSkew r), Nonempty (Restriction b)

end Specs.LieNotes.Quantum.RootCobracket
