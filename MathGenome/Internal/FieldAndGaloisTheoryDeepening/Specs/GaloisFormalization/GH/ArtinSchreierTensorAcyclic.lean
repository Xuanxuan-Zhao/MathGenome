import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains

namespace Specs.GaloisFormalization.GH.ArtinSchreierTensorAcyclic

open ArtinSchreierTensor (Tensor diagonalAction primeFieldModule)
open KrullLayers (AbsoluteGaloisGroup)
open _root_.GaloisFormalization.GH.Model (ContinuousH)

universe u v w

/-- The diagonal tensor of a discrete continuous module killed by `p` with a chosen
separable closure has trivial continuous cohomology in every positive degree.
The continuous-action witness supplies the instance used to form the cochain complex. -/
def tensorAcyclic_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    (M : Type w) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup k S) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (AbsoluteGaloisGroup k S) M]
    (h : ∀ m : M, p • m = 0),
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : Module (ZMod p) M := primeFieldModule p M h
    let W := Tensor p S M
    letI : DistribMulAction (AbsoluteGaloisGroup k S) W := diagonalAction p S M
    ∀ [TopologicalSpace W] [DiscreteTopology W],
      ∃ hW : ContinuousSMul (AbsoluteGaloisGroup k S) W,
        letI := hW
        ∀ q : ℕ, 0 < q → Subsingleton (ContinuousH (AbsoluteGaloisGroup k S) W q)

end Specs.GaloisFormalization.GH.ArtinSchreierTensorAcyclic
