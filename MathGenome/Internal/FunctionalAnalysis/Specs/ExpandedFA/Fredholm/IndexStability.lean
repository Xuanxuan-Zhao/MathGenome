import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
Independent Banach-stage statements of `fa2:p2:index`, paper.tex:10620–10664.
The predicates refer to closed actual ranges, actual kernels and actual quotient
cokernels. Scalars are real or complex, and zero spaces are allowed.
Binary direct sums carry the usual product norm, an equivalent norm to any
finite topological direct-sum norm.
-/

noncomputable section
namespace ExpandedFA.Fredholm.IndexStabilitySpec
open scoped Topology
universe u v w z t
open DefinitionsSpec

def CompositionFredholm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z],
  ∀ (T : X →L[𝕜] Y) (S : Y →L[𝕜] Z),
    IsFredholmValue T → IsFredholmValue S → IsFredholmValue (S.comp T)

def CompositionIndex : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z],
  ∀ (T : X →L[𝕜] Y) (S : Y →L[𝕜] Z)
    (hT : IsFredholmValue T) (hS : IsFredholmValue S)
    (hST : IsFredholmValue (S.comp T)),
    fredholmIndexValue (S.comp T) hST =
      fredholmIndexValue S hS + fredholmIndexValue T hT

def DirectSumFredholm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜]
    {X : Type v} {Y : Type w} {X' : Type z} {Y' : Type t}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup X'] [NormedAddCommGroup Y']
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [NormedSpace 𝕜 X'] [NormedSpace 𝕜 Y']
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace X'] [CompleteSpace Y'],
  ∀ (S : X →L[𝕜] Y) (T : X' →L[𝕜] Y'),
    IsFredholmValue S → IsFredholmValue T → IsFredholmValue (S.prodMap T)

def DirectSumIndex : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜]
    {X : Type v} {Y : Type w} {X' : Type z} {Y' : Type t}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup X'] [NormedAddCommGroup Y']
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [NormedSpace 𝕜 X'] [NormedSpace 𝕜 Y']
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace X'] [CompleteSpace Y'],
  ∀ (S : X →L[𝕜] Y) (T : X' →L[𝕜] Y')
    (hS : IsFredholmValue S) (hT : IsFredholmValue T)
    (hST : IsFredholmValue (S.prodMap T)),
    fredholmIndexValue (S.prodMap T) hST =
      fredholmIndexValue S hS + fredholmIndexValue T hT

def FredholmOpen : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
    IsOpen {T : X →L[𝕜] Y | IsFredholmValue T}

def IndexLocallyConstant : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (T : X →L[𝕜] Y) (hT : IsFredholmValue T),
    ∀ᶠ S in 𝓝 T, ∃ hS : IsFredholmValue S,
      fredholmIndexValue S hS = fredholmIndexValue T hT

def CompactPerturbationFredholm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (T K : X →L[𝕜] Y),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    (IsFredholmValue (T + K) ↔ IsFredholmValue T)

def CompactPerturbationIndex : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (T K : X →L[𝕜] Y)
    (hK : Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap)
    (hT : IsFredholmValue T) (hTK : IsFredholmValue (T + K)),
    fredholmIndexValue (T + K) hTK = fredholmIndexValue T hT

end ExpandedFA.Fredholm.IndexStabilitySpec
