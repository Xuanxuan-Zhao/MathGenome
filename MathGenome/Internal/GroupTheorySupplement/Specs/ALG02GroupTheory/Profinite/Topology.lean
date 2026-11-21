import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Completion

/-! The topology, density, and kernel assertions of GR02-C05.02. -/

open Filter
open scoped Topology

namespace Specs.ALG02GroupTheory.Profinite

universe u

def CompletionTopology : Prop :=
  ∀ (G : Type u) [Group G],
    CompactSpace (completionValue G) ∧ T2Space (completionValue G) ∧
      TotallyDisconnectedSpace (completionValue G) ∧ IsTopologicalGroup (completionValue G)

def ProjectionContinuous : Prop :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G),
    Continuous (projectionValue N : completionValue G → finiteQuotient N)

def ProjectionSurjective : Prop :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G),
    Function.Surjective (projectionValue N : completionValue G → finiteQuotient N)

def ProjectionKernelClopen : Prop :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G),
    IsClopen ((projectionValue N).toMonoidHom.ker : Set (completionValue G))

def ProjectionKernelNormal : Prop :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G),
    (projectionValue N).toMonoidHom.ker.Normal

def ProjectionKernelHasBasis : Prop :=
  ∀ (G : Type u) [Group G],
    (𝓝 (1 : completionValue G)).HasBasis (fun _ : FiniteIndexNormalSubgroup G => True)
      (fun N => ((projectionValue N).toMonoidHom.ker : Set (completionValue G)))

def EtaDenseRange : Prop :=
  ∀ (G : Type u) [Group G], DenseRange (etaValue G : G → completionValue G)

def EtaKernel : Prop :=
  ∀ (G : Type u) [Group G], (etaValue G).ker = ⨅ N : FiniteIndexNormalSubgroup G, N.toSubgroup

end Specs.ALG02GroupTheory.Profinite
