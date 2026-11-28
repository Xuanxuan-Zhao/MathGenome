import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

namespace RepTheorySurvey.Geometric.GrassmannianIncidenceTopologySpecs

open LatticeModelSpecs

/-- Adjoining the fixed summand `A` gives a closed embedding for the analytic
graph-chart topologies. Its image consists of the planes between the two
indicated incidence subspaces. -/
def IncidenceClosedEmbedding : Prop :=
  ∀ {U W A C ι κ : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bU : Module.Basis ι ℂ U) (bW : Module.Basis κ ℂ W)
    (e : W ≃ₗ[ℂ] U × (A × C)) {d d' : ℕ}
    (hd : d ≤ Module.finrank ℂ U) (hd' : d' ≤ Module.finrank ℂ W),
    d' = d + Module.finrank ℂ A →
    ∀ (f : GrassmannianPoints bU hd → GrassmannianPoints bW hd'),
      (∀ p w, w ∈ grassmannianSubspace bW hd' (f p) ↔
        (e w).1 ∈ grassmannianSubspace bU hd p ∧ (e w).2.2 = 0) →
      Topology.IsClosedEmbedding f ∧
      Set.range f = {q |
        Submodule.comap e.toLinearMap
          ((⊥ : Submodule ℂ U).prod ((⊤ : Submodule ℂ A).prod (⊥ : Submodule ℂ C))) ≤
          grassmannianSubspace bW hd' q ∧
        grassmannianSubspace bW hd' q ≤ Submodule.comap e.toLinearMap
          ((⊤ : Submodule ℂ U).prod ((⊤ : Submodule ℂ A).prod (⊥ : Submodule ℂ C)))}

/-- Restricting a closed embedding to a closed source locus gives a closed
embedding into any target subspace containing the restricted image. -/
def RestrictClosedEmbedding : Prop :=
  ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {S : Set X} {T : Set Y},
    Topology.IsClosedEmbedding f → IsClosed S →
    ∀ h : Set.MapsTo f S T, Topology.IsClosedEmbedding (Set.MapsTo.restrict f S T h)

/-- Componentwise closed embeddings induce a closed embedding of disjoint sums
when the index map is injective. -/
def SigmaClosedEmbedding : Prop :=
  ∀ {I J : Type} {X : I → Type} {Y : J → Type}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    {shift : I → J} {f : ∀ i, X i → Y (shift i)},
    Function.Injective shift → (∀ i, Topology.IsClosedEmbedding (f i)) →
    Topology.IsClosedEmbedding (Sigma.map shift f)

end RepTheorySurvey.Geometric.GrassmannianIncidenceTopologySpecs
