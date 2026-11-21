import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Data.List.Chain

/-!
Independent statements for paper.tex:621–630.
A polygonal path is represented by its finite ordered vertex list `a :: vertices`.
`List.IsChain` requires every consecutive closed real segment to lie in Ω;
the last vertex is b. The singleton list represents the constant path a=b.
No path-connectedness hypothesis is substituted for connectedness. Using
`IsPreconnected` allows the empty set, for which the endpoint statement is vacuous.
-/

namespace Specs.D12Complex.Ch03.PolygonalConnectivity

def polygonal_connectivity_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → IsPreconnected Ω →
    ∀ (a : ℂ), a ∈ Ω → ∀ (b : ℂ), b ∈ Ω →
      ∃ vertices : List ℂ,
        (a :: vertices).IsChain (fun x y => segment ℝ x y ⊆ Ω) ∧
        (a :: vertices).getLast (List.cons_ne_nil _ _) = b

def joinedIn_of_open_isPreconnected_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → IsPreconnected Ω →
    ∀ (a : ℂ), a ∈ Ω → ∀ (b : ℂ), b ∈ Ω → JoinedIn Ω a b

def exists_complexPath_of_open_isPreconnected_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → IsPreconnected Ω →
    ∀ (a : ℂ), a ∈ Ω → ∀ (b : ℂ), b ∈ Ω →
      ∃ γ : D12Complex.ComplexPath,
        γ.source = a ∧ γ.target = b ∧ γ.trace ⊆ Ω

def isPathConnected_of_open_isConnected_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → IsConnected Ω → IsPathConnected Ω

end Specs.D12Complex.Ch03.PolygonalConnectivity
