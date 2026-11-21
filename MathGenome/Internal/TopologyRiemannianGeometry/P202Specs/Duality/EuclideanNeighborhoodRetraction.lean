import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.LocallyContractible

/-!
Independent statement of paper.tex, Lemma `lem:p202-enr` (lines 2391–2400).
The hypothesis is classical local contractibility of the subspace: a smaller
neighborhood has nullhomotopic inclusion into the prescribed neighborhood.
It does not require contractible neighborhoods or any geometric regularity.
-/

namespace P202.Duality

/-- The source's Euclidean ambient space, including dimension zero. -/
abbrev EuclideanAmbient (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A continuous retraction from some ambient open neighborhood onto `K`.
The empty neighborhood is allowed, as required when `K` is empty. -/
def HasOpenNeighborhoodRetraction {E : Type*} [TopologicalSpace E] (K : Set E) : Prop :=
  ∃ (N : Set E) (_hN : IsOpen N) (hKN : K ⊆ N) (r : C(N, K)),
    ∀ x : K, r ⟨x.1, hKN x.2⟩ = x

end P202.Duality

namespace P202Specs.Duality.EuclideanNeighborhoodRetraction

open P202.Duality

/-- Every compact classically locally contractible Euclidean subset is an ENR.
No restriction on dimension, nonemptiness, or the embedding is imposed. -/
def euclideanNeighborhoodRetraction : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanAmbient n)),
    IsCompact K → LocallyContractibleSpace K → HasOpenNeighborhoodRetraction K

end P202Specs.Duality.EuclideanNeighborhoodRetraction
