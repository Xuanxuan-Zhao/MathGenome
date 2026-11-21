import MathGenome.Internal.Specs.D07.Ch21.RegularDecompositionFiniteIrreducibleTypes
import MathGenome.Internal.Specs.D07.Ch21.MatrixOrthogonality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! K07.21.regular_decomposition, paper.tex:6340–6390.
The multiplicities are dimensions of the original representation spaces.
Completeness below quantifies over arbitrary dimensional representations;
no finiteness assumption is imposed on a representation being classified.
The external sum is indexed by a type and one of its d_i copies.
-/
namespace Specs.D07.Ch21.RegularDecomposition

universe u r v w
noncomputable section
open scoped Classical

/-- Exhaustiveness of a chosen family, including infinite dimensional targets.
The universe u includes the subspaces of the actual regular representation. -/
def IsComplete {G : Type u} [Group G] {I : Type r} {V : I → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
    Representation.IsIrreducible σ → ∃ i, Nonempty ((ρ i).Equiv σ)

/-- Exhaustiveness in the regular space's universe implies exhaustiveness
in every universe. In particular IsComplete imposes no size restriction. -/
def CompletenessUniversal : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) (V : I → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)), IsComplete ρ →
    ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
      Representation.IsIrreducible σ → ∃ i, Nonempty ((ρ i).Equiv σ)

/-- Finite dimension is proved for every irreducible, not assumed. -/
def IrreducibleFinite : Prop := RegularDecompositionFiniteIrreducibleTypes.DimensionBound.{u,w}

/-- Existence of representatives, pairwise inequivalent and complete across
arbitrary universes, in the fixed set of regular subrepresentations. -/
def FiniteTypes : Prop := RegularDecompositionFiniteIrreducibleTypes.FiniteCompleteFamily.{u,w}

/-- Exact square sum for any exhaustive, nonrepeating choice of types. -/
def SquareSum : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) → IsComplete ρ →
    Fintype.card G = ∑ i, Module.finrank ℂ (V i) ^ 2

/-- The actual regular action is equivariantly equivalent to precisely d_i
copies of each V_i. This uses the finite-support external direct sum. -/
def Decomposition : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) → IsComplete ρ →
    Nonempty ((Representation.leftRegular ℂ G).Equiv
      (Representation.directSum (fun p : Σ i, Fin (Module.finrank ℂ (V i)) => ρ p.1)))

/-- Every matrix coefficient, with its two coordinate indices, belongs to
an orthogonal basis of the entire function space, not just class functions.
The metric convention is linearity in the first argument. -/
def MatrixCoefficientBasis : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i))
    (b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) → IsComplete ρ →
    (∀ i g, LinearMap.toMatrix (b i) (b i) (ρ i g) ∈
      Matrix.unitaryGroup (Fin (Module.finrank ℂ (V i))) ℂ) →
    let f : (Σ i, Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))) → G → ℂ :=
      fun p => MatrixOrthogonality.coefficient (ρ p.1) (b p.1) p.2.1 p.2.2
    ∃ B : Module.Basis (Σ i, Fin (Module.finrank ℂ (V i)) ×
        Fin (Module.finrank ℂ (V i))) ℂ (G → ℂ),
      (∀ p, B p = f p) ∧
      ∀ p q, HomPairing.pairingValue G (B p) (B q) =
        if p = q then (Module.finrank ℂ (V p.1) : ℂ)⁻¹ else 0

/-- The existence statement with all the data for one and the same choice
of types: exact multiplicities and square sum, and completeness among all
irreducibles even when finite dimension was not part of their definition. -/
def RegularTheorem : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∃ s : Finset (Subrepresentation (Representation.leftRegular ℂ G)),
      s.Nonempty ∧
      (∀ U ∈ s, Representation.IsIrreducible U.toRepresentation) ∧
      (s : Set (Subrepresentation (Representation.leftRegular ℂ G))).Pairwise
        (fun U W => ¬ Nonempty (U.toRepresentation.Equiv W.toRepresentation)) ∧
      IsComplete (fun i : s => i.val.toRepresentation) ∧
      (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
        Representation.IsIrreducible σ →
          Module.Finite ℂ W ∧ ∃ i : s, Nonempty (i.val.toRepresentation.Equiv σ)) ∧
      Fintype.card G = ∑ i : s, Module.finrank ℂ i.val.toSubmodule ^ 2 ∧
      Nonempty ((Representation.leftRegular ℂ G).Equiv
        (Representation.directSum (fun p : Σ i : s,
          Fin (Module.finrank ℂ i.val.toSubmodule) => p.1.val.toRepresentation)))

end
end Specs.D07.Ch21.RegularDecomposition
