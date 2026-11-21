import MathGenome.Internal.Specs.D05.M06.SumDimension
import MathGenome.Internal.Specs.D05.M12.OrthogonalComplement

/-!
Independent statements for K05.12.orthogonal_decomposition,
paper.tex:2014–2021. The orthogonal complement is the shared canonical
`Submodule.orthogonal`, whose membership formula is `D05.firstInner v u = 0`.
The first two statements and the double-complement strengthening require only
that U be finite dimensional. No completeness or dimension hypothesis on V is
present. Natural-number dimension formulas are used only when V is finite
dimensional. All statements include zero subspaces and zero ambient spaces.
-/

namespace Specs.D05.M12.OrthogonalDecomposition

/-- Both components are actual elements of their subspaces, and the pair is
unique. This expresses existence and uniqueness together. -/
def exists_unique_components : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (v : V),
    ∃! p : U × U.orthogonal, (p.1 : V) + (p.2 : V) = v

/-- The paper's existing unique-expression predicate, applied to U and U⊥. -/
def internal_direct_sum : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U],
    Specs.D05.M06.DirectSum.UniqueDecomposition
      (fun b : Bool => if b then U.orthogonal else U)

/-- Dimensions add in the finite-dimensional ambient case. -/
def dimension_add : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (U : Submodule F V),
    Module.finrank F U + Module.finrank F U.orthogonal = Module.finrank F V

/-- The subtraction formula stated in the theorem. -/
def dimension_orthogonal : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (U : Submodule F V),
    Module.finrank F U.orthogonal = Module.finrank F V - Module.finrank F U

/-- The strengthening at the end of the proof: V can be infinite dimensional. -/
def double_orthogonal_of_finiteDimensional_subspace : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U], U.orthogonal.orthogonal = U

/-- The finite ambient version explicitly stated in the theorem. -/
def double_orthogonal : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (U : Submodule F V), U.orthogonal.orthogonal = U

end Specs.D05.M12.OrthogonalDecomposition
