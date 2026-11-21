import MathGenome.Internal.Specs.D05.M09.MinpolyCriterion
import MathGenome.Internal.Specs.D05.M08.RestrictionMinpoly
import MathGenome.Internal.Specs.D05.M09.CommutantInvariance

/-! Independent statements for the finite-family stage of
K05.09.simultaneous_diagonal, paper.tex:1303–1312. All scalars and
all eigenvalues are in the original field. Empty families and zero spaces
are included. Diagonalizability uses the upstream eigenbasis definition. -/

namespace Specs.D05.M09.SimultaneousDiagonal.Finite

/-- Invariant restriction preserves diagonalizability, without a complement
hypothesis. This is the minimal-polynomial step used on each eigenspace. -/
def restriction_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V) (S : Module.End K V)
    (hU : M06.Invariant.invariant_value K V U S),
    Diagonalizable.diagonalizable_value K V S →
      Diagonalizable.diagonalizable_value K U
        (M06.Invariant.restriction_value K V U S hU)

/-- On every eigenspace of one member, every commuting diagonalizable
member has a diagonalizable restriction. -/
def eigenspace_restriction_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S T : Module.End K V),
    Commute S T → Diagonalizable.diagonalizable_value K V S →
      ∀ a : K, ∃ hU : M06.Invariant.invariant_value K V (T.eigenspace a) S,
        Diagonalizable.diagonalizable_value K (T.eigenspace a)
          (M06.Invariant.restriction_value K V (T.eigenspace a) S hU)

/-- Every finite pairwise commuting family of individually diagonalizable
operators has a common finite eigenbasis, with an eigenvalue for each
operator and each basis vector. No hypothesis on linear combinations occurs. -/
def finite_common_eigenbasis : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Finite ι] (T : ι → Module.End K V),
    Pairwise (fun i j => Commute (T i) (T j)) →
    (∀ i, Diagonalizable.diagonalizable_value K V (T i)) →
      ∃ (d : ℕ) (b : Module.Basis (Fin d) K V) (μ : ι → Fin d → K),
        ∀ i j, T i (b j) = μ i j • b j

/-- The empty-family base case requires no operator assumptions. -/
def empty_family_common_eigenbasis : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [IsEmpty ι] (T : ι → Module.End K V),
      ∃ (d : ℕ) (b : Module.Basis (Fin d) K V) (μ : ι → Fin d → K),
        ∀ i j, T i (b j) = μ i j • b j

/-- The zero space has a common empty eigenbasis, for every finite family. -/
def zero_space_common_eigenbasis : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Subsingleton V] [Finite ι] (T : ι → Module.End K V),
      ∃ (b : Module.Basis (Fin 0) K V) (μ : ι → Fin 0 → K),
        ∀ i j, T i (b j) = μ i j • b j

end Specs.D05.M09.SimultaneousDiagonal.Finite
