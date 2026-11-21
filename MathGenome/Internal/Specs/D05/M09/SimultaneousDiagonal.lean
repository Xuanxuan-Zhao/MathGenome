import MathGenome.Internal.Specs.D05.M09.SimultaneousDiagonal.Finite
import MathGenome.Internal.Specs.D05.M03.HomDimension.FiniteOperatorSpan

/-! Independent statements for K05.09.simultaneous_diagonal,
paper.tex:1303–1312. The index type is arbitrary, including infinite and
empty types. All eigenvalues belong to the original field. -/

namespace Specs.D05.M09.SimultaneousDiagonal

universe u v w

def simultaneouslyDiagonalizable_type :=
  (K : Type u) → (V : Type v) → (ι : Type w) →
    [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → (ι → Module.End K V) → Prop

def simultaneouslyDiagonalizable_value : simultaneouslyDiagonalizable_type.{u, v, w} :=
  fun K V ι _ _ _ _ T =>
    ∃ (d : ℕ) (b : Module.Basis (Fin d) K V) (μ : ι → Fin d → K),
      ∀ i j, T i (b j) = μ i j • b j

/-- No finiteness assumption on the family and no diagonalizability
assumption on its linear combinations. -/
def common_eigenbasis : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V),
    Pairwise (fun i j => Commute (T i) (T j)) →
    (∀ i, Diagonalizable.diagonalizable_value K V (T i)) →
      simultaneouslyDiagonalizable_value K V ι T

/-- Both necessary conditions follow from a common eigenbasis. -/
def common_eigenbasis_converse : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V),
    simultaneouslyDiagonalizable_value K V ι T →
      (∀ i, Diagonalizable.diagonalizable_value K V (T i)) ∧
        Pairwise (fun i j => Commute (T i) (T j))

def simultaneous_iff_diagonalizable_and_commute : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V),
    simultaneouslyDiagonalizable_value K V ι T ↔
      (∀ i, Diagonalizable.diagonalizable_value K V (T i)) ∧
        Pairwise (fun i j => Commute (T i) (T j))

/-- The paper's equivalence for individually diagonalizable families. -/
def commute_iff_simultaneous : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V),
    (∀ i, Diagonalizable.diagonalizable_value K V (T i)) →
      (Pairwise (fun i j => Commute (T i) (T j)) ↔
        simultaneouslyDiagonalizable_value K V ι T)

/-- The same result for a family presented as an arbitrary set. -/
def set_common_eigenbasis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : Set (Module.End K V)),
    (∀ S ∈ F, ∀ T ∈ F, Commute S T) →
    (∀ T ∈ F, Diagonalizable.diagonalizable_value K V T) →
      ∃ (d : ℕ) (b : Module.Basis (Fin d) K V),
        ∀ T ∈ F, ∃ μ : Fin d → K, ∀ j, T (b j) = μ j • b j

def empty_family_common_eigenbasis : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [IsEmpty ι] (T : ι → Module.End K V),
    simultaneouslyDiagonalizable_value K V ι T

/-- Even an infinite family on the zero space has the empty common basis. -/
def zero_space_common_eigenbasis : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Subsingleton V] (T : ι → Module.End K V),
      ∃ (b : Module.Basis (Fin 0) K V) (μ : ι → Fin 0 → K),
        ∀ i j, T i (b j) = μ i j • b j

end Specs.D05.M09.SimultaneousDiagonal
