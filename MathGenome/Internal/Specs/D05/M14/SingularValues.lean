import MathGenome.Internal.Specs.D05.M14.PositiveSpectrum
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Data.List.OfFn

/-! K05.14.singular_values, paper.tex:2435–2439.
The full source list has length dim(V), even for rectangular maps. Occurrences
are retained. Its element at library index i is the paper's s_(i+1).
The positive list uses the first rank(T) indices; the implementation must prove
that these are precisely the positive occurrences of the full source list.
No nonzero-space or injectivity assumption is made. -/

noncomputable section

namespace D05

variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- All n singular values, including zeros, in nonincreasing order. -/
def singularValues (T : V →ₗ[F] W) : List ℝ :=
  List.ofFn fun i : Fin (Module.finrank F V) =>
    Real.sqrt (T.isSymmetric_adjoint_comp_self.eigenvalues rfl i)

/-- The list of r positive singular values, in the same order. -/
def positiveSingularValues (T : V →ₗ[F] W) : List ℝ :=
  List.ofFn fun i : Fin (Module.finrank F (LinearMap.range T)) =>
    T.singularValues i

end D05

namespace Specs.D05.M14.SingularValues

universe u v w

-- Definition bindings also check the prescribed values.
def fullList_type :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W], (V →ₗ[F] W) → List ℝ

def fullList_value : fullList_type := @_root_.D05.singularValues

def positiveList_type := fullList_type

def positiveList_value : positiveList_type := @_root_.D05.positiveSingularValues


def gram_positive : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.positiveSemidefinite ((LinearMap.adjoint T).comp T)


def full_length : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.singularValues T).length = Module.finrank F V


def library_prefix : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.singularValues T =
      List.ofFn (fun i : Fin (Module.finrank F V) => T.singularValues i)


def full_get : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (i : ℕ) (hi : i < (_root_.D05.singularValues T).length),
    (_root_.D05.singularValues T)[i] = T.singularValues i


def nonnegative : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ∀ s ∈ _root_.D05.singularValues T, 0 ≤ s


def nonincreasing : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.singularValues T).Pairwise (fun a b => b ≤ a)


def squared_eigenvalues : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.singularValues T).map (fun s => s ^ 2) =
      List.ofFn (T.isSymmetric_adjoint_comp_self.eigenvalues rfl)


def charpoly_roots : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ((LinearMap.adjoint T).comp T).charpoly.roots =
      ((_root_.D05.singularValues T).map (fun s => ((s ^ 2 : ℝ) : F)) : Multiset F)


def charpoly_characterization : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.singularValues T =
      ((((LinearMap.adjoint T).comp T).charpoly.roots.map RCLike.re).sort (· ≥ ·)).map
        Real.sqrt


def eigenbasis_multiplicities : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) {n : ℕ}
    (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ),
    (∀ i, ((LinearMap.adjoint T).comp T) (b i) = (a i : F) • b i) →
    (List.ofFn a : Multiset ℝ) =
      ((_root_.D05.singularValues T).map (fun s => s ^ 2) : Multiset ℝ)


def eigenbasis_sqrt_multiplicities : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) {n : ℕ}
    (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ),
    (∀ i, ((LinearMap.adjoint T).comp T) (b i) = (a i : F) • b i) →
    ((List.ofFn a).map Real.sqrt : Multiset ℝ) =
      (_root_.D05.singularValues T : Multiset ℝ)


def kernel_gram : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    LinearMap.ker ((LinearMap.adjoint T).comp T) = LinearMap.ker T


def positive_length : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.positiveSingularValues T).length = Module.finrank F (LinearMap.range T)


def positive_library_prefix : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.positiveSingularValues T =
      List.ofFn (fun i : Fin (Module.finrank F (LinearMap.range T)) => T.singularValues i)


def positive_entries : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ∀ s ∈ _root_.D05.positiveSingularValues T, 0 < s


def positive_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (i : ℕ),
    0 < T.singularValues i ↔ i < Module.finrank F (LinearMap.range T)


def zero_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (i : ℕ),
    T.singularValues i = 0 ↔ Module.finrank F (LinearMap.range T) ≤ i


def full_decomposition : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.singularValues T = _root_.D05.positiveSingularValues T ++
      List.replicate (Module.finrank F (LinearMap.ker T)) 0


def positive_filter : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.singularValues T).filter (fun s => decide (0 < s)) =
      _root_.D05.positiveSingularValues T


def positive_nonincreasing : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.positiveSingularValues T).Pairwise (fun a b => b ≤ a)


def zero_multiplicity : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.singularValues T).count 0 = Module.finrank F (LinearMap.ker T)


def zero_eigenvalue_multiplicity : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ((LinearMap.adjoint T).comp T).charpoly.roots.count 0 =
      Module.finrank F (LinearMap.ker T)


def rank_nullity : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.positiveSingularValues T).length =
      Module.finrank F V - Module.finrank F (LinearMap.ker T)


def rank_bound : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (_root_.D05.positiveSingularValues T).length ≤
      min (Module.finrank F V) (Module.finrank F W)


def empty_domain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), Module.finrank F V = 0 →
    _root_.D05.singularValues T = [] ∧ _root_.D05.positiveSingularValues T = []


def zero_map : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    _root_.D05.singularValues (0 : V →ₗ[F] W) = List.replicate (Module.finrank F V) 0 ∧
    _root_.D05.positiveSingularValues (0 : V →ₗ[F] W) = []

end Specs.D05.M14.SingularValues
