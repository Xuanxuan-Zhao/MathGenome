import MathGenome.Internal.Specs.D05.M13.NormalReducing
import MathGenome.Internal.Specs.D05.M13.Unitary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent specifications for K05.13.real_normal_blocks, paper.tex:2235–2250.
A block is specified by its action on basis vectors (columns). Both orientations
of a two-element block are allowed, so the assertion applies to every basis
index. The parameter b is strictly positive in either orientation. For an
orthonormal basis the partner is unique and these two-element blocks are
disjoint: the nonzero off-diagonal coordinate singles out the partner.
Consequently the conditions below state precisely a basis of real lines and
planes with matrices [a,-b;b,a], rather than merely invariant subspaces.
No positive-dimension or spectral certificate is a hypothesis.
-/
noncomputable section
namespace Specs.D05.M13.RealNormalBlocks
universe u

/-- The two columns of a positively oriented real normal plane block. -/
def PlaneAction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (e f : V) (a b : ℝ) : Prop :=
  T e = a • e + b • f ∧ T f = (-b) • e + a • f

/-- Each index belongs to a real eigenline or to one of the two positions of
an oriented plane block. The index inequality makes its two positions distinct. -/
def BlockAt {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (v : ι → V) (i : ι) : Prop :=
  (∃ a : ℝ, T (v i) = a • v i) ∨
    ∃ j : ι, j ≠ i ∧ ∃ a b : ℝ, 0 < b ∧
      (PlaneAction T (v i) (v j) a b ∨ PlaneAction T (v j) (v i) a b)

/-- The same blocks with the orthogonal-map parameter restrictions. -/
def OrthogonalBlockAt {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (v : ι → V) (i : ι) : Prop :=
  (T (v i) = v i ∨ T (v i) = -v i) ∨
    ∃ j : ι, j ≠ i ∧ ∃ a b : ℝ, 0 < b ∧ a ^ 2 + b ^ 2 = 1 ∧
      (PlaneAction T (v i) (v j) a b ∨ PlaneAction T (v j) (v i) a b)

/-- The full real normal block theorem, including an empty basis. -/
def normal_blocks : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V), _root_.D05.normalOperator T →
    ∃ n : ℕ, ∃ B : OrthonormalBasis (Fin n) ℝ V, ∀ i, BlockAt T B i

/-- The full orthogonal specialization; no normality premise is added. -/
def orthogonal_blocks : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V), _root_.D05.IsUnitaryMap T →
    ∃ n : ℕ, ∃ B : OrthonormalBasis (Fin n) ℝ V, ∀ i, OrthogonalBlockAt T B i

/-- Norm preservation imposes the stated scalar restrictions on any blocks. -/
def orthogonal_parameters : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →ₗ[ℝ] V) (v : ι → V), _root_.D05.IsInnerIsometry T →
    Orthonormal ℝ v → ∀ i, BlockAt T v i → OrthogonalBlockAt T v i

/-- The local step from which the dimension induction constructs the basis. -/
def normal_small_block : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] (T : V →ₗ[ℝ] V),
    _root_.D05.normalOperator T →
      (∃ a : ℝ, ∃ e : V, ‖e‖ = 1 ∧ T e = a • e) ∨
      ∃ a b : ℝ, ∃ e f : V, 0 < b ∧ ‖e‖ = 1 ∧ ‖f‖ = 1 ∧
        inner ℝ e f = 0 ∧ PlaneAction T e f a b

/-- A selected partition into singleton indices and paired indices. An
involutive partner function has disjoint orbits of size one or two. -/
def PartitionAt {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (v : ι → V) (p : ι → ι) (i : ι) : Prop :=
  (p i = i ∧ ∃ a : ℝ, T (v i) = a • v i) ∨
    (p i ≠ i ∧ ∃ a b : ℝ, 0 < b ∧
      (PlaneAction T (v i) (v (p i)) a b ∨ PlaneAction T (v (p i)) (v i) a b))

/-- The index pairing carries the orthogonal scalar constraints too. -/
def OrthogonalPartitionAt {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (v : ι → V) (p : ι → ι) (i : ι) : Prop :=
  (p i = i ∧ (T (v i) = v i ∨ T (v i) = -v i)) ∨
    (p i ≠ i ∧ ∃ a b : ℝ, 0 < b ∧ a ^ 2 + b ^ 2 = 1 ∧
      (PlaneAction T (v i) (v (p i)) a b ∨ PlaneAction T (v (p i)) (v i) a b))

/-- Bridge from per-column block equations to a disjoint block partition. -/
def block_partition : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →ₗ[ℝ] V) (v : ι → V), Orthonormal ℝ v →
    (∀ i, BlockAt T v i) →
      ∃ p : ι → ι, Function.Involutive p ∧ ∀ i, PartitionAt T v p i

/-- Explicitly partitioned form of the complete real normal block theorem. -/
def normal_blocks_partitioned : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V), _root_.D05.normalOperator T →
    ∃ n : ℕ, ∃ B : OrthonormalBasis (Fin n) ℝ V, ∃ p : Fin n → Fin n,
      Function.Involutive p ∧ ∀ i, PartitionAt T B p i

/-- Explicitly partitioned orthogonal specialization, including dimension zero. -/
def orthogonal_blocks_partitioned : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V), _root_.D05.IsUnitaryMap T →
    ∃ n : ℕ, ∃ B : OrthonormalBasis (Fin n) ℝ V, ∃ p : Fin n → Fin n,
      Function.Involutive p ∧ ∀ i, OrthogonalPartitionAt T B p i

/-- The explicit transpose products from the paper's last sentence. -/
def plane_gram_products : Prop :=
  ∀ a b : ℝ,
    (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℝ).transpose * !![a, -b; b, a] =
      (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℝ) * (!![a, -b; b, a]).transpose =
      (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- A displayed plane block is orthogonal exactly when a²+b²=1. This
criterion itself does not require b>0. -/
def plane_orthogonal_iff : Prop :=
  ∀ a b : ℝ,
    _root_.D05.IsUnitaryMap
      (Matrix.toEuclideanLin (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℝ)) ↔
      a ^ 2 + b ^ 2 = 1
end Specs.D05.M13.RealNormalBlocks
