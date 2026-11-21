import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.Specs.D05.M15.WedgeSign
import MathGenome.Internal.Specs.D05.M05.OperatorDet

/-!
Independent statements for K05.15.determinant_line, paper.tex:2957–2966,
and the top-exterior comparison in K05.05.operator_det, paper.tex:901–907.
The exterior powers and their maps are the accepted homogeneous submodules
of the square-relation quotient. Determinants use the earlier column Leibniz
sum and operator determinant. All fields and all finite dimensions, including
zero, are allowed; no averaging, invertibility, or splitting is assumed.
-/

noncomputable section
namespace Specs.D05.M15.DeterminantLine

universe u v

/-- The ordered top wedge belonging to a specified finite basis. -/
abbrev volume {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) : Exterior.homogeneousPart_value K V n :=
  exteriorPower.ιMulti K n b

/-- The top exterior space is a line with this particular wedge as basis. -/
def top_wedge_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V),
    ∃ B : Module.Basis (Fin 1) K (Exterior.homogeneousPart_value K V n), B 0 = volume b

/-- Expansion of an arbitrary ordered tuple in the top wedge. Rows of the
matrix are basis coordinates, and columns are tuple positions. -/
def wedge_expansion : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (x : Fin n → V),
    exteriorPower.ιMulti K n x =
      D05.M05.determinant (Matrix.of (fun i j => b.repr (x j) i)) • volume b

/-- The explicit signed sum in the source, with no characteristic restriction. -/
def leibniz_action : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    exteriorPower.ιMulti K n (T ∘ b) =
      (∑ σ : Equiv.Perm (Fin n), (D05.Foundations.permutationSign σ : K) *
        ∏ j, Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T (σ j) j) • volume b

/-- A matrix satisfying the paper's column equations gives the claimed wedge
coefficient; the matrix is not an assumed determinant-action certificate. -/
def matrix_action : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (A : Matrix (Fin n) (Fin n) K),
    (∀ j, T (b j) = ∑ i, A i j • b i) →
      WedgeSign.powerMap_value n T (volume b) = D05.M05.determinant A • volume b

/-- Equality of actual linear maps on the entire top exterior power. -/
def top_power_in_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    WedgeSign.powerMap_value n T =
      Specs.D05.M05.OperatorDet.detInBasis_value b T • LinearMap.id

/-- Coordinate-independent bridge to the previously defined operator determinant. -/
def top_power_operator_det : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    WedgeSign.powerMap_value (Module.finrank K V) T =
      Specs.D05.M05.OperatorDet.operatorDet_value T • LinearMap.id

/-- The same comparison inside the exterior algebra, via the canonical
inclusion of its top homogeneous part. -/
def exterior_algebra_action : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (z : Exterior.homogeneousPart_value K V n),
    WedgeSign.exteriorMap_value T (z : _root_.ExteriorAlgebra K V) =
      Specs.D05.M05.OperatorDet.detInBasis_value b T • (z : _root_.ExteriorAlgebra K V)

/-- Rescaling the volume by a nonzero scalar preserves the determinant scalar,
and that scalar is uniquely determined by the action on the new volume. -/
def rescaled_volume : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V) (c : K), c ≠ 0 →
    WedgeSign.powerMap_value n T (c • volume b) =
      Specs.D05.M05.OperatorDet.detInBasis_value b T • (c • volume b) ∧
    ∀ a : K, WedgeSign.powerMap_value n T (c • volume b) = a • (c • volume b) →
      a = Specs.D05.M05.OperatorDet.detInBasis_value b T

/-- Degree zero is the identity on K under the canonical scalar identification,
for every endomorphism, even if its original space has positive dimension. -/
def degree_zero_identity : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V),
    WedgeSign.powerMap_value 0 T = LinearMap.id ∧
    ∀ a : K, exteriorPower.zeroEquiv K V
      (WedgeSign.powerMap_value 0 T ((exteriorPower.zeroEquiv K V).symm a)) = a

/-- In dimension zero the determinant scalar is one, as is the empty wedge. -/
def zero_dim_scalar : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 0) K V) (T : Module.End K V),
    Specs.D05.M05.OperatorDet.detInBasis_value b T = 1 ∧
    ((volume b : Exterior.homogeneousPart_value K V 0) : _root_.ExteriorAlgebra K V) = 1

end Specs.D05.M15.DeterminantLine
