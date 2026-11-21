import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M06.Invariant
import MathGenome.Internal.Specs.D05.Foundations.QuotientBasisUnits
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The quotient-field proof stage of paper.tex:1320–1326. The quotient is
`AdjoinRoot p = K[X] / Ideal.span {p}`, and W has its inherited K-structure.
An action is required to satisfy the evaluation formula for every representative;
no module or decomposition certificate is assumed in the existence statement.
The later statements apply to every module satisfying that formula. -/
noncomputable section
namespace Specs.D05.M09.Existence.QuotientFieldBasis

abbrev Kernel {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) :=
  LinearMap.ker (Polynomial.aeval T p)

/-- Compatibility with the original operator, including all representatives. -/
def ActionAgrees {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K)
    [Module (AdjoinRoot p) (Kernel T p)] : Prop :=
  ∀ (q : Polynomial K) (w : Kernel T p),
    ((AdjoinRoot.mk p q • w : Kernel T p) : V) = Polynomial.aeval T q (w : V)

/-- Construction includes all module laws, and works even without irreducibility. -/
def quotient_module : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K),
    ∃ m : Module (AdjoinRoot p) (Kernel T p), @ActionAgrees K V _ _ _ T p m

/-- Changing a representative by a multiple of p does not change its value on W. -/
def representative_independence : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q r : Polynomial K),
    p ∣ q - r → ∀ w : Kernel T p,
      Polynomial.aeval T q (w : V) = Polynomial.aeval T r (w : V)

/-- Every finite K-spanning list also spans over the quotient field. -/
def spanning_over_quotient : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) [Fact (Irreducible p)]
    [Module (AdjoinRoot p) (Kernel T p)], ActionAgrees T p →
    ∀ (s : ℕ) (w : Fin s → Kernel T p),
      Submodule.span K (Set.range w) = ⊤ →
      Submodule.span (AdjoinRoot p) (Set.range w) = ⊤

/-- A supplied finite K-spanning list yields finite dimension and an actual
finite F-basis. No finite-dimensional ambient-space instance is required. -/
def finite_basis_of_spanning : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) [Fact (Irreducible p)]
    [Module (AdjoinRoot p) (Kernel T p)], ActionAgrees T p →
    ∀ (s : ℕ) (w : Fin s → Kernel T p),
      Submodule.span K (Set.range w) = ⊤ →
      FiniteDimensional (AdjoinRoot p) (Kernel T p) ∧
        ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (AdjoinRoot p) (Kernel T p))

/-- Finite dimension is deduced, rather than assumed over F. -/
def finite_dimensional : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K)
    [Fact (Irreducible p)] [Module (AdjoinRoot p) (Kernel T p)],
    ActionAgrees T p → FiniteDimensional (AdjoinRoot p) (Kernel T p)

/-- The original vectors, with index i and exponent j kept distinct, form a
K-basis for any F-basis. The stronger arbitrary-index version needs no finite
ambient dimension; in particular it includes every finite F-basis in the paper. -/
def expanded_basis : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) [Fact (Irreducible p)]
    [Module (AdjoinRoot p) (Kernel T p)], ActionAgrees T p →
    ∀ b : Module.Basis I (AdjoinRoot p) (Kernel T p),
      ∃ c : Module.Basis (I × Fin p.natDegree) K (Kernel T p),
        ∀ i j, (c (i, j) : V) = (T ^ (j : ℕ)) (b i : V)

/-- Both dimensions refer to the same kernel and the specified quotient action.
There is no nonzero-kernel hypothesis, so this includes W = 0. -/
def dimension_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K)
    [Fact (Irreducible p)] [Module (AdjoinRoot p) (Kernel T p)],
    ActionAgrees T p →
      Module.finrank K (Kernel T p) =
        p.natDegree * Module.finrank (AdjoinRoot p) (Kernel T p)

end Specs.D05.M09.Existence.QuotientFieldBasis
