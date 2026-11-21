import MathGenome.Internal.Specs.D05.M04.Trace
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M15.DeterminantLine.MinorCoefficients
import MathGenome.Internal.Specs.D05.M15.Charcoefficients.PrincipalExpansion

/-! K05.15.charcoefficients, paper.tex:3174–3187.
The powers are the actual homogeneous submodules of the exterior quotient,
with their accepted functorial maps. All statements hold over every field,
including finite fields and positive characteristic, and include dimension zero.
The polynomial identity is formal; its scalar version is also stated explicitly.
-/
noncomputable section
namespace Specs.D05.M15.Charcoefficients
open scoped BigOperators

/-- The exterior trace is the sum of the principal minors of the same degree. -/
def trace_principal_minors : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : V →ₗ[K] V) (p : ℕ),
    LinearMap.trace K (⋀[K]^p V) (WedgeSign.powerMap_value p T) =
      ∑ I : Set.powersetCard (Fin n) p,
        Matrix.det ((Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T).submatrix
          (Subtype.val : I.val → Fin n) (Subtype.val : I.val → Fin n))

/-- The characteristic polynomial, computed in any finite ordered basis. -/
def based_polynomial_expansion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : V →ₗ[K] V),
    Specs.D05.M08.Charpoly.charpoly_value T =
      ∑ p ∈ Finset.range (n + 1),
        Polynomial.C ((-1 : K)^p *
          LinearMap.trace K (⋀[K]^p V) (WedgeSign.powerMap_value p T)) *
            Polynomial.X ^ (n - p)

/-- The same full identity without any basis choice in the statement. -/
def polynomial_expansion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    Specs.D05.M08.Charpoly.charpoly_value T =
      ∑ p ∈ Finset.range (Module.finrank K V + 1),
        Polynomial.C ((-1 : K)^p *
          LinearMap.trace K (⋀[K]^p V) (WedgeSign.powerMap_value p T)) *
            Polynomial.X ^ (Module.finrank K V - p)

/-- Evaluation at an arbitrary scalar is the displayed determinant identity. -/
def scalar_expansion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : V →ₗ[K] V) (t : K),
    D05.M05.determinant (t • (1 : Matrix (Fin n) (Fin n) K) -
      Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T) =
      ∑ p ∈ Finset.range (n + 1), (-1 : K)^p *
        LinearMap.trace K (⋀[K]^p V) (WedgeSign.powerMap_value p T) * t^(n-p)

/-- Degree zero contributes one, even on the zero space. -/
def degree_zero_trace : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    LinearMap.trace K (⋀[K]^0 V) (WedgeSign.powerMap_value 0 T) = 1

/-- In dimension zero the full polynomial identity reduces to one. -/
def zero_dimensional : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    Module.finrank K V = 0 → Specs.D05.M08.Charpoly.charpoly_value T = 1

/-- The source's consequence for products, with no invertibility hypothesis. -/
def charpoly_comp_comm : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B : V →ₗ[K] V),
    Specs.D05.M08.Charpoly.charpoly_value (A.comp B) =
      Specs.D05.M08.Charpoly.charpoly_value (B.comp A)

end Specs.D05.M15.Charcoefficients
