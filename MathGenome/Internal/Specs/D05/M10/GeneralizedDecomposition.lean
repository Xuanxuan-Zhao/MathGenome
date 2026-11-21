import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M06.DirectSum
import MathGenome.Internal.Specs.D05.M10.Generalized
import Mathlib.Algebra.Polynomial.Splits

/-!
Independent statements for K05.10.generalized_decomposition, paper.tex:1445–1453.
The indexing set is the actual spectrum over K. The summands are the shared
kernels at the ambient dimension; the direct-sum assertion is bijectivity of
canonical addition of finitely supported subspace components. Only the
characteristic polynomial is assumed to split, with no scalar extension or
positive-dimension hypothesis.
-/

noncomputable section
open scoped Classical
namespace Specs.D05.M10.GeneralizedDecomposition

/-- The internal direct sum is indexed by precisely the K-spectrum. -/
def decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (Specs.D05.M08.Charpoly.charpoly_value T).Splits →
      _root_.DirectSum.IsInternal
        (fun μ : spectrum K T => Generalized.generalizedEigenspace_value K V T μ.val)

/-- The summand restrictions are actual restrictions of T and T - μ I.
A positive power of the latter vanishes, including when V is zero. -/
def summand_structure : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : spectrum K T),
    ∃ (hT : Specs.D05.M06.Invariant.invariant_value K V
        (Generalized.generalizedEigenspace_value K V T μ.val) T)
      (hN : Specs.D05.M06.Invariant.invariant_value K V
        (Generalized.generalizedEigenspace_value K V T μ.val) (T - μ.val • 1)),
      T.restrict hT = μ.val • LinearMap.id + (T - μ.val • 1).restrict hN ∧
        ∃ r : ℕ, 0 < r ∧ ((T - μ.val • 1).restrict hN) ^ r = 0

/-- A scalar outside the spectrum contributes no vectors. -/
def outside_spectrum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    μ ∉ spectrum K T → Generalized.generalizedEigenspace_value K V T μ = ⊥

/-- Dimension zero has an empty spectral index set and the empty decomposition. -/
def zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K V = 0 →
      IsEmpty (spectrum K T) ∧
        _root_.DirectSum.IsInternal
          (fun μ : spectrum K T => Generalized.generalizedEigenspace_value K V T μ.val)

end Specs.D05.M10.GeneralizedDecomposition
