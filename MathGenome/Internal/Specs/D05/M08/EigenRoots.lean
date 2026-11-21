import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.M09.Eigenspace

/-!
Independent specifications for K05.08.eigen_roots, paper.tex:1164–1170.
The polynomials are the canonical objects from the prerequisite interfaces.
The kernel is a submodule of the original space, and the scalar belongs to
the original field. No splitting or positive-dimension hypothesis is added.
-/

noncomputable section

namespace Specs.D05.M08.EigenRoots

/-- The first two conditions in the source theorem. -/
def kernel_iff_charpoly_root : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ≠ ⊥ ↔
      (Charpoly.charpoly_value T).eval μ = 0

/-- The first and third conditions in the source theorem. -/
def kernel_iff_minpoly_root : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ≠ ⊥ ↔
      (Minpoly.minimalPolynomial_value K V T).eval μ = 0

/-- Both polynomials have exactly the same scalar roots over the named field. -/
def charpoly_root_iff_minpoly_root : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    (Charpoly.charpoly_value T).eval μ = 0 ↔
      (Minpoly.minimalPolynomial_value K V T).eval μ = 0

/-- The three source conditions are equivalent, expressed by two equivalences
with their common first condition. -/
def eigen_roots : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    (LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ≠ ⊥ ↔
      (Charpoly.charpoly_value T).eval μ = 0) ∧
    (LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) ≠ ⊥ ↔
      (Minpoly.minimalPolynomial_value K V T).eval μ = 0)

/-- On the zero-dimensional space both polynomials are one and all three
conditions in the theorem are false. -/
def zero_dimensional : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    Module.finrank K V = 0 →
      Charpoly.charpoly_value T = 1 ∧
      Minpoly.minimalPolynomial_value K V T = 1 ∧
      LinearMap.ker (T - μ • (LinearMap.id : Module.End K V)) = ⊥ ∧
      (Charpoly.charpoly_value T).eval μ ≠ 0 ∧
      (Minpoly.minimalPolynomial_value K V T).eval μ ≠ 0

end Specs.D05.M08.EigenRoots
