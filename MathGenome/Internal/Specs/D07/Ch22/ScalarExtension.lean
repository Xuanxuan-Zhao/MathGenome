import MathGenome.Internal.Specs.D07.Ch22.TensorConstruction
import MathGenome.Internal.Specs.D07.Ch22.TensorDirectSums
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specification of K07.22.scalar_extension, paper.tex:6880–6914.
An `Algebra R S` records an arbitrary unital homomorphism of commutative
rings; it does not impose injectivity. The explicit ring-hom construction
below includes the zero ring. Compatible `Module R N` and `IsScalarTower`
data express restriction of scalars, rather than a second unrelated action.
Finsupp is the source's direct sum of copies of the coefficient field.
-/

universe u v w t
namespace Specs.D07.Ch22.ScalarExtension
open scoped TensorProduct

/-- Every unital ring map gives the stated action on the canonical tensor.
The action is defined on all tensors, with all four module axioms. -/
def RingHomAction : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] (φ : R →+* S)
    (M : Type w) [AddCommGroup M] [Module R M],
    letI : Algebra R S := φ.toAlgebra
    Ch16.Definition.ModuleLaws S (S ⊗[R] M) ∧
      ∀ (s' s : S) (m : M), s' • (s ⊗ₜ[R] m) = (s' * s) ⊗ₜ[R] m

/-- The R-action on an S-module is the one obtained through the given map. -/
def RestrictionOfScalars : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] (φ : R →+* S)
    (N : Type t) [AddCommGroup N] [Module S N],
    ∃ inst : Module R N,
      letI := inst
      ∀ (r : R) (n : N), r • n = φ r • n

/-- The map to scalar extension is R-linear, including when it is not injective. -/
def NaturalMap : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M],
    ∃ η : M →ₗ[R] S ⊗[R] M, ∀ m, η m = (1 : S) ⊗ₜ[R] m

/-- The proposed inverse construction is balanced and biadditive. -/
def LiftBalanced : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type t) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : M →ₗ[R] N), TensorConstruction.IsBalanced R S M (fun s m => s • h m)

/-- The Hom correspondence, with both specified evaluation formulas. -/
def HomEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type t) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
    ∃ e : ((S ⊗[R] M) →ₗ[S] N) ≃ₗ[S] (M →ₗ[R] N),
      (∀ F m, e F m = F ((1 : S) ⊗ₜ[R] m)) ∧
      (∀ h s m, e.symm h (s ⊗ₜ[R] m) = s • h m)

/-- The same correspondence starting with just a ring map and an S-module;
restriction of scalars and its compatible tower are explicitly constructed. -/
def RingHomHomEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] (φ : R →+* S)
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type t) [AddCommGroup N] [Module S N],
    letI : Algebra R S := φ.toAlgebra
    letI : Module R N := Module.compHom N φ
    letI : IsScalarTower R S N :=
      { smul_assoc := fun r s n => mul_smul (φ r) s n }
    ∃ e : ((S ⊗[R] M) →ₗ[S] N) ≃ₗ[S] (M →ₗ[R] N),
      (∀ F m, e F m = F ((1 : S) ⊗ₜ[R] m)) ∧
      (∀ h s m, e.symm h (s ⊗ₜ[R] m) = s • h m)

/-- Every R-linear map has a unique S-linear extension with the full tensor rule. -/
def UniversalProperty : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type t) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : M →ₗ[R] N),
    ∃! F : (S ⊗[R] M) →ₗ[S] N, ∀ s m, F (s ⊗ₜ[R] m) = s • h m

/-- The source's elementary torsion computation, for any nonzero annihilator. -/
def TorsionTensor : Prop :=
  ∀ (M : Type w) [AddCommGroup M] (q : ℚ) (m : M) (d : ℤ),
    d ≠ 0 → d • m = 0 →
      q ⊗ₜ[ℤ] m = (q / (d : ℚ)) ⊗ₜ[ℤ] (d • m) ∧ q ⊗ₜ[ℤ] m = 0

/-- In fact finiteness is unnecessary: every torsion abelian group vanishes
under rational scalar extension. `x = 0` means the entire tensor module is zero. -/
def TorsionVanishing : Prop :=
  ∀ (M : Type w) [AddCommGroup M],
    (∀ m : M, ∃ d : ℤ, d ≠ 0 ∧ d • m = 0) → ∀ x : ℚ ⊗[ℤ] M, x = 0

/-- In particular every finite abelian group has zero rational scalar extension. -/
def FiniteVanishing : Prop :=
  ∀ (M : Type w) [AddCommGroup M] [Finite M], ∀ x : ℚ ⊗[ℤ] M, x = 0

/-- An explicit noninjective natural map, from a nonzero finite torsion group. -/
def NoninjectiveExample : Prop :=
  ¬ Function.Injective (fun m : ZMod 2 => (1 : ℚ) ⊗ₜ[ℤ] m)

/-- Arbitrary chosen bases extend, with their entire coordinate formula.
No finite-dimension hypothesis is imposed on this assertion. -/
def FieldBasis : Prop :=
  ∀ (F : Type u) [Field F] (L : Type v) [Field L] [Algebra F L]
    (M : Type w) [AddCommGroup M] [Module F M]
    (ι : Type t) (b : Module.Basis ι F M),
    ∃ c : Module.Basis ι L (L ⊗[F] M),
      (∀ i, c i = (1 : L) ⊗ₜ[F] b i) ∧
      (∀ s m i, c.repr (s ⊗ₜ[F] m) i = s * algebraMap F L (b.repr m i))

/-- The direct sum model has the stated coordinates and sends its unit
coordinate vectors back to the extended basis vectors. -/
def FieldCoordinates : Prop :=
  ∀ (F : Type u) [Field F] (L : Type v) [Field L] [Algebra F L]
    (M : Type w) [AddCommGroup M] [Module F M]
    (ι : Type t) (b : Module.Basis ι F M),
    ∃ e : (L ⊗[F] M) ≃ₗ[L] (ι →₀ L),
      (∀ m i, e ((1 : L) ⊗ₜ[F] m) i = algebraMap F L (b.repr m i)) ∧
      (∀ i, e.symm (Finsupp.single i 1) = (1 : L) ⊗ₜ[F] b i)

/-- The natural map is injective over every field extension. -/
def FieldInjectivity : Prop :=
  ∀ (F : Type u) [Field F] (L : Type v) [Field L] [Algebra F L]
    (M : Type w) [AddCommGroup M] [Module F M],
    Function.Injective (fun m : M => (1 : L) ⊗ₜ[F] m)

/-- Extending a finite-dimensional vector space preserves its finite dimension. -/
def FiniteDimension : Prop :=
  ∀ (F : Type u) [Field F] (L : Type v) [Field L] [Algebra F L]
    (M : Type w) [AddCommGroup M] [Module F M] [FiniteDimensional F M],
    FiniteDimensional L (L ⊗[F] M) ∧ Module.finrank L (L ⊗[F] M) = Module.finrank F M

end Specs.D07.Ch22.ScalarExtension
