import MathGenome.Internal.Specs.D07.Ch17.Definition
import MathGenome.Internal.Specs.D07.Ch05.ActionDefinition
import MathGenome.Internal.Specs.D07.Ch02.TranspositionsParity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.CharP.Two

/-!
Independent specifications for K07.17.examples, paper.tex:4621–4645.
`MonoidAlgebra K X` is a wrapper around `X →₀ K`, even when X has no
multiplication. Only its vector space is used here. Thus infinite G-sets
are allowed and the permutation space is a direct sum, not a product.
The canonical basis consists of `MonoidAlgebra.single x 1`.
-/
namespace Specs.D07.Ch17.Examples

universe u v w

def TrivialType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V], Representation K G V

abbrev trivialValue : TrivialType.{u, v, w} :=
  fun K G V _ _ _ _ => Representation.trivial K G V

def PermutationType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X], Representation K G (MonoidAlgebra K X)

noncomputable abbrev permutationValue : PermutationType.{u, v, w} :=
  fun K G X _ _ _ => Representation.ofMulAction K G X

def RegularType : Type (max u v + 1) :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G],
    Representation K G (MonoidAlgebra K G)

noncomputable abbrev regularValue : RegularType.{u, v} :=
  fun K G _ _ => Representation.leftRegular K G

def SignType : Type (max u v + 1) :=
  ∀ (K : Type u) (X : Type v) [Field K] [Fintype X],
    Representation K (Equiv.Perm X) K

/-- Cast the integer-valued sign to K, then act by multiplication on K. -/
noncomputable abbrev signValue : SignType.{u, v} :=
  fun K X _ _ =>
    (algebraMap K (Module.End K K)).toMonoidHom.comp
      (((Int.castRingHom K).toMonoidHom.comp (Units.coeHom ℤ)).comp
        (Specs.D07.Ch02.TranspositionsParity.signValue X))

def TrivialAction : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] (g : G),
    trivialValue K G V g = LinearMap.id

/-- Explicitly identify the finite-support model with its coefficient space. -/
def FormalSumsModel : Prop :=
  ∀ (K : Type u) (X : Type w) [Field K],
    ∃ e : MonoidAlgebra K X ≃ₗ[K] (X →₀ K),
      (∀ f, e f = f.coeff) ∧
      (∀ x, e (MonoidAlgebra.single x 1) = Finsupp.single x 1)

def PermutationBasis : Prop :=
  ∀ (K : Type u) (X : Type w) [Field K],
    ∃ b : Module.Basis X K (MonoidAlgebra K X),
      ∀ x, b x = MonoidAlgebra.single x 1

def PermutationOnBasis : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] (g : G) (x : X) (a : K),
    permutationValue K G X g (MonoidAlgebra.single x a) =
      MonoidAlgebra.single (g • x) a

/-- Extension from the prescribed basis action is unique among linear maps. -/
def PermutationUniqueExtension : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X]
    (r : G → Module.End K (MonoidAlgebra K X)),
    (∀ g x, r g (MonoidAlgebra.single x 1) = MonoidAlgebra.single (g • x) 1) →
    r = (permutationValue K G X : G → Module.End K (MonoidAlgebra K X))

def PermutationLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X],
    permutationValue K G X 1 = LinearMap.id ∧
      ∀ g h, permutationValue K G X (g * h) =
        (permutationValue K G X g).comp (permutationValue K G X h)

/-- Coefficients transform by inverse pullback for a left action. -/
def PermutationCoefficients : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] (g : G) (f : MonoidAlgebra K X) (x : X),
    (permutationValue K G X g f).coeff x = f.coeff (g⁻¹ • x)

/-- The support of the image is exactly the image of the original finite support. -/
def PermutationSupport : Prop := by
  classical
  exact ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] (g : G) (f : MonoidAlgebra K X),
    (permutationValue K G X g f).coeff.support = f.coeff.support.image (g • ·)

def PermutationFiniteDimension : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] [Finite X],
    FiniteDimensional K (MonoidAlgebra K X) ∧
      Module.finrank K (MonoidAlgebra K X) = Nat.card X

def PermutationFixesBasisIff : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] (g : G),
    (∀ x, permutationValue K G X g (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single x 1) ↔ ∀ x : X, g • x = x

/-- This identifies the representation kernel with the action kernel, including X empty. -/
def PermutationKernel : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] (g : G),
    g ∈ (permutationValue K G X).ker ↔ ∀ x : X, g • x = x

def PermutationFaithfulIff : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X],
    Function.Injective (permutationValue K G X) ↔
      Specs.D07.Ch05.ActionDefinition.faithfulValue G X

def RegularOnBasis : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G] (g h : G) (a : K),
    regularValue K G g (MonoidAlgebra.single h a) = MonoidAlgebra.single (g * h) a

def RegularFaithful : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G],
    Function.Injective (regularValue K G)

def RegularKernel : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G],
    (regularValue K G).ker = ⊥

def RegularFiniteDimension : Prop :=
  ∀ (K : Type u) (G : Type v) [Field K] [Group G] [Finite G],
    FiniteDimensional K (MonoidAlgebra K G) ∧
      Module.finrank K (MonoidAlgebra K G) = Nat.card G

def SignAction : Prop :=
  ∀ (K : Type u) (X : Type v) [Field K] [Fintype X] (σ : Equiv.Perm X) (a : K),
    signValue K X σ a = (((Specs.D07.Ch02.TranspositionsParity.signValue X σ : ℤˣ) : ℤ) : K) * a

def SignLaws : Prop :=
  ∀ (K : Type u) (X : Type v) [Field K] [Fintype X],
    signValue K X 1 = LinearMap.id ∧
      ∀ σ τ, signValue K X (σ * τ) = (signValue K X σ).comp (signValue K X τ)

def SignDimension : Prop :=
  ∀ (K : Type u) (X : Type v) [Field K] [Fintype X],
    FiniteDimensional K K ∧ Module.finrank K K = 1

def SignCharacteristicTwo : Prop :=
  ∀ (K : Type u) (X : Type v) [Field K] [Fintype X] [CharP K 2],
    signValue K X = trivialValue K (Equiv.Perm X) K

/-- A permutation basis alone need not give an irreducible representation:
there can be a nonzero proper invariant subspace. No irreducibility API is
assumed from a later chapter entry. -/
def PermutationReducibleExample : Prop :=
  ∀ (K : Type u) [Field K],
    ∃ U : Submodule K (MonoidAlgebra K (Fin 2)),
      U ≠ ⊥ ∧ U ≠ ⊤ ∧
      ∀ (g : PUnit.{1}) (f : MonoidAlgebra K (Fin 2)), f ∈ U →
        permutationValue K PUnit.{1} (Fin 2) g f ∈ U

end Specs.D07.Ch17.Examples
