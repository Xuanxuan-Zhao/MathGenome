import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Localization

/-! The second paragraph of Theorem 4.2 (paper.tex 851–856, 873).
R and B are arbitrary commutative unital rings, including the zero ring.
Only M is finitely presented; N is arbitrary. A linear map is an isomorphism
precisely when its underlying function is bijective. Naturality is stated
without finiteness or flatness hypotheses, so in particular applies whenever
the comparison maps are isomorphisms. -/

universe u v w x y
namespace P103.Specs.Ch04.HomFlatBaseChange
open TensorProduct

/-- The canonical B-linear comparison map. -/
def canonicalType :=
  ∀ (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type x) [AddCommGroup N] [Module R N],
    (B ⊗[R] (M →ₗ[R] N)) →ₗ[B] ((B ⊗[R] M) →ₗ[B] (B ⊗[R] N))

def canonicalValue : canonicalType.{u,v,w,x} :=
  fun R _ B _ _ M _ _ N _ _ => LinearMap.tensorProduct R B M N

def formulaType : Prop :=
  ∀ (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type x) [AddCommGroup N] [Module R N]
    (b b' : B) (f : M →ₗ[R] N) (m : M),
    canonicalValue R B M N (b ⊗ₜ[R] f) (b' ⊗ₜ[R] m) = (b * b') ⊗ₜ[R] f m

/-- Bijectivity of this specified linear map asserts the required isomorphism. -/
def bijectiveType : Prop :=
  ∀ (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type x) [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.Flat R B],
    Function.Bijective (canonicalValue R B M N)

/-- Contravariance in the source module, on all tensors and all arguments. -/
def naturalitySourceType : Prop :=
  ∀ (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    (M : Type w) (M' : Type x) (N : Type y)
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] (h : M' →ₗ[R] M)
    (z : B ⊗[R] (M →ₗ[R] N)) (t : B ⊗[R] M'),
    canonicalValue R B M' N ((h.lcomp R N).baseChange B z) t =
      canonicalValue R B M N z (h.baseChange B t)

/-- Covariance in the target module, on all tensors and all arguments. -/
def naturalityTargetType : Prop :=
  ∀ (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
    (M : Type w) (N : Type x) (N' : Type y)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N')
    (z : B ⊗[R] (M →ₗ[R] N)) (t : B ⊗[R] M),
    canonicalValue R B M N' ((LinearMap.compRight R g).baseChange B z) t =
      g.baseChange B (canonicalValue R B M N z t)

/-- Includes every multiplicative subset, even those containing zero. -/
def localizationType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type x) [AddCommGroup N] [Module R N] [Module.FinitePresentation R M],
    Function.Bijective (canonicalValue R (Localization S) M N)

end P103.Specs.Ch04.HomFlatBaseChange
