import MathGenome.Internal.Specs.D07.Ch14.AutomorphismBound

/-!
Independent specification for K07.14.galois_definition, paper.tex:4146–4157.

The canonical `IsGalois` predicate is normality and separability, both of
which include algebraicity. Its full agreement with the source's definition
is stated below with algebraicity explicit. No finite-degree hypothesis is
imposed on that definition. `Gal` is the existing base-fixing automorphism
type, with its existing composition group structure. Only the final
automorphism-count criterion assumes finite degree.
-/

universe u v

namespace Specs.D07.Ch14.GaloisDefinition

def ExtensionPredicateType :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Prop

def galoisExtensionValue : ExtensionPredicateType.{u, v} :=
  fun K L _ _ _ => IsGalois K L

def GaloisGroupType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Type v

/-- The same field automorphisms, with the same specified base embedding. -/
def galoisGroupValue : GaloisGroupType.{u, v} :=
  AutomorphismGroup.autValue

/-- The definition applies to algebraic extensions of arbitrary degree. -/
def GaloisCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    galoisExtensionValue K L ↔
      Algebra.IsAlgebraic K L ∧ Normal K L ∧ Algebra.IsSeparable K L

/-- The Galois group uses left function composition and the inherited inverse. -/
def GaloisGroupOperations : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (∀ (σ τ : L ≃ₐ[K] L) (x : L), (σ * τ) x = σ (τ x)) ∧
      (1 : L ≃ₐ[K] L) = AlgEquiv.refl ∧
      (∀ σ : L ≃ₐ[K] L, σ⁻¹ = σ.symm)

/-- The finite convention is equivalent to the general definition, with
finite vector-space degree explicitly required. -/
def FiniteIffAutomorphismCount : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    galoisExtensionValue K L ↔
      Nat.card (galoisGroupValue K L) = Module.finrank K L

end Specs.D07.Ch14.GaloisDefinition
