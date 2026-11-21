import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
Independent specification for K07.14.automorphism_bound (paper.tex:4138–4145).

`Algebra K L` retains the chosen field embedding. Finite degree is explicitly
`FiniteDimensional K L`, not finiteness of the underlying field. Automorphisms
are the upstream canonical `L ≃ₐ[K] L`, with left function composition.

`IsGalois K L` is defined as `Algebra.IsSeparable K L` and `Normal K L`;
both predicates imply algebraicity. Thus this uses the source's normal and
separable definition, rather than assuming an automorphism-count criterion.
The bottom intermediate field is the image of the specified embedding of K.
The top subgroup consists of every K-automorphism, so its canonical fixed
field is exactly the source's full fixed field. No separability, normality,
characteristic, or nontrivial-degree hypothesis is added.
-/

universe u v

namespace Specs.D07.Ch14.AutomorphismBound

/-- The automorphism count is a finite cardinality under the degree hypothesis. -/
def FiniteAutomorphisms : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], Finite (L ≃ₐ[K] L)

/-- Every finite extension has at most its degree many base automorphisms. -/
def OrderBound : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Nat.card (L ≃ₐ[K] L) ≤ Module.finrank K L

/-- Equality holds exactly for normal, separable algebraic extensions. -/
def EqualityIffGalois : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Nat.card (L ≃ₐ[K] L) = Module.finrank K L ↔ IsGalois K L

/-- Equality holds exactly when the full fixed field is the embedded base. -/
def EqualityIffFixedField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    Nat.card (L ≃ₐ[K] L) = Module.finrank K L ↔
      FixedField.fixedFieldValue K L (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥

end Specs.D07.Ch14.AutomorphismBound
