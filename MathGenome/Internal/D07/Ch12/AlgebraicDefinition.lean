import MathGenome.Internal.Specs.D07.Ch12.AlgebraicDefinition

/-!
# Algebraic and transcendental elements

K07.12.algebraic_definition, paper.tex:3570–3574.
The first three results check the canonical predicates against the source's
full definitions. The rational-function example retains its coefficient
field: t has no nonzero annihilator over K, whereas X-C(t) annihilates it
over K(t). All fields and structure maps are arbitrary as in the source.
-/

universe u v

namespace D07.Ch12.AlgebraicDefinition

open Specs.D07.Ch12.AlgebraicDefinition

/-- The paper's algebraic-element predicate, using the canonical definition. -/
abbrev algebraicElement : ElementPredicateType.{u, v} :=
  fun K _ _ _ _ α => IsAlgebraic K α

/-- The paper's transcendental-element predicate, with its base explicit. -/
abbrev transcendentalElement : ElementPredicateType.{u, v} :=
  fun K _ _ _ _ α => Transcendental K α

/-- The paper's algebraic-extension predicate, using the canonical class. -/
abbrev algebraicExtension : ExtensionPredicateType.{u, v} :=
  fun K L _ _ _ => Algebra.IsAlgebraic K L

theorem algebraicElementCharacterization : AlgebraicElementCharacterization.{u, v} := by
  intro K L _ _ _ α
  rfl

theorem transcendentalElementCharacterization :
    TranscendentalElementCharacterization.{u, v} := by
  intro K L _ _ _ α
  rfl

theorem algebraicExtensionCharacterization :
    AlgebraicExtensionCharacterization.{u, v} := by
  intro K L _ _ _
  exact Algebra.isAlgebraic_def

theorem indeterminateTranscendentalOverBase : IndeterminateTranscendentalOverBase.{u} := by
  intro K _
  exact RatFunc.transcendental_X

theorem indeterminateAlgebraicOverRationalFunctions :
    IndeterminateAlgebraicOverRationalFunctions.{u} := by
  intro K _
  refine ⟨Polynomial.X - Polynomial.C (RatFunc.X : RatFunc K),
    Polynomial.X_sub_C_ne_zero _, ?_⟩
  simp

end D07.Ch12.AlgebraicDefinition
