import MathGenome.Internal.Specs.D07.Ch12.MinpolyDivisibility
import MathGenome.Internal.Specs.D07.Ch12.SimpleClassification

/-!
Independent specification for K07.12.simple_embeddings, paper.tex:3679–3686.

All extensions have their specified `Algebra` structure. The simple fields and
their generators are the canonical upstream `IntermediateField.adjoin` objects.
Roots are elements satisfying polynomial evaluation equal to zero, without any
separability or algebraic-closedness hypothesis or restriction on multiplicity.
Only the chosen element is assumed algebraic; its ambient extension is arbitrary.

For a change of base field, an ordinary ring equivalence together with the
displayed scalar compatibility expresses an isomorphism extending precisely σ.
The four field types can inhabit independent universes.
-/

universe u v w z

namespace Specs.D07.Ch12.SimpleEmbeddings

/-- The bijection is specifically evaluation at the chosen generator. -/
def EmbeddingsRoots : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] (α : L),
    IsAlgebraic K α →
      ∃ e : (IntermediateField.adjoin K {α} →ₐ[K] Ω) ≃
          {β : Ω // Polynomial.aeval β (minpoly K α) = 0},
        ∀ f, (e f).val = f (IntermediateField.AdjoinSimple.gen K α)

/-- Each root of the coefficient-transported minimal polynomial determines
exactly one isomorphism of the generated fields extending the base isomorphism. -/
def BaseIsomorphismExtension : Prop :=
  ∀ (K : Type u) (K' : Type v) (L : Type w) (L' : Type z)
    [Field K] [Field K'] [Field L] [Field L'] [Algebra K L] [Algebra K' L']
    (σ : K ≃+* K') (α : L), IsAlgebraic K α → ∀ β : L',
    Polynomial.aeval β ((minpoly K α).map σ.toRingHom) = 0 →
      ∃! e : IntermediateField.adjoin K {α} ≃+* IntermediateField.adjoin K' {β},
        e (IntermediateField.AdjoinSimple.gen K α) =
          IntermediateField.AdjoinSimple.gen K' β ∧
        ∀ a : K, e (algebraMap K (IntermediateField.adjoin K {α}) a) =
          algebraMap K' (IntermediateField.adjoin K' {β}) (σ a)

/-- The source's boundary observation: an embedding preserves transcendence,
although the totalized minimal polynomial is zero and vanishes everywhere. -/
def TranscendentalBoundary : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] (α : L),
    Transcendental K α →
      (∀ f : IntermediateField.adjoin K {α} →ₐ[K] Ω,
        Transcendental K (f (IntermediateField.AdjoinSimple.gen K α))) ∧
      minpoly K α = 0 ∧
      ∀ β : Ω, Polynomial.aeval β (minpoly K α) = 0

end Specs.D07.Ch12.SimpleEmbeddings
