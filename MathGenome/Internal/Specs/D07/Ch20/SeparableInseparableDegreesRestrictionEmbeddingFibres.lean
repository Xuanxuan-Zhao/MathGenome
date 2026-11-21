import Mathlib.FieldTheory.SeparableDegree

/-!
Independent specifications for the restriction-fibre argument in
K07.20.separable_inseparable_degrees, paper.tex:5848–5866, and its use at
paper.tex:5931. All six algebra structures and all scalar towers below
are the specified compatible inclusions. Ω is algebraically closed and
algebraic over L; neither finite extension is assumed separable.

`Field.finSepDegree M L` is the number of M-embeddings into an algebraic
closure of L. Finiteness of the extension makes these natural cardinalities
actual finite counts. Fibres are those of the actual restriction map, not
of an unrelated bijection. The automorphism and equivalence assertions make
independence of the chosen embedding of M explicit.
-/

universe u v w z

namespace Specs.D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres

/-- Every specified base embedding extends to an automorphism of the closure. -/
def AutomorphismExtension : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w) (Ω : Type z)
    [Field K] [Field M] [Field L] [Field Ω]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra L Ω] [Algebra M Ω] [Algebra K Ω]
    [IsScalarTower K M L] [IsScalarTower M L Ω]
    [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [Algebra.IsAlgebraic L Ω] [IsAlgClosed Ω],
    ∀ τ : M →ₐ[K] Ω, ∃ e : Ω ≃ₐ[K] Ω,
      ∀ x : M, e (algebraMap M Ω x) = τ x

/-- Restriction onto embeddings of the middle field is surjective. -/
def RestrictionSurjective : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w) (Ω : Type z)
    [Field K] [Field M] [Field L] [Field Ω]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra L Ω] [Algebra M Ω] [Algebra K Ω]
    [IsScalarTower K M L] [IsScalarTower M L Ω]
    [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [Algebra.IsAlgebraic L Ω] [IsAlgClosed Ω],
    Function.Surjective (fun σ : L →ₐ[K] Ω => σ.domRestrict M)

/-- Each restriction fibre is equivalent to embeddings fixing the specified M. -/
def FibreEquivalence : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w) (Ω : Type z)
    [Field K] [Field M] [Field L] [Field Ω]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra L Ω] [Algebra M Ω] [Algebra K Ω]
    [IsScalarTower K M L] [IsScalarTower M L Ω]
    [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [Algebra.IsAlgebraic L Ω] [IsAlgClosed Ω],
    ∀ τ : M →ₐ[K] Ω,
      Nonempty ({σ : L →ₐ[K] Ω // σ.domRestrict M = τ} ≃ (L →ₐ[M] Ω))

/-- Every fibre has exactly s(L/M) elements, independently of τ. -/
def FibreCard : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w) (Ω : Type z)
    [Field K] [Field M] [Field L] [Field Ω]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra L Ω] [Algebra M Ω] [Algebra K Ω]
    [IsScalarTower K M L] [IsScalarTower M L Ω]
    [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [Algebra.IsAlgebraic L Ω] [IsAlgClosed Ω],
    ∀ τ : M →ₐ[K] Ω,
      Nat.card {σ : L →ₐ[K] Ω // σ.domRestrict M = τ} = Field.finSepDegree M L

/-- Counting the actual fibres in the common closure. -/
def EmbeddingCountProduct : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w) (Ω : Type z)
    [Field K] [Field M] [Field L] [Field Ω]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [Algebra L Ω] [Algebra M Ω] [Algebra K Ω]
    [IsScalarTower K M L] [IsScalarTower M L Ω]
    [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [Algebra.IsAlgebraic L Ω] [IsAlgClosed Ω],
    Nat.card (L →ₐ[K] Ω) = Field.finSepDegree M L * Nat.card (M →ₐ[K] Ω)

/-- Multiplicativity of the finite separable degrees in any finite tower. -/
def FinSepDegreeTower : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L],
      Field.finSepDegree K L = Field.finSepDegree M L * Field.finSepDegree K M

end Specs.D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres
