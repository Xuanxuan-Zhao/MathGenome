import Mathlib.FieldTheory.Galois.Basic
import MathGenome.Internal.Specs.D07.Ch13.Existence
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Independent statements for K07.20.normal_basis, paper.tex:5969–5998.
The algebra structure specifies the base embedding. Finite degree and the
Galois condition are separate hypotheses. The basis index is the entire
relative automorphism group, with each vector the indicated conjugate.
The finite-field conclusion uses the cardinality of K (not its
characteristic), and applies to every finite-degree extension of K.
There is no assumption on the characteristic relative to the degree.
The final two statements retain the source remark that normality and
multiplicative primitivity do not imply each other.
-/

universe u v

namespace Specs.D07.Ch20.NormalBasis

/-- The normal basis theorem for arbitrary finite Galois extensions. -/
def NormalBasisExists : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    ∃ a : L, ∃ B : Module.Basis (L ≃ₐ[K] L) K L, ∀ σ, B σ = σ a

/-- The ordered Frobenius basis for every finite-degree extension of a
finite field. Neither normality nor separability is an extra hypothesis. -/
def FiniteFieldNormalBasis : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L] (q n : ℕ),
    Nat.card K = q → Module.finrank K L = n →
    ∃ a : L, ∃ B : Module.Basis (Fin n) K L,
      ∀ j : Fin n, B j = a ^ (q ^ (j : ℕ))

/-- In particular, the statement holds in the specified embedded field
F_(q^n) inside any fixed algebraic closure of K, using its inherited algebra
structure rather than identifying an unrelated field copy with it. -/
def EmbeddedNormalBasis : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n : ℕ), Nat.card K = q → 1 ≤ n →
    let E := Specs.D07.Ch13.Existence.rootFieldValue K Ω q n
    ∃ a : E, ∃ B : Module.Basis (Fin n) K E,
      ∀ j : Fin n, B j = a ^ (q ^ (j : ℕ))

/-- A concrete normal element which is not a multiplicative generator.
The unit order is compared with the size of the entire unit group. -/
def NormalNotPrimitive : Prop :=
  ∃ a : (ZMod 3)ˣ,
    (∃ B : Module.Basis (ZMod 3 ≃ₐ[ZMod 3] ZMod 3) (ZMod 3) (ZMod 3),
      ∀ σ, B σ = σ (a : ZMod 3)) ∧
    orderOf a ≠ Nat.card (ZMod 3)ˣ

/-- In F_8 over F_2 there is a multiplicative generator whose conjugates
are not a basis. This is the opposite nonimplication in the source remark. -/
def PrimitiveNotNormal : Prop :=
  ∃ a : (GaloisField 2 3)ˣ,
    orderOf a = Nat.card (GaloisField 2 3)ˣ ∧
    ¬ ∃ B : Module.Basis (GaloisField 2 3 ≃ₐ[ZMod 2] GaloisField 2 3)
      (ZMod 2) (GaloisField 2 3), ∀ σ, B σ = σ (a : GaloisField 2 3)

end Specs.D07.Ch20.NormalBasis
