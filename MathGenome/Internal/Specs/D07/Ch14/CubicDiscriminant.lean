import MathGenome.Internal.Specs.D07.Ch14.Discriminant
import Mathlib.Data.ZMod.Basic

/-!
K07.14.cubic_discriminant, paper.tex:4291–4299.
The Galois group is the group of base-fixing automorphisms of any realization
of the splitting field. Its image is compared with A₃ and S₃ using the actual
numbered root action, not merely an abstract group of the right order.
The source's discriminant is D²; the usual leading-coefficient normalization
is included through its equivalent square test. No monicity or characteristic
zero assumption is imposed.
-/

universe u v

namespace Specs.D07.Ch14.CubicDiscriminant

open Polynomial Discriminant

/-- Classification with a chosen numbering and the base discriminant D².
C₃ is represented as the multiplicative form of the additive group Z/3Z. -/
def ClassificationAt {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (b : Fin 3 ≃ f.rootSet L) (Δ : K) : Prop :=
  ((numberedAction b).range = alternatingGroup (Fin 3) ↔ IsSquare Δ) ∧
  ((numberedAction b).range = ⊤ ↔ ¬ IsSquare Δ) ∧
  (IsSquare Δ →
    Nonempty ((L ≃ₐ[K] L) ≃* alternatingGroup (Fin 3)) ∧
    Nonempty ((L ≃ₐ[K] L) ≃* Multiplicative (ZMod 3))) ∧
  (¬ IsSquare Δ → Nonempty ((L ≃ₐ[K] L) ≃* Equiv.Perm (Fin 3)))

/-- Every numbering and every base element equal to D² give this classification. -/
def NumberedCriterion : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : K[X]), (2 : K) ≠ 0 → Irreducible f → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = 3 →
    ∀ (b : Fin 3 ≃ f.rootSet L) (Δ : K),
      algebraMap K L Δ = differenceProduct (fun i => (b i).val) ^ 2 →
      ClassificationAt b Δ

/-- Complete cubic criterion: neither a numbering nor a discriminant in the
base field is an extra premise. It applies to every splitting-field realization. -/
def CubicCriterion : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : K[X]), (2 : K) ≠ 0 → Irreducible f → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = 3 →
    ∃ (b : Fin 3 ≃ f.rootSet L) (Δ : K),
      Δ ≠ 0 ∧ algebraMap K L Δ = differenceProduct (fun i => (b i).val) ^ 2 ∧
      ClassificationAt b Δ ∧
      (IsSquare (f.leadingCoeff ^ (2 * (f.natDegree - 1)) * Δ) ↔ IsSquare Δ)

end Specs.D07.Ch14.CubicDiscriminant
