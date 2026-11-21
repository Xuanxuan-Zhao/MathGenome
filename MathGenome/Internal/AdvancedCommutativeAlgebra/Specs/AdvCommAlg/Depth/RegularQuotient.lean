import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Independent specifications for DP-05, paper.tex:2777–2789 and 2798–2804.
`I.map (Ideal.Quotient.mk A)` denotes the image ideal `(I + A)/A`.
The module structures below are the actual Mathlib quotient actions.
The scalar-change assertion holds without Noetherianity or finite generation,
and hence in particular for all finite modules in the source.
The type/socle assertion is allocated separately to DP-05-type. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth

/-- The local structure on a quotient by a list in the maximal ideal.
Properness is proved here, rather than imposed as another hypothesis. -/
@[instance_reducible] def regularQuotientLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    (xs : List R) (hmem : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.ofList xs) := by
  have hle : Ideal.ofList xs ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr hmem
  letI : Nontrivial (R ⧸ Ideal.ofList xs) :=
    (Ideal.Quotient.nontrivial_iff).mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

namespace Specs

def grade_quotient_scalarsType : Prop :=
  ∀ {R : Type u} [CommRing R] (A I : Ideal R)
    (U : Type v) [AddCommGroup U] [Module R U]
    (hA : Module.IsTorsionBySet R U A),
    letI := hA.module
    gradeValue (I.map (Ideal.Quotient.mk A)) U = gradeValue I U

def grade_quotient_regularType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R), I • (⊤ : Submodule R M) ≠ ⊤ → ∀ xs : List R,
    RingTheory.Sequence.IsRegular M xs → (∀ x ∈ xs, x ∈ I) →
    gradeValue I (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) =
      gradeValue I M - xs.length

def grade_regular_quotientType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R), I • (⊤ : Submodule R M) ≠ ⊤ → ∀ xs : List R,
    RingTheory.Sequence.IsRegular M xs → (∀ x ∈ xs, x ∈ I) →
    gradeValue (I.map (Ideal.Quotient.mk (Ideal.ofList xs)))
        (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) =
      gradeValue I (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) ∧
    gradeValue I (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) =
      gradeValue I M - xs.length

def depth_regular_quotientType : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    [IsLocalRing R]
    (xs : List R), RingTheory.Sequence.IsRegular M xs →
    ∀ hmem : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R,
    letI := regularQuotientLocalRing xs hmem
    depthValue (R ⧸ Ideal.ofList xs)
      (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) = depthValue R M - xs.length

end Specs
end AdvCommAlg.Depth
