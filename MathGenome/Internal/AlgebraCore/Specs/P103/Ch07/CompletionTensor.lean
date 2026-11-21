import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Noetherian.Basic

/-! The tensor comparison in Theorem 7.4 (paper.tex:1209–1226).
The completion and its scalar actions are those of the common inverse-limit
interface. The comparison is specified by the balanced scalar pairing itself.
No separatedness, localness, or Jacobson-radical condition is imposed.
-/

universe u v w

namespace P103.Specs.Ch07.CompletionTensor

open P103.Adic TensorProduct

/-- The canonical map is linear over the completed ring, acting on the first
factor of the tensor product and coordinatewise on the target. -/
def comparisonType :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M],
    Completion I R ⊗[R] M →ₗ[Completion I R] Completion I M

noncomputable def comparisonValue (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Completion I R ⊗[R] M →ₗ[Completion I R] Completion I M :=
  AlgebraTensorModule.lift
    { toFun r := LinearMap.lsmul (Completion I R) (Completion I M) r ∘ₗ
        AdicCompletion.of I M
      map_add' x y := by
        apply LinearMap.ext
        simp
      map_smul' r x := by
        apply LinearMap.ext
        simp [mul_smul] }

def comparison_tmulType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (r : Completion I R) (m : M),
    comparisonValue R I M (r ⊗ₜ[R] m) = r • AdicCompletion.of I M m

/-- Bijectivity of the specified linear map, including zero rings and ideals. -/
def comparison_bijectiveType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    Function.Bijective (comparisonValue R I M)

/-- An isomorphism whose forward map is exactly the comparison. -/
def comparison_isomorphismType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ e : Completion I R ⊗[R] M ≃ₗ[Completion I R] Completion I M,
      e.toLinearMap = comparisonValue R I M

/-- Naturality holds even without finiteness. Thus it applies to every map
between the finite modules in the theorem. -/
def comparison_naturalType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
    (AdicCompletion.map I f).comp (comparisonValue R I M) =
      (comparisonValue R I N).comp (AlgebraTensorModule.map LinearMap.id f)

/-- Finite free completion, with the empty basis allowed. -/
def finiteFreeCompletionType :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ),
    Completion I (Fin n → R) ≃ₗ[Completion I R] (Fin n → Completion I R)

noncomputable def finiteFreeCompletionValue (R : Type u) [CommRing R]
    (I : Ideal R) (n : ℕ) :
    Completion I (Fin n → R) ≃ₗ[Completion I R] (Fin n → Completion I R) :=
  AdicCompletion.piEquivFin I n

/-- Each coordinate is the completion of the original coordinate projection. -/
def finiteFreeCompletion_coordinateType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)
    (x : Completion I (Fin n → R)) (j : Fin n),
    finiteFreeCompletionValue R I n x j =
      AdicCompletion.map I (LinearMap.proj j) x

/-- Under these coordinates, comparison on a finite free module is the usual
scalar-extension basis isomorphism. This also fixes its scalar action. -/
def finiteFreeComparisonType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ),
    (finiteFreeCompletionValue R I n).toLinearMap.comp
        (comparisonValue R I (Fin n → R)) =
      (TensorProduct.piScalarRight R (Completion I R) (Completion I R) (Fin n)).toLinearMap

end P103.Specs.Ch07.CompletionTensor
