import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplitMatrixColumns
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! Independent statements for the idempotent lifts and projective covers in MR09. -/

namespace RepTheorySurvey.Modular.MR09CoversSpec

universe uF uG uO uK uR

def principalLeftIdealType := {R : Type uR} → [Ring R] → R → Ideal R

/-- The left ideal of all left multiples of the indicated element. -/
def principalLeftIdealValue : principalLeftIdealType.{uR} :=
  fun e => Ideal.span {e}

def principalLeftIdealProjective : Prop :=
  ∀ {R : Type uR} [Ring R] {e : R}, IsIdempotentElem e →
    Module.Projective R (principalLeftIdealValue e)

def modularIdempotentLift : Prop :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] [Finite G]
    (E : MR01Spec.radicalQuotientValue F G), IsIdempotentElem E →
    ∃ e : MonoidAlgebra F G, IsIdempotentElem e ∧ MR01Spec.radicalQuotientMapValue F G e = E

def integralIdempotentLift : Prop :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData G p O K →
    ∀ e : MonoidAlgebra (IsLocalRing.ResidueField O) G, IsIdempotentElem e →
      ∃ lift : MonoidAlgebra O G, IsIdempotentElem lift ∧ MR01Spec.reductionValue O G lift = e

open Classical in
def modularRankOneIdempotentLift : Prop :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] [Finite G]
    {r : ℕ} {d : Fin r → ℕ}
    (split : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F))
    (i : Fin r) (E : Matrix (Fin (d i)) (Fin (d i)) F),
    IsIdempotentElem E → E.rank = 1 →
    ∃ e : MonoidAlgebra F G, IsIdempotentElem e ∧
      SplitMatrixColumnsSpec.modularColumnMap split e = Pi.single i E

def modularProjectiveCover : Prop :=
  ∀ {F : Type uF} [Field F] {G : Type uG} [Group G] [Finite G]
    {r : ℕ} {d : Fin r → ℕ}
    (split : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F)),
    (∀ j, 0 < d j) → ∀ (i : Fin r) (e : MonoidAlgebra F G), IsIdempotentElem e →
    let q := SplitMatrixColumnsSpec.modularColumnMap split
    (q e i).rank = 1 → (∀ j, j ≠ i → q e j = 0) →
    let A := MonoidAlgebra F G
    let P := principalLeftIdealValue e
    let J := Ring.jacobson A
    let JP := J • (⊤ : Submodule A P)
    Module.Projective A P ∧
      ∃ top : (P ⧸ JP) ≃ₗ[A] SplitMatrixColumnsSpec.columnModule q i,
        Function.Surjective (top.toLinearMap.comp JP.mkQ) ∧
          ∀ U : Submodule A P, U.map (top.toLinearMap.comp JP.mkQ) = ⊤ → U = ⊤

end RepTheorySurvey.Modular.MR09CoversSpec
