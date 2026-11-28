import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.IntegralMultiplicity
import Mathlib.Data.Matrix.Mul

/-! Independent specification for Brauer reciprocity and the Cartan matrix (MR09). -/

namespace RepTheorySurvey.Modular.MR09Spec

universe uG uO uK uI uV

open IsLocalRing (ResidueField)

/-- For every choice of successive idempotent lifts, the modular left ideals are
projective covers, the ordinary left ideals have multiplicities given by the
columns of the decomposition matrix, and the Cartan matrix is its Gram matrix. -/
def cartanMatrixFormula : Prop :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (system : MR01Spec.SplittingSystemData G p O K)
    {r : ℕ} {d : Fin r → ℕ}
    (split : MR01Spec.radicalQuotientValue (ResidueField O) G ≃ₐ[ResidueField O]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) (ResidueField O))),
    (∀ i, 0 < d i) →
    ∀ {ι : Type uI} [Fintype ι]
      (V : ι → ModuleCat.{max uO uK uG uV} (MonoidAlgebra K G)),
    MR01Spec.SimpleRepresentativeFamily V →
    ∀ (eBar : Fin r → MonoidAlgebra (ResidueField O) G) (e : Fin r → MonoidAlgebra O G),
    (∀ i, IsIdempotentElem (eBar i)) →
    (∀ i, IsIdempotentElem (e i)) →
    (∀ i, MR01Spec.reductionValue O G (e i) = eBar i) →
    let q := SplitMatrixColumnsSpec.modularColumnMap split
    (∀ i, (q (eBar i) i).rank = 1) →
    (∀ i j, j ≠ i → q (eBar i) j = 0) →
    let A := MonoidAlgebra (ResidueField O) G
    let S := SplitMatrixColumnsSpec.columnModule q
    let P := fun i => MR09CoversSpec.principalLeftIdealValue (eBar i)
    let PK := fun i => MR09CoversSpec.principalLeftIdealValue (MR01Spec.fractionMapValue O K G (e i))
    let D := MR06Spec.decompositionMatrixValue system V S
    let C : Matrix (Fin r) (Fin r) ℕ :=
      fun i j => CompositionMultiplicity.Spec.multiplicity (ResidueField O) G (P j) (S i)
    (∀ i,
      let JP := Ring.jacobson A • (⊤ : Submodule A (P i))
      Module.Projective A (P i) ∧
        ∃ top : (P i ⧸ JP) ≃ₗ[A] S i,
          Function.Surjective (top.toLinearMap.comp JP.mkQ) ∧
            ∀ U : Submodule A (P i), U.map (top.toLinearMap.comp JP.mkQ) = ⊤ → U = ⊤) ∧
    (∀ χ i, CompositionMultiplicity.Spec.multiplicity K G (PK i) (V χ) = D χ i) ∧
    C = D.transpose * D

end RepTheorySurvey.Modular.MR09Spec
