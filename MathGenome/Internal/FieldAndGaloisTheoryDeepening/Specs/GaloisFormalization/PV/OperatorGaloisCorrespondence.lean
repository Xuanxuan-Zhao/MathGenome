import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateFixedRing

namespace GaloisFormalization.PV.Specs

open scoped Matrix MatrixGroupCoordinates.Specs

/-- The Galois correspondence for the total ring of a Picard–Vessiot extension,
with fixed subalgebras and pointwise stabilizers as the two inverse maps. -/
def operatorGaloisCorrespondence.{u, v} : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    let G := matrixGaloisGroup δ E Y
    let ClosedSubgroups := {H : Subgroup G // IsClosed (H : Set G)}
    let IntermediateTotalRings := {F : Subalgebra K Q // isIntermediateTotalRing T F}
    (∀ H : Subgroup G,
      isIntermediateTotalRing T (matrixFixedSubalgebra δ E Y (H : Set G))) ∧
    (∃ e : ClosedSubgroups ≃o IntermediateTotalRingsᵒᵈ,
      (∀ H : ClosedSubgroups,
        (OrderDual.ofDual (e H)).val = matrixFixedSubalgebra δ E Y (H.val : Set G)) ∧
      (∀ F : IntermediateTotalRings,
        ((e.symm (OrderDual.toDual F)).val : Set G) = relativeStabilizer δ E Y F.val)) ∧
    (kind = .differential →
      IsField Q ∧ ∀ F : Subalgebra K Q,
        isIntermediateTotalRing T F ↔ isStable T (F : Set Q) ∧ IsField F) ∧
    matrixFixedSubalgebra δ E Y (Set.univ : Set G) = ⊥

end GaloisFormalization.PV.Specs
