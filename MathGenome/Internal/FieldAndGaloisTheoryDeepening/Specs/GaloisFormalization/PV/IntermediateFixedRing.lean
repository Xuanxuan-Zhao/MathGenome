import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RelativePicardVessiotTensor

namespace GaloisFormalization.PV.Specs

open scoped Matrix MatrixGroupCoordinates.Specs
open MatrixGroupCoordinates.Specs (IsAlgebraicSubgroup)

noncomputable section

/-- The elements of the total extension fixed by every member of a set of
the concrete matrix Galois group. -/
def matrixFixedSubalgebra.{u, v} {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (E : operator kind R) (Y : GL (Fin n) R) :
    let Q := totalQuotientRing R
    Set (matrixGaloisGroup δ E Y) → Subalgebra K Q := by
  intro Q S
  let act := matrixFractionAutomorphism δ E Y
  refine
    { carrier := {q | ∀ g ∈ S, act g q = q}
      zero_mem' := fun g _ => map_zero (act g)
      one_mem' := fun g _ => map_one (act g)
      add_mem' := fun hx hy g hg =>
        (map_add (act g) _ _).trans (congrArg₂ (· + ·) (hx g hg) (hy g hg))
      mul_mem' := fun hx hy g hg =>
        (map_mul (act g) _ _).trans (congrArg₂ (· * ·) (hx g hg) (hy g hg))
      algebraMap_mem' := ?_ }
  intro k g _
  let τ := (matrixAutomorphism δ E Y g).val
  change IsFractionRing.ringEquivOfRingEquiv τ.toRingEquiv
    (algebraMap R Q (algebraMap K R k)) = algebraMap R Q (algebraMap K R k)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact congrArg (algebraMap R Q) (τ.commutes k)

/-- The pointwise stabilizer of an intermediate total ring is an algebraic
subgroup of the original matrix group and has that intermediate ring as its
fixed subalgebra. -/
def intermediateFixedRing.{u, v} : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    ∀ (F : Subalgebra K Q), isIntermediateTotalRing T F →
      let S := relativeStabilizer δ E Y F
      (∃ H : Subgroup (GL (Fin n) (constantSubfield δ)),
        (H : Set (GL (Fin n) (constantSubfield δ))) = Subtype.val '' S ∧
        IsAlgebraicSubgroup H) ∧
      matrixFixedSubalgebra δ E Y S = F

end

end GaloisFormalization.PV.Specs
