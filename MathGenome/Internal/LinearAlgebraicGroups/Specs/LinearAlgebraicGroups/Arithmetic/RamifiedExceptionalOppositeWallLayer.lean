import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

/-! The opposite layer of a marked simple affine wall in the ramified outer E₆ group. -/

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalOppositeWallLayer

open CategoryTheory ValuativeRel WithZero
open scoped CategoryTheory.MonObj Classical WithZero
open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat (DiagramCompositum ExceptionalNumbering FieldPoints FoldedApartment
  FoldedLevel IsUnramifiedLocalExtension RamifiedReference)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalIwahoriCongruence (cellValue integralRing)
open ExceptionalLocalRootCoordinates (ramificationIndex)
open ExceptionalMarkedRootDescent (markedWeylWord wallMatrix)
open IntegralRootRelations (lower upper)
open IntegralSemisimpleModel (Integers Model integerAlgebra)
open Pinning (BasedRootDatum)

universe u

attribute [local instance] integerAlgebra ExceptionalLocalRootCoordinates.canonicalExtension

/-- The lower subgroup of each rank-one witness from `LocalComparison.RankOneLifts`
has only the opposite relative parameter in the original ordered marked chart.
Its parameter change is a bijection preserving depth in parameter-field
uniformizer steps. -/
def OppositeWallLayer : Prop :=
  ∀ {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeExtension F k]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F k]
    (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 →
    1 < ramificationIndex F L → IsUnramifiedLocalExtension F k →
    ∀ {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
      (numbering : Fin 6 ≃ D.base.support),
    ExceptionalNumbering D 6 numbering →
    D.datum.rootSpan ℤ = ⊤ →
    (∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i)) →
    ∀ (A : FoldedApartment (R.diagram σ)) (T : DiagramCompositum F L k σ)
      (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
      (a : A.roots.SimpleWall A.basepoint),
    let C := X.comparison.chart
    let P := C.parameter a.val.1
    let S := CommAlgCat.of Integers.{u} T.field
    let opposite := A.roots.opposite a.val
    let labels := fun (word : List D.I) (orbit : List (D.base.support × (P →+* T.field))) =>
      orbit.map fun b =>
        ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv b.1.val
    ∀ (word : List D.I) (orbit : List (D.base.support × (P →+* T.field)))
      (r : Matrix.SpecialLinearGroup (Fin 2) P →*
        GroupPoints R.descent.group.val (CommAlgCat.of F k))
      (t c : Pˣ) (u₀ : C.chart.torus),
    (∀ i ∈ word, i ∈ D.base.support) →
    orbit.length = (if (∃ i b : D.I, i ≠ b ∧
      C.direction i = a.val.1 ∧ C.direction b = a.val.1) then 2 else 1) →
    (labels word orbit).Nodup →
    (∀ i, C.direction i = a.val.1 ↔ i ∈ labels word orbit) →
    (∀ U, X.points (r U) =
      let m := markedWeylWord M.toIntegralMarking S word
      m * (orbit.map (fun b => (show FieldPoints M T.field from
        (M.rankOne b.1).app S (Matrix.SpecialLinearGroup.map b.2 U)))).prod * m⁻¹) →
    u₀.val = 1 →
    C.value a.val.1 (c : P) = 1 →
    (∀ z : P, X.points (r (upper z)) =
      cellValue M.toIntegralMarking (integralRing T.field) C.negative C.positive
        (C.chart.coordinates u₀ (@Function.update _ C.parameter
          (fun i j => Classical.propDecidable (i = j)) (fun _ => 0) a.val.1 ((c : P) * z)))) →
    C.value a.val.1 (t : P) = exp (-a.val.2) →
    (X.comparison.lift (X.comparison.coxeter.coxeter.simple a) :
      GroupPoints R.descent.group.val (CommAlgCat.of F k)) = r (wallMatrix t) →
    (∃ e : P ≃ C.parameter opposite.1, ∀ z : P,
      C.value opposite.1 (e z) = C.value a.val.1 z ∧
      X.points (r (lower z)) =
        cellValue M.toIntegralMarking (integralRing T.field) C.negative C.positive
          (C.chart.coordinates u₀ (Function.update (fun _ => 0) opposite.1 (e z)))) ∧
    (fun z : P => r (lower z)) '' {z | C.value a.val.1 z ≤ exp a.val.2} =
      {g | ∃ (s : C.chart.torus) (y : C.parameter opposite.1), s.val = 1 ∧
        C.value opposite.1 y ≤ exp (-opposite.2) ∧
        X.points g = cellValue M.toIntegralMarking (integralRing T.field) C.negative C.positive
          (C.chart.coordinates s (Function.update (fun _ => 0) opposite.1 y))}

end LinearAlgebraicGroups.Specs.RamifiedExceptionalOppositeWallLayer
