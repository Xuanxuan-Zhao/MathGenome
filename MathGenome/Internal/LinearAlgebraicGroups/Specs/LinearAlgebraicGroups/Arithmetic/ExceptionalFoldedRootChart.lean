import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

namespace LinearAlgebraicGroups.Specs.ExceptionalFoldedRootChart

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct WithZero Classical
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (IntegralAlgebra IntegralMarking IntegralPoints Integers Model
  TorusValues integerAlgebra torusPoint)
open IntegralRootRelations (upper diagonal)
open ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection diagramAverage
  diagramCocharacters foldedDepthDenominator)
open ExceptionalIwahoriCongruence (CellValues cellValue integralRing)
open ExceptionalIwahoriImageComparison (MarkedLocalNormalizer integralUnitTorus pinnedGroundPoint)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open ExceptionalMarkedRootDescent (MarkedFibre SimpleRootOrbit TransportedOrbit markedWeylWord
  pinnedDiagram rationalOrbitParameter transportedLabels transportedRootPoint markedRootPoint
  wallMatrix weylWordPerm)
open ExceptionalValuedTorusNormalizer (FibreNormalizer fixedWeylGroup invariantApartment markedDiagramEquiv)
open AdjointBorelCohomology (PinnedTwist)
open OrderedRootProducts (Enumerates)

universe u

attribute [local instance] integerAlgebra

noncomputable section

/-- One ordered block for each relative direction, with the absolute labels
in the order used by the integral cell. -/
structure OrbitOrdering {D : BasedRootDatum.{u}} (direction : D.I → FoldedRootDirection) where
  block : FoldedRootDirection → TransportedOrbit D
  negative : List (TransportedOrbit D)
  positive : List (TransportedOrbit D)
  fibre (a : FoldedRootDirection) (i : D.I) : i ∈ transportedLabels (block a) ↔ direction i = a
  ordered (b : TransportedOrbit D) : b ∈ negative ++ positive → ∃ a, block a = b
  negative_enumerates : Enumerates (negative.flatMap transportedLabels) {i | ¬D.base.IsPos i}
  positive_enumerates : Enumerates (positive.flatMap transportedLabels) {i | D.base.IsPos i}

section Parameters

variable {D : BasedRootDatum.{u}} {k K : Type u} [Field k] [Field K]

instance parameterField (b : TransportedOrbit D) : Field (rationalOrbitParameter k K b) := by
  rcases b with ⟨⟨a, _ | b⟩, w⟩ <;> assumption

instance parameterValuativeRel [ValuativeRel k] [ValuativeRel K] (b : TransportedOrbit D) :
    ValuativeRel (rationalOrbitParameter k K b) := by
  rcases b with ⟨⟨a, _ | b⟩, w⟩ <;> assumption

instance parameterTopology [TopologicalSpace k] [TopologicalSpace K] (b : TransportedOrbit D) :
    TopologicalSpace (rationalOrbitParameter k K b) := by
  rcases b with ⟨⟨a, _ | b⟩, w⟩ <;> assumption

instance parameterLocalField [ValuativeRel k] [ValuativeRel K]
    [TopologicalSpace k] [TopologicalSpace K] [IsNonarchimedeanLocalField k]
    [IsNonarchimedeanLocalField K] (b : TransportedOrbit D) :
    IsNonarchimedeanLocalField (rationalOrbitParameter k K b) := by
  rcases b with ⟨⟨a, _ | b⟩, w⟩
  · exact (inferInstance : IsNonarchimedeanLocalField k)
  · exact (inferInstance : IsNonarchimedeanLocalField K)

variable [Algebra k K]

/-- A singleton uses the scalar inclusion. A pair uses identity followed
by the diagram-field involution in the order of its two transported labels. -/
def slotMap (σ : Gal(K/k)) : (b : TransportedOrbit D) → D.I → rationalOrbitParameter k K b →+* K
  | (⟨_, none⟩, _), _ => algebraMap k K
  | (⟨a, some _⟩, w), i => by
      classical
      exact if i = weylWordPerm (w.flatMap SimpleRootOrbit.roots) (a : D.I) then RingHom.id K
        else σ.toRingHom

/-- The multiplier from a transported root line to the original integral
coordinate of its absolute label. -/
def slotUnit (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (b : TransportedOrbit D) (i : D.I) :
    Integers.{u}ˣ :=
  u b ((weylWordPerm (b.2.flatMap SimpleRootOrbit.roots)).symm i)

def OrbitOrdering.coordinates {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) (u : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (σ : Gal(K/k)) (t : TorusValues D (integralRing K))
    (x : ∀ a, rationalOrbitParameter k K (o.block a)) :
    CellValues D (integralRing K) (o.negative.flatMap transportedLabels) (o.positive.flatMap transportedLabels) :=
  let v (i : D.I) : K :=
    let b := o.block (direction i)
    algebraMap Integers.{u} K (slotUnit u b i : Integers.{u}) * slotMap σ b i (x (direction i))
  ((fun i => v (o.negative.flatMap transportedLabels)[i]), t,
    fun i => v (o.positive.flatMap transportedLabels)[i])

/-- The integral change of each transported root coordinate, uniform in
the test algebra and hence in every later coefficient field. -/
def IsTransportUnitSystem (M : IntegralMarking D)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) : Prop :=
  ∀ (R : IntegralAlgebra.{u}) (b : TransportedOrbit D) (a : D.I) (z : R),
    transportedRootPoint M R b a z =
      markedRootPoint M R (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) a)
        (algebraMap Integers.{u} R (u b a : Integers.{u}) * z)

end Parameters

section Comparisons


/-- The intersection of the actual descended points with the integral
marked cell in its generic fibre. All charts use the same chosen units
and the same ordered root directions. -/
def OrderedChart : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M k) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T) (σ : Gal(K/k)),
  Module.finrank k K = 2 → σ ≠ 1 →
  (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
  ∀ (direction : D.I → FoldedRootDirection) (o : OrbitOrdering direction),
    (∀ b ∈ o.negative ++ o.positive, b.1.Matches C (pinnedDiagram d σ) ∧
      ∀ v ∈ b.2, v.Matches C (pinnedDiagram d σ)) →
    ∀ (u : TransportedOrbit D → D.I → Integers.{u}ˣ),
      IsTransportUnitSystem M.toIntegralMarking u →
    ∀ (j : (𝟙_ (SchemeOver k) ⟶ G.val.X) →* (IntegralPoints M.group (integralRing K))),
      (∀ g, j g = pinnedGroundPoint C d g) →
    ∀ z : CellValues D (integralRing K) (o.negative.flatMap transportedLabels)
        (o.positive.flatMap transportedLabels),
      cellValue M.toIntegralMarking (integralRing K) _ _ z ∈ j.range ↔
        ∃ (t : TorusValues D (integralRing K)) (x : ∀ a, rationalOrbitParameter k K (o.block a)),
          (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) ∈ j.range ∧
          o.coordinates u σ t x = z

/-- The transported rank-one map uses the same coordinates as the chart.
Its uniformizer wall element is in the actual rational normalizer and
acts by the specified normalized affine reflection. -/
def WallLifts : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension k K]
    {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M k) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T) (σ : Gal(K/k)),
  let τ := (markedDiagramEquiv C.realization (d.outer σ)).asIso.hom
  Module.finrank k K = 2 → σ ≠ 1 →
  (∀ z : k, normalizedValuation K (algebraMap k K z) = normalizedValuation k z ^ 2) →
  (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
  Function.Involutive τ.val.indexEquiv →
  ∀ (direction : D.I → FoldedRootDirection) (o : OrbitOrdering direction),
    (∀ i a, direction i = direction a ↔ a = i ∨ a = τ.val.indexEquiv i) →
    (∀ i, ExceptionalAffineRootSystems.IsLongF4Doubled (direction i).val ↔
      τ.val.indexEquiv i = i) →
    (∀ a, (o.block a).1.Matches C (pinnedDiagram d σ) ∧
      ∀ v ∈ (o.block a).2, v.Matches C (pinnedDiagram d σ)) →
    (∀ a, (transportedLabels (o.block a)).Nodup) →
    ∀ (u : TransportedOrbit D → D.I → Integers.{u}ˣ),
      IsTransportUnitSystem M.toIntegralMarking u →
    ∀ (j : (𝟙_ (SchemeOver k) ⟶ G.val.X) →* (IntegralPoints M.group (integralRing K))), Function.Injective j →
      (∀ g, j g = pinnedGroundPoint C d g) →
    ∀ (N : MarkedLocalNormalizer K j (fixedWeylGroup D τ)) (F : FibreNormalizer M K),
      (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = (N.label n).val) →
    let V := invariantApartment D τ
    ∀ (A : ApartmentRoots ℚ V FoldedRootDirection),
      (∀ i x, A.root (direction i) x = (foldedDepthDenominator (direction i) : ℚ) *
        (ApartmentRoots.split D.datum ℚ).root i x.val) →
      (∀ i, (A.coroot (direction i)).val =
        diagramAverage (diagramCocharacters τ.val) ((ApartmentRoots.split D.datum ℚ).coroot i)) →
    ∀ (action : N.normalizer →* (V ≃ᵃ[ℚ] V)),
      (∀ n x, (action n x).val =
        (N.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
          ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)) →
    ∀ (a : FoldedRootDirection) (m : ℤ),
      let b := o.block a
      let P := rationalOrbitParameter k K b
      let word := b.2.flatMap SimpleRootOrbit.roots
      let R := integralRing K
      let H := markedWeylWord M.toIntegralMarking R word
      ∃ (ρ : Matrix.SpecialLinearGroup (Fin 2) P →* (𝟙_ (SchemeOver k) ⟶ G.val.X)) (t : Pˣ) (n : N.normalizer),
        (∀ U, j (ρ U) = H * ((b.1.1 :: b.1.2.toList).map (fun (i : D.base.support) =>
          (show (IntegralPoints M.group (integralRing K)) from (M.rankOne i.val).app R
            (Matrix.SpecialLinearGroup.map (slotMap σ b (weylWordPerm word i.val)) U)))).prod * H⁻¹) ∧
        (∀ z : P, j (ρ (upper z)) =
          cellValue M.toIntegralMarking R _ _ (o.coordinates u σ 1
            (Function.update (fun _ => 0) a z))) ∧
        (∀ z : Pˣ, normalizedValuation P (z : P) = 1 →
          ρ (diagonal z) ∈ (integralUnitTorus (K := K) M).comap j) ∧
        normalizedValuation P (t : P) = WithZero.exp (-m) ∧
        (n : (𝟙_ (SchemeOver k) ⟶ G.val.X)) = ρ (wallMatrix t) ∧
        action n = A.wallReflection a m

end Comparisons

end
end LinearAlgebraicGroups.Specs.ExceptionalFoldedRootChart
