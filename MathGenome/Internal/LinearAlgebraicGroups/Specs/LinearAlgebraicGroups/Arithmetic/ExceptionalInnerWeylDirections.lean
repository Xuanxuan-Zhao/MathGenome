import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerWeylDirections

open ExceptionalAffineRootSystems (ApartmentRoots exceptionalCartan simpleRootValues)
open ExceptionalAffineBruhat (ExceptionalNumbering SplitLevel)
open ExceptionalInnerStandardTorusDescent (markedCocharacterMap)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)

/-- The change in simple-root values under reflection in the simple root numbered `j`. -/
def reflectValues {n : ℕ} (j : Fin n) (r : Fin n → ℚ) : Fin n → ℚ :=
  fun i => r i - (exceptionalCartan n j i : ℚ) * r j

/-- Apply the listed simple reflections in order, starting at the head of the list. -/
def reflectWord {n : ℕ} (word : List (Fin n)) (r : Fin n → ℚ) : Fin n → ℚ :=
  word.foldl (fun v j => reflectValues j v) r

/-- The central cover transports the simple-root numbering, and a lift of the
reflection word acts on the rational cocharacter images through the marked torus. -/
def MarkedWeylDirections : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M')
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e) {n : ℕ} (b : Fin n ≃ D.base.support),
    (n = 6 ∨ n = 7) → ExceptionalNumbering D n b → Module.finrank ℤ E.Y = n →
    ∀ word : List (Fin n),
      let A := ApartmentRoots.split D.datum ℚ
      let P := Y.sc_fibre.realization.pinned.pair
      let values := simpleRootValues D.datum D.base b ℚ
      let push := c.pushCocharacter.baseChange ℚ
      ∃ bAd : Fin n ≃ E.base.support,
        ExceptionalNumbering E n bAd ∧
        (∀ j, (bAd j : E.I) = c.rootEquiv (b j : D.I)) ∧
        let valuesAd := simpleRootValues E.datum E.base bAd ℚ
        (∀ x, valuesAd (push x) = values x) ∧
        ∃ (g : 𝟙_ (SchemeOver K) ⟶ P.G.val.X)
          (hg : markedGroundPoint Y.sc_fibre g ∈ Y.sc.N),
          (∀ x, Y.sc.affine ⟨markedGroundPoint Y.sc_fibre g, hg⟩ x =
            word.foldl (fun z j => A.wallReflection (b j) 0 z) x) ∧
          ∀ (a : P.T.group ≅ P.T.group),
            (a.hom ≫ P.T.inclusion).hom.hom =
              (toUnit P.T.group.X ≫ g) * P.T.inclusion.hom.hom *
                (toUnit P.T.group.X ≫ g)⁻¹ →
            ∀ {H : GroupScheme K} [IsCommMonObj H.X] (s : H ⟶ P.T.group),
              let V := (markedCocharacterMap Y.sc_fibre s).baseChange ℚ
              let Vg := (markedCocharacterMap Y.sc_fibre (s ≫ a.hom)).baseChange ℚ
              values '' (LinearMap.range Vg : Set _) =
                reflectWord word '' (valuesAd '' (LinearMap.range (push.comp V) : Set _))

end LinearAlgebraicGroups.Specs.ExceptionalInnerWeylDirections
