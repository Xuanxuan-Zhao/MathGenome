import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.DiscreteValuationRing.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups.Specs.SplitIwahoriDilatationGeometry

noncomputable section

abbrev base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

abbrev closedPoint {R : Type u} [CommRing R] (π : R) :
    base (R ⧸ Ideal.span {π}) ⟶ base R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π})))

abbrev genericPoint (R K : Type u) [CommRing R] [Field K] [Algebra R K] :
    base K ⟶ base R := Spec.map (CommRingCat.ofHom (algebraMap R K))

abbrev algebraScheme (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (base R) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))

abbrev algebraSchemeMap {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] (f : A →ₐ[R] T) :
    algebraScheme R T ⟶ algebraScheme R A :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op

/-- A morphism of test schemes reduces into the specified subgroup. -/
def FactorsThroughSpecialSubgroup {S S₀ : Scheme.{u}} (j : S₀ ⟶ S)
    {G : Grp (Over S)} {B : Grp (Over S₀)} (b : B ⟶ (Over.pullback j).mapGrp.obj G)
    {T : Over S} (f : T ⟶ G.X) : Prop :=
  ∃ z : (Over.pullback j).obj T ⟶ B.X, z ≫ b.hom.hom = (Over.pullback j).map f

/-- The representing property, with all flat test schemes over the base. -/
def RepresentsDilatation {S S₀ : Scheme.{u}} (j : S₀ ⟶ S)
    {G : Grp (Over S)} {B : Grp (Over S₀)} (b : B ⟶ (Over.pullback j).mapGrp.obj G)
    {D : Over S} (p : D ⟶ G.X) : Prop :=
  FactorsThroughSpecialSubgroup j b p ∧
    ∀ ⦃T : Over S⦄, Flat T.hom → ∀ f : T ⟶ G.X,
      FactorsThroughSpecialSubgroup j b f ↔ ∃! q : T ⟶ D, q ≫ p = f

section Chart

variable (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] (ι : Type u)

/-- The polynomial presentation of the product of affine space with `Spec C`. -/
abbrev chart := algebraScheme R (MvPolynomial ι C)

/-- The projection of the polynomial chart onto its coefficient scheme. -/
abbrev chartProjection : (chart R C ι).left ⟶ (algebraScheme R C).left :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : C →+* MvPolynomial ι C))

/-- The distinguished coordinates are multiplied by the uniformizer. -/
def scaleCoordinates (π : R) : MvPolynomial ι C →ₐ[R] MvPolynomial ι C :=
  (MvPolynomial.aeval (R := C)
    (fun i : ι => MvPolynomial.C (algebraMap R C π) * MvPolynomial.X i)).restrictScalars R

/-- The endomorphism of the chart over `Spec C` multiplying each coordinate by `π`. -/
def scale (π : R) : chart R C ι ⟶ chart R C ι :=
  algebraSchemeMap (scaleCoordinates R C ι π)

/-- The zero section of the chart over `Spec C`. -/
def zeroSection : algebraScheme R C ⟶ chart R C ι :=
  algebraSchemeMap ((MvPolynomial.aeval (R := C) (fun _ : ι => (0 : C))).restrictScalars R)

variable {R C ι}

/-- The Borel is the zero section of the polynomial chart on the special fibre. -/
def IsCentreChart (π : R) {G : Grp (Over (base R))}
    {B : Grp (Over (base (R ⧸ Ideal.span {π})))}
    (b : B ⟶ (Over.pullback (closedPoint π)).mapGrp.obj G)
    (v : chart R C ι ⟶ G.X) : Prop :=
  IsOpenImmersion v.left ∧
    ∃ e : B.X ≅ (Over.pullback (closedPoint π)).obj (algebraScheme R C),
      e.hom ≫ (Over.pullback (closedPoint π)).map (zeroSection R C ι ≫ v) = b.hom.hom

/-- The inverse image of the chart has the scaled coordinates and contains the special fibre. -/
def IsScaledChart (π : R) {G D : Over (base R)}
    (v : chart R C ι ⟶ G) (p : D ⟶ G) : Prop :=
  ∃ w : chart R C ι ⟶ D,
    IsOpenImmersion w.left ∧ IsPullback w.left (scale R C ι π).left p.left v.left ∧
      Set.range (pullback.fst D.hom (closedPoint π)) ⊆ Set.range w.left

end Chart

/-- The polynomial chart realizes the product of relative affine space and the coefficient scheme. -/
def ChartIsAffineSpaceProduct : Prop :=
  ∀ (R C ι : Type u) [CommRing R] [CommRing C] [Algebra R C],
    chartProjection R C ι ≫ (algebraScheme R C).hom = (chart R C ι).hom ∧
      ∃ a : (chart R C ι).left ⟶ AffineSpace ι (base R),
        IsPullback (chartProjection R C ι) a (algebraScheme R C).hom
          (AffineSpace ι (base R) ↘ base R)

/-- The smooth, affine dilatation and its scaled open chart over a DVR. -/
def SmoothDilatationExists : Prop :=
  ∀ (R K C ι : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CommRing C] [Algebra R C] [Finite ι]
    (π : R), Irreducible π →
    ∀ (G : Grp (Over (base R))), IsAffine G.X.left → Smooth G.X.hom →
    GeometricallyConnected G.X.hom →
    ∀ (B : Grp (Over (base (R ⧸ Ideal.span {π}))))
      (b : B ⟶ (Over.pullback (closedPoint π)).mapGrp.obj G),
      IsClosedImmersion b.hom.hom.left →
      Smooth (algebraScheme R C).hom → GeometricallyConnected (algebraScheme R C).hom →
      ∀ (v : chart R C ι ⟶ G.X), IsCentreChart π b v →
        ∃ (D : Grp (Over (base R))) (p : D ⟶ G),
          IsAffine D.X.left ∧ Smooth D.X.hom ∧ GeometricallyConnected D.X.hom ∧
          IsIso ((Over.pullback (genericPoint R K)).mapGrp.map p) ∧
          RepresentsDilatation (closedPoint π) b p.hom.hom ∧
          IsScaledChart π v p.hom.hom

/-- Any affine flat model representing the same condition has the same chart. -/
def ScaledChartComparison : Prop :=
  ∀ (R C ι : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing C] [Algebra R C]
    (π : R), Irreducible π →
    ∀ (G : Grp (Over (base R))), IsAffine G.X.left →
    ∀ (B : Grp (Over (base (R ⧸ Ideal.span {π}))))
      (b : B ⟶ (Over.pullback (closedPoint π)).mapGrp.obj G)
      (v : chart R C ι ⟶ G.X), IsCentreChart π b v →
    ∀ (D : Over (base R)) (p : D ⟶ G.X),
      IsAffine D.left → Flat D.hom → Flat (algebraScheme R C).hom →
      RepresentsDilatation (closedPoint π) b p → IsScaledChart π v p

/-- Morphisms into an affine scheme are determined by their generic base change. -/
def GenericHomExt : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (X Y : Over (base R)),
    Flat X.hom → IsAffine Y.left →
    ∀ f g : X ⟶ Y,
      (Over.pullback (genericPoint R K)).map f = (Over.pullback (genericPoint R K)).map g →
      f = g

/-- A flat affine model with generic isomorphism and the unique lifting
criterion represents the special-fibre condition. -/
def RepresentsOfGenericIso : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (π : R)
    (G : Grp (Over (base R))) (B : Grp (Over (base (R ⧸ Ideal.span {π}))))
    (b : B ⟶ (Over.pullback (closedPoint π)).mapGrp.obj G)
    (D : Over (base R)) (p : D ⟶ G.X), IsAffine D.left → Flat D.hom →
    IsIso ((Over.pullback (genericPoint R K)).map p) →
    (∀ ⦃T : Over (base R)⦄, Flat T.hom → ∀ f : T ⟶ G.X,
      FactorsThroughSpecialSubgroup (closedPoint π) b f ↔ ∃! q : T ⟶ D, q ≫ p = f) →
    RepresentsDilatation (closedPoint π) b p

/-- The representing schemes are uniquely isomorphic over the target. -/
def SchemeDilatationUnique : Prop :=
  ∀ (S S₀ : Scheme.{u}) (j : S₀ ⟶ S) (G : Grp (Over S)) (B : Grp (Over S₀))
    (b : B ⟶ (Over.pullback j).mapGrp.obj G) (D E : Over S) (p : D ⟶ G.X) (q : E ⟶ G.X),
    Flat D.hom → Flat E.hom → RepresentsDilatation j b p → RepresentsDilatation j b q →
    ∃! e : D ≅ E, e.hom ≫ q = p

/-- The representing group models are uniquely isomorphic over the target group. -/
def GroupDilatationUnique : Prop :=
  ∀ (S S₀ : Scheme.{u}) (j : S₀ ⟶ S) (G : Grp (Over S)) (B : Grp (Over S₀))
    (b : B ⟶ (Over.pullback j).mapGrp.obj G) (D E : Grp (Over S)) (p : D ⟶ G) (q : E ⟶ G),
    Flat D.X.hom → Flat E.X.hom →
    RepresentsDilatation j b p.hom.hom → RepresentsDilatation j b q.hom.hom →
    ∃! e : D ≅ E, e.hom ≫ q = p

end

end LinearAlgebraicGroups.Specs.SplitIwahoriDilatationGeometry
