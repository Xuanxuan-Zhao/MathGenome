import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GrassmannianCharts
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.LinearAlgebra.ExteriorPower.Basis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinearAlgebraicGroups.Specs.PluckerEmbedding

noncomputable section

abbrev Wedge (R : Type u) [CommRing R] (d : ℕ) (M : Type u)
    [AddCommGroup M] [Module R M] := ⋀[R]^d M

/-- The canonical comparison between extending scalars and taking an exterior power. -/
structure ExteriorComparison (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (M : Type u) [AddCommGroup M] [Module R M] where
  equiv : S ⊗[R] Wedge R d M ≃ₗ[S] Wedge S d (S ⊗[R] M)
  pure : ∀ v : Fin d → M,
    equiv ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R d v) =
      exteriorPower.ιMulti S d (fun i => (1 : S) ⊗ₜ[R] v i)

def ExteriorBaseChange : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (M : Type u) [AddCommGroup M] [Module R M],
    Nonempty (ExteriorComparison R S d M)

open GrassmannianCharts ProjectiveSpaces

section Affine

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {d : ℕ}
  {R : TestAlgebra k}

/-- The image of the top exterior power of the given plane in the extended exterior space. -/
def lineSubmodule (c : ExteriorComparison k R d V) (L : Plane k V d R) :
    Submodule R (R ⊗[k] Wedge k d V) :=
  LinearMap.range (c.equiv.symm.toLinearMap.comp (exteriorPower.map (M := ↥L.toSubmodule) d L.toSubmodule.subtype))

/-- Taking the exterior line on every test algebra gives split rank-one modules
and commutes with the stated functors' base change, including nonflat base change. -/
structure AffineExteriorLines (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    (d : ℕ) where
  compare : ∀ R : TestAlgebra k, ExteriorComparison k R d V
  line : ∀ R : TestAlgebra k, Plane k V d R → AffineLine k (Wedge k d V) R
  image_eq : ∀ R L, (line R L).submodule = lineSubmodule (compare R) L
  baseChange : ∀ {R T : TestAlgebra k} (a : R ⟶ T) (L : Plane k V d R),
    (line T (Module.Grassmannian.map a.hom L)).submodule =
      changeLineSubmodule k (Wedge k d V) a (line R L).submodule

def AffineExteriorLineGeometry : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (d : ℕ), d ≤ Module.finrank k V → Nonempty (AffineExteriorLines k V d)

/-- On an extended vector space the exterior representation is carried to the
extension of the exterior space using the canonical comparison. -/
def exteriorTransport (c : ExteriorComparison k R d V)
    (g : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V)) :
    R ⊗[k] Wedge k d V →ₗ[R] R ⊗[k] Wedge k d V :=
  c.equiv.symm.toLinearMap.comp ((exteriorPower.map d g.toLinearMap).comp c.equiv.toLinearMap)

def AffineExteriorEquivariance : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] (d : ℕ)
    (R : TestAlgebra k) (c : ExteriorComparison k R d V)
    (g : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V))
    (L M : Plane k V d R), M.toSubmodule = L.toSubmodule.map g.toLinearMap →
      lineSubmodule c M = (lineSubmodule c L).map (exteriorTransport c g)

end Affine

section Charts

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V]
    [Fintype Index] [LinearOrder Index]
    (b : Basis Index k V) {d : ℕ}

/-- The increasing enumeration of the pivot rows. -/
def pivotEnumeration (I : Pivot Index d) : Fin d ≃ Inside I :=
  Equiv.ofBijective
    (fun i => ⟨Set.powersetCard.ofFinEmbEquiv.symm I i,
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I _).mp ⟨i, rfl⟩⟩)
    ⟨fun i j h => (Set.powersetCard.ofFinEmbEquiv.symm I).injective (congrArg Subtype.val h),
      fun j => by
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I j.val).mpr j.prop
        exact ⟨i, Subtype.ext hi⟩⟩

/-- The wedge of the normalized graph columns in increasing pivot order. -/
def graphExteriorVector (I : Pivot Index d) (R : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) R) : Wedge R d (R ⊗[k] V) :=
  exteriorPower.ιMulti R d (fun i =>
    graphInclusion b I R A (Pi.single (pivotEnumeration I i) 1))

/-- A Plücker coordinate on the chart, equivalently the indicated maximal minor. -/
def graphExteriorCoordinate (I J : Pivot Index d) (R : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) R) : R :=
  ((b.baseChange R).exteriorPower d).coord ⟨J.val, J.property⟩ (graphExteriorVector b I R A)

/-- Over the polynomial chart algebra, the graph with all entries independent. -/
def universalGraph (I : Pivot Index d) :
    Matrix (Outside I) (Inside I) (GrassmannianCharts.chartAlgebra (k := k) I) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

def ChartAlgebraSurjectivity : Prop :=
  ∀ (k V Index : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype Index] [LinearOrder Index] (b : Basis Index k V) {d : ℕ} (I : Pivot Index d),
    ∃ f : chartRing k (Pivot Index d) I →ₐ[k] GrassmannianCharts.chartAlgebra (k := k) I,
      Function.Surjective f ∧
      ∀ J : Pivot Index d, f (coordinateRatio k (Pivot Index d) I J) =
        graphExteriorCoordinate b I J (CommAlgCat.of k _) (universalGraph (k := k) I)

end Charts

section Geometry

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Fintype Index] [DecidableEq Index] (b : Basis Index k V) (d : ℕ)

/-- The Plücker map between the standard Grassmannian and the projective
scheme of lines, with its exterior image formula on every affine restriction
of every scheme family. -/
structure PluckerMorphism where
  charts : ChartSystem (k := k) (V := V) b d
  families : SchemePoints (k := k) (V := V) d charts.scheme charts.affinePoints
  affineComparison : ∀ (R : TestAlgebra k) (p : Points charts.scheme R),
    IsTildePlane (k := k) (V := V) b R (charts.affinePoints.hom.app R p)
      (families.subbundle _ (families.family _ p))
  lines : LineRepresentation k (Wedge k d V)
  basisFormula : BasisPointFormula k (Wedge k d V) lines
  exteriorLines : AffineExteriorLines k V d
  morphism : charts.scheme ⟶ projectiveSpace k (Wedge k d V)
  imageFormula : ∀ (S : SchemeOver k) (p : S ⟶ charts.scheme)
      (R : TestAlgebra k) (a : Points S R),
    ((lines.points S (p ≫ morphism)).line R a).submodule =
      lineSubmodule (exteriorLines.compare R) ((families.family S p).app R a)

def PluckerMorphismGeometry : Prop :=
  ∀ (k V Index : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Fintype Index] [DecidableEq Index] (b : Basis Index k V) (d : ℕ), d ≤ Module.finrank k V →
    ∃ P : PluckerMorphism b d,
      (d = 0 ∨ d = Module.finrank k V) →
        Nonempty (IsTerminal P.charts.scheme) ∧ IsIso (projectiveSpace k (Wedge k d V)).hom

/-- A Plücker map sends each source chart by the displayed closed immersion
into the corresponding projective chart. -/
def PluckerChartRestrictions : Prop :=
  ∀ (k V Index : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Fintype Index] [LinearOrder Index] (b : Basis Index k V) (d : ℕ) (P : PluckerMorphism b d),
    ∃ e : coordinateProjectiveSpace k (Pivot Index d) ≅ projectiveSpace k (Wedge k d V),
      ∀ I : Pivot Index d,
        ∃ f : chartRing k (Pivot Index d) I →ₐ[k] GrassmannianCharts.chartAlgebra (k := k) I,
          Function.Surjective f ∧
          (∀ J : Pivot Index d, f (coordinateRatio k (Pivot Index d) I J) =
            graphExteriorCoordinate b I J (CommAlgCat.of k _) (universalGraph (k := k) I)) ∧
          (testSpec k).map (CommAlgCat.ofHom f).op ≫ chartMorphism I ≫ e.hom =
            P.charts.chart I ≫ P.morphism

/-- The same morphism given by the exterior line of the family is a closed immersion. -/
def PluckerClosedImmersion : Prop :=
  ∀ (k V Index : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Fintype Index] [LinearOrder Index] (b : Basis Index k V) (d : ℕ) (P : PluckerMorphism b d),
      IsClosedImmersion P.morphism.left

end Geometry

section LinearGroupAction

variable {k V Index : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype Index] [DecidableEq Index] (b : Basis Index k V) {d : ℕ}

/-- The matrix of a general linear group point acts in the base-changed basis. -/
def matrixTransport (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup Index R) :
    (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V) :=
  (Matrix.GeneralLinearGroup.toLin' (b.baseChange R) g).toLinearEquiv

/-- An action of a group scheme in the category of schemes over the base. -/
structure SchemeAction (G : Specs.GroupScheme k) (X : SchemeOver k) where
  act : G.X ⊗ X ⟶ X
  unit : lift (toUnit X ≫ η[G.X]) (𝟙 X) ≫ act = 𝟙 X
  assoc :
    (lift ((lift (fst G.X (G.X ⊗ X)) (snd G.X (G.X ⊗ X) ≫ fst G.X X)) ≫ μ[G.X])
      (snd G.X (G.X ⊗ X) ≫ snd G.X X)) ≫ act =
    lift (fst G.X (G.X ⊗ X)) (snd G.X (G.X ⊗ X) ≫ act) ≫ act

def IsEquivariant (P : PluckerMorphism b d) : Prop :=
  ∃ (G : Specs.GroupScheme k)
    (c : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k Index)
    (α : SchemeAction G P.charts.scheme)
    (β : SchemeAction G (projectiveSpace k (Wedge k d V))),
    (∀ (R : TestAlgebra k) (g : Points G.X R) (p : Points P.charts.scheme R),
      let t := matrixTransport b R (c.hom.app R g)
      (P.charts.affinePoints.hom.app R (lift g p ≫ α.act)).toSubmodule =
        (P.charts.affinePoints.hom.app R p).toSubmodule.map t.toLinearMap) ∧
    (∀ (R : TestAlgebra k) (g : Points G.X R)
      (p : Points (projectiveSpace k (Wedge k d V)) R),
      let t := matrixTransport b R (c.hom.app R g)
      ((P.lines.points _ (lift g p ≫ β.act)).line R (𝟙 _)).submodule =
        ((P.lines.points _ p).line R (𝟙 _)).submodule.map
          (exteriorTransport (P.exteriorLines.compare R) t)) ∧
    α.act ≫ P.morphism =
      lift (fst G.X P.charts.scheme) (snd G.X P.charts.scheme ≫ P.morphism) ≫ β.act

def PluckerEquivariantGeometry : Prop :=
  ∀ (k V Index : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Fintype Index] [DecidableEq Index] (b : Basis Index k V) (d : ℕ), d ≤ Module.finrank k V →
      ∃ P : PluckerMorphism b d, IsClosedImmersion P.morphism.left ∧ IsEquivariant b P ∧
        ((d = 0 ∨ d = Module.finrank k V) →
          Nonempty (IsTerminal P.charts.scheme) ∧ IsIso (projectiveSpace k (Wedge k d V)).hom)

end LinearGroupAction

end

end LinearAlgebraicGroups.Specs.PluckerEmbedding
