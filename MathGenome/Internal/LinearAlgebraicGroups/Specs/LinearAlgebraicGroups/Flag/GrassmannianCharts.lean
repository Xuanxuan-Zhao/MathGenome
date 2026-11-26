import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.MvPolynomial.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.GrassmannianCharts

noncomputable section

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The affine rank-d plane is stored by its finite projective quotient of rank n-d. -/
abbrev Plane (d : ℕ) (R : TestAlgebra k) :=
  Module.Grassmannian R (R ⊗[k] V) (Module.finrank k V - d)

abbrev planeFunctor (d : ℕ) : TestAlgebra k ⥤ Type u :=
  Module.Grassmannian.functor (R := k) (M := V) (Module.finrank k V - d)

/-- A family of planes on affine probes, compatible with canonical base change. -/
abbrev Family (d : ℕ) (S : SchemeOver k) :=
  pointsFunctor S ⟶ planeFunctor k V d

/-- The constant vector bundle with fibre V, viewed as a sheaf of modules. -/
def ambient (S : SchemeOver k) : S.left.Modules :=
  (Scheme.Modules.pullback S.hom).obj (tilde (ModuleCat.of k V))

/-- Rank-d subbundles, recorded as subobjects. Locally the source is free
of rank d and its inclusion admits a retraction. -/
def Subbundles (d : ℕ) (S : SchemeOver k) :=
  { L : Subobject (ambient k V S) //
    ∀ x : S.left, ∃ U : S.left.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj (L : S.left.Modules) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) ∧
      IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map L.arrow) }

def ambientPullback {T S : SchemeOver k} (f : T ⟶ S) :
    (Scheme.Modules.pullback f.left).obj (ambient k V S) ≅ ambient k V T :=
  (Scheme.Modules.pullbackComp f.left S.hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr (Over.w f)).app _

/-- Equality with a pullback expressed by an isomorphism of the included modules. -/
def IsPullbackSubbundle {T S : SchemeOver k} (f : T ⟶ S)
    {d : ℕ} (L : Subbundles k V d S) (M : Subbundles k V d T) : Prop :=
  ∃ e : (Scheme.Modules.pullback f.left).obj (L.val : S.left.Modules) ≅
      (M.val : T.left.Modules),
    e.hom ≫ M.val.arrow =
      (Scheme.Modules.pullback f.left).map L.val.arrow ≫ (ambientPullback k V f).hom

/-- Pullback of a locally split subbundle exists and is unique as a subobject. -/
def SubbundlePullback : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    (d : ℕ) {T S : SchemeOver k} (f : T ⟶ S) (L : Subbundles k V d S),
      ∃! M : Subbundles k V d T, IsPullbackSubbundle k V f L M

abbrev Pivot (ι : Type u) (d : ℕ) := { I : Finset ι // I.card = d }
abbrev Inside {ι : Type u} {d : ℕ} (I : Pivot ι d) := {i : ι // i ∈ I.val}
abbrev Outside {ι : Type u} {d : ℕ} (I : Pivot ι d) := {i : ι // i ∉ I.val}

section Coordinates

variable {k V} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι k V) {d : ℕ} (I : Pivot ι d) (R : TestAlgebra k)

/-- Coordinates in the base change of the chosen basis. -/
def coordinates : (R ⊗[k] V) ≃ₗ[R] (ι → R) :=
  (b.baseChange R).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite R R ι

/-- Restrict coordinates to the pivot rows. -/
def pivotProjection : R ⊗[k] V →ₗ[R] (Inside I → R) :=
  (LinearMap.funLeft R R Subtype.val).comp (coordinates b R).toLinearMap

/-- The normalized inclusion has identity pivot rows and entries A in the other rows. -/
def graphColumns (A : Matrix (Outside I) (Inside I) R) :
    (Inside I → R) →ₗ[R] (ι → R) :=
  LinearMap.pi fun i : ι ↦
    if hi : i ∈ I.val then LinearMap.proj (R := R) (φ := fun _ : Inside I ↦ R) ⟨i, hi⟩
    else (LinearMap.proj (R := R) (φ := fun _ : Outside I ↦ R) ⟨i, hi⟩).comp
      (Matrix.toLin' A)

def graphInclusion (A : Matrix (Outside I) (Inside I) R) :
    (Inside I → R) →ₗ[R] R ⊗[k] V :=
  (coordinates b R).symm.toLinearMap.comp (graphColumns I R A)

def IsPivot (L : Plane k V d R) : Prop :=
  Function.Bijective ((pivotProjection b I R).comp L.toSubmodule.subtype)

def pivotChange (J : Pivot ι d) (A : Matrix (Outside I) (Inside I) R) :
    (Inside I → R) →ₗ[R] (Inside J → R) :=
  (LinearMap.funLeft R R Subtype.val).comp (graphColumns I R A)

end Coordinates

variable {k} {ι : Type u} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- One variable per nonpivot row and pivot column. -/
abbrev chartAlgebra (I : Pivot ι d) := MvPolynomial (Outside I × Inside I) k

abbrev chartScheme (I : Pivot ι d) : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (chartAlgebra (k := k) I)))

def matrixOfPoint (I : Pivot ι d) (R : TestAlgebra k)
    (f : Points (chartScheme (k := k) I) R) : Matrix (Outside I) (Inside I) R :=
  let g := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f
  Matrix.of fun i j ↦ g.unop.hom (MvPolynomial.X (i, j))

/-- Ordering the pivot subsets allows the minor to be evaluated as a square determinant. -/
def pivotOrder (I : Pivot ι d) : Inside I ≃ Fin d :=
  Fintype.equivFinOfCardEq (by simpa using I.property)

/-- The square matrix of the new pivot rows, with the chosen row and column orders. -/
def pivotMinor (I J : Pivot ι d) (R : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) R) : Matrix (Fin d) (Fin d) R :=
  let eI := LinearEquiv.funCongrLeft R R (pivotOrder I).symm
  let eJ := LinearEquiv.funCongrLeft R R (pivotOrder J).symm
  LinearMap.toMatrix' (eJ.toLinearMap.comp ((pivotChange I R J A).comp eI.symm.toLinearMap))

def overlapDet (I J : Pivot ι d) : chartAlgebra (k := k) I :=
  (pivotMinor I J (CommAlgCat.of k (chartAlgebra (k := k) I))
    (Matrix.of fun j i ↦ MvPolynomial.X (j, i))).det

variable (k) in
def chartOverlap (I J : Pivot ι d) : SchemeOver k :=
  Over.mk ((Scheme.Opens.ι (X := (chartScheme (k := k) I).left)
    (PrimeSpectrum.basicOpen (overlapDet (k := k) I J))) ≫
    (chartScheme (k := k) I).hom)

def overlapInclusion (I J : Pivot ι d) :
    chartOverlap k I J ⟶ chartScheme (k := k) I :=
  Over.homMk (Scheme.Opens.ι (X := (chartScheme (k := k) I).left)
    (PrimeSpectrum.basicOpen (overlapDet (k := k) I J))) rfl

/-- The polynomial chart describes exactly the planes whose pivot projection is invertible. -/
def GraphCoordinates : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) {d : ℕ}
    (I : Pivot ι d) (R : TestAlgebra k),
    ∃ e : Points (chartScheme (k := k) I) R ≃ {L : Plane k V d R // IsPivot b I R L},
      ∀ f, (e f).val.toSubmodule = (graphInclusion b I R (matrixOfPoint I R f)).range

def FieldPivotCoverage : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (d : ℕ),
    d ≤ Module.finrank k V →
    ∀ (F : Type u) [Field F] [Algebra k F] (L : Plane k V d (CommAlgCat.of k F)),
      ∃ I : Pivot ι d, IsPivot b I (CommAlgCat.of k F) L

def GraphBaseChange : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) {d : ℕ}
    (I : Pivot ι d) {R S : TestAlgebra k} (a : R ⟶ S)
    (A : Matrix (Outside I) (Inside I) R) (L : Plane k V d R),
    L.toSubmodule = (graphInclusion b I R A).range →
    (Module.Grassmannian.map a.hom L).toSubmodule =
      (graphInclusion b I S (A.map a.hom)).range

def GraphTransition : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) {d : ℕ}
    (I J : Pivot ι d) (R : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) R) (B : Matrix (Outside J) (Inside J) R),
    (graphInclusion b I R A).range = (graphInclusion b J R B).range →
    ∃ e : (Inside I → R) ≃ₗ[R] (Inside J → R),
      e.toLinearMap = pivotChange I R J A ∧
      graphInclusion b J R B = (graphInclusion b I R A).comp e.symm.toLinearMap

def OverlapCoordinates : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) {d : ℕ}
    (I J : Pivot ι d) (R : TestAlgebra k) (L : Plane k V d R)
    (f : Points (chartScheme (k := k) I) R),
    L.toSubmodule = (graphInclusion b I R (matrixOfPoint I R f)).range →
      (IsPivot b J R L ↔ ∃ g : Points (chartOverlap k I J) R, g ≫ overlapInclusion I J = f)

def PivotGluing : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (_b : Module.Basis ι k V) (d : ℕ),
    ∃ (X : SchemeOver k) (chart : ∀ I : Pivot ι d, chartScheme (k := k) I ⟶ X),
      (∀ I, IsOpenImmersion (chart I).left) ∧
      (∀ x : X.left, ∃ (I : Pivot ι d) (y : (chartScheme (k := k) I).left),
        (chart I).left y = x) ∧
      (∀ I J : Pivot ι d, ∃ e : chartOverlap k I J ≅ pullback (chart I) (chart J),
        e.hom ≫ pullback.fst (chart I) (chart J) = overlapInclusion I J) ∧
      (d = 0 ∨ d = Module.finrank k V → Nonempty (IsTerminal X))

/-- A Grassmannian with its standard basis-indexed affine open cover. -/
structure ChartSystem {ι : Type u} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (d : ℕ) where
  scheme : SchemeOver k
  affinePoints : pointsFunctor scheme ≅ planeFunctor k V d
  chart : ∀ I : Pivot ι d, chartScheme (k := k) I ⟶ scheme
  openChart : ∀ I, IsOpenImmersion (chart I).left
  cover : ∀ x : scheme.left, ∃ (I : Pivot ι d) (y : (chartScheme (k := k) I).left),
    (chart I).left y = x
  coordinates_eq : ∀ (I : Pivot ι d) (R : TestAlgebra k)
    (f : Points (chartScheme (k := k) I) R),
      (affinePoints.hom.app R (f ≫ chart I)).toSubmodule =
        (graphInclusion b I R (matrixOfPoint I R f)).range
  factor_iff : ∀ (I : Pivot ι d) (R : TestAlgebra k) (p : Points scheme R),
    (∃ f : Points (chartScheme (k := k) I) R, f ≫ chart I = p) ↔
      IsPivot b I R (affinePoints.hom.app R p)
  overlap : ∀ I J : Pivot ι d,
    ∃ e : chartOverlap k I J ≅ pullback (chart I) (chart J),
      e.hom ≫ pullback.fst (chart I) (chart J) = overlapInclusion I J
  transition : ∀ (I J : Pivot ι d) (R : TestAlgebra k)
    (f : Points (chartScheme (k := k) I) R) (g : Points (chartScheme (k := k) J) R),
    f ≫ chart I = g ≫ chart J →
      ∃ e : (Inside I → R) ≃ₗ[R] (Inside J → R),
        e.toLinearMap = pivotChange I R J (matrixOfPoint I R f) ∧
        graphInclusion b J R (matrixOfPoint J R g) =
          (graphInclusion b I R (matrixOfPoint I R f)).comp e.symm.toLinearMap

def AffineConstruction : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
    (d : ℕ), d ≤ Module.finrank k V → Nonempty (ChartSystem (k := k) (V := V) b d)

/-- On an affine test scheme the constant bundle is the tilde of scalar extension.
The comparison uses the same basis on both sides. -/
def affineAmbientOfBasis {ι : Type u} (b : Module.Basis ι k V) (R : TestAlgebra k) :
    ambient k V ((testSpec k).obj (op R)) ≅
      tilde (ModuleCat.of R (R ⊗[k] V)) :=
  let f := ((testSpec k).obj (op R)).hom
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  (Scheme.Modules.pullback f).mapIso
    (((tilde.functor (CommRingCat.of k)).mapIso b.repr.toModuleIso) ≪≫
      tildeFinsupp ι) ≪≫
    SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom ι ≪≫
    ((tilde.functor (CommRingCat.of R)).mapIso (b.baseChange R).repr.toModuleIso ≪≫
      tildeFinsupp ι).symm

/-- The affine subbundle is obtained by sheafifying the corresponding submodule inclusion. -/
def IsTildePlane {ι : Type u} (b : Module.Basis ι k V) {d : ℕ}
    (R : TestAlgebra k) (P : Plane k V d R)
    (L : Subbundles k V d ((testSpec k).obj (op R))) : Prop :=
  ∃ e : tilde (ModuleCat.of R P.toSubmodule) ≅
      (L.val : ((testSpec k).obj (op R)).left.Modules),
    e.hom ≫ L.val.arrow ≫ (affineAmbientOfBasis (k := k) (V := V) b R).hom =
      (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom P.toSubmodule.subtype)

/-- On every affine test scheme, the rank-d subbundles are exactly the tilde
inclusions of the affine planes. -/
def AffineSubbundleComparison : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
    (d : ℕ), d ≤ Module.finrank k V → ∀ R : TestAlgebra k,
      ∃ e : Plane k V d R ≃ Subbundles k V d ((testSpec k).obj (op R)),
        ∀ L, IsTildePlane (k := k) (V := V) b R L (e L)

/-- All-scheme points extend the affine comparison and give the pullback of the
corresponding subbundle along every test morphism. -/
structure SchemePoints (d : ℕ) (X : SchemeOver k)
    (affinePoints : pointsFunctor X ≅ planeFunctor k V d) where
  family : ∀ S : SchemeOver k, (S ⟶ X) ≃ Family k V d S
  family_apply : ∀ (S : SchemeOver k) (p : S ⟶ X) (R : TestAlgebra k) (a : Points S R),
    (family S p).app R a = affinePoints.hom.app R (a ≫ p)
  subbundle : ∀ S : SchemeOver k, Family k V d S ≃ Subbundles k V d S
  pullback : ∀ {T S : SchemeOver k} (f : T ⟶ S) (p : S ⟶ X),
    IsPullbackSubbundle k V f (subbundle S (family S p)) (subbundle T (family T (f ≫ p)))

def Construction : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
    (d : ℕ), d ≤ Module.finrank k V →
      ∃ (C : ChartSystem (k := k) (V := V) b d)
        (P : SchemePoints (k := k) (V := V) d C.scheme C.affinePoints),
        ∀ (R : TestAlgebra k) (p : Points C.scheme R),
          IsTildePlane (k := k) (V := V) b R (C.affinePoints.hom.app R p)
            (P.subbundle ((testSpec k).obj (op R)) (P.family ((testSpec k).obj (op R)) p))

def PlaneSplitAndRank : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (d : ℕ), d ≤ Module.finrank k V → ∀ (R : TestAlgebra k) (L : Plane k V d R),
    (∃ C : Submodule R (R ⊗[k] V), IsCompl L.toSubmodule C) ∧
      Module.Finite R L.toSubmodule ∧ Module.Projective R L.toSubmodule ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk L.toSubmodule p = d

def PlaneEndpointSubmodules : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (R : TestAlgebra k),
    (∀ L : Plane k V 0 R, L.toSubmodule = ⊥) ∧
      (∀ L : Plane k V (Module.finrank k V) R, L.toSubmodule = ⊤)

def PlaneEndpointsUnique : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (R : TestAlgebra k),
    Nonempty (Unique (Plane k V 0 R)) ∧ Nonempty (Unique (Plane k V (Module.finrank k V) R))

def Endpoints : Prop :=
  ∀ (k V ι : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V),
    (∀ C : ChartSystem (k := k) (V := V) b 0, Nonempty (IsTerminal C.scheme)) ∧
    (∀ C : ChartSystem (k := k) (V := V) b (Module.finrank k V), Nonempty (IsTerminal C.scheme))

end

end LinearAlgebraicGroups.Specs.GrassmannianCharts
