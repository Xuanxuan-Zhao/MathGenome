import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Free

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped DirectSum TensorProduct BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinearAlgebraicGroups.Specs.ProjectiveSpaces

noncomputable section

variable (k ι : Type u) [Field k]

/-- The grading of the polynomial algebra in the coordinates dual to a basis. -/
abbrev grading := MvPolynomial.homogeneousSubmodule ι k

/-- The inclusion of constants into the degree-zero part. -/
def constants : k →+* grading k ι 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C ι a⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

/-- Projective space in an indexed system of homogeneous coordinates. -/
abbrev coordinateProjectiveSpace : SchemeOver k :=
  Over.mk (Proj.toSpecZero (grading k ι) ≫ Spec.map (CommRingCat.ofHom (constants k ι)))

def CoordinateProjectiveSpaceType :=
  ∀ (k _ι : Type u) [Field k], SchemeOver k

/-- The scheme of lines in W, using the coordinates given by the finite basis of W. -/
abbrev projectiveSpace (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W] :
    SchemeOver k :=
  coordinateProjectiveSpace k (ULift.{u} (Fin (Module.finrank k W)))

def ProjectiveSpaceType :=
  ∀ (k : Type u) [Field k] (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W], SchemeOver k

def ProjectiveSpaceProper : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W],
    IsProper (projectiveSpace k W).hom

/-- The ring of the standard Proj open where the indicated coordinate is nonzero. -/
abbrev chartRing (i : ι) :=
  HomogeneousLocalization.Away (grading k ι) (MvPolynomial.X i)

abbrev coordinateOpen (i : ι) :=
  Proj.basicOpen (grading k ι) (MvPolynomial.X i)

theorem coordinate_mem_degree_one (i : ι) : MvPolynomial.X i ∈ grading k ι 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- The standard embedding of an affine chart in the ambient projective scheme. -/
abbrev chartInclusion (i : ι) : Spec (CommRingCat.of (chartRing k ι i)) ⟶
    Proj (grading k ι) :=
  Proj.awayι (grading k ι) _ (coordinate_mem_degree_one k ι i) Nat.one_pos

/-- The coordinate ratio X_j/X_i in the degree-zero localization. -/
def coordinateRatio (i j : ι) : chartRing k ι i :=
  HomogeneousLocalization.Away.mk (grading k ι) (MvPolynomial.isHomogeneous_X k i)
    1 (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X k j)

def CoordinateOpenCover : Prop :=
  ∀ (k ι : Type u) [Field k], (⨆ i, coordinateOpen k ι i) = ⊤

def CoordinateAffineCharts : Prop :=
  ∀ (k ι : Type u) [Field k] (i : ι),
    IsOpenImmersion (chartInclusion k ι i) ∧
    Set.range (chartInclusion k ι i) = (coordinateOpen k ι i : Set _)

def PolynomialChartCoordinates : Prop :=
  ∀ (k ι : Type u) [Field k] [Finite ι] (i : ι),
    ∃ e : MvPolynomial {j : ι // j ≠ i} k ≃+* chartRing k ι i,
      (∀ a, e (MvPolynomial.C a) =
        HomogeneousLocalization.fromZeroRingHom (grading k ι) _ (constants k ι a)) ∧
      ∀ j, e (MvPolynomial.X j) = coordinateRatio k ι i j.val

section LineFamilies

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- A split rank-one submodule on an affine test, with rank checked at every prime. -/
structure AffineLine (R : TestAlgebra k) where
  submodule : Submodule R (R ⊗[k] W)
  split : ∃ C, IsCompl submodule C
  finite : Module.Finite R submodule
  projective : Module.Projective R submodule
  rank_one : ∀ p : PrimeSpectrum R, Module.rankAtStalk submodule p = 1

/-- Extension of scalars for a submodule, viewed in the new ambient space. -/
def changeLineSubmodule {R T : TestAlgebra k} (a : R ⟶ T)
    (L : Submodule R (R ⊗[k] W)) : Submodule T (T ⊗[k] W) :=
  letI : Algebra R T := a.hom.toAlgebra
  letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  (L.baseChange T).map (TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W).toLinearMap

/-- A cartesian family of affine lines on the affine tests of a scheme. -/
structure LineFamily (S : SchemeOver k) where
  line : ∀ (R : TestAlgebra k), Points S R → AffineLine k W R
  compatible : ∀ {R T : TestAlgebra k} (a : R ⟶ T) (p : Points S R),
    (line T (mapPoints a p)).submodule = changeLineSubmodule k W a (line R p).submodule

/-- Base change between arbitrary test schemes acts by precomposition on affine tests. -/
def LineFamily.pullback {S T : SchemeOver k} (f : T ⟶ S) (L : LineFamily k W S) :
    LineFamily k W T where
  line R p := L.line R (p ≫ f)
  compatible a p := by simpa only [mapPoints, Category.assoc] using L.compatible a (p ≫ f)

/-- The constant vector bundle with fibre W on an arbitrary test scheme. -/
def constantBundle (S : SchemeOver k) : S.left.Modules :=
  (Scheme.Modules.pullback S.hom).obj (tilde (ModuleCat.of k W))

/-- An inclusion is locally split with source locally isomorphic to the structure sheaf. -/
def IsLocalLineInclusion {X : Scheme.{u}} {M E : X.Modules} (i : M ⟶ E) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) ∧
      ∃ r : (Scheme.Modules.pullback U.ι).obj E ⟶ (Scheme.Modules.pullback U.ι).obj M,
        (Scheme.Modules.pullback U.ι).map i ≫ r = 𝟙 _

/-- A rank-one subobject that is locally trivial and locally split in the ambient bundle. -/
def LineSubbundle (S : SchemeOver k) :=
  {L : Subobject (constantBundle k W S) // IsLocalLineInclusion L.arrow}

abbrev pullbackAmbientIso {S T : SchemeOver k} (f : T ⟶ S) :
    (Scheme.Modules.pullback f.left).obj (constantBundle k W S) ≅ constantBundle k W T :=
  ((Scheme.Modules.pullbackComp f.left S.hom) ≪≫
    Scheme.Modules.pullbackCongr (Over.w f)).app (tilde (ModuleCat.of k W))

/-- Isomorphism of the displayed pullback inclusion with the proposed line inclusion. -/
def IsPullbackLine {S T : SchemeOver k} (f : T ⟶ S)
    (L : LineSubbundle k W S) (M : LineSubbundle k W T) : Prop :=
  ∃ e : (Scheme.Modules.pullback f.left).obj (L.val : S.left.Modules) ≅
      (M.val : T.left.Modules),
    (Scheme.Modules.pullback f.left).map L.val.arrow ≫ (pullbackAmbientIso k W f).hom =
      e.hom ≫ M.val.arrow

variable [Module.Finite k W]

/-- Natural representation by the same Proj scheme on all test schemes. -/
structure LineRepresentation where
  points (S : SchemeOver k) : (S ⟶ projectiveSpace k W) ≃ LineFamily k W S
  naturality {S T : SchemeOver k} (f : T ⟶ S) (p : S ⟶ projectiveSpace k W) :
    points T (f ≫ p) = (points S p).pullback k W f

end LineFamilies

section Charts

variable {k ι : Type u} [Field k]

/-- Restricting scalars along the inclusion of constants makes a chart a k-algebra. -/
instance chartAlgebra (i : ι) : Algebra k (chartRing k ι i) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading k ι) _).comp (constants k ι)).toAlgebra

abbrev chartScheme (i : ι) : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (chartRing k ι i)))

def chartMorphism (i : ι) : chartScheme i ⟶ coordinateProjectiveSpace k ι :=
  Over.homMk (chartInclusion k ι i) (by
    change Proj.awayι (grading k ι) _ (coordinate_mem_degree_one k ι i) Nat.one_pos ≫
      (Proj.toSpecZero (grading k ι) ≫ Spec.map _) = Spec.map _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl)

end Charts

section Geometry

variable (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- The algebraic meaning of the universal line on each standard chart in a basis. -/
def BasisPointFormula (ρ : LineRepresentation k W) : Prop :=
  ∀ (ι : Type u) [Finite ι] (b : Basis ι k W),
    ∃ e : coordinateProjectiveSpace k ι ≅ projectiveSpace k W,
      ∀ (i : ι) (R : TestAlgebra k) (a : chartRing k ι i →ₐ[k] R),
        let q := (testSpec k).map (CommAlgCat.ofHom a).op ≫ chartMorphism i ≫ e.hom
        ((ρ.points _ q).line R (𝟙 _)).submodule =
          Submodule.span R (Set.singleton ((b.baseChange R).equivFun.symm
            (fun j => a (coordinateRatio k ι i j))))

/-- Under linear transport the line is taken to its actual image in the constant bundle. -/
def AutomorphismPointFormula (ρ : LineRepresentation k W)
    (transport : (W ≃ₗ[k] W) → (projectiveSpace k W ≅ projectiveSpace k W)) : Prop :=
  (transport (LinearEquiv.refl k W) = Iso.refl _) ∧
  (∀ g h, transport (g.trans h) = transport g ≪≫ transport h) ∧
  ∀ (g : W ≃ₗ[k] W) (S : SchemeOver k) (p : S ⟶ projectiveSpace k W)
      (R : TestAlgebra k) (a : Points S R),
    ((ρ.points S (p ≫ (transport g).hom)).line R a).submodule =
      ((ρ.points S p).line R a).submodule.map (g.baseChange k R W W).toLinearMap

/-- The basis and transport formulas use the same natural representation by Proj. -/
def ProjectiveSpaceLineGeometry : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W],
    ∃ (ρ : LineRepresentation k W)
      (transport : (W ≃ₗ[k] W) → (projectiveSpace k W ≅ projectiveSpace k W)),
      BasisPointFormula k W ρ ∧ AutomorphismPointFormula k W ρ transport

/-- The affine-test and sheaf descriptions describe the same subbundles,
with their base-change operations. -/
def SheafPointFormula (ρ : LineRepresentation k W) : Prop :=
  ∃ (e : ∀ S, LineFamily k W S ≃ LineSubbundle k W S)
    (c : ∀ R : TestAlgebra k, tilde (ModuleCat.of R (R ⊗[k] W)) ≅
      constantBundle k W ((testSpec k).obj (op R))),
    (∀ {S T : SchemeOver k} (f : T ⟶ S) (p : S ⟶ projectiveSpace k W),
      IsPullbackLine k W f (e S (ρ.points S p)) (e T (ρ.points T (f ≫ p)))) ∧
    ∀ (R : TestAlgebra k) (p : Points (projectiveSpace k W) R),
      let S := (testSpec k).obj (op R)
      let L := (ρ.points S p).line R (𝟙 S)
      let M := e S (ρ.points S p)
      ∃ d : tilde (ModuleCat.of R L.submodule) ≅ (M.val : S.left.Modules),
        (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom L.submodule.subtype) ≫ (c R).hom =
          d.hom ≫ M.val.arrow

end Geometry

section Segre

variable {k : Type u} [Field k]
variable {ι : Type u} [Finite ι] (W : ι → Type u)
variable [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]

/-- The finite product of the projective spaces over the base field. -/
abbrev projectiveProduct : SchemeOver k :=
  ∏ᶜ (fun i => projectiveSpace k (W i))

/-- The tensor product of the vector spaces in the finite family. -/
abbrev tensorSpace : Type u := ⨂[k] i, W i

/-- On affine tests, the Segre map takes the tensor product of the submodule inclusions. -/
def SegrePointFormula
    (ρ : ∀ i, LineRepresentation k (W i)) (τ : LineRepresentation k (tensorSpace (k := k) W))
    (σ : projectiveProduct W ⟶ projectiveSpace k (tensorSpace (k := k) W)) : Prop :=
  ∃ c : ∀ R : TestAlgebra k, (⨂[R] i, R ⊗[k] W i) ≃ₗ[R] R ⊗[k] tensorSpace (k := k) W,
    (∀ (R : TestAlgebra k) (v : ∀ i, W i),
      c R (PiTensorProduct.tprod R (fun i => (1 : R) ⊗ₜ[k] v i)) =
        (1 : R) ⊗ₜ[k] PiTensorProduct.tprod k v) ∧
    ∀ (S : SchemeOver k) (p : S ⟶ projectiveProduct W) (R : TestAlgebra k) (a : Points S R),
      let L := fun i => ((ρ i).points S (p ≫ Limits.Pi.π _ i)).line R a
      ((τ.points S (p ≫ σ)).line R a).submodule =
        (LinearMap.range (PiTensorProduct.mapIncl (fun i => (L i).submodule))).map
          (c R).toLinearMap

/-- The universal property, chart and transport formulas, and Segre embeddings
for the same projective spaces. This also includes indices of cardinality zero. -/
def ProjectiveSpaceGeometry : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (ρ : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W],
          LineRepresentation k W)
      (transport : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W],
          (W ≃ₗ[k] W) → (projectiveSpace k W ≅ projectiveSpace k W)),
      (∀ (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W],
          BasisPointFormula k W (ρ W) ∧ SheafPointFormula k W (ρ W) ∧
            AutomorphismPointFormula k W (ρ W) (transport W)) ∧
      ∀ (ι : Type u) [Finite ι] (W : ι → Type u)
        [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)],
        ∃ σ : projectiveProduct W ⟶ projectiveSpace k (tensorSpace (k := k) W),
          IsClosedImmersion σ.left ∧ SegrePointFormula W (fun i => ρ (W i)) (ρ (tensorSpace (k := k) W)) σ ∧
          ∀ g : ∀ i, W i ≃ₗ[k] W i,
            Limits.Pi.map (fun i => (transport (W i) (g i)).hom) ≫ σ =
              σ ≫ (transport (tensorSpace (k := k) W) (PiTensorProduct.congr g)).hom

end Segre

/-- A common projective line representation and its transport maps give Segre
closed immersions for all finite families, with their tensor point formulas. -/
def ProjectiveSpaceSegreGeometry : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (ρ : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W],
          LineRepresentation k W)
      (transport : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W],
          (W ≃ₗ[k] W) → (projectiveSpace k W ≅ projectiveSpace k W)),
      (∀ (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W],
          BasisPointFormula k W (ρ W) ∧ AutomorphismPointFormula k W (ρ W) (transport W)) ∧
      ∀ (ι : Type u) [Finite ι] (W : ι → Type u)
        [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)],
        ∃ σ : projectiveProduct W ⟶ projectiveSpace k (tensorSpace (k := k) W),
          IsClosedImmersion σ.left ∧ SegrePointFormula W (fun i => ρ (W i)) (ρ (tensorSpace (k := k) W)) σ ∧
          (∀ g : ∀ i, W i ≃ₗ[k] W i,
            Limits.Pi.map (fun i => (transport (W i) (g i)).hom) ≫ σ =
              σ ≫ (transport (tensorSpace (k := k) W) (PiTensorProduct.congr g)).hom) ∧
          (IsEmpty ι → IsIso σ ∧ Nonempty (tensorSpace (k := k) W ≃ₗ[k] k))

/-- On an affine test the constant bundle is the associated sheaf of the extended module. -/
def AffineConstantBundle : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] (R : TestAlgebra k),
    Nonempty (tilde (ModuleCat.of R (R ⊗[k] W)) ≅ constantBundle k W ((testSpec k).obj (op R)))

/-- A split rank-one submodule on an affine test gives its associated line subbundle. -/
def AffineLineSheafInclusion : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W],
    ∃ c : ∀ R : TestAlgebra k, tilde (ModuleCat.of R (R ⊗[k] W)) ≅
        constantBundle k W ((testSpec k).obj (op R)),
      ∀ (R : TestAlgebra k) (L : AffineLine k W R),
        let S := (testSpec k).obj (op R)
        ∃ (M : LineSubbundle k W S) (d : tilde (ModuleCat.of R L.submodule) ≅ (M.val : S.left.Modules)),
          (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom L.submodule.subtype) ≫ (c R).hom =
            d.hom ≫ M.val.arrow

/-- On an affine test every line subbundle is the associated sheaf of an affine line. -/
def AffineLineSheafReverse : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W],
    ∃ c : ∀ R : TestAlgebra k, tilde (ModuleCat.of R (R ⊗[k] W)) ≅
        constantBundle k W ((testSpec k).obj (op R)),
      ∀ (R : TestAlgebra k) (M : LineSubbundle k W ((testSpec k).obj (op R))),
        let S := (testSpec k).obj (op R)
        ∃ (L : AffineLine k W R) (d : tilde (ModuleCat.of R L.submodule) ≅ (M.val : S.left.Modules)),
          (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom L.submodule.subtype) ≫ (c R).hom =
            d.hom ≫ M.val.arrow

/-- A single coordinate in an affine projective chart, normalized by the pivot. -/
def normalizedCoordinate {ι : Type u} (p q : ι) :
    MvPolynomial {j : ι // j ≠ p} k := by
  classical
  exact if h : q = p then 1 else MvPolynomial.X ⟨q, h⟩

section SegreCharts

variable {I : Type u} [Fintype I] {J : I → Type u} (p : ∀ i, J i)

/-- Chart map for Segre, in polynomial coordinates. Its domain corresponds to the
tensor pivot and its codomain to the product of the individual pivot charts. -/
def segreChartMap :
    MvPolynomial {q : ∀ i, J i // q ≠ p} k →ₐ[k]
      MvPolynomial (Σ i, {j : J i // j ≠ p i}) k :=
  MvPolynomial.aeval fun q => ∏ i,
    MvPolynomial.rename (Sigma.mk i) (normalizedCoordinate k (p i) (q.val i))

def SegreChartSurjective : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] (J : I → Type u) (p : ∀ i, J i),
    Function.Surjective (segreChartMap k p)

end SegreCharts

section SegreBaseChange

variable {I : Type u} [Fintype I] (W : I → Type u)
variable [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]

def TensorBaseChange : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] (W : I → Type u)
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]
    (R : TestAlgebra k),
    ∃ c : (⨂[R] i, R ⊗[k] W i) ≃ₗ[R] R ⊗[k] tensorSpace (k := k) W,
      ∀ (r : I → R) (v : ∀ i, W i),
        c (PiTensorProduct.tprod R (fun i => r i ⊗ₜ[k] v i)) =
          (∏ i, r i) ⊗ₜ[k] PiTensorProduct.tprod k v

end SegreBaseChange

section AffinePivot

variable (k : Type u) [Field k]
variable {ι W : Type u} [Finite ι] [AddCommGroup W] [Module k W]
variable (b : Basis ι k W) (i : ι) (R : TestAlgebra k)

/-- Lines for which projection onto the pivot coordinate is an isomorphism. -/
def AffinePivotLine :=
  {L : AffineLine k W R //
    Function.Bijective ((b.baseChange R).coord i ∘ L.submodule.subtype)}

/-- A pivot chart records a unique generator with pivot coordinate equal to one. -/
def AffinePivotNormalForm : Prop :=
  ∀ (k ι W : Type u) [Field k] [Finite ι] [AddCommGroup W] [Module k W]
      (b : Basis ι k W) (i : ι) (R : TestAlgebra k),
    ∃ e : {v : R ⊗[k] W // (b.baseChange R).coord i v = 1} ≃ AffinePivotLine k b i R,
      ∀ v, (e v).val.submodule = Submodule.span R (Set.singleton (v : R ⊗[k] W))

/-- The same affine chart of Proj represents the normalized affine lines. -/
def AffinePivotCoordinates : Prop :=
  ∀ (k ι W : Type u) [Field k] [Finite ι] [AddCommGroup W] [Module k W]
      (b : Basis ι k W) (i : ι) (R : TestAlgebra k),
    ∃ e : (chartRing k ι i →ₐ[k] R) ≃ AffinePivotLine k b i R,
      ∀ a, (e a).val.submodule = Submodule.span R
        (Set.singleton ((b.baseChange R).equivFun.symm (fun j => a (coordinateRatio k ι i j))))

end AffinePivot

/-- The projective scheme of a one-dimensional vector space is the base point. -/
def OneDimensionalProjectiveSpace : Prop :=
  ∀ (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W],
    Module.finrank k W = 1 → IsProper (projectiveSpace k W).hom ∧
      IsIso (projectiveSpace k W).hom

/-- With no factors the source is the terminal k-scheme. The tensor of the empty
family is the unit k, and the Segre embedding is the unique isomorphism of points. -/
def EmptySegre : Prop :=
  ∀ (k I : Type u) [Field k] [IsEmpty I] (W : I → Type u)
      [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)],
    ∃ e : projectiveProduct (k := k) W ≅ projectiveSpace k (tensorSpace (k := k) W),
      IsClosedImmersion e.hom.left ∧ Nonempty (tensorSpace (k := k) W ≃ₗ[k] k)

section ChartOverlaps

/-- The coordinates in which two projective opens overlap. -/
abbrev overlapRing (i j : ι) :=
  HomogeneousLocalization.Away (grading k ι) (MvPolynomial.X i * MvPolynomial.X j)

abbrev overlapFromFirst (i j : ι) : chartRing k ι i →+* overlapRing k ι i j :=
  HomogeneousLocalization.awayMap (grading k ι) (coordinate_mem_degree_one k ι j) rfl

abbrev overlapFromSecond (i j : ι) : chartRing k ι j →+* overlapRing k ι i j :=
  HomogeneousLocalization.awayMap (grading k ι) (coordinate_mem_degree_one k ι i) (mul_comm _ _)

def CoordinateOverlap : Prop :=
  ∀ (k ι : Type u) [Field k] (i j : ι),
    chartInclusion k ι i ⁻¹ᵁ coordinateOpen k ι j =
      PrimeSpectrum.basicOpen (coordinateRatio k ι i j)

def CoordinateTransition : Prop :=
  ∀ (k ι : Type u) [Field k] (i j l : ι),
    overlapFromFirst k ι i j (coordinateRatio k ι i l) =
      overlapFromSecond k ι i j (coordinateRatio k ι j l) *
        overlapFromFirst k ι i j (coordinateRatio k ι i j)

end ChartOverlaps

end

end LinearAlgebraicGroups.Specs.ProjectiveSpaces
