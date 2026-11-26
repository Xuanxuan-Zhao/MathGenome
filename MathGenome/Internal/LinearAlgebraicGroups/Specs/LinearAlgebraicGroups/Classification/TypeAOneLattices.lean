import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.TypeAOneLattices

open StandardGroups GeneralLinearCentralIsogeny CentralDerived
open GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open Unipotent (Index)
open AdjointCocharacters (IsAdjointQuotient)
open CentralTorus (IsSchemeCentre)
open GeometricRadicals (IsReductive)
open QuotientEmbedding (Presentation)
open HomogeneousQuotient (IsQuotientTorsor)
open CentralIsogenies (IsCentralIsogeny)
open SmoothnessAndIsogenies (rootsOfUnityCoordinates)
open DiagonalizableGroups (rootsOfUnityPoints)

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}
variable {G S M : AffineAlgebraicGroup k}

/-- The scalar quotient of the standard matrix group and its determinant-one map. -/
structure ScalarQuotient (g : MatrixPoints G n) (s : SpecialMatrixPoints S n)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k) where
  Z : ClosedSubgroup G.val
  scalarIso : M.val ≅ Z.group
  scalar_eq : ∀ (R : TestAlgebra k) (z : Points M.val.X R),
    g.hom.app R (pointMap (scalarIso.hom ≫ Z.inclusion) R z) =
      Matrix.GeneralLinearGroup.scalar (Index.{u} n) (a.hom.app R z)
  P : AffineAlgebraicGroup k
  q : G.val ⟶ P.val
  adjoint : IsAdjointQuotient Z q
  smooth : Smooth q.hom.hom.left
  reductive : IsReductive P
  presentation : Presentation Z
  torsor : IsQuotientTorsor presentation
  iso : presentation.scheme ≅ P.val.X
  projection_eq : presentation.projection ≫ iso.hom = q.hom.hom
  f : S.val ⟶ G.val
  f_eq : ∀ (R : TestAlgebra k) (x : Points S.val.X R),
    g.hom.app R (pointMap f R x) = Matrix.SpecialLinearGroup.toGL (s.hom.app R x)

variable {g : MatrixPoints G n} {s : SpecialMatrixPoints S n}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

abbrev ScalarQuotient.map (Q : ScalarQuotient g s a) := Q.f ≫ Q.q

/-- Scalar multiplication is the pullback of the determinant-one map
along the scalar quotient cover. The determinant-root algebra gives its finite free fibre. -/
def ScalarRescaling (Q : ScalarQuotient g s a) : Prop :=
  ∃ (T : ClosedSubgroup Q.Z.group), IsIso T.inclusion ∧
  ∃ m : (T.group ⊗ S.val) ⟶ G.val,
    IsPullback (secondProjection T.group S.val).hom.hom m.hom.hom
      Q.map.hom.hom Q.q.hom.hom ∧
    Flat m.hom.hom.left ∧ Surjective m.hom.hom.left ∧
    (∀ (R : TestAlgebra k) (z : Points (T.group ⊗ S.val).X R),
      g.hom.app R (pointMap m R z) =
        Matrix.GeneralLinearGroup.scalar (Index.{u} n)
          (a.hom.app R (pointMap (firstProjection T.group S.val ≫ T.inclusion ≫ Q.scalarIso.inv) R z)) *
        Matrix.SpecialLinearGroup.toGL
          (s.hom.app R (pointMap (secondProjection T.group S.val) R z))) ∧
    ∀ (R : TestAlgebra k) (x : Points G.val.X R),
      let d := Matrix.GeneralLinearGroup.det (g.hom.app R x)
      let B := determinantRootTestAlgebra R n d
      let b := determinantRootMap R n d
      Module.Free R (determinantRootAlgebra R n d) ∧
      Module.Finite R (determinantRootAlgebra R n d) ∧
      Module.FaithfullyFlat R (determinantRootAlgebra R n d) ∧
      ∃ (z : Bˣ) (v : Points (T.group ⊗ S.val).X B),
        (z : B) = AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (d : R)) ∧
        z ^ n = Units.map b.hom.toMonoidHom d ∧
        a.hom.app B (pointMap (firstProjection T.group S.val ≫ T.inclusion ≫ Q.scalarIso.inv) B v) = z ∧
        Matrix.SpecialLinearGroup.toGL
          (s.hom.app B (pointMap (secondProjection T.group S.val) B v)) =
            Matrix.GeneralLinearGroup.scalar (Index.{u} n) z⁻¹ *
              Matrix.GeneralLinearGroup.map b.hom.toRingHom (g.hom.app R x) ∧
        pointMap m B v = mapPoints b x ∧
        IsPullback v ((testSpec k).map b.op) m.hom.hom x

/-- Identification of the scheme kernel, with its scalar inclusion on all test rings. -/
def ScalarKernel (Q : ScalarQuotient g s a) : Prop :=
  ∃ (N : ClosedSubgroup S.val) (e : N.group ≅ specGroup (rootsOfUnityCoordinates k n))
    (r : (groupPointsFunctor k).obj (specGroup (rootsOfUnityCoordinates k n)) ≅
      rootsOfUnityPoints k n),
    IsSchemeKernel Q.map N ∧ IsFinite N.group.X.hom ∧ IsSchemeCentre N ∧
    (∀ (R : TestAlgebra k)
        (φ : MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod n))) →ₐ[k] R)
        (x : Points (specGroup (rootsOfUnityCoordinates k n)).X R),
      x.left = Spec.map (CommRingCat.ofHom φ.toRingHom) →
      ((r.hom.app R x).val : R) = φ (MonoidAlgebra.single ⟨Multiplicative.ofAdd 1⟩ 1)) ∧
    (∀ (R : TestAlgebra k) (x : Points N.group.X R),
      Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
        Matrix.GeneralLinearGroup.scalar (Index.{u} n) (((groupPointsFunctor k).mapIso e ≪≫ r).hom.app R x).val) ∧
    ∀ (p : ℕ) [CharP k p], 0 < p → p ∣ n → ¬ Smooth N.group.X.hom ∧ ¬ Etale N.group.X.hom

def MatrixProjectiveIsogeny : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
    ∀ (G S M : AffineAlgebraicGroup k) (g : MatrixPoints G n) (s : SpecialMatrixPoints S n)
      (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k),
      ∃ Q : ScalarQuotient g s a,
        IsCentralIsogeny Q.map ∧ ScalarKernel Q ∧ ScalarRescaling Q

/-- The scalar matrices in the tangent space of the matrix group. -/
def scalarLine (k : Type u) [Field k] (n : ℕ) :
    Submodule k (Matrix (Index.{u} n) (Index.{u} n) k) :=
  k ∙ (1 : Matrix (Index.{u} n) (Index.{u} n) k)

section Lie
variable {g₂ : MatrixPoints G 2} {s₂ : SpecialMatrixPoints S 2}

/-- Dual-number lifts through the scalar quotient, and the resulting Lie quotient
with the class map from both GL₂ and SL₂. -/
def ProjectiveLieComparison : Prop :=
  ∀ (k : Type u) [Field k] (G S M : AffineAlgebraicGroup k)
    (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (Q : ScalarQuotient g s a) (b : IdentityLieStructure Q.P.val),
    letI := b.lieRing
    letI := b.lieAlgebra
    Function.Surjective (mapPointKernel Q.q) ∧
    (∀ (x : Lie k G.val) (i j : Index.{u} 2),
      (g.hom.app (CommAlgCat.of k (DualNumber k)) x.toMul.val).val i j =
        ((1 : Matrix (Index.{u} 2) (Index.{u} 2) k) i j, glTangentCoefficient g x i j)) ∧
    (∀ x y : Lie k G.val, mapPointKernel Q.q y = mapPointKernel Q.q x ↔
      ∃ z : Lie k M.val, y = mapPointKernel (Q.scalarIso.hom ≫ Q.Z.inclusion) z + x) ∧
    ∃ e : Lie k Q.P.val ≃ₗ[k] (Matrix (Index.{u} 2) (Index.{u} 2) k ⧸ scalarLine k 2),
      (∀ x, e (mapPointKernel Q.q x) = (scalarLine k 2).mkQ (glTangentCoefficient g x)) ∧
      (∀ x, e (mapPointKernel Q.map x) = (scalarLine k 2).mkQ (slTangentCoefficient s x)) ∧
      ∀ x y, e ⁅mapPointKernel Q.q x, mapPointKernel Q.q y⁆ =
        (scalarLine k 2).mkQ (glTangentCoefficient g x * glTangentCoefficient g y -
          glTangentCoefficient g y * glTangentCoefficient g x)

/-- In characteristic two the kernel is precisely the scalar line,
and the actual μ₂ kernel accounts for the whole line. -/
def ProjectiveLieKernelInCharacteristicTwo : Prop :=
  ∀ (k : Type u) [Field k] [CharP k 2] (G S M : AffineAlgebraicGroup k)
    (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (Q : ScalarQuotient g s a), ScalarKernel Q →
      (∀ x, mapPointKernel Q.map x = 0 ↔
        slTangentCoefficient s x ∈ scalarLine k 2) ∧
      ∃ (N : ClosedSubgroup S.val) (_ : N.group ≅ specGroup (rootsOfUnityCoordinates k 2)),
        IsSchemeKernel Q.map N ∧ ∀ (b : IdentityLieStructure N.group),
          letI := b.lieRing
          letI := b.lieAlgebra
          ∃ e : Lie k N.group ≃ₗ[k] k, ∀ z,
            slTangentCoefficient s (mapPointKernel N.inclusion z) = e z • 1

end Lie
section Tori

open RankOneFlag (IsGeometricallyMaximal)
open GeometricRadicals (IsSplitTorus)
open GeneralLinearStructure (IsDiagonal)
open SpecialLinearDatum (DiagonalTorus)
open CentralIsogenies (IsTorusRestriction)

abbrev firstIndex : Index.{u} 2 := ⟨0⟩
abbrev lastIndex : Index.{u} 2 := ⟨1⟩

variable {g₂ : MatrixPoints G 2} {s₂ : SpecialMatrixPoints S 2}

/-- The ratio torus is the closed image of the actual diagonal of GL₂,
and the full inverse image of the ratio torus is that diagonal. -/
structure RatioTorus (Q : ScalarQuotient g₂ s₂ a) where
  diagonal : ClosedSubgroup G.val
  diagonal_points : ∀ (R : TestAlgebra k) (x : Points G.val.X R),
    x ∈ SubgroupSections diagonal ((testSpec k).obj (Opposite.op R)) ↔ IsDiagonal (g₂.hom.app R x)
  diagonal_maximal : IsGeometricallyMaximal diagonal
  subgroup : ClosedSubgroup Q.P.val
  split : IsSplitTorus subgroup.group
  maximal : IsGeometricallyMaximal subgroup
  coordinate : subgroup.group ≅ M.val
  ratio : diagonal.group ⟶ subgroup.group
  pullback : IsPullback diagonal.inclusion.hom.hom ratio.hom.hom Q.q.hom.hom subgroup.inclusion.hom.hom
  ratio_eq : ∀ (R : TestAlgebra k) (x : Points diagonal.group.X R),
    let A := (g₂.hom.app R (pointMap diagonal.inclusion R x)).val
    let z : Rˣ := a.hom.app R (pointMap (ratio ≫ coordinate.hom) R x)
    (z : R) * A lastIndex lastIndex = A firstIndex firstIndex

def ProjectiveRatioTorus : Prop :=
  ∀ (k : Type u) [Field k] (G S M : AffineAlgebraicGroup k)
    (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (Q : ScalarQuotient g s a), Nonempty (RatioTorus Q)

/-- On the determinant-one diagonal, the projective torus map is the fppf square map. -/
def RankOneTorusRestriction : Prop :=
  ∀ (k : Type u) [Field k] (G S M : AffineAlgebraicGroup k)
    (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (Q : ScalarQuotient g s a) (U : RatioTorus Q) (T : DiagonalTorus s),
    ∃ p : T.subgroup.group ⟶ U.subgroup.group,
      IsTorusRestriction Q.map p ∧ LocallyOfFinitePresentation p.hom.hom.left ∧
      ∀ (R : TestAlgebra k) (x : Points T.subgroup.group.X R),
        a.hom.app R (pointMap (p ≫ U.coordinate.hom) R x) =
          (SpecialLinearDatum.determinantOneUnits (T.pointsIso.hom.app R x) firstIndex) ^ 2


open CharacterDescent (Character Cocharacter)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open CharacterPairing (powerMorphism pairing)
open AbstractPairing (Root)
open AbstractPairing (IsAttachedCoroot)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- An identification with the rank-one split torus marks dual generators.
Writing them as morphisms gives the usual powers in the two lattices. -/
def DualGenerators {T : GroupScheme k}
    (e : specGroup (groupAlgebra k IntegerCharacters.{u}) ≅ T) : Prop :=
  pairing T e.inv e.hom = 1 ∧
    (∀ χ : Character T, ∃! i : ℤ, χ = e.inv ≫ powerMorphism i) ∧
    (∀ y : Cocharacter T, ∃! j : ℤ, y = powerMorphism j ≫ e.hom)

/-- The marked root and coroot pairs of the two determinant-one and projective diagonals. -/
def RankOneLatticeComparison : Prop :=
  ∀ (k : Type u) [Field k] (G S M : AffineAlgebraicGroup k)
    (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (Q : ScalarQuotient g s a) (U : RatioTorus Q), IsCentralIsogeny Q.map →
    ∃ (T : DiagonalTorus s) (p : T.subgroup.group ⟶ U.subgroup.group)
      (eS : specGroup (groupAlgebra k IntegerCharacters.{u}) ≅ T.subgroup.group)
      (eP : specGroup (groupAlgebra k IntegerCharacters.{u}) ≅ U.subgroup.group),
      GeometricRadicals.IsSplitReductive S ∧ GeometricRadicals.IsSplitReductive Q.P ∧
      IsGeometricallyMaximal T.subgroup ∧ IsTorusRestriction Q.map p ∧
      LocallyOfFinitePresentation p.hom.hom.left ∧
      DualGenerators eS ∧ DualGenerators eP ∧
      (∀ (R : TestAlgebra k) (t : Rˣ),
        (s.hom.app R (pointMap T.subgroup.inclusion R (cocharacterPoint eS.hom R t))).val =
          Matrix.diagonal (fun i => ((if i = firstIndex then t else t⁻¹ : Rˣ) : R))) ∧
      (∀ (R : TestAlgebra k) (t : Rˣ),
        a.hom.app R (pointMap U.coordinate.hom R (cocharacterPoint eP.hom R t)) = t) ∧
      p ≫ eP.inv = eS.inv ≫ powerMorphism 2 ∧
      eS.hom ≫ p = powerMorphism 2 ≫ eP.hom ∧
      (∀ j : ℤ, j = 1 ∨ j = -1 →
        ∃ (α : Root T.subgroup) (β : Root U.subgroup),
          α.val = eS.inv ≫ powerMorphism (2 * j) ∧
          β.val = eP.inv ≫ powerMorphism j ∧
          IsAttachedCoroot T.subgroup α (powerMorphism j ≫ eS.hom) ∧
          IsAttachedCoroot U.subgroup β (powerMorphism (2 * j) ≫ eP.hom)) ∧
      (∀ α : Root T.subgroup, ∃ j : ℤ, (j = 1 ∨ j = -1) ∧
        α.val = eS.inv ≫ powerMorphism (2 * j)) ∧
      (∀ β : Root U.subgroup, ∃ j : ℤ, (j = 1 ∨ j = -1) ∧
        β.val = eP.inv ≫ powerMorphism j)


end Tori

end
end LinearAlgebraicGroups.Specs.TypeAOneLattices
