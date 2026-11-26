import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceReduction

open CategoryTheory ValuativeRel WithZero
open scoped CategoryTheory.MonObj TensorProduct WithZero
open ExceptionalAffineBruhat (FieldPoints scalarPoints RamifiedReference DiagramCompositum FoldedApartment FoldedLevel)
open ExceptionalAffineBuilding (Building Weights rationalPoint simplexPoint)
open ExceptionalIwahoriCongruence (integralRing)
open ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open ExceptionalValuedTorusNormalizer (invariantApartment valuationRingInclusion)
open IntegralSemisimpleModel (Model integerAlgebra IntegralPoints integralPointFunctor torusPoint cocharacter)
open Pinning (BasedRootDatum)

universe u

attribute [local instance] integerAlgebra ExceptionalLocalRootCoordinates.canonicalExtension

/-- Scaling on the marked Iwahori at a single finite coefficient level.
The auxiliary extension and integral homomorphism use the same chosen
uniformizer root as the torus point in the field-point identity. -/
def RamifiedIwahoriScaling : Prop :=
  ∀ {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M) (σ : Gal(L/F))
    (T : DiagramCompositum F L k σ) (A : FoldedApartment (R.diagram σ))
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (B : Building X.comparison)
    (t : Weights (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)),
    rationalPoint B.realization.coordinates x = simplexPoint B.realization.coordinates B.realization.vertex t →
    ∀ (π : Lˣ), normalizedValuation L (π : L) = exp (-1) →
    ∃ (d : ℕ) (y : D.Y), 0 < d ∧
      (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y ∧
      ∃ (E : Type u) (hE : Field E), letI := hE
        ∃ (aE : Algebra T.field E) (vE : ValuativeRel E) (tE : TopologicalSpace E),
          letI := aE; letI := vE; letI := tE
          ∃ (_ : IsNonarchimedeanLocalField E) (_ : ValuativeExtension T.field E)
            (_ : FiniteDimensional T.field E) (ξ : Eˣ),
            Module.finrank T.field E = d ∧
            (ξ : E) ^ d = algebraMap T.field E (algebraMap L T.field (π : L)) ∧
            Function.Bijective (residueMap T.field E) ∧
            ∃ s : X.comparison.I →* IntegralPoints M.group (integralRing (valuation E).valuationSubring),
              ∀ g : X.comparison.I,
                let p : FieldPoints M E :=
                  torusPoint D (integralRing E) (cocharacter D y (integralRing E) ξ) ≫ M.torus.hom.hom
                ((integralPointFunctor M.group).map (valuationRingInclusion E)).hom (s g) =
                  MulAut.conj p (scalarPoints M (algebraMap T.field E) (X.points g))

noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

open RamifiedExceptionalAuxiliaryTower (UnramifiedLevel AuxiliaryTower)
open RamifiedExceptionalLocalFaceCoordinates (AuxiliaryExtension MarkedLevel ScaledParahoric
  LocalReductionCoordinates InvariantTorusValues rootResiduePoint)

open AlgebraicGeometry IsLocalRing
open scoped Classical Pointwise
open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat (coefficientPoints residue IsUnramifiedLocalExtension)
open ExceptionalAffineBuilding (IsBarycenter cotype parahoric standardWallSubgroup)
open ExceptionalAffineRootSystems (FoldedRootDirection IsLongF4Doubled threshold)
open ExceptionalIwahoriCongruence (CellValues cellValue changeRingHom integralRingMap)
open ExceptionalIwahoriImageComparison (residueReduction)
open ExceptionalMarkedRootDescent (wallMatrix)
open IntegralRootRelations (upper lower)
open IntegralSemisimpleModel (Integers TorusValues fibre forgetFibrePoint)
open OrderedRootProducts (Enumerates)

local notation "Oᵥ[" K "]" => Valuation.valuationSubring (valuation K)
local notation "kᵥ[" K "]" => ExceptionalAffineBruhat.residue K

/-- Turn the chosen uniformizer-root field of the tower into the valued
extension used by the single-level point comparison. -/
def localAuxiliary {K : Type u} [Field K] [ValuativeRel K] {d : ℕ} {π : K}
    (U : RamifiedExceptionalAuxiliaryTower.UniformizerRootExtension K d π) :
    AuxiliaryExtension K d π where
  field := U.field
  root := U.root
  power := U.power
  residue_bijective := U.residue_bijective

section GeometricImage

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}

variable (X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field)

/-- The finite Weyl subgroup attached to the face by the actual comparison. -/
abbrev faceWeylGroup {k : UnramifiedLevel F S}
    (J : Set (A.roots.SimpleWall A.basepoint)) :=
  standardWallSubgroup (X k).folded.comparison.coxeter.coxeter J

/-- The map on a standard face induced by the inclusion of coefficient fields. -/
def faceInclusion {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (J : Set (A.roots.SimpleWall A.basepoint))
    (he : ((X k').parahoric J).comap
      (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)) = (X k).parahoric J) :
    (X k).parahoric J →* (X k').parahoric J :=
  ((coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)).comp
    ((X k).parahoric J).subtype).codRestrict _ (fun g =>
      show g.val ∈ ((X k').parahoric J).comap
        (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)) from
      Eq.mpr (congrArg (fun U => g.val ∈ U) he) g.property)

/-- The scaled copies of the same actual face, linked by coefficient inclusion
and by the valued maps of the common auxiliary extension. -/
structure ScaledParahoricTower (J : Set (A.roots.SimpleWall A.basepoint))
    (π : Lˣ) (d : ℕ) (y : D.Y) where
  auxiliary : AuxiliaryTower (fun k => (X k).compositum) d (π : L)
  auxiliary_valued : auxiliary.ValuedCompatibility
  scale (k : UnramifiedLevel F S) :
    ScaledParahoric (X k) J π d y (localAuxiliary (auxiliary.extension k))
  iwahori_comap {k k' : UnramifiedLevel F S} (h : k ≤ k') :
    (X k').folded.comparison.I.comap
      (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)) =
      (X k).folded.comparison.I
  lift_compare {k k' : UnramifiedLevel F S} (h : k ≤ k') (w : A.roots.affineWeylGroup) :
    coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)
        ((X k).folded.comparison.lift w).val *
      ((X k').folded.comparison.lift w).val⁻¹ ∈ (X k').folded.comparison.T₀
  face_comap {k k' : UnramifiedLevel F S} (h : k ≤ k') :
    ((X k').parahoric J).comap
      (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)) =
      (X k).parahoric J
  integral_compare {k k' : UnramifiedLevel F S} (h : k ≤ k') (g : (X k).parahoric J) :
    (scale k').integral (faceInclusion X h J (face_comap h) g) = changeRingHom M.group
      (integralRingMap (auxiliary.transition h).valued.integers) ((scale k).integral g)
  reduction_compare {k k' : UnramifiedLevel F S} (h : k ≤ k') (g : (X k).parahoric J) :
    (scale k').reduction (faceInclusion X h J (face_comap h) g) =
      scalarPoints M (auxiliary.transition h).valued.residue ((scale k).reduction g)

variable {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)

abbrev ScaledParahoricTower.geometricReduction (k : UnramifiedLevel F S) :
    (X k).parahoric J →* FieldPoints M (AlgebraicClosure kᵥ[F]) :=
  (scalarPoints M (P.auxiliary.residueEmbedding k)).comp (P.scale k).reduction

/-- Image of subsets of the actual face subgroups in the common geometric
special fibre, via the compatible reductions and residue embeddings. -/
def ScaledParahoricTower.geometricImage
    (U : ∀ k : UnramifiedLevel F S,
      Set (GroupPoints R.descent.group.val (CommAlgCat.of F k.field))) :
    Set (FieldPoints M (AlgebraicClosure kᵥ[F])) :=
  ⋃ k, P.geometricReduction k '' ((↑) ⁻¹' U k : Set ((X k).parahoric J))

abbrev ScaledParahoricTower.parahoricImage :=
  P.geometricImage (fun _ => Set.univ)

abbrev ScaledParahoricTower.iwahoriImage :=
  P.geometricImage (fun k => ((X k).folded.comparison.I : Set _))

abbrev ScaledParahoricTower.torusImage :=
  P.geometricImage (fun k => ((X k).folded.comparison.T₀ : Set _))

abbrev ScaledParahoricTower.rootImage (a : FoldedRootDirection × ℤ) :=
  P.geometricImage (fun k => (X k).rootLayer a)

abbrev residueGroup (M : Model D) (κ : Type u) [Field κ] := (fibre κ).obj M.group

/-- Geometric image of a homomorphism defined over the original residue field. -/
def geometricImageOfHom {κ : Type u} [Field κ] {H : GroupScheme κ}
    (M : Model D) (f : H ⟶ residueGroup M κ) : Set (FieldPoints M (AlgebraicClosure κ)) :=
  Set.range fun s : GroupPoints H (CommAlgCat.of κ (AlgebraicClosure κ)) =>
    forgetFibrePoint M.group (CommAlgCat.of κ (AlgebraicClosure κ)) (s ≫ f.hom.hom)

/-- A morphism from a finite-type residue parameter scheme to the
marked split residue group. -/
structure ResidueParameterMap (M : Model D) (κ : Type u) [Field κ] where
  source : SchemeOver κ
  locallyFiniteType : LocallyOfFiniteType source.hom
  quasiCompact : QuasiCompact source.hom
  morphism : source ⟶ (residueGroup M κ).X

def ResidueParameterMap.geometricImage {κ : Type u} [Field κ] (f : ResidueParameterMap M κ) :
    Set (FieldPoints M (AlgebraicClosure κ)) :=
  Set.range fun s : Points f.source (CommAlgCat.of κ (AlgebraicClosure κ)) =>
    forgetFibrePoint M.group (CommAlgCat.of κ (AlgebraicClosure κ)) (s ≫ f.morphism)

/-- An Iwahori direction survives when its initial depth scales to zero. -/
def survivingIwahoriRoots (A : FoldedApartment (R.diagram σ))
    (x : invariantApartment D (R.diagram σ)) : Set (FoldedRootDirection × ℤ) :=
  {a | a.2 = threshold (A.roots.root a.1 A.basepoint) ∧ A.roots.wallValue a x = 0}

/-- The surviving Iwahori directions and the two signs for the wall words. -/
def residueRootDirections (A : FoldedApartment (R.diagram σ))
    (J : Set (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)) :
    Set (FoldedRootDirection × ℤ) :=
  survivingIwahoriRoots A x ∪
    ⋃ w ∈ J, {w.val, A.roots.opposite w.val}

/-- All geometric images are those of the actual scaled subgroups.
The morphisms over the original residue field use these same images. -/
structure GeometricReduction (ϖ : Fˣ) (x : invariantApartment D (R.diagram σ)) where
  localCoordinates : ∀ k, LocalReductionCoordinates (P.scale k) ϖ x
  iwahori_root (k : UnramifiedLevel F S) (a : survivingIwahoriRoots A x) :
    (X k).rootLayer a.val ⊆ (X k).folded.comparison.I ∧
    (P.scale k).image ((X k).rootLayer a.val) =
      Set.range (rootResiduePoint (X k) ϖ π a.val ((localCoordinates k).leading a.val)
        (residueMap (X k).compositum.field (P.auxiliary.extension k).field))
  torus : GroupScheme kᵥ[F]
  torus_split : GeometricRadicals.IsSplitTorus torus
  torus_connected : GeometricallyConnected torus.X.hom
  torus_finite_type : LocallyOfFiniteType torus.X.hom
  torus_quasiCompact : QuasiCompact torus.X.hom
  torusMap : torus ⟶ residueGroup M kᵥ[F]
  torus_image : geometricImageOfHom M torusMap = P.torusImage
  torus_coordinates :
    P.torusImage = Set.range (fun t : InvariantTorusValues (R.diagram σ) (AlgebraicClosure kᵥ[F]) =>
      (show FieldPoints M (AlgebraicClosure kᵥ[F]) from
        torusPoint D (integralRing (AlgebraicClosure kᵥ[F])) t.val ≫ M.torus.hom.hom))
  root_connected : GeometricallyConnected (((fibre kᵥ[F]).obj M.line.group).X.hom)
  rootMaps : residueRootDirections A J x →
    ((fibre kᵥ[F]).obj M.line.group ⟶ residueGroup M kᵥ[F])
  root_image (a : residueRootDirections A J x) :
    geometricImageOfHom M (rootMaps a) = P.rootImage a.val
  iwahori_product :
    ∃ (negative positive : List (FoldedRootDirection × ℤ)),
      Enumerates negative {a ∈ survivingIwahoriRoots A x |
        ¬ ∃ i, A.direction i = a.1 ∧ D.base.IsPos i} ∧
      Enumerates positive {a ∈ survivingIwahoriRoots A x |
        ∃ i, A.direction i = a.1 ∧ D.base.IsPos i} ∧
      P.iwahoriImage = (negative.map P.rootImage).prod * P.torusImage * (positive.map P.rootImage).prod
  iwahoriMap : ResidueParameterMap M kᵥ[F]
  iwahori_image : iwahoriMap.geometricImage = P.iwahoriImage
  wall_reduction (k : UnramifiedLevel F S) (a : A.roots.SimpleWall A.basepoint) (ha : a ∈ J)
    (h : (X k).wallLift a ∈ (X k).parahoric J) :
    P.geometricReduction k ⟨(X k).wallLift a, h⟩ ∈
      Subgroup.closure (P.rootImage a.val ∪ P.rootImage (A.roots.opposite a.val))
  generation :
    P.parahoricImage = (Subgroup.closure (P.torusImage ∪
      ⋃ a : residueRootDirections A J x, P.rootImage a.val) : Set _)
  finiteWeylGroup : Finite (faceWeylGroup X (k := P.auxiliary.base) J)
  doubleCosetMap : faceWeylGroup X (k := P.auxiliary.base) J → ResidueParameterMap M kᵥ[F]
  double_coset (w : faceWeylGroup X (k := P.auxiliary.base) J) :
    ∃ (n : (X P.auxiliary.base).parahoric J) (g : FieldPoints M kᵥ[F]),
      n.val = ((X P.auxiliary.base).folded.comparison.lift w.val).val ∧
      scalarPoints M (algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F])) g = P.geometricReduction P.auxiliary.base n ∧
      (doubleCosetMap w).geometricImage =
        P.iwahoriImage * {P.geometricReduction P.auxiliary.base n} * P.iwahoriImage
  finite_image :
    P.parahoricImage = ⋃ w, (doubleCosetMap w).geometricImage
  lift_finite {Index : Type u} [Finite Index]
      (z : Index → FieldPoints M (AlgebraicClosure kᵥ[F])) :
    (∀ i, z i ∈ P.parahoricImage) →
    ∃ (k : UnramifiedLevel F S) (g : Index → (X k).parahoric J),
      ∀ i, P.geometricReduction k (g i) = z i

end GeometricImage

/-- The scaled reduction of the actual adjoint standard face in the
ramified outer comparison, at the given rational barycenter and over
its finite unramified enlargements. -/
def RamifiedParahoricScaling : Prop :=
  ∀ {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [FiniteDimensional F L] [IsGalois F L] [IsSepClosed S] [Algebra.IsSeparable F S]
    (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 →
    1 < ExceptionalLocalRootCoordinates.ramificationIndex F L →
    ∀ {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
      (numbering : Fin 6 ≃ D.base.support),
    ExceptionalAffineBruhat.ExceptionalNumbering D 6 numbering →
    D.datum.rootSpan ℤ = ⊤ →
    (∀ i, (R.diagram σ).val.indexEquiv (numbering i) =
      numbering (ExceptionalAffineRootSystems.e6Partner i)) →
    ∀ (A : FoldedApartment (R.diagram σ))
      (X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field)
      (k₀ : UnramifiedLevel F S)
      (t : Weights (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)),
    let B := (X k₀).building
    IsBarycenter (cotype t) t →
    rationalPoint B.realization.coordinates x = simplexPoint B.realization.coordinates B.realization.vertex t →
    ∀ (π : Lˣ), normalizedValuation L (π : L) = exp (-1) →
    let J := cotype t
    J = {a | A.roots.wallValue a.val x = 0} ∧ Function.Bijective (residueMap F L) ∧
    ∃ (ϖ : Fˣ) (d : ℕ) (y : D.Y), normalizedValuation F (ϖ : F) = exp (-1) ∧
      0 < d ∧ (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y ∧
      ∃ P : ScaledParahoricTower X J π d y, Nonempty (GeometricReduction P ϖ x)

end

end LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceReduction
