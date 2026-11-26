import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AutomorphismScheme
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.PeirceFrames
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SchemeCentre

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u v

namespace LinearAlgebraicGroups.Composition.OctonionAutomorphismSpecification

open Specification
open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open LinearAlgebraicGroups.Specs
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots characterValue)
open GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeCentre (rootLattice)

noncomputable section

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C]

/-- The multiplication and the unit used by the bilinear automorphism functor. -/
def octonionAlgebra : BilinearAlgebra R C where
  product := LinearMap.mul R C
  unit := some 1
  unit_mul := by rintro _ ⟨⟩; exact one_mul
  mul_unit := by rintro _ ⟨⟩; exact mul_one

abbrev AutomorphismGroup (R : Type u) (C : Type v) [CommRing R] [NonAssocRing C]
    [Module R C] [IsScalarTower R C C] [SMulCommClass R C C] :=
  ClosedLinearSubgroup (fun S : CommAlgCat.{u} R => bilinearStabilizer (octonionAlgebra (C := C)) S)

abbrev RingScheme (R : Type u) [CommRing R] := Over (Spec (CommRingCat.of R))

abbrev scalarExtension (K : Type u) [CommRing K] [Algebra R K] :
    RingScheme R ⥤ RingScheme K :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))

abbrev scalarExtensionGroup (K : Type u) [CommRing K] [Algebra R K] :
    Grp (RingScheme R) ⥤ Grp (RingScheme K) :=
  (scalarExtension (R := R) K).mapGrp

abbrev forgetScalars {K : Type u} [CommRing K] [Algebra R K]
    (S : CommAlgCat.{u} K) : CommAlgCat.{u} R :=
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  CommAlgCat.of R S

/-- A point of the pullback, regarded as a point of the original scheme over the base ring. -/
def forgetFiberPoint {K : Type u} [CommRing K] [Algebra R K]
    (X : RingScheme R) (S : CommAlgCat.{u} K)
    (t : (algSpec (CommRingCat.of K)).obj (op S) ⟶ (scalarExtension (R := R) K).obj X) :
    (algSpec (CommRingCat.of R)).obj (op (forgetScalars (R := R) S)) ⟶ X :=
  Over.homMk (t.left ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (by
    erw [Category.assoc, pullback.condition]
    change t.left ≫ ((scalarExtension (R := R) K).obj X).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) = _
    rw [← Category.assoc, Over.w t]
    exact (Spec.map_comp
      (CommRingCat.ofHom (algebraMap R K)) (CommRingCat.ofHom (algebraMap K S))).symm)

/-- Exponents for the three diagonal entries of the determinant-one torus.
The first two entries are independent and the third is their inverse product. -/
abbrev FrameCharacters := ULift.{u} (Multiplicative (Fin 2 → ℤ))

def frameExponent (i : Fin 3) : FrameCharacters.{u} :=
  ⟨Multiplicative.ofAdd (![![1, 0], ![0, 1], ![-1, -1]] i)⟩

abbrev frameTorusAlgebra (R : Type u) [CommRing R] :=
  CommHopfAlgCat.of R (MonoidAlgebra R FrameCharacters.{u})

/-- The split torus of determinant-one diagonal changes of the upper frame. -/
abbrev frameTorus (R : Type u) [CommRing R] : Grp (RingScheme R) :=
  (hopfSpec (CommRingCat.of R)).obj (op (frameTorusAlgebra R))

def frameCoordinate (i : Fin 3) (S : CommAlgCat.{u} R)
    (t : ((schemePoints R).obj (frameTorus R)).obj S) : S :=
  let f := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
    (show (algSpec (CommRingCat.of R)).obj (op S) ⟶
      (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R
        (MonoidAlgebra R FrameCharacters.{u}))) from t)).unop
  f.hom (MonoidAlgebra.single (frameExponent i) 1)

/-- The differential weights of a (G_2) torus in its two-dimensional character lattice. -/
def HasG2Roots {K : Type u} [Field K] {G : GroupScheme K}
    (T : ClosedSubgroup G) (ε : Fin 3 → Character T.group) : Prop :=
  (∏ i, ε i) = 1 ∧
  (∀ m : Fin 3 → ℤ, (∏ i, ε i ^ m i) = 1 ↔ ∀ i j, m i = m j) ∧
  absoluteRoots T =
    {χ | (∃ i j : Fin 3, i ≠ j ∧ χ = ε i * (ε j)⁻¹) ∨
      (∃ i : Fin 3, χ = ε i ∨ χ = (ε i)⁻¹)} ∧
  rootLattice T = ⊤

/-- The scheme-theoretic centre is trivial, evaluated on every test algebra. -/
def HasTrivialCentre {K : Type u} [Field K] (G : GroupScheme K) : Prop :=
  ∀ (S : TestAlgebra K) (g : Points G.X S), Centralizes (𝟙 G) g → g = 1

/-- The type of the geometric fibre is specified by the full lattice and roots. -/
def IsAdjointG2 {K : Type u} [Field K] (G : AffineAlgebraicGroup K) : Prop :=
  IsReductive G ∧ IsSemisimple G ∧ HasTrivialCentre G.val ∧
    ∃ (T : ClosedSubgroup G.val) (ε : Fin 3 → Character T.group),
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧ HasG2Roots T ε

/-- Pulling the actual automorphism scheme back gives the asserted geometric group. -/
def HasGeometricFibers (A : AutomorphismGroup R C) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
    ∃ h : IsAffine ((scalarExtensionGroup (R := R) K).obj A.group).X.left ∧
        LocallyOfFiniteType ((scalarExtensionGroup (R := R) K).obj A.group).X.hom ∧
        QuasiCompact ((scalarExtensionGroup (R := R) K).obj A.group).X.hom,
      IsAdjointG2 (⟨(scalarExtensionGroup (R := R) K).obj A.group, h⟩ :
        AffineAlgebraicGroup K)

/-- The torus acts by the diagonal entries on the upper corner and by their inverses on the
dual lower corner. The two diagonal idempotents are fixed. -/
def IsFrameTorus {n : QuadraticForm R C} (F : ZornIsomorphism n)
    (A : AutomorphismGroup R C) (inclusion : frameTorus R ⟶ A.group) : Prop :=
  ∀ (S : CommAlgCat.{u} R) (t : ((schemePoints R).obj (frameTorus R)).obj S)
    (x : Zorn S),
    let coordinates := (ZornSpecification.baseChange R S).symm.trans
      (F.toLinearEquiv.baseChange R S _ _)
    let g := A.subgroupPoints S (((schemePoints R).map inclusion).app S t)
    let (a, u, v, b) := Zorn.coordinates S x
    g.val.val (coordinates x) = coordinates (Zorn.ofCoordinates
      (a, fun i => frameCoordinate i S t * u i,
        fun i => frameCoordinate (i + 1) S t * frameCoordinate (i + 2) S t * v i, b))

/-- The split structure uses the particular frame torus over the base ring and its
pullback over every field. The character values are the chosen diagonal coordinates. -/
def HasSplitFrameTorus {n : QuadraticForm R C} (A : AutomorphismGroup R C) : Prop :=
  ∀ F : ZornIsomorphism n,
    ∃ inclusion : frameTorus R ⟶ A.group,
      IsClosedImmersion inclusion.hom.hom.left ∧ IsFrameTorus F A inclusion ∧
      ∀ (K : Type u) [Field K] [Algebra R K],
        let B := scalarExtensionGroup (R := R) K
        ∃ h : IsClosedImmersion (B.map inclusion).hom.hom.left,
          let T : ClosedSubgroup (B.obj A.group) := ⟨B.obj (frameTorus R), B.map inclusion, h⟩
          IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
          ∃ ε : Fin 3 → Character T.group, HasG2Roots T ε ∧
            ∀ (S : TestAlgebra K) (t : Points T.group.X S) i,
              characterValue (ε i) S t =
                frameCoordinate i (forgetScalars (R := R) S)
                  (forgetFiberPoint (frameTorus R).X S t)

/-- Smoothness, connected geometric fibres, adjoint type (G_2), and the split case
for the automorphism group scheme of an octonion algebra. -/
def HasOctonionAutomorphisms (n : QuadraticForm R C) : Prop :=
  ∃ A : AutomorphismGroup R C,
    Smooth A.group.X.hom ∧ GeometricallyConnected A.group.X.hom ∧
      HasGeometricFibers A ∧ HasSplitFrameTorus (n := n) A

def OctonionAutomorphisms : Prop :=
  ∀ {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → HasOctonionAutomorphisms n

def OctonionAutomorphismsOverField : Prop :=
  ∀ {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C},
    FieldNormConditions n → Module.finrank k C = 8 → HasOctonionAutomorphisms n

section GeometricRepresentation

variable (K : Type u) [Field K]

/-- Unital algebra automorphisms of the coordinate Zorn algebra over a field. -/
abbrev ZornPointGroup :=
  operationStabilizer (S := K) ((· * ·) : Zorn K → Zorn K → Zorn K) ({1} : Set (Zorn K))

abbrev traceZero := (AdjointSpecification.trace (ZornSpecification.norm K)).ker

abbrev scalarLine : Submodule K (Zorn K) := Submodule.span K ({1} : Set (Zorn K))

abbrev traceZeroQuotient := traceZero K ⧸ (scalarLine K).comap (traceZero K).subtype

/-- Irreducibility for a group acting linearly on a nonzero vector space. -/
def IrreduciblePointAction {H W : Type u} [Group H] [AddCommGroup W] [Module K W]
    (ρ : H →* (Module.End K W)ˣ) : Prop :=
  Nontrivial W ∧ ∀ U : Submodule K W,
    (∀ (g : H) (x : W), x ∈ U → (ρ g).val x ∈ U) → U = ⊥ ∨ U = ⊤

end GeometricRepresentation

/-- Over a geometric field the trace-zero representation is faithful and irreducible
when (2) is nonzero. In characteristic two the induced action on trace zero modulo
the scalar line is irreducible and has trivial kernel on geometric points. -/
def SplitGeometricRepresentation : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K],
    ∃ τ : ZornPointGroup K →* (Module.End K (traceZero K))ˣ,
      (∀ (g : ZornPointGroup K) (x : traceZero K), ((τ g).val x).val = g.val.val x.val) ∧
      ((2 : K) ≠ 0 → IrreduciblePointAction K τ ∧ Function.Injective τ) ∧
      ((2 : K) = 0 →
        scalarLine K ≤ traceZero K ∧
        ∃ ρ : ZornPointGroup K →* (Module.End K (traceZeroQuotient K))ˣ,
          (∀ (g : ZornPointGroup K) (x : traceZero K),
            (ρ g).val (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((τ g).val x)) ∧
          IrreduciblePointAction K ρ ∧ Function.Injective ρ)

end

end LinearAlgebraicGroups.Composition.OctonionAutomorphismSpecification
