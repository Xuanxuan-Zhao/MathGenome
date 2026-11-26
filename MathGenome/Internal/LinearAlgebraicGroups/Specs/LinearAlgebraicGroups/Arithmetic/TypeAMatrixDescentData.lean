import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Mathlib.Data.Fin.Rev
import Mathlib.Data.ZMod.Basic

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.TypeAMatrixDescentData

open StandardGroups GeneralLinearStructure AutomorphismSequence
open Pinning (AttachedDatum BasedRootDatum PinnedGroup Pinning)
open RootGroups (AdditiveLine)
open OrderedRootProducts (RootSubgroupFamily)
open SpecialLinearDatum (DiagonalTorus LatticeIdentification RootIdentification UpperTriangularBorel)
open Unipotent (Index)
open Matrix
open _root_.LinearAlgebraicGroups.Descent.MatrixAlgebraForms (ProjectivePresentation)

open _root_.LinearAlgebraicGroups.Descent

noncomputable section

/-- An edge of the type A chain on its ordered simple roots. -/
def Adjacent {r : ℕ} (i j : Fin r) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance {r : ℕ} (i j : Fin r) : Decidable (Adjacent i j) :=
  inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

/-- All permutations preserving the Cartan chain. -/
def ChainSymmetries (r : ℕ) : Subgroup (Equiv.Perm (Fin r)) where
  carrier := {p | ∀ i j, Adjacent (p i) (p j) ↔ Adjacent i j}
  one_mem' := by intro i j; rfl
  mul_mem' hp hq := by
    intro i j
    exact (hp _ _).trans (hq _ _)
  inv_mem' {p} hp := by
    intro i j
    have h := (hp (p.symm i) (p.symm j)).symm
    change Adjacent (p.symm i) (p.symm j) ↔ Adjacent i j
    simpa only [Equiv.apply_symm_apply] using h

def ChainClassification : Prop :=
  ∀ {r : ℕ}, 2 ≤ r → ∀ p : ChainSymmetries r,
    p.val = 1 ∨ p.val = Fin.revPerm

/-- The order-two diagram group, with zero in `ZMod 2` its identity. -/
abbrev DiagramParity := Multiplicative (ZMod 2)

/-- The identification of the based automorphism group acts on the actual simple
roots, in their specified order. -/
structure ChainIdentification (D : BasedRootDatum.{u}) (r : ℕ) where
  vertices : Fin r ≃ ↥D.base.support
  cartan : ∀ i j, D.datum.pairing (vertices i).val (vertices j).val =
    if i = j then 2 else if Adjacent i j then -1 else 0
  symmetries : Aut D ≃* ChainSymmetries r
  onRoots : ∀ (d : Aut D) i,
    d.asIso.hom.val.indexEquiv (vertices i).val = (vertices ((symmetries d).val i)).val
  parity : ChainSymmetries r ≃* DiagramParity
  reversal : ∀ c, c.val = Fin.revPerm → parity c = Multiplicative.ofAdd 1

/-- The split matrix formula, applied after scalar extension of its conjugating
matrix to the test ring. -/
def MatrixFormula {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
    (s : SpecialMatrixPoints G n) (f : Aut G.val) (g : GL (Index.{u} n) k)
    (δ : DiagramParity) : Prop :=
  ∀ (R : TestAlgebra k) (x : Points G.val.X R),
    let A := GeneralLinearGroup.map (algebraMap k R) g
    let X := s.hom.app R x
    (s.hom.app R (x ≫ f.asIso.hom.hom.hom)).val =
      A.val * (if δ = 1 then X.val else X⁻¹.val.transpose) * (A⁻¹).val

/-- Taking the outer label of a field automorphism uses the actual sheaf
quotient evaluated at the unique point of the field spectrum. -/
def fieldDiagram {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {Q : AdjointQuotient G} {D : BasedRootDatum.{u}}
    (E : ExactSequence G Q (constantGroup (Aut D))) : Aut G.val →* Aut D :=
  let S := (testSpec k).obj (op (CommAlgCat.of k k))
  let x₀ : S.left := IsLocalRing.closedPoint k
  let m : Aut G.val →* RelativeAut G.val S := Functor.mapAut G.val
    (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op)
  let ev : (constantGroup (k := k) (Aut D)).obj (op S) →* Aut D :=
    { toFun := fun f => f.down x₀, map_one' := rfl, map_mul' := fun _ _ => rfl }
  ev.comp ((E.outer.app (op S)).hom.comp m)

/-- Over a field the matrix formula describes every group-scheme automorphism.
Its two cases are precisely the two classes in the based diagram quotient. -/
def FieldMatrixAutomorphisms : Prop :=
  ∀ {k : Type u} [Field k] {r : ℕ}, 2 ≤ r →
    ∀ {G : AffineAlgebraicGroup k} (s : SpecialMatrixPoints G (r + 1)),
    ∃ (T : DiagonalTorus s) (L : LatticeIdentification T) (M : RootIdentification T L)
      (B : UpperTriangularBorel T L M) (A : AdditiveLine k) (U : RootSubgroupFamily T.subgroup)
      (pin : Pinning A B.pair U) (D : AttachedDatum B.pair)
      (l : Aut D.toBased ≃* Aut (⟨B.pair, U, pin⟩ : PinnedGroup A))
      (Q : AdjointQuotient G) (E : SplitSequence (⟨B.pair, U, pin⟩ : PinnedGroup A) D l Q)
      (C : ChainIdentification D.toBased r),
      let δ := C.parity.toMonoidHom.comp (C.symmetries.toMonoidHom.comp (fieldDiagram E.toExactSequence))
      (∀ i : Fin r, (C.vertices i).val = M.indices ⟨(i.castSucc, i.succ), ne_of_lt Fin.castSucc_lt_succ⟩) ∧
      (∀ f, ∃ g, MatrixFormula s f g (δ f)) ∧
      ∀ f g p, MatrixFormula s f g p → δ f = p

/-- The central quotient is the matrix projective quotient, via the usual
inclusion of determinant-one matrices into invertible matrices. -/
def ProjectiveAdjoint : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ}, 0 < n →
    {G : AffineAlgebraicGroup k} → (s : SpecialMatrixPoints G n) →
    (P : ProjectivePresentation k n) → (Q : AdjointQuotient G) →
    ∃ e : Q.quotient.val ≅ P.projectiveGroup.val,
      ∀ (R : TestAlgebra k) (x : Points G.val.X R),
        x ≫ Q.projection.hom.hom ≫ e.hom.hom.hom =
          P.linearPoints.inv.app R (Matrix.SpecialLinearGroup.toGL (s.hom.app R x)) ≫
            P.projection.hom.hom

/-- The local lifts from invertible matrices to special linear matrices
require only adjoining a root of an invertible element. -/
def FppfRoot : Prop :=
  ∀ {k : Type u} [Field k] (R : TestAlgebra k) {n : ℕ}, 0 < n →
    ∀ a : Rˣ, ∃ (S : TestAlgebra k) (f : R ⟶ S) (b : Sˣ),
      Fppf.IsFppf ((testSpec k).map f.op).left ∧ b ^ n = Units.map f.hom.toMonoidHom a

/-- Finite splitting of the given separable form of the matrix scheme. -/
def FiniteMatrixSplitting : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ}, 3 ≤ n →
    {G : AffineAlgebraicGroup k} → SpecialMatrixPoints G n →
    ∀ H : AffineAlgebraicGroup k, IsSeparableForm G H →
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
        (_ : IsGalois k K),
        Nonempty ((groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val)

section Coordinates

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The standard coordinate action of a field automorphism on a scalar extension. -/
abbrev standardCoordinateAction (P : HopfAlgebraCategory k) :=
  SemilinearAction.scalarExtension (k := k) (K := K) P

/-- Inverse pullback transports the form's standard action to the split model.
This definition uses the given trivialization of the full coordinate Hopf algebra. -/
def transportedCoordinateAction {P Q : HopfAlgebraCategory k}
    (i : extendedHopf K P ≅ extendedHopf K Q) (σ : Gal(K/k)) (x : extendedHopf K P) :
    extendedHopf K P :=
  i.inv.hom ((standardCoordinateAction Q).act σ (i.hom.hom x))

/-- An equivariant coordinate comparison between two split trivializations descends
uniquely to an isomorphism of their base Hopf algebras, hence of the affine groups
by the inverse-pullback comparison of F03. -/
def EquivariantComparisonDescends : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {P Q U : HopfAlgebraCategory k}
    (i : extendedHopf K P ≅ extendedHopf K Q)
    (j : extendedHopf K P ≅ extendedHopf K U) (e : Aut (extendedHopf K P)),
    (∀ σ x, e.asIso.hom.hom (transportedCoordinateAction i σ x) =
      transportedCoordinateAction j σ (e.asIso.hom.hom x)) →
    ∃! b : Q ≅ U, extendedHopfMap K b.hom = (i.symm ≪≫ e.asIso ≪≫ j).hom

/-- The corresponding comparison of group schemes descends with the given
trivializations and their canonical scalar-extension projections. -/
def EquivariantSchemeComparisonDescends : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {P Q U : HopfAlgebraCategory k}
    (t : ∀ A : HopfAlgebraCategory k, specGroup (extendedHopf K A) ≅
      (groupBaseChange k K).obj (specGroup A)), Forms.IsScalarExtensionComparison t →
    ∀ (i : extendedHopf K P ≅ extendedHopf K Q)
      (j : extendedHopf K P ≅ extendedHopf K U) (e : Aut (extendedHopf K P)),
    (∀ σ x, e.asIso.hom.hom (transportedCoordinateAction i σ x) =
      transportedCoordinateAction j σ (e.asIso.hom.hom x)) →
    ∃! b : specGroup Q ≅ specGroup U, (groupBaseChange k K).mapIso b =
      (t Q).symm ≪≫ Forms.spectrumIso (i.symm ≪≫ e.asIso ≪≫ j) ≪≫ t U

end Coordinates

section SemilinearPoints

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G H : AffineAlgebraicGroup k}

/-- Coordinates for the specified splitting isomorphism, with canonical base
change on the two coordinate models. -/
structure TrivializationCoordinates
    (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val) where
  split : HopfAlgebraCategory k
  form : HopfAlgebraCategory k
  splitModel : specGroup split ≅ G.val
  formModel : specGroup form ≅ H.val
  extension : ∀ P : HopfAlgebraCategory k,
    specGroup (extendedHopf K P) ≅ (groupBaseChange k K).obj (specGroup P)
  extensionProjection : Forms.IsScalarExtensionComparison extension
  iso : extendedHopf K split ≅ extendedHopf K form
  compatibility : i = ((extension split) ≪≫ (groupBaseChange k K).mapIso splitModel).symm ≪≫
    Forms.spectrumIso iso ≪≫ (extension form) ≪≫ (groupBaseChange k K).mapIso formModel

abbrev TrivializationCoordinates.splitComparison
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) := C.extension C.split ≪≫ (groupBaseChange k K).mapIso C.splitModel

abbrev TrivializationCoordinates.formComparison
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) := C.extension C.form ≪≫ (groupBaseChange k K).mapIso C.formModel

/-- The coefficient automorphism on the split group is inverse pullback. -/
def TrivializationCoordinates.schemeAut
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (a : Aut (extendedHopf K C.split)) :
    Aut ((groupBaseChange k K).obj G.val) :=
  Aut.of (C.splitComparison.symm ≪≫ Forms.spectrumIso a.asIso ≪≫ C.splitComparison)

/-- A change of commutative test algebra over a specified field automorphism. -/
def IsSemilinearTestMap (σ : Gal(K/k)) {R S : TestAlgebra K}
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S) : Prop :=
  ∀ c : K, b.hom (algebraMap K R c) = algebraMap K S (σ c)

/-- The field automorphism regarded as a map on the restricted field test algebra. -/
def fieldSemilinearMap (σ : Gal(K/k)) :
    (restrictTestAlgebra k K).obj (CommAlgCat.of K K) ⟶
      (restrictTestAlgebra k K).obj (CommAlgCat.of K K) := by
  have hc (c : k) : σ (algebraMap k K c) = algebraMap k K c := σ.commutes c
  let R := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
  letI : Algebra k R := R.algebra
  exact ConcreteCategory.ofHom (C := CommAlgCat k) (X := R) (Y := R)
    ({ toRingHom := σ.toRingHom
       commutes' := hc } : R →ₐ[k] R)

/-- Transport the standard action of the form through the specified splitting.
The two base-change projections here are the canonical projections in A01. -/
def IsTransportedPoint
    (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val)
    {R S : TestAlgebra K}
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (x : Points ((groupBaseChange k K).obj G.val).X R)
    (y : Points ((groupBaseChange k K).obj G.val).X S) : Prop :=
  baseChangePoint k K H.val.X S (y ≫ i.hom.hom.hom) =
    mapPoints b (baseChangePoint k K H.val.X R (x ≫ i.hom.hom.hom))

/-- The split matrix coordinates use the original matrix model and the
canonical scalar-extension projection. -/
def baseChangeMatrix {n : ℕ} (s : SpecialMatrixPoints G n) (R : TestAlgebra K)
    (x : Points ((groupBaseChange k K).obj G.val).X R) : SpecialLinearGroup (Index.{u} n) R :=
  s.hom.app ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.val.X R x)

/-- The parity and matrix representatives of a specified finite Galois
trivialization, with the transported action on every test algebra. -/
def MatrixDescentAt [FiniteDimensional k K] [IsGalois k K]
    {n : ℕ} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val) : Prop :=
  ∃ (C : TrivializationCoordinates i)
    (ρ : Gal(K/k) →* MulAut (Aut (extendedHopf K C.split)))
    (a : @NonabelianCohomology.Cocycle _ _ _ (krullTopology k K) _ ⊥ ρ)
    (m : SpecialMatrixPoints (Unipotent.baseChangedAlgebraicGroup K G) n)
    (δ : Aut ((groupBaseChange k K).obj G.val) →* DiagramParity)
    (χ : Gal(K/k) →* DiagramParity) (g : Gal(K/k) → GL (Index.{u} n) K)
    (act : Gal(K/k) →* MulAut (SpecialLinearGroup (Index.{u} n) K)),
    Forms.IsStandardAction ρ ∧ Forms.IsTransportedCocycle C.iso a ∧
    (∀ R x, m.hom.app R x = baseChangeMatrix s R x) ∧
    (∀ f, ∃ A, MatrixFormula m f A (δ f)) ∧
    (∀ f A p, MatrixFormula m f A p → δ f = p) ∧
    (∀ σ, χ σ = δ (C.schemeAut (a σ)) ∧ MatrixFormula m (C.schemeAut (a σ)) (g σ) (χ σ)) ∧
    (∀ {R S : TestAlgebra K}
      (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S) x,
      ∃! y, IsTransportedPoint i b x y) ∧
    (∀ σ {R S : TestAlgebra K} (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S),
      IsSemilinearTestMap σ b → ∀ x y, IsTransportedPoint i b x y →
      let A := GeneralLinearGroup.map (algebraMap K S) (g σ)
      let X := baseChangeMatrix s R x
      (baseChangeMatrix s S y).val = A.val *
        (if χ σ = 1 then X.val.map b.hom.toRingHom else (X⁻¹).val.transpose.map b.hom.toRingHom) * (A⁻¹).val) ∧
    (∀ σ x y, IsTransportedPoint i (fieldSemilinearMap σ) x y →
      act σ (baseChangeMatrix s (CommAlgCat.of K K) x) = baseChangeMatrix s (CommAlgCat.of K K) y) ∧
    ∀ σ X, (act σ X).val = (g σ).val *
      (if χ σ = 1 then X.val.map σ else ((X⁻¹).val.map σ).transpose) * ((g σ)⁻¹).val

def MatrixDescentForTrivialization : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {n : ℕ}, 3 ≤ n → ∀ {G H : AffineAlgebraicGroup k} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val), MatrixDescentAt s i

/-- A separable form admits a finite Galois matrix descent datum. -/
def FiniteMatrixDescent : Prop :=
  ∀ {k : Type u} [Field k] {n : ℕ}, 3 ≤ n → {G : AffineAlgebraicGroup k} →
    (s : SpecialMatrixPoints G n) → ∀ H : AffineAlgebraicGroup k, IsSeparableForm G H →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K) (_ : IsGalois k K)
      (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val), MatrixDescentAt s i

end SemilinearPoints

end

end LinearAlgebraicGroups.Specs.TypeAMatrixDescentData
