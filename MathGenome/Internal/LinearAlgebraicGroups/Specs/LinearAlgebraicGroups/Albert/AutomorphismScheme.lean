import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieBracket
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Automorphism functors and infinitesimal preservation equations for NA13-C04.07. -/

namespace Specs.LinearAlgebraicGroups.Albert.Automorphisms

open TensorProduct
open scoped DualNumber

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A bilinear multiplication with an optional two-sided unit. -/
structure BilinearAlgebra (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] where
  product : LinearMap.BilinMap R M M
  unit : Option M
  unit_mul : ∀ e ∈ unit, ∀ x, product e x = x
  mul_unit : ∀ e ∈ unit, ∀ x, product x e = x

/-- Preservation of the scalar-extended product and of the unit, if specified. -/
def PreservesBilinear (A : BilinearAlgebra R M) (S : Type u) [CommRing S] [Algebra R S]
    (g : Module.End S (S ⊗[R] M)) : Prop :=
  (∀ e ∈ A.unit, g (1 ⊗ₜ[R] e) = 1 ⊗ₜ[R] e) ∧
    ∀ x y, g (A.product.baseChange S x y) =
      A.product.baseChange S (g x) (g y)

/-- Preservation of the unit and of the scalar-extended quadratic operator. -/
def PreservesQuadratic (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (g : Module.End S (S ⊗[R] M)) : Prop :=
  g (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit ∧
    ∀ x y, g (J.op S x y) = J.op S (g x) (g y)

/-- The subgroup of linear automorphisms preserving a given operation and elements. -/
def operationStabilizer {S V : Type*} [CommRing S] [AddCommGroup V] [Module S V]
    (op : V → V → V) (units : Set V) : Subgroup (Module.End S V)ˣ where
  carrier := {g | (∀ u ∈ units, g.val u = u) ∧ ∀ x y, g.val (op x y) = op (g.val x) (g.val y)}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    change (∀ u ∈ units, a.val (b.val u) = u) ∧
      ∀ x y, a.val (b.val (op x y)) = op (a.val (b.val x)) (a.val (b.val y))
    exact ⟨fun u hu => (congrArg a.val (hb.1 u hu)).trans (ha.1 u hu),
      fun x y => (congrArg a.val (hb.2 x y)).trans (ha.2 _ _)⟩
  inv_mem' := by
    intro a h
    have hr z : a.val ((a⁻¹).val z) = z := by
      exact DFunLike.congr_fun (a.mul_inv : a.val * (a⁻¹).val = 1) z
    have hl z : (a⁻¹).val (a.val z) = z := by
      exact DFunLike.congr_fun (a.inv_mul : (a⁻¹).val * a.val = 1) z
    have hi : Function.Injective a.val := fun x y hxy => by
      have he := congrArg (fun w => (a⁻¹).val w) hxy
      rwa [hl, hl] at he
    refine ⟨?_, ?_⟩
    · intro u hu
      exact hi ((hr u).trans (h.1 u hu).symm)
    · intro x y
      apply hi
      rw [hr, h.2, hr, hr]

/-- Automorphisms of the scalar-extended bilinear algebra. -/
def bilinearStabilizer (A : BilinearAlgebra R M) (S : Type u) [CommRing S] [Algebra R S] :
    Subgroup (Module.End S (S ⊗[R] M))ˣ :=
  operationStabilizer (fun x y => A.product.baseChange S x y)
    {z | ∃ e ∈ A.unit, (1 ⊗ₜ[R] e : S ⊗[R] M) = z}

theorem mem_bilinearStabilizer (A : BilinearAlgebra R M) (S : Type u) [CommRing S]
    [Algebra R S] (g : (Module.End S (S ⊗[R] M))ˣ) :
    g ∈ bilinearStabilizer A S ↔ PreservesBilinear A S g.val := by
  change ((∀ z, (∃ e ∈ A.unit, (1 ⊗ₜ[R] e : S ⊗[R] M) = z) → g.val z = z) ∧ _) ↔ _
  exact and_congr_left' ⟨fun h e he => h _ ⟨e, he, rfl⟩, fun h z ⟨e, he, hz⟩ =>
    hz ▸ h e he⟩

/-- Automorphisms of the scalar-extended unital quadratic Jordan algebra. -/
def quadraticStabilizer (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S] :
    Subgroup (Module.End S (S ⊗[R] M))ˣ :=
  operationStabilizer (fun x y => J.op S x y) {1 ⊗ₜ[R] J.unit}

theorem mem_quadraticStabilizer (J : QuadraticJordan R M) (S : Type u) [CommRing S]
    [Algebra R S] (g : (Module.End S (S ⊗[R] M))ˣ) :
    g ∈ quadraticStabilizer J S ↔ PreservesQuadratic J S g.val := by
  change ((∀ z ∈ {(1 ⊗ₜ[R] J.unit : S ⊗[R] M)}, g.val z = z) ∧ _) ↔ _
  simp [PreservesQuadratic]

/-- The ordinary Leibniz rule for a bilinear multiplication. -/
def IsDerivation (p : LinearMap.BilinMap R M M) (D : Module.End R M) : Prop :=
  ∀ x y, D (p x y) = p (D x) y + p x (D y)

/-- The quadratic infinitesimal identities as polynomial laws. -/
def IsQuadraticDerivation (J : QuadraticJordan R M) (D : Module.End R M) : Prop :=
  D J.unit = 0 ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M),
      D.baseChange S (J.op S x y) =
        J.op S x (D.baseChange S y) + J.polar S x (D.baseChange S x) y

/-- The endomorphism of the dual-number extension with matrix I + εD. -/
def infinitesimal (D : Module.End R M) : Module.End (DualNumber R) (DualNumber R ⊗[R] M) :=
  1 + (ε : DualNumber R) • D.baseChange (DualNumber R)

/-- Reduction on the scalar-extended module. -/
abbrev dualModuleReduction : DualNumber R ⊗[R] M →ₗ[R] R ⊗[R] M :=
  (TrivSqZeroExt.fstHom R R R).toLinearMap.rTensor M

/-- The tangent kernel for a pointwise preservation predicate. -/
def Tangent (P : Module.End (DualNumber R) (DualNumber R ⊗[R] M) → Prop) :=
  {g : (Module.End (DualNumber R) (DualNumber R ⊗[R] M))ˣ //
    P g.val ∧ ∀ m : M, dualModuleReduction (g.val (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] m}

def BilinearUnitDerivation : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (A : BilinearAlgebra R M) (D : Module.End R M),
    IsDerivation A.product D → ∀ e ∈ A.unit, D e = 0

def BilinearTangent : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (A : BilinearAlgebra R M),
    ∃ e : {D : Module.End R M // IsDerivation A.product D} ≃
        Tangent (PreservesBilinear A (DualNumber R)),
      ∀ D, (e D).val.val = infinitesimal D.val

def QuadraticTangent : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M),
    ∃ e : {D : Module.End R M // IsQuadraticDerivation J D} ≃
        Tangent (PreservesQuadratic J (DualNumber R)),
      ∀ D, (e D).val.val = infinitesimal D.val

def JordanDerivationComparison : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (d : Rˣ) (_ : (↑d : R) = 2) (D : Module.End R M),
    IsQuadraticDerivation J D ↔ IsDerivation (J.groundProduct d) D

/-- The commutator convention is composition in the order DE minus ED. -/
def commutator (D E : Module.End R M) : Module.End R M := D * E - E * D

def BilinearCommutator : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (A : BilinearAlgebra R M) {D E : Module.End R M},
    IsDerivation A.product D → IsDerivation A.product E →
    IsDerivation A.product (commutator D E)

def QuadraticCommutator : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) {D E : Module.End R M},
    IsQuadraticDerivation J D → IsQuadraticDerivation J E →
    IsQuadraticDerivation J (commutator D E)

/-- The commutator of the scalar extensions of the two first-order maps. -/
def InfinitesimalCommutator : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (D E : Module.End R M),
    let B := LinearAlgebraicGroups.InfinitesimalCommutator.TwoVariables R
    let d := D.baseChange B
    let e := E.baseChange B
    let s : B := TrivSqZeroExt.inl (ε : DualNumber R)
    let t : B := ε
    (1 + s • d) * (1 + t • e) * (1 - s • d) * (1 - t • e) =
      1 + (s * t) • (commutator D E).baseChange B

section Matrices

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The matrix of indeterminates before inverting its determinant. -/
def genericMatrix (R ι : Type u) [CommRing R] : Matrix ι ι (MvPolynomial (ι × ι) R) :=
  fun i j => MvPolynomial.X (i, j)

/-- The usual determinant localization of the polynomial algebra on matrix entries. -/
abbrev MatrixCoordinates (R : Type u) (ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι] :=
  Localization.Away ((genericMatrix R ι).det)

/-- The matrix with universal entries in the determinant localization. -/
def coordinateMatrix : Matrix ι ι (MatrixCoordinates R ι) :=
  fun i j => algebraMap (MvPolynomial (ι × ι) R) _ (MvPolynomial.X (i, j))

/-- A group of matrices at every scalar algebra, compatible with change of scalars. -/
structure MatrixSubgroup (R : Type u) (ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι] where
  subgroup (S : Type u) [CommRing S] [Algebra R S] : Subgroup (Matrix.GeneralLinearGroup ι S)
  map_mem {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (g : Matrix.GeneralLinearGroup ι S) :
    g ∈ subgroup S → Matrix.GeneralLinearGroup.map f.toRingHom g ∈ subgroup T

/-- A coordinate ideal cuts out precisely the designated matrices over each test algebra. -/
def CutsOut (I : Ideal (MatrixCoordinates R ι)) (H : MatrixSubgroup R ι) : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (f : MatrixCoordinates R ι →ₐ[R] S)
    (g : Matrix.GeneralLinearGroup ι S), g.val = f.mapMatrix coordinateMatrix →
      (g ∈ H.subgroup S ↔ ∀ a ∈ I, f a = 0)

def MatrixCoordinateEvaluation : Prop :=
  ∀ (R ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι]
    (S : Type u) [CommRing S] [Algebra R S],
    ∃ e : (MatrixCoordinates R ι →ₐ[R] S) ≃ Matrix.GeneralLinearGroup ι S,
      ∀ f, (e f).val = f.mapMatrix coordinateMatrix

/-- The natural group-valued points of a matrix subgroup. -/
def MatrixSubgroup.points (H : MatrixSubgroup R ι) : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj S := GrpCat.of (H.subgroup S)
  map f := GrpCat.ofHom
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map f.hom.toRingHom g.val,
        H.map_mem f.hom g.val g.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _) }
  map_id _ :=  GrpCat.ext fun _ => Subtype.ext (Matrix.GeneralLinearGroup.ext fun _ _ => rfl)
  map_comp _ _ := GrpCat.ext fun _ => Subtype.ext (Matrix.GeneralLinearGroup.ext fun _ _ => rfl)

def MatrixSubgroup.full (R ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι] :
    MatrixSubgroup R ι where
  subgroup _ := ⊤
  map_mem _ _ _ := Subgroup.mem_top _

/-- The same group-valued scheme points as in A01, over any commutative base ring. -/
abbrev schemePoints (R : Type u) [CommRing R] :
    Grp (Over (Spec (CommRingCat.of R))) ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (algSpec (CommRingCat.of R)).rightOp

/-- A closed subgroup realizes the given coordinate equations and group-valued functor. -/
def ClosedMatrixSubgroup : Prop :=
  ∀ (R ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι]
    (H : MatrixSubgroup R ι) (I : Ideal (MatrixCoordinates R ι)), CutsOut I H →
    ∃ (G L : Grp (Over (Spec (CommRingCat.of R)))) (j : G ⟶ L),
      ∃ (a : G.X ≅ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (MatrixCoordinates R ι ⧸ I))))
        (b : L.X ≅ (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (MatrixCoordinates R ι))))
        (e : (schemePoints R).obj G ≅ H.points)
        (l : (schemePoints R).obj L ≅ (MatrixSubgroup.full R ι).points),
        IsClosedImmersion j.hom.hom.left ∧
        j.hom.hom ≫ b.hom = a.hom ≫ (algSpec (CommRingCat.of R)).map
          (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ∧
        ∀ (S : CommAlgCat.{u} R) (g : ((schemePoints R).obj G).obj S),
          (l.hom.app S (((schemePoints R).map j).app S g)).val = (e.hom.app S g).val

/-- Scalar-compatible equations on invertible matrices, indexed by a finite type. -/
structure MatrixEquations (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n] where
  Index : Type v
  finite : Finite Index
  equation (S : Type u) [CommRing S] [Algebra R S] : Matrix.GeneralLinearGroup n S → Index → S
  natural {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (g : Matrix.GeneralLinearGroup n S) (a : Index) :
    f (equation S g a) = equation T (Matrix.GeneralLinearGroup.map f.toRingHom g) a

def MatrixEquationsPresent : Prop :=
  ∀ (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]
    (H : MatrixSubgroup R n) (E : MatrixEquations.{u,v} R n),
    (∀ (S : Type u) [CommRing S] [Algebra R S] (g : Matrix.GeneralLinearGroup n S),
      g ∈ H.subgroup S ↔ ∀ a, E.equation S g a = 0) →
    ∃ generators : E.Index → MatrixCoordinates R n,
      CutsOut (Ideal.span (Set.range generators)) H ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] (f : MatrixCoordinates R n →ₐ[R] S)
        (g : Matrix.GeneralLinearGroup n S), g.val = f.mapMatrix coordinateMatrix →
        ∀ a, f (generators a) = E.equation S g a

/-- The matrix action on the scalar extension of a module with a chosen basis. -/
def matrixAction (b : Module.Basis ι R M) (S : Type u) [CommRing S] [Algebra R S]
    (g : Matrix.GeneralLinearGroup ι S) : Module.End S (S ⊗[R] M) :=
  Matrix.toLinAlgEquiv (b.baseChange S) g.val

/-- Single basis vectors test the diagonal values of the quadratic law. The pair
sums also test the polar values, including when two vanishes. -/
def basisOperationTest (b : Module.Basis ι R M) (S : Type u) [CommRing S] [Algebra R S] :
    ι ⊕ (ι × ι) → S ⊗[R] M
  | .inl i => b.baseChange S i
  | .inr (i, j) => b.baseChange S i + b.baseChange S j

abbrev OperationEquationIndex (ι : Type u) := ι × (Unit ⊕ ((ι ⊕ (ι × ι)) × ι))

/-- Coordinates of the unit and operation discrepancies at the designated inputs. -/
def operationDiscrepancy (b : Module.Basis ι R M) (S : Type u) [CommRing S] [Algebra R S]
    (p : S ⊗[R] M → S ⊗[R] M → S ⊗[R] M) (e : Option M)
    (g : Matrix.GeneralLinearGroup ι S) (a : OperationEquationIndex ι) : S :=
  let gS := matrixAction b S g
  (b.baseChange S).repr
    (match a.2 with
     | .inl _ => e.elim 0 fun v => gS (1 ⊗ₜ[R] v) - 1 ⊗ₜ[R] v
     | .inr (i, j) =>
         let x := basisOperationTest b S i
         let y := b.baseChange S j
         gS (p x y) - p (gS x) (gS y)) a.1

/-- The representing ideal is generated by the evaluated coordinate discrepancies. -/
def ActionPresentation (b : Module.Basis ι R M)
    (p : ∀ (S : Type u) [CommRing S] [Algebra R S], S ⊗[R] M → S ⊗[R] M → S ⊗[R] M)
    (e : Option M) : Prop :=
  ∃ (H : MatrixSubgroup R ι) (c : OperationEquationIndex ι → MatrixCoordinates R ι),
    CutsOut (Ideal.span (Set.range c)) H ∧
    (∀ (S : Type u) [CommRing S] [Algebra R S] (g : Matrix.GeneralLinearGroup ι S),
      let gS := matrixAction b S g
      g ∈ H.subgroup S ↔
        (∀ v ∈ e, gS (1 ⊗ₜ[R] v) = 1 ⊗ₜ[R] v) ∧ ∀ x y, gS (p S x y) = p S (gS x) (gS y)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (f : MatrixCoordinates R ι →ₐ[R] S)
      (g : Matrix.GeneralLinearGroup ι S), g.val = f.mapMatrix coordinateMatrix →
      ∀ a, f (c a) = operationDiscrepancy b S (p S) e g a

def BilinearCoordinates : Prop :=
  ∀ {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (b : Module.Basis ι R M)
    (A : BilinearAlgebra R M),
    ActionPresentation b (fun S _ _ x y => A.product.baseChange S x y) A.unit

def QuadraticCoordinates : Prop :=
  ∀ {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (b : Module.Basis ι R M)
    (J : QuadraticJordan R M),
    ActionPresentation b (fun S _ _ x y => J.op S x y) (some J.unit)

/-- The reduction kernel of the matrix stabilizer, expressed on the scalar-extended module. -/
def MatrixTangentComparison : Prop :=
  ∀ {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module k M] (b : Module.Basis ι k M)
    (H : MatrixSubgroup k ι) (P : Module.End (DualNumber k) (DualNumber k ⊗[k] M) → Prop),
    (∀ g, g ∈ H.subgroup (DualNumber k) ↔ P (matrixAction b (DualNumber k) g)) →
    ∃ e : _root_.LinearAlgebraicGroups.DualKernel H.points ≃ Tangent P,
      ∀ g, (e g).val.val = matrixAction b (DualNumber k) g.toMul.val.val

/-- The coefficient of ε is the matrix of the infinitesimal endomorphism. -/
def MatrixInfinitesimalCoefficient : Prop :=
  ∀ {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module k M] (b : Module.Basis ι k M)
    (D : Module.End k M) (g : Matrix.GeneralLinearGroup ι (DualNumber k)),
    matrixAction b (DualNumber k) g = infinitesimal D →
    (fun i j => (g.val i j).snd : Matrix ι ι k) = LinearMap.toMatrix b b D

end
end Matrices

section Schemes

open AlgebraicGeometry CategoryTheory

/-- A closed subgroup of the general linear group of a module, with its action over each
test algebra. Change of scalars on linear automorphisms is characterized by its action
on the images of the original module. -/
structure ClosedLinearSubgroup
    (P : ∀ S : CommAlgCat.{u} R, Subgroup (Module.End S (S ⊗[R] M))ˣ) where
  group : Grp (Over (Spec (CommRingCat.of R)))
  generalLinear : Grp (Over (Spec (CommRingCat.of R)))
  inclusion : group ⟶ generalLinear
  closed : IsClosedImmersion inclusion.hom.hom.left
  groupAffine : IsAffine group.X.left
  linearAffine : IsAffine generalLinear.X.left
  groupFiniteType : LocallyOfFiniteType group.X.hom
  linearFiniteType : LocallyOfFiniteType generalLinear.X.hom
  groupQuasiCompact : QuasiCompact group.X.hom
  linearQuasiCompact : QuasiCompact generalLinear.X.hom
  linearPoints (S : CommAlgCat.{u} R) :
    ((schemePoints R).obj generalLinear).obj S ≃* (Module.End S (S ⊗[R] M))ˣ
  subgroupPoints (S : CommAlgCat.{u} R) :
    ((schemePoints R).obj group).obj S ≃* P S
  evaluatesInclusion (S : CommAlgCat.{u} R) (p : ((schemePoints R).obj group).obj S) :
    linearPoints S (((schemePoints R).map inclusion).app S p) = (subgroupPoints S p).val
  scalarChange {S T : CommAlgCat.{u} R} (f : S ⟶ T)
      (p : ((schemePoints R).obj generalLinear).obj S) (x : S ⊗[R] M) :
    (linearPoints T (((schemePoints R).obj generalLinear).map f p)).val
      (f.hom.toLinearMap.rTensor M x) =
    f.hom.toLinearMap.rTensor M ((linearPoints S p).val x)

def BilinearAutomorphismScheme : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (A : BilinearAlgebra R M),
    Nonempty (ClosedLinearSubgroup (fun S => bilinearStabilizer A S))

def QuadraticAutomorphismScheme : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (J : QuadraticJordan R M),
    Nonempty (ClosedLinearSubgroup (fun S => quadraticStabilizer J S))

/-- The differential embeds the actual identity tangent kernel into endomorphisms,
with image the indicated derivations and with their usual Lie operations. -/
def TangentDerivations {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    {P : ∀ S : CommAlgCat.{u} k, Subgroup (Module.End S (S ⊗[k] V))ˣ}
    (G : ClosedLinearSubgroup P) (Q : Module.End k V → Prop) : Prop :=
  letI := G.groupAffine
  ∃ d : _root_.LinearAlgebraicGroups.Specs.Lie k G.group → Module.End k V,
    Function.Injective d ∧
    (∀ D, (∃ p, d p = D) ↔ Q D) ∧
    (∀ p, (G.subgroupPoints (CommAlgCat.of k (DualNumber k)) p.toMul.val).val.val =
      infinitesimal (d p)) ∧
    (∀ p q, d (p + q) = d p + d q) ∧
    (∀ (c : k) p, d (_root_.LinearAlgebraicGroups.scalePointKernel G.group c p) = c • d p) ∧
    (∀ p q, d (_root_.LinearAlgebraicGroups.Specs.intrinsicLieBracket k G.group p q) =
      commutator (d p) (d q))

def BilinearLieIdentification : Prop :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (A : BilinearAlgebra k V) (G : ClosedLinearSubgroup (fun S => bilinearStabilizer A S)),
    TangentDerivations G (IsDerivation A.product)

def QuadraticLieIdentification : Prop :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (J : QuadraticJordan k V) (G : ClosedLinearSubgroup (fun S => quadraticStabilizer J S)),
    TangentDerivations G (IsQuadraticDerivation J)

end Schemes

end Specs.LinearAlgebraicGroups.Albert.Automorphisms
