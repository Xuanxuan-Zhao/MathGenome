import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.Parabolics
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj Matrix TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport

noncomputable section

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.AdjointRepresentation (GroupPoints)

variable {F E : Type u} [Field F] [Field E]

abbrev RationalPoints (X : SchemeOver F) := Points X (CommAlgCat.of F F)

/-- Evaluation of a global coordinate at a rational point. -/
def evaluation {X : SchemeOver F} (p : RationalPoints X) : Γ(X.left, ⊤) →+* F :=
  (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom

/-- The local-field topology of affine points, induced by all regular coordinates. -/
@[instance_reducible] def pointTopology [TopologicalSpace F] (X : SchemeOver F) :
    TopologicalSpace (RationalPoints X) :=
  .induced (fun p (a : Γ(X.left, ⊤)) ↦ evaluation p a) inferInstance

/-- The algebra structure used for transport is precisely the specified field isomorphism. -/
abbrev scalarStructure {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Algebra R S := e.toRingHom.toAlgebra

abbrev testScalarStructure (e : F ≃+* E) (R : Type u) [CommRing R] [Algebra E R] :
    Algebra F R := ((algebraMap E R).comp e.toRingHom).toAlgebra

/-- A coefficient algebra, including a noncommutative one, on an `E`-test algebra.
The two sides extend respectively directly from `F` and through `E`. -/
def testAlgebraRebase (e : F ≃+* E) (R A : Type u) [CommRing R] [Algebra E R]
    [Ring A] [Algebra F A] :
    letI := scalarStructure e
    letI := testScalarStructure e R
    R ⊗[F] A ≃ₐ[R] R ⊗[E] (E ⊗[F] A) := by
  letI := scalarStructure e
  letI := testScalarStructure e R
  letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
  let f := (TensorProduct.AlgebraTensorModule.cancelBaseChange F E R R A).symm
  apply Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct f
  · intro r s a b
    simp only [f, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · change f (1 ⊗ₜ[F] 1) = (1 : R) ⊗ₜ[E] ((1 : E) ⊗ₜ[F] (1 : A))
    rfl

/-- The rational point obtained by projecting from the pullback and precomposing
with the inverse identification of the two base spectra. -/
def originalPoint (e : F ≃+* E) (X : SchemeOver F)
    (p : letI := scalarStructure e; RationalPoints ((baseChange F E).obj X)) :
    RationalPoints X := by
  letI := scalarStructure e
  let a : CommAlgCat.of F E ⟶ CommAlgCat.of F F :=
    CommAlgCat.ofHom
      { toRingHom := e.symm.toRingHom
        commutes' := e.symm_apply_apply }
  exact mapPoints a (baseChangePoint F E X (CommAlgCat.of E E) p)

/-- Coordinate-wise topology and the rational-point isomorphism for the actual
scalar extension of an affine algebraic group. -/
def RationalGroupTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E]
    [TopologicalSpace F] [TopologicalSpace E]
    (e : F ≃+* E), Continuous e → Continuous e.symm →
    ∀ G : AffineAlgebraicGroup F,
      letI := scalarStructure e
      let G' := Specs.Unipotent.baseChangedAlgebraicGroup E G
      letI := pointTopology G.val.X
      letI := pointTopology G'.val.X
      ∃ f : RationalPoints G.val.X ≃* RationalPoints G'.val.X,
        Continuous f ∧ Continuous f.symm ∧
          (∀ p, f.symm p = originalPoint e G.val.X p)

/-- The affine coordinate topology makes rational points a topological group. -/
def RationalPointTopologicalGroup : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (G : AffineAlgebraicGroup F),
    letI := pointTopology G.val.X
    IsTopologicalGroup (RationalPoints G.val.X)

/-- Pullback of a regular coordinate along the canonical projection of the base change. -/
def coordinatePullback (e : F ≃+* E) (X : SchemeOver F) :
    letI := scalarStructure e
    Γ(X.left, ⊤) →+* Γ(((baseChange F E).obj X).left, ⊤) := by
  letI := scalarStructure e
  exact (pullback.fst X.hom (fieldSpecMap F E)).appTop.hom

def EvaluationTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) (X : SchemeOver F),
    letI := scalarStructure e
    ∀ (p : RationalPoints ((baseChange F E).obj X)) (a : Γ(X.left, ⊤)),
      evaluation p (coordinatePullback e X a) = e (evaluation (originalPoint e X p) a)

def PointNaturality : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    {X Y : SchemeOver F} (f : X ⟶ Y),
    letI := scalarStructure e
    ∀ p : RationalPoints ((baseChange F E).obj X),
      originalPoint e Y (p ≫ (baseChange F E).map f) = originalPoint e X p ≫ f

/-- Every scheme morphism acts continuously in affine coordinates. -/
def RationalMorphismContinuous : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] {X Y : SchemeOver F} (f : X ⟶ Y),
    letI := pointTopology X
    letI := pointTopology Y
    Continuous (fun p : RationalPoints X ↦ p ≫ f)

/-- The coordinate algebra with its original structural map from the field. -/
abbrev coordinateAlgebra (X : SchemeOver F) : Algebra F Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.hom.appTop).hom.toAlgebra

/-- The topology can be computed in any generating system of affine coordinates. -/
def CoordinateTopology : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (X : SchemeOver F) {idx : Type u} (c : idx → Γ(X.left, ⊤)),
    letI := coordinateAlgebra X
    Algebra.adjoin F (Set.range c) = ⊤ →
      pointTopology X =
        TopologicalSpace.induced (fun p (i : idx) ↦ evaluation p (c i)) inferInstance

open ValuativeRel in
/-- A uniformizer has the largest valuation strictly below that of one. -/
def IsUniformizingUnit [ValuativeRel F] (π : Fˣ) : Prop :=
  (π : F) <ᵥ 1 ∧ ∀ x : F, x <ᵥ 1 → x ≤ᵥ (π : F)

open ValuativeRel in
/-- The valuative comparison characterizes a generator of the maximal ideal
of the canonical valuation ring. -/
def UniformizerGeneratesMaximalIdeal : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] (π : Fˣ),
    let O := (valuation F).valuationSubring
    IsUniformizingUnit π ↔
      ∃ p : O, (p : F) = π ∧ IsLocalRing.maximalIdeal O = Ideal.span {p}

open ValuativeRel in
def UniformizerTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] [ValuativeRel F] [ValuativeRel E]
    (e : F ≃+* E), (∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) →
    ∀ π : Fˣ, IsUniformizingUnit (Units.map e.toMonoidHom π) ↔ IsUniformizingUnit π

open CocharacterDynamics (cocharacterPoint unitPoint)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.CharacterDescent (Cocharacter)
open Specs.RootGroups (AdditiveLine rootPoint)

/-- The pullback of the marked cocharacter, evaluated in the base-changed
multiplicative coordinate. The pullback point is characterized by its image
under the scalar-extension bijection. -/
def CocharacterTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) {G : GroupScheme F}
    (c : Cocharacter G),
    letI := scalarStructure e
    ∀ (p : RationalPoints ((groupBaseChange F E).obj G).X) (s : Fˣ),
      baseChangePoint F E G.X (CommAlgCat.of E E) p =
        cocharacterPoint c ((restrictTestAlgebra F E).obj (CommAlgCat.of E E))
          (Units.map e.toMonoidHom s) ↔
      originalPoint e G.X p = cocharacterPoint c (CommAlgCat.of F F) s

/-- A marked root map uses the original additive generator after base change,
and its scalar parameter is carried by the field isomorphism. -/
def RootParameterTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) {G : GroupScheme F}
    {A : AdditiveLine F} (x : A.group ⟶ G),
    letI := scalarStructure e
    ∀ (p : RationalPoints ((groupBaseChange F E).obj G).X) (a : F),
      baseChangePoint F E G.X (CommAlgCat.of E E) p =
        rootPoint x ((restrictTestAlgebra F E).obj (CommAlgCat.of E E)) (e a) ↔
      originalPoint e G.X p = rootPoint x (CommAlgCat.of F F) a

/-- The transported root embedding uses the same polynomial parameter on all
test algebras. Its underlying affine-line points are determined by that parameter. -/
def RootMorphismTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) {G : GroupScheme F}
    {A : AdditiveLine F} (x : A.group ⟶ G),
    letI := scalarStructure e
    ∃ param : ∀ R : TestAlgebra E, R ≃ GroupPoints ((groupBaseChange F E).obj A.group) R,
      (∀ (R : TestAlgebra E) (a : R),
        baseChangePoint F E A.group.X R (param R a) =
          rootPoint (𝟙 A.group) ((restrictTestAlgebra F E).obj R) a ∧
        baseChangePoint F E G.X R
            (param R a ≫ ((groupBaseChange F E).map x).hom.hom) =
          rootPoint x ((restrictTestAlgebra F E).obj R) a) ∧
      (∀ {R S : TestAlgebra E} (f : R ⟶ S) (a : R),
        mapPoints f (param R a) = param S (f.hom a)) ∧
      (∀ (R : TestAlgebra E) (a b : R), param R (a + b) = param R a * param R b)

/-- The multiplicative source of a marked cocharacter over the new field
carries the same unit parameter on every test algebra. -/
def CocharacterMorphismTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) {G : GroupScheme F}
    (c : Cocharacter G),
    letI := scalarStructure e
    let M := specGroup (groupAlgebra F IntegerCharacters)
    ∃ i : specGroup (groupAlgebra E IntegerCharacters) ≅ (groupBaseChange F E).obj M,
      (∀ (R : TestAlgebra E) (s : Rˣ),
        baseChangePoint F E M.X R (unitPoint R s ≫ i.hom.hom.hom) =
          unitPoint ((restrictTestAlgebra F E).obj R) s) ∧
      let c' : Cocharacter ((groupBaseChange F E).obj G) := i.hom ≫ (groupBaseChange F E).map c
      ∀ s : Fˣ,
        originalPoint e G.X (cocharacterPoint c' (CommAlgCat.of E E) (Units.map e.toMonoidHom s)) =
          cocharacterPoint c (CommAlgCat.of F F) s

/-- A matrix presentation may include the inverse determinant among its generators.
The rational points still carry the topology induced by the matrix entries. -/
def MatrixTopology : Prop :=
  ∀ {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
    (X : SchemeOver F) {n : Type u} [Fintype n] [DecidableEq n]
    (c : Matrix n n Γ(X.left, ⊤)) (d : Γ(X.left, ⊤)),
    letI := coordinateAlgebra X
    let m := fun p : RationalPoints X ↦ c.map (evaluation p)
    Algebra.adjoin F (insert d (Set.range fun ij : n × n ↦ c ij.1 ij.2)) = ⊤ →
    (∀ p, (m p).det ≠ 0) →
    (∀ p, evaluation p d = (m p).det⁻¹) →
    pointTopology X = TopologicalSpace.induced m inferInstance

/-- An arbitrary finite matrix of regular coordinates transforms entrywise. -/
def MatrixCoordinateTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) (X : SchemeOver F)
    {n : Type u} (c : Matrix n n Γ(X.left, ⊤)),
    letI := scalarStructure e
    ∀ (p : RationalPoints ((baseChange F E).obj X)),
      (c.map (coordinatePullback e X)).map (evaluation p) =
        (c.map (evaluation (originalPoint e X p))).map e

/-- The Hermitian or skew-Hermitian matrix isometry equation transports over
any coefficient-ring isomorphism that intertwines the involutions. -/
def SesquilinearMatrixTransport : Prop :=
  ∀ {A B n : Type u} [Ring A] [Ring B] [StarRing A] [StarRing B]
    [Fintype n] (i : A ≃+* B), (∀ a, i (star a) = star (i a)) →
    ∀ M H : Matrix n n A,
      (M.map i)ᴴ * H.map i * M.map i = H.map i ↔ Mᴴ * H * M = H

/-- The determinant-one condition of the special unitary model is also transported. -/
def SpecialMatrixTransport : Prop :=
  ∀ {A B n : Type u} [CommRing A] [CommRing B] [Fintype n] [DecidableEq n]
    (i : A ≃+* B) (M : Matrix n n A), (M.map i).det = 1 ↔ M.det = 1

/-- Conjugate an involution along the specified ring equivalence. -/
@[instance_reducible] def transportedInvolution {A B : Type u} [Ring A] [Ring B] [StarRing A]
    (i : A ≃+* B) : StarRing B := by
  letI : Star B := ⟨fun b ↦ i (star (i.symm b))⟩
  exact i.symm.injective.starRing i.symm (fun _ ↦ i.symm_apply_apply _) (map_add _) (map_mul _)

def CoefficientAlgebraTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    (A : Type u) [Ring A] [Algebra F A] [StarRing A],
    (∀ r : F, star (algebraMap F A r) = algebraMap F A r) →
    letI := scalarStructure e
    ∃ i : A ≃+* E ⊗[F] A,
      (∀ a, i a = (1 : E) ⊗ₜ[F] a) ∧
      (∀ r : F, i (algebraMap F A r) = algebraMap E (E ⊗[F] A) (e r)) ∧
      letI := transportedInvolution i
      ∀ t : E, ∀ a : A, star (t ⊗ₜ[F] a) = t ⊗ₜ[F] star a


/-- The equation for the quaternionic quadratic-pair model uses the class of this
value modulo the scalar subspace. -/
def quaternionicValue {A n : Type u} [Ring A] [StarRing A] [Fintype n]
    (H L : Matrix n n A) (v : n → A) : A :=
  (star ∘ v) ⬝ᵥ (H *ᵥ (L *ᵥ v))

def PreservesQuaternionicQuadraticForm (F : Type u) [Field F] {A n : Type u}
    [Ring A] [Algebra F A] [StarRing A] [Fintype n]
    (M H L : Matrix n n A) : Prop :=
  ∀ v, quaternionicValue H L (M *ᵥ v) - quaternionicValue H L v ∈ Set.range (algebraMap F A)

def QuaternionicQuadraticFormTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    {A B n : Type u} [Ring A] [Ring B] [Algebra F A] [Algebra E B] [StarRing A] [StarRing B]
    [Fintype n] (i : A ≃+* B),
    (∀ r : F, i (algebraMap F A r) = algebraMap E B (e r)) →
    (∀ a, i (star a) = star (i a)) →
    ∀ M H L : Matrix n n A,
      PreservesQuaternionicQuadraticForm E (M.map i) (H.map i) (L.map i) ↔
        PreservesQuaternionicQuadraticForm F M H L

/-- The actual scalar extension carries the Hermitian isometry equation and its
determinant-one condition for a commutative coefficient algebra. -/
def SpecialUnitaryMatrixTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    (A : Type u) [CommRing A] [Algebra F A] [StarRing A],
    (∀ r : F, star (algebraMap F A r) = algebraMap F A r) →
    letI := scalarStructure e
    ∃ i : A ≃+* E ⊗[F] A,
      (∀ a, i a = (1 : E) ⊗ₜ[F] a) ∧
      letI := transportedInvolution i
      ∀ {n : Type u} [Fintype n] [DecidableEq n] (M H : Matrix n n A),
        ((M.map i)ᴴ * H.map i * M.map i = H.map i ∧ (M.map i).det = 1) ↔
          (Mᴴ * H * M = H ∧ M.det = 1)

/-- The characteristic-two quadratic-pair equations are transported together
with the polar isometry equation on the same quaternionic matrices. -/
def QuaternionicMatrixTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    (A : Type u) [Ring A] [Algebra F A] [StarRing A],
    (∀ r : F, star (algebraMap F A r) = algebraMap F A r) →
    letI := scalarStructure e
    ∃ i : A ≃+* E ⊗[F] A,
      (∀ a, i a = (1 : E) ⊗ₜ[F] a) ∧
      letI := transportedInvolution i
      ∀ {n : Type u} [Fintype n] (M H L : Matrix n n A),
        ((M.map i)ᴴ * H.map i * M.map i = H.map i ∧
          PreservesQuaternionicQuadraticForm E (M.map i) (H.map i) (L.map i)) ↔
        (Mᴴ * H * M = H ∧ PreservesQuaternionicQuadraticForm F M H L)

/-- The spin equations in the Clifford model used over the local field. -/
def IsSpinPoint {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) (x : (CliffordAlgebra Q)ˣ) : Prop :=
  (x : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q ∧
    CliffordAlgebra.reverse (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) = 1 ∧
    ∀ z : CliffordAlgebra Q, z ∈ Set.range (CliffordAlgebra.ι Q) ↔
      (x : CliffordAlgebra Q) * z * (↑x⁻¹ : CliffordAlgebra Q) ∈
        Set.range (CliffordAlgebra.ι Q)

/-- Compatibility with the scalars, vector generators, grading, and spin equations. -/
def IsCliffordTransport {R S V W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    (e : R ≃+* S) (g : V → W) (Q : QuadraticForm R V) (P : QuadraticForm S W)
    (b : CliffordAlgebra Q ≃+* CliffordAlgebra P) : Prop :=
  (∀ r, b (algebraMap R (CliffordAlgebra Q) r) =
    algebraMap S (CliffordAlgebra P) (e r)) ∧
  (∀ v, b (CliffordAlgebra.ι Q v) = CliffordAlgebra.ι P (g v)) ∧
  (∀ x, b (CliffordAlgebra.reverse x) = CliffordAlgebra.reverse (b x)) ∧
  (∀ x, b (CliffordAlgebra.involute x) = CliffordAlgebra.involute (b x)) ∧
  (∀ x, b x ∈ CliffordAlgebra.even P ↔ x ∈ CliffordAlgebra.even Q) ∧
  (∀ x, IsSpinPoint P (Units.map b.toMonoidHom x) ↔ IsSpinPoint Q x)

/-- Relabeling the scalars of a quadratic space transports its Clifford algebra,
including in characteristic two. -/
def CliffordTransport : Prop :=
  ∀ {R S V W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    (e : R ≃+* S),
    letI := RingHomInvPair.of_ringEquiv e
    letI := RingHomInvPair.symm (↑e : R →+* S) (↑e.symm : S →+* R)
    ∀ (g : V ≃ₛₗ[(↑e : R →+* S)] W) (Q : QuadraticForm R V) (P : QuadraticForm S W),
      (∀ v, P (g v) = e (Q v)) →
      ∃ b, IsCliffordTransport e g Q P b

/-- The transported form lies on the actual scalar extension of the original vector
space. Both the scalar extension and the spin point comparison preserve its vectors. -/
def CliffordBaseChangeTransport : Prop :=
  ∀ {R S V : Type u} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V]
    (e : R ≃+* S) (Q : QuadraticForm R V),
    letI := scalarStructure e
    ∃ P : QuadraticForm S (S ⊗[R] V),
      (∀ v, P ((1 : S) ⊗ₜ[R] v) = e (Q v)) ∧
      ∃ b : CliffordAlgebra Q ≃+* CliffordAlgebra P,
        IsCliffordTransport e (fun v ↦ (1 : S) ⊗ₜ[R] v) Q P b

section EvenClifford

open CliffordAlgebra

variable {R S V W : Type u} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
  {Q : QuadraticForm R V} {P : QuadraticForm S W}

/-- Restrict a Clifford equivalence preserving parity to the even algebra. -/
def evenCliffordEquiv (b : CliffordAlgebra Q ≃+* CliffordAlgebra P)
    (hb : ∀ x, b x ∈ even P ↔ x ∈ even Q) : even Q ≃+* even P where
  toFun x := ⟨b x.val, (hb x.val).2 x.property⟩
  invFun y := ⟨b.symm y.val, (hb _).1 (by simpa only [b.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x.val)
  right_inv y := Subtype.ext (b.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul b x.val y.val)
  map_add' x y := Subtype.ext (map_add b x.val y.val)

/-- The action of a semilinear similitude on the even Clifford algebra.
The inverse multiplier occurs once per pair of vectors, so projective
similitudes give a well-defined action. -/
def IsEvenCliffordAction (Q : QuadraticForm R V) (σ : R ≃+* R)
    (s : V → V) (c : Rˣ) (a : even Q ≃+* even Q) : Prop :=
  (∀ r, a (algebraMap R (even Q) r) = algebraMap R (even Q) (σ r)) ∧
  ∀ v w, a ((even.ι Q).bilin v w) =
    algebraMap R (even Q) (↑c⁻¹ : R) * (even.ι Q).bilin (s v) (s w)

/-- The covering equation with its vector action specified. For an invertible
vector action this is the even Clifford norm-one normalizer with its projection. -/
def IsCliffordLift (Q : QuadraticForm R V) (x : (even Q)ˣ) (T : V → V) : Prop :=
  reverse (x.val.val : CliffordAlgebra Q) * x.val.val = 1 ∧
  ∀ v, x.val.val * CliffordAlgebra.ι Q v = CliffordAlgebra.ι Q (T v) * x.val.val

/-- Conjugating the marked descent action by the coefficient comparison gives
the action of the transported similitude, uniquely determined by its formulas. -/
def CliffordDescentTransport : Prop :=
  ∀ {R S V W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    (e : R ≃+* S) (g : V ≃ W) (Q : QuadraticForm R V) (P : QuadraticForm S W)
    (b : CliffordAlgebra Q ≃+* CliffordAlgebra P) (hb : IsCliffordTransport e g Q P b),
    let d := evenCliffordEquiv b hb.2.2.2.2.1
    ∀ (σ : R ≃+* R) (s : V → V) (c : Rˣ) (a : even Q ≃+* even Q),
      IsEvenCliffordAction Q σ s c a →
      let σ' := e.symm.trans (σ.trans e)
      let s' := g ∘ s ∘ g.symm
      let c' := Units.map e.toMonoidHom c
      IsEvenCliffordAction P σ' s' c' (d.symm.trans (a.trans d)) ∧
        ∀ a', IsEvenCliffordAction P σ' s' c' a' → ∀ x, a' (d x) = d (a x)

/-- The comparison preserves the vector action of a spin lift and its scalar
units. The statements hold over arbitrary commutative rings. -/
def CliffordProjectionTransport : Prop :=
  ∀ {R S V W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    (e : R ≃+* S) (g : V ≃ W) (Q : QuadraticForm R V) (P : QuadraticForm S W)
    (b : CliffordAlgebra Q ≃+* CliffordAlgebra P) (hb : IsCliffordTransport e g Q P b),
    let d := evenCliffordEquiv b hb.2.2.2.2.1
    (∀ (x : (even Q)ˣ) (T : V → V),
      IsCliffordLift P (Units.map d.toMonoidHom x) (g ∘ T ∘ g.symm) ↔ IsCliffordLift Q x T) ∧
    ∀ r : Rˣ, Units.map d.toMonoidHom (Units.map (algebraMap R (even Q)) r) =
      Units.map (algebraMap S (even P)) (Units.map e.toMonoidHom r)

end EvenClifford

section QuaternionicSpin

open CliffordAlgebra

/-- Apply a homomorphism of test algebras to the test factor of a coefficient algebra. -/
abbrev extendTestCoefficients {k : Type u} [Field k] {R S : TestAlgebra k} (a : R ⟶ S)
    (B : Type u) [Ring B] [Algebra k B] : R ⊗[k] B →ₐ[k] S ⊗[k] B :=
  Algebra.TensorProduct.map a.hom (AlgHom.id k B)

/-- Choose coordinates after splitting the endomorphism algebra of the
quaternionic module. The split form is the form of the adjoint involution or
quadratic pair in this splitting. The descent action uses its similitudes. -/
structure QuaternionicSpinChart (R A S n m J : Type u) [CommRing R] [Ring A] [CommRing S]
    [Algebra R A] [Algebra R S] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] where
  splitting : S ⊗[R] Matrix n n A ≃ₐ[S] Matrix m m S
  form : QuadraticForm S (m → S)
  scalarAction : J → S ≃+* S
  vectorAction : J → (m → S) ≃ (m → S)
  multiplier : J → Sˣ
  vectorAction_add : ∀ a v w, vectorAction a (v + w) = vectorAction a v + vectorAction a w
  vectorAction_smul : ∀ a (s : S) v, vectorAction a (s • v) = scalarAction a s • vectorAction a v
  similitude : ∀ a v, form (vectorAction a v) = (multiplier a : S) * scalarAction a (form v)
  evenAction : J → even form ≃+* even form
  evenAction_formula : ∀ j, IsEvenCliffordAction form (scalarAction j)
    (vectorAction j) (multiplier j) (evenAction j)

variable {R A B S T n m J : Type u} [CommRing R] [Ring A] [Ring B] [CommRing S] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- View a quaternionic matrix as a vector matrix over the marked splitting algebra. -/
def QuaternionicSpinChart.splitMatrix (D : QuaternionicSpinChart R A S n m J)
    (M : Matrix n n A) : Matrix m m S := D.splitting ((1 : S) ⊗ₜ[R] M)

/-- Descent of the covering diagram on an arbitrary test algebra. A point has
both its quaternionic matrix and its fixed even Clifford unit. The relation
between them is conjugation on the vectors in the marked splitting. -/
abbrev QuaternionicSpinChart.CoverPoints (D : QuaternionicSpinChart R A S n m J) :=
  {p : (Matrix n n A)ˣ × (even D.form)ˣ //
    IsCliffordLift D.form p.2 (fun v ↦ D.splitMatrix p.1.val *ᵥ v) ∧
      ∀ j, D.evenAction j p.2.val = p.2.val}

/-- Entrywise transport of a splitting, together with transport of the split
quadratic form, the normalized similitude action, and its fixed covering points. -/
structure QuaternionicSpinChartComparison (i : A ≃ₐ[R] B) (j : S ≃ₐ[R] T)
    (D : QuaternionicSpinChart R A S n m J) where
  chart : QuaternionicSpinChart R B T n m J
  splitting_eq : ∀ s M, chart.splitting (j s ⊗ₜ[R] M.map i) = (D.splitting (s ⊗ₜ[R] M)).map j
  form_eq : ∀ v : m → S, chart.form (fun k ↦ j (v k)) = j (D.form v)
  descent_eq :
    let g := Equiv.piCongrRight fun _ : m ↦ j.toEquiv
    ∀ a, chart.scalarAction a = j.toRingEquiv.symm.trans ((D.scalarAction a).trans j.toRingEquiv) ∧
      chart.vectorAction a = g.symm.trans ((D.vectorAction a).trans g) ∧
      chart.multiplier a = Units.map j.toRingEquiv.toMonoidHom (D.multiplier a)
  clifford : CliffordAlgebra D.form ≃+* CliffordAlgebra chart.form
  clifford_formula : IsCliffordTransport j.toRingEquiv (fun v k ↦ j (v k)) D.form chart.form clifford
  equivariant :
    let d := evenCliffordEquiv clifford clifford_formula.2.2.2.2.1
    ∀ a x, chart.evenAction a (d x) = d (D.evenAction a x)
  cover : D.CoverPoints ≃ chart.CoverPoints
  cover_eq :
    let d := evenCliffordEquiv clifford clifford_formula.2.2.2.2.1
    ∀ p, (cover p).val.1 = Units.map i.toRingEquiv.mapMatrix.toMonoidHom p.val.1 ∧
      (cover p).val.2 = Units.map d.toMonoidHom p.val.2
  reducedNorm_eq : ∀ M : Matrix n n A, (chart.splitMatrix (M.map i)).det = j (D.splitMatrix M).det
  reducedTrace_eq : ∀ M : Matrix n n A,
    (chart.splitMatrix (M.map i)).trace = j (D.splitMatrix M).trace
  scalar_iff : ∀ (p : D.CoverPoints) (z : Rˣ),
    (cover p).val.2 = Units.map ((algebraMap T (even chart.form)).comp (algebraMap R T)) z ↔
      p.val.2 = Units.map ((algebraMap S (even D.form)).comp (algebraMap R S)) z

def QuaternionicSpinChartTransport : Prop :=
  ∀ {R A B S T n m J : Type u} [CommRing R] [Ring A] [Ring B] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (i : A ≃ₐ[R] B) (j : S ≃ₐ[R] T) (D : QuaternionicSpinChart R A S n m J),
    Nonempty (QuaternionicSpinChartComparison i j D)

abbrev QuaternionicSpinChartComparison.evenEquiv {i : A ≃ₐ[R] B} {j : S ≃ₐ[R] T}
    {D : QuaternionicSpinChart R A S n m J} (C : QuaternionicSpinChartComparison i j D) :
    even D.form ≃+* even C.chart.form :=
  evenCliffordEquiv C.clifford C.clifford_formula.2.2.2.2.1

/-- A split matrix is fixed by conjugation under the marked semilinear similitudes. -/
def QuaternionicSpinChart.IsFixedSplitMatrix (D : QuaternionicSpinChart R A S n m J)
    (M : Matrix m m S) : Prop :=
  ∀ a v, D.vectorAction a (M *ᵥ v) = M *ᵥ D.vectorAction a v

/-- The descended even Clifford algebra inside the marked splitting. -/
def QuaternionicSpinChart.fixedEven (D : QuaternionicSpinChart R A S n m J) :
    Subring (even D.form) :=
  ⨅ a, (D.evenAction a).toRingHom.eqLocus (RingHom.id (even D.form))

/-- Entrywise transport carries the marked similitude matrices, the fixed
matrix algebra, and the descended even Clifford algebra. -/
def QuaternionicSpinDescentAlgebraTransport : Prop :=
  ∀ {R A B S T n m J : Type u} [CommRing R] [Ring A] [Ring B] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {i : A ≃ₐ[R] B} {j : S ≃ₐ[R] T} {D : QuaternionicSpinChart R A S n m J}
    (C : QuaternionicSpinChartComparison i j D),
    (∀ a (M : Matrix m m S),
      (∀ w, C.chart.vectorAction a w = (M.map j) *ᵥ fun k ↦ C.chart.scalarAction a (w k)) ↔
      (∀ v, D.vectorAction a v = M *ᵥ fun k ↦ D.scalarAction a (v k))) ∧
    (∀ M, C.chart.IsFixedSplitMatrix (M.map j) ↔ D.IsFixedSplitMatrix M) ∧
    (Set.range C.chart.splitMatrix = {M | C.chart.IsFixedSplitMatrix M} ↔
      Set.range D.splitMatrix = {M | D.IsFixedSplitMatrix M}) ∧
    ∃ d : D.fixedEven ≃+* C.chart.fixedEven, ∀ x, (d x).val = C.evenEquiv x.val

/-- The descended adjoint is read using the polar form in the marked split
matrix algebra. -/
def QuaternionicSpinChart.IsAdjoint (D : QuaternionicSpinChart R A S n m J)
    (σ : Matrix n n A → Matrix n n A) : Prop :=
  ∀ M v w, D.form.polarBilin (D.splitMatrix M *ᵥ v) w =
    D.form.polarBilin v (D.splitMatrix (σ M) *ᵥ w)

/-- The split quadratic form recovers the semitrace representative in
characteristic two through (q(v)=h(v,ℓv)). -/
def QuaternionicSpinChart.IsSemitraceRepresentative (D : QuaternionicSpinChart R A S n m J)
    (ℓ : Matrix n n A) : Prop :=
  ∀ v, D.form v = D.form.polarBilin v (D.splitMatrix ℓ *ᵥ v)

/-- The semitrace with representative `ℓ`, restricted to self-adjoint
endomorphisms, is the reduced trace of `ℓ * M`. -/
def QuaternionicSpinChart.semitrace (D : QuaternionicSpinChart R A S n m J)
    (ℓ M : Matrix n n A) : S :=
  (D.splitMatrix (ℓ * M)).trace

/-- The isometry equations in the marked quaternionic matrix model. With no
semitrace the target is the reduced-norm-one orthogonal group. With a semitrace
these are the equations for the full isometry group of the quadratic pair. -/
def QuaternionicSpinChart.IsIsometry (D : QuaternionicSpinChart R A S n m J)
    (σ : Matrix n n A → Matrix n n A) (ℓ : Option (Matrix n n A))
    (M : (Matrix n n A)ˣ) : Prop :=
  σ M.val * M.val = 1 ∧
    match ℓ with
    | none => (D.splitMatrix M.val).det = 1
    | some L => ∀ X, σ X = X → D.semitrace L (M.val * X * (M⁻¹).val) = D.semitrace L X

/-- The split adjoint, semitrace and isometry equations are expressed by the
same operations on the transported quaternionic coefficients. -/
def QuaternionicSpinEquationTransport : Prop :=
  ∀ {R A B S T n m J : Type u} [CommRing R] [Ring A] [Ring B] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {i : A ≃ₐ[R] B} {j : S ≃ₐ[R] T} {D : QuaternionicSpinChart R A S n m J}
    (C : QuaternionicSpinChartComparison i j D) (σ : Matrix n n A → Matrix n n A),
    let f := i.mapMatrix (m := n)
    let σ' := f ∘ σ ∘ f.symm
    (C.chart.IsAdjoint σ' ↔ D.IsAdjoint σ) ∧
    (∀ ℓ, C.chart.IsSemitraceRepresentative (f ℓ) ↔ D.IsSemitraceRepresentative ℓ) ∧
    (∀ ℓ X, C.chart.semitrace (f ℓ) (f X) = j (D.semitrace ℓ X)) ∧
    ∀ ℓ (M : (Matrix n n A)ˣ),
      C.chart.IsIsometry σ' (ℓ.map f) (Units.map f.toMonoidHom M) ↔ D.IsIsometry σ ℓ M

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The marked split-and-descended presentation of the original cover on all
test algebras, with its isometry coordinates and projection. -/
structure QuaternionicSpinCoverPresentation (F B L n m J : Type u) [Field F] [Ring B]
    [Algebra F B] [Field L] [Algebra F L]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G I : GroupScheme F} (π : G ⟶ I) where
  chart (R : TestAlgebra F) : QuaternionicSpinChart R (R ⊗[F] B) (R ⊗[F] L) n m J
  spin (R : TestAlgebra F) : GroupPoints G R ≃ (chart R).CoverPoints
  spin_mul (R : TestAlgebra F) (p q : GroupPoints G R) :
    (spin R (p * q)).val = (spin R p).val * (spin R q).val
  vector (R : TestAlgebra F) : GroupPoints I R →* (Matrix n n (R ⊗[F] B))ˣ
  vector_injective (R : TestAlgebra F) : Function.Injective (vector R)
  projection (R : TestAlgebra F) (p : GroupPoints G R) :
    vector R (p ≫ π.hom.hom) = (spin R p).val.1
  scalarKernel (R : TestAlgebra F) (p : GroupPoints G R) :
    (p ≫ π.hom.hom : GroupPoints I R) = 1 ↔ ∃ z : rootsOfUnity 2 R,
      (spin R p).val.2 = Units.map ((algebraMap (R ⊗[F] L) (even (chart R).form)).comp
        (algebraMap R (R ⊗[F] L))) z.val
  cliffordMap {R S : TestAlgebra F} (a : R ⟶ S) : even (chart R).form →+* even (chart S).form
  cliffordMap_scalar {R S : TestAlgebra F} (a : R ⟶ S) (t : R ⊗[F] L) :
    cliffordMap a (algebraMap (R ⊗[F] L) (even (chart R).form) t) =
      algebraMap (S ⊗[F] L) (even (chart S).form) (extendTestCoefficients a L t)
  cliffordMap_pair {R S : TestAlgebra F} (a : R ⟶ S) (v w : m → R ⊗[F] L) :
    cliffordMap a ((even.ι (chart R).form).bilin v w) =
      (even.ι (chart S).form).bilin (extendTestCoefficients a L ∘ v) (extendTestCoefficients a L ∘ w)
  spin_natural {R S : TestAlgebra F} (a : R ⟶ S) (p : GroupPoints G R) :
    (spin S (mapPoints a p)).val.1 =
        Units.map ((extendTestCoefficients a B).toRingHom.mapMatrix (m := n)).toMonoidHom (spin R p).val.1 ∧
      (spin S (mapPoints a p)).val.2 = Units.map (cliffordMap a) (spin R p).val.2
  vector_natural {R S : TestAlgebra F} (a : R ⟶ S) (p : GroupPoints I R) :
    vector S (mapPoints a p) =
      Units.map ((extendTestCoefficients a B).toRingHom.mapMatrix (m := n)).toMonoidHom (vector R p)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar action of an automorphism of the marked splitting field is
extended on the splitting-field factor of the new coefficient algebra. -/
def QuaternionicSpinGaloisActionTransport : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I : GroupScheme F} (π : G ⟶ I)
    (D : QuaternionicSpinCoverPresentation F B L n m J π),
    letI := scalarStructure e
    ∀ R : TestAlgebra E,
      let R₀ := (restrictTestAlgebra F E).obj R
      let i := testAlgebraRebase e R B
      let j := testAlgebraRebase e R L
      ∀ (C : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L) (T := R ⊗[E] (E ⊗[F] L))
          i j (D.chart R₀)) (a : J) (σ : L ≃ₐ[F] L),
        (∀ (r : R₀) (t : L), (D.chart R₀).scalarAction a (r ⊗ₜ[F] t) = r ⊗ₜ[F] σ t) →
        ∀ (r : R) (s : E) (t : L),
          C.chart.scalarAction a (r ⊗ₜ[E] (s ⊗ₜ[F] t)) = r ⊗ₜ[E] (s ⊗ₜ[F] σ t)

set_option backward.isDefEq.respectTransparency false in
/-- The actual base-changed cover is presented by the coefficient-transported
quaternionic splitting and fixed Clifford equations on every test algebra.
The formula for marked morphisms applies to the lifted opposite root maps, the
rank-one group, and the diagonal cocharacter. -/
def QuaternionicSpinCoverTransport : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I : GroupScheme F} (π : G ⟶ I)
    (D : QuaternionicSpinCoverPresentation F B L n m J π),
    letI := scalarStructure e
    let G' := (groupBaseChange F E).obj G
    let I' := (groupBaseChange F E).obj I
    let π' := (groupBaseChange F E).map π
    ∀ R : TestAlgebra E,
      let R₀ := (restrictTestAlgebra F E).obj R
      let i := testAlgebraRebase e R B
      let j := testAlgebraRebase e R L
      ∃ C : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L) (T := R ⊗[E] (E ⊗[F] L))
          i j (D.chart R₀),
        ∃ spin : GroupPoints G' R ≃ C.chart.CoverPoints,
          (∀ p, spin p = C.cover (D.spin R₀ (baseChangePoint F E G.X R p))) ∧
          (∀ p q, (spin (p * q)).val = (spin p).val * (spin q).val) ∧
        ∃ vector : GroupPoints I' R →* (Matrix n n (R ⊗[E] (E ⊗[F] B)))ˣ,
          Function.Injective vector ∧
          (∀ p, vector p = Units.map (i.toRingEquiv.mapMatrix (m := n)).toMonoidHom
            (D.vector R₀ (baseChangePoint F E I.X R p))) ∧
          (∀ p, vector (p ≫ π'.hom.hom) = (spin p).val.1) ∧
          (∀ p, (p ≫ π'.hom.hom : GroupPoints I' R) = 1 ↔ (spin p).val.1 = 1) ∧
          (∀ p, (p ≫ π'.hom.hom : GroupPoints I' R) = 1 ↔ ∃ z : rootsOfUnity 2 R,
            (spin p).val.2 = Units.map ((algebraMap (R ⊗[E] (E ⊗[F] L)) (even C.chart.form)).comp
              (algebraMap R (R ⊗[E] (E ⊗[F] L)))) z.val) ∧
          (∀ p q, (p ≫ π'.hom.hom : GroupPoints I' R) = 1 → Commute p q) ∧
          ∀ {U : GroupScheme F} (x : U ⟶ G) (p : GroupPoints ((groupBaseChange F E).obj U) R),
            spin (p ≫ ((groupBaseChange F E).map x).hom.hom) =
              C.cover (D.spin R₀ (baseChangePoint F E U.X R p ≫ x.hom.hom))

set_option backward.isDefEq.respectTransparency false in
/-- The cover comparison on test points is natural in the test algebra. The
Clifford map is determined by the new coefficient map on scalars and pairs. -/
def QuaternionicSpinCoverNaturality : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I : GroupScheme F} (π : G ⟶ I)
    (D : QuaternionicSpinCoverPresentation F B L n m J π),
    letI := scalarStructure e
    ∀ {R S : TestAlgebra E} (a : R ⟶ S),
      let R₀ := (restrictTestAlgebra F E).obj R
      let S₀ := (restrictTestAlgebra F E).obj S
      let a₀ := (restrictTestAlgebra F E).map a
      let iR := testAlgebraRebase e R B
      let iS := testAlgebraRebase e S B
      let jR := testAlgebraRebase e R L
      let jS := testAlgebraRebase e S L
      ∀ (CR : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L) (T := R ⊗[E] (E ⊗[F] L))
          iR jR (D.chart R₀))
        (CS : QuaternionicSpinChartComparison (S := S₀ ⊗[F] L) (T := S ⊗[E] (E ⊗[F] L))
          iS jS (D.chart S₀)),
      let f := CS.evenEquiv.toRingHom.comp ((D.cliffordMap a₀).comp CR.evenEquiv.symm.toRingHom)
      let g := extendTestCoefficients a (E ⊗[F] L)
      let b := extendTestCoefficients a (E ⊗[F] B)
      (∀ t : R ⊗[E] (E ⊗[F] L), f (algebraMap _ (even CR.chart.form) t) =
        algebraMap _ (even CS.chart.form) (g t)) ∧
      (∀ v w : m → R ⊗[E] (E ⊗[F] L), f ((even.ι CR.chart.form).bilin v w) =
        (even.ι CS.chart.form).bilin (g ∘ v) (g ∘ w)) ∧
      (∀ p : GroupPoints ((groupBaseChange F E).obj G) R,
        let pR := CR.cover (D.spin R₀ (baseChangePoint F E G.X R p))
        let pS := CS.cover (D.spin S₀ (baseChangePoint F E G.X S (mapPoints a p)))
        pS.val.1 = Units.map (b.toRingHom.mapMatrix (m := n)).toMonoidHom pR.val.1 ∧
          pS.val.2 = Units.map f pR.val.2) ∧
      ∀ p : GroupPoints ((groupBaseChange F E).obj I) R,
        let pR := Units.map (iR.toRingEquiv.mapMatrix (m := n)).toMonoidHom
          (D.vector R₀ (baseChangePoint F E I.X R p))
        let pS := Units.map (iS.toRingEquiv.mapMatrix (m := n)).toMonoidHom
          (D.vector S₀ (baseChangePoint F E I.X S (mapPoints a p)))
        pS = Units.map (b.toRingHom.mapMatrix (m := n)).toMonoidHom pR

set_option backward.isDefEq.respectTransparency false in
/-- On rational points the quaternionic matrix and the Clifford coordinates
of the actual scalar extension are obtained from the original `F`-point. -/
def QuaternionicSpinRationalTransport : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I : GroupScheme F} (π : G ⟶ I)
    (D : QuaternionicSpinCoverPresentation F B L n m J π),
    letI := scalarStructure e
    let R := CommAlgCat.of E E
    let R₀ := (restrictTestAlgebra F E).obj R
    let R_F := CommAlgCat.of F F
    let a : R_F ⟶ R₀ := CommAlgCat.ofHom
      { toRingHom := e.toRingHom, commutes' := fun _ ↦ rfl }
    let i := testAlgebraRebase e R B
    let j := testAlgebraRebase e R L
    ∀ C : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L) (T := R ⊗[E] (E ⊗[F] L))
        i j (D.chart R₀),
      let b := (Algebra.TensorProduct.lid E (E ⊗[F] B)).toRingHom.comp
        (i.toRingHom.comp (extendTestCoefficients a B).toRingHom)
      let t := j.toRingHom.comp (extendTestCoefficients a L).toRingHom
      let d := C.evenEquiv.toRingHom.comp (D.cliffordMap a)
      (∀ (r : F) (z : B), b (r ⊗ₜ[F] z) = e r ⊗ₜ[F] z) ∧
      (∀ (r : F) (z : L), t (r ⊗ₜ[F] z) = e r ⊗ₜ[E] ((1 : E) ⊗ₜ[F] z)) ∧
      Function.Bijective d ∧
      (∀ s, d (algebraMap (R_F ⊗[F] L) (even (D.chart R_F).form) s) =
        algebraMap (R ⊗[E] (E ⊗[F] L)) (even C.chart.form) (t s)) ∧
      (∀ v w : m → R_F ⊗[F] L, d ((even.ι (D.chart R_F).form).bilin v w) =
        (even.ι C.chart.form).bilin (t ∘ v) (t ∘ w)) ∧
      (∀ p : RationalPoints ((groupBaseChange F E).obj G).X,
        let x := C.cover (D.spin R₀ (baseChangePoint F E G.X R p))
        let y := D.spin R_F (originalPoint e G.X p)
        Units.map (Algebra.TensorProduct.lid E (E ⊗[F] B)).toRingHom.mapMatrix.toMonoidHom
          x.val.1 = Units.map (b.mapMatrix (m := n)).toMonoidHom y.val.1 ∧
        x.val.2 = Units.map d y.val.2) ∧
      ∀ p : RationalPoints ((groupBaseChange F E).obj I).X,
        Units.map ((Algebra.TensorProduct.lid E (E ⊗[F] B)).toRingHom.comp i.toRingHom).mapMatrix.toMonoidHom
          (D.vector R₀ (baseChangePoint F E I.X R p)) =
        Units.map (b.mapMatrix (m := n)).toMonoidHom (D.vector R_F (originalPoint e I.X p))

set_option backward.isDefEq.respectTransparency false in
/-- In the transported covering coordinates the additive root lift and the
diagonal lift use the corresponding scalar and unit parameters, respectively. -/
def QuaternionicSpinMarkedLiftTransport : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I : GroupScheme F} (π : G ⟶ I)
    (D : QuaternionicSpinCoverPresentation F B L n m J π)
    {A : AdditiveLine F} (x : A.group ⟶ G) (c : Cocharacter G),
    letI := scalarStructure e
    let K := groupBaseChange F E
    let M := specGroup (groupAlgebra F IntegerCharacters)
    ∃ param : ∀ R : TestAlgebra E, R ≃ GroupPoints (K.obj A.group) R,
      ∃ torus : specGroup (groupAlgebra E IntegerCharacters) ≅ K.obj M,
        let c' : Cocharacter (K.obj G) := torus.hom ≫ K.map c
        (∀ a : F, originalPoint e G.X
          (param (CommAlgCat.of E E) (e a) ≫ (K.map x).hom.hom) =
            rootPoint x (CommAlgCat.of F F) a) ∧
        (∀ s : Fˣ, originalPoint e G.X
          (cocharacterPoint c' (CommAlgCat.of E E) (Units.map e.toMonoidHom s)) =
            cocharacterPoint c (CommAlgCat.of F F) s) ∧
        ∀ R : TestAlgebra E,
          let R₀ := (restrictTestAlgebra F E).obj R
          let i := testAlgebraRebase e R B
          let j := testAlgebraRebase e R L
          ∀ C : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L)
              (T := R ⊗[E] (E ⊗[F] L)) i j (D.chart R₀),
            let spin := fun p : GroupPoints (K.obj G) R ↦
              C.cover (D.spin R₀ (baseChangePoint F E G.X R p))
            (∀ a : R, spin (param R a ≫ (K.map x).hom.hom) =
              C.cover (D.spin R₀ (rootPoint x R₀ a))) ∧
            ∀ s : Rˣ, spin (cocharacterPoint c' R s) =
              C.cover (D.spin R₀ (cocharacterPoint c R₀ s))

open Specs.DiagonalizableGroups (rootsOfUnityPoints)

/-- The marked scalar `μ₂` stays the scheme kernel of the covering projection.
Its identification on all test algebras is natural and uses the same scalar. -/
def QuaternionicSpinKernelTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    {G I Z U : GroupScheme F} (π : G ⟶ I) (z : Z ⟶ G) (p : Z ⟶ U) (unitInclusion : U ⟶ I),
    IsTerminal U → IsPullback z p π unitInclusion →
    ∀ h : (groupPointsFunctor F).obj Z ≅ rootsOfUnityPoints F 2,
      letI := scalarStructure e
      let K := groupBaseChange F E
      IsPullback (K.map z) (K.map p) (K.map π) (K.map unitInclusion) ∧ Nonempty (IsTerminal (K.obj U)) ∧
      ∃ h' : (groupPointsFunctor E).obj (K.obj Z) ≅ rootsOfUnityPoints E 2,
        ∀ (R : TestAlgebra E) (q : GroupPoints (K.obj Z) R),
          h'.hom.app R q = h.hom.app ((restrictTestAlgebra F E).obj R) (baseChangePoint F E Z.X R q)

set_option backward.isDefEq.respectTransparency false in
/-- The scalar identification of the scheme kernel agrees with the scalar
Clifford unit in the transported coordinate presentation. -/
def QuaternionicSpinScalarKernelTransport : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I Z U : GroupScheme F} (π : G ⟶ I)
    (D : QuaternionicSpinCoverPresentation F B L n m J π)
    (z : Z ⟶ G) (p : Z ⟶ U) (unitInclusion : U ⟶ I),
    IsTerminal U → IsPullback z p π unitInclusion →
    ∀ h : (groupPointsFunctor F).obj Z ≅ rootsOfUnityPoints F 2,
      (∀ (R : TestAlgebra F) (q : GroupPoints Z R),
        let x := D.spin R (q ≫ z.hom.hom)
        x.val.1 = 1 ∧
          x.val.2 = Units.map ((algebraMap (R ⊗[F] L) (even (D.chart R).form)).comp
            (algebraMap R (R ⊗[F] L))) (h.hom.app R q).val) →
      letI := scalarStructure e
      let K := groupBaseChange F E
      IsPullback (K.map z) (K.map p) (K.map π) (K.map unitInclusion) ∧
        Nonempty (IsTerminal (K.obj U)) ∧
      ∃ h' : (groupPointsFunctor E).obj (K.obj Z) ≅ rootsOfUnityPoints E 2,
        ∀ R : TestAlgebra E,
          let R₀ := (restrictTestAlgebra F E).obj R
          let i := testAlgebraRebase e R B
          let j := testAlgebraRebase e R L
          ∀ (C : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L)
              (T := R ⊗[E] (E ⊗[F] L)) i j (D.chart R₀))
            (q : GroupPoints (K.obj Z) R),
            let q₀ := baseChangePoint F E Z.X R q
            let x := C.cover (D.spin R₀ (baseChangePoint F E G.X R (q ≫ (K.map z).hom.hom)))
            h'.hom.app R q = h.hom.app R₀ q₀ ∧
            x.val.1 = 1 ∧
            x.val.2 = Units.map ((algebraMap (R ⊗[E] (E ⊗[F] L)) (even C.chart.form)).comp
              (algebraMap R (R ⊗[E] (E ⊗[F] L)))) (h'.hom.app R q).val

end QuaternionicSpin

/-- The specified closed subgroup and its inclusion, after scalar extension. -/
def transportedSubgroup (F E : Type u) [Field F] [Field E] [Algebra F E]
    {G : GroupScheme F} (U : ClosedSubgroup G) :
    ClosedSubgroup ((groupBaseChange F E).obj G) := by
  let b := fieldSpecMap F E
  let j := U.inclusion.hom.hom
  let j' := ((baseChange F E).map j).left
  have hU : IsPullback (pullback.fst U.group.X.hom b) (pullback.snd U.group.X.hom b)
      (j.left ≫ G.X.hom) b := by
    rw [Over.w j]
    exact IsPullback.of_hasPullback _ _
  have h₁ : j' ≫ pullback.fst G.X.hom b = pullback.fst U.group.X.hom b ≫ j.left :=
    pullback.lift_fst _ _ _
  have h₂ : j' ≫ pullback.snd G.X.hom b = pullback.snd U.group.X.hom b :=
    pullback.lift_snd _ _ _
  exact ⟨_, (groupBaseChange F E).map U.inclusion, MorphismProperty.of_isPullback
    (IsPullback.of_bot (h₂.symm ▸ hU) h₁.symm (IsPullback.of_hasPullback G.X.hom b))
      U.isClosedImmersion⟩

/-- Extension along a field isomorphism is an equivalence of group schemes.
The embedding condition on each marked morphism is reflected as well. -/
def GroupSchemeTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E),
    letI := scalarStructure e
    (groupBaseChange F E).IsEquivalence ∧
      ∀ {G H : GroupScheme F} (f : G ⟶ H),
        IsClosedImmersion ((groupBaseChange F E).map f).hom.hom.left ↔
          IsClosedImmersion f.hom.hom.left

def identitySchemePoint {F : Type u} [Field F] (G : GroupScheme F) : G.X.left :=
  (1 : RationalPoints G.X).left (default : PrimeSpectrum F)

/-- The open subgroup given by the identity component is carried to the
identity component of the transported group. This applies to the isometries
of the quaternionic quadratic pair in characteristic two. -/
def IdentityComponentTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) {H G : GroupScheme F} (i : H ⟶ G),
    letI := scalarStructure e
    let G' := (groupBaseChange F E).obj G
    let i' := (groupBaseChange F E).map i
    (IsOpenImmersion i'.hom.hom.left ∧
      Set.range i'.hom.hom.left = connectedComponent (identitySchemePoint G')) ↔
    (IsOpenImmersion i.hom.hom.left ∧
      Set.range i.hom.hom.left = connectedComponent (identitySchemePoint G))

/-- A marked isometry model is specified on every test algebra. In odd
characteristic take the vector target itself, with no semitrace. In
characteristic two take the full isometry group, with the vector target included
as its open identity component. -/
structure QuaternionicSpinIsometryPresentation (F B L n m J : Type u) [Field F] [Ring B]
    [Algebra F B] [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G I O : GroupScheme F} {π : G ⟶ I} (D : QuaternionicSpinCoverPresentation F B L n m J π)
    (incl : I ⟶ O) where
  adjoint (R : TestAlgebra F) : Matrix n n (R ⊗[F] B) → Matrix n n (R ⊗[F] B)
  adjoint_eq (R : TestAlgebra F) : (D.chart R).IsAdjoint (adjoint R)
  semitrace (R : TestAlgebra F) : Option (Matrix n n (R ⊗[F] B))
  semitrace_eq (R : TestAlgebra F) (ℓ : Matrix n n (R ⊗[F] B)) :
    semitrace R = some ℓ → (D.chart R).IsSemitraceRepresentative ℓ
  coordinates (R : TestAlgebra F) : GroupPoints O R →* (Matrix n n (R ⊗[F] B))ˣ
  coordinates_injective (R : TestAlgebra F) : Function.Injective (coordinates R)
  coordinates_range (R : TestAlgebra F) (M : (Matrix n n (R ⊗[F] B))ˣ) :
    M ∈ Set.range (coordinates R) ↔ (D.chart R).IsIsometry (adjoint R) (semitrace R) M
  inclusion (R : TestAlgebra F) (p : GroupPoints I R) :
    coordinates R (p ≫ incl.hom.hom) = D.vector R p

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of the isometry model has the transported matrix equations.
The transported covering projection takes the quaternionic matrix of the same
fixed Clifford point. The open identity component and the finite faithfully
flat covering property are preserved. -/
def QuaternionicSpinIsometryTransport : Prop :=
  ∀ {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
    [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : F ≃+* E) {G I O : GroupScheme F} (π : G ⟶ I) (incl : I ⟶ O)
    (D : QuaternionicSpinCoverPresentation F B L n m J π)
    (V : QuaternionicSpinIsometryPresentation F B L n m J D incl),
    letI := scalarStructure e
    let K := groupBaseChange F E
    let incl' := K.map incl
    let π' := (K.map π).hom.hom.left
    ((IsFinite π' ∧ Flat π' ∧ Surjective π') ↔
      (IsFinite π.hom.hom.left ∧ Flat π.hom.hom.left ∧ Surjective π.hom.hom.left)) ∧
    (IsOpenImmersion incl'.hom.hom.left ∧
      Set.range incl'.hom.hom.left = connectedComponent (identitySchemePoint (K.obj O)) ↔
      IsOpenImmersion incl.hom.hom.left ∧
        Set.range incl.hom.hom.left = connectedComponent (identitySchemePoint O)) ∧
    ∀ R : TestAlgebra E,
      let R₀ := (restrictTestAlgebra F E).obj R
      let i := testAlgebraRebase e R B
      let j := testAlgebraRebase e R L
      ∀ C : QuaternionicSpinChartComparison (S := R₀ ⊗[F] L) (T := R ⊗[E] (E ⊗[F] L))
          i j (D.chart R₀),
        let f := i.mapMatrix (m := n)
        let σ' := f ∘ V.adjoint R₀ ∘ f.symm
        let ℓ' := (V.semitrace R₀).map f
        ∃ coordinates : GroupPoints (K.obj O) R →* (Matrix n n (R ⊗[E] (E ⊗[F] B)))ˣ,
          Function.Injective coordinates ∧
          (∀ p, coordinates p = Units.map f.toMonoidHom
            (V.coordinates R₀ (baseChangePoint F E O.X R p))) ∧
          C.chart.IsAdjoint σ' ∧
          (∀ ℓ, ℓ' = some ℓ → C.chart.IsSemitraceRepresentative ℓ) ∧
          (∀ M, M ∈ Set.range coordinates ↔ C.chart.IsIsometry σ' ℓ' M) ∧
          ∀ p : GroupPoints (K.obj G) R,
            coordinates ((p ≫ (K.map π).hom.hom) ≫ incl'.hom.hom) =
              (C.cover (D.spin R₀ (baseChangePoint F E G.X R p))).val.1

/-- The image of the actual subgroup inclusion on rational points is carried to
the image of the base-changed inclusion. -/
def RationalSubgroupTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E)
    {G : GroupScheme F} (U : ClosedSubgroup G),
    letI := scalarStructure e
    let U' := transportedSubgroup F E U
    ∀ p : RationalPoints ((groupBaseChange F E).obj G).X,
      (∃ q : RationalPoints U'.group.X, q ≫ U'.inclusion.hom.hom = p) ↔
      (∃ q : RationalPoints U.group.X, q ≫ U.inclusion.hom.hom = originalPoint e G.X p)

def RadicalTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) (G : AffineAlgebraicGroup F)
    (U : ClosedSubgroup G.val),
    letI := scalarStructure e
    Specs.GeometricRadicals.IsUnipotentRadical (Specs.Unipotent.baseChangedAlgebraicGroup E G)
      (transportedSubgroup F E U) ↔ Specs.GeometricRadicals.IsUnipotentRadical G U

def ParabolicTransport : Prop :=
  ∀ {F E : Type u} [Field F] [Field E] (e : F ≃+* E) (G : AffineAlgebraicGroup F)
    (P : ClosedSubgroup G.val),
    letI := scalarStructure e
    Specs.BorelProper.IsParabolic (Specs.Unipotent.baseChangedAlgebraicGroup E G)
      (transportedSubgroup F E P) ↔ Specs.BorelProper.IsParabolic G P

end

end LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
