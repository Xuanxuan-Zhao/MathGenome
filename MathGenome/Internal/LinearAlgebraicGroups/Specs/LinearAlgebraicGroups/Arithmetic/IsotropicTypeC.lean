import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import Mathlib.LinearAlgebra.Matrix.Notation

open MulOpposite AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped Matrix

universe u v w

namespace LinearAlgebraicGroups.Specs.IsotropicTypeC

open SymplecticInvolutionModels (AntiAutomorphism HermitianPairing quaternionConjugate)
open Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)

variable {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]

/-- The value of quaternion conjugation, with the opposite multiplication removed. -/
def conjugate (s : AntiAutomorphism F B) (a : B) : B := unop (s a)

def Admissible (s : AntiAutomorphism F B) (q : Fˣ) (a b : B) : Prop :=
  b + conjugate s b = -(a * conjugate s a * algebraMap F B (↑q⁻¹ : F))

def upper (s : AntiAutomorphism F B) (q : Fˣ) (a b : B) : Matrix (Fin 3) (Fin 3) B :=
  !![1, a, b; 0, 1, -(conjugate s a * algebraMap F B (↑q⁻¹ : F)); 0, 0, 1]

def lower (s : AntiAutomorphism F B) (q : Fˣ) (a b : B) : Matrix (Fin 3) (Fin 3) B :=
  !![1, 0, 0; conjugate s a * algebraMap F B (↑q⁻¹ : F), 1, 0; b, -a, 1]

def interchange (s : AntiAutomorphism F B) (q : Fˣ) (a b : B) :
    Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, b; 0, 1 + conjugate s a * b⁻¹ * a * algebraMap F B (↑q⁻¹ : F), 0;
    (conjugate s b)⁻¹, 0, 0]

def gram (q : Fˣ) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 0, 1; 0, algebraMap F B (q : F), 0; 1, 0, 0]

/-- Admissible words consist of invertible matrices preserving the same
quaternionic Hermitian Gram matrix. -/
def ShearIsometries : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (s : AntiAutomorphism F B), Function.Involutive (conjugate s) →
    ∀ (q : Fˣ) (a b : B), Admissible s q a b →
    let H : Matrix (Fin 3) (Fin 3) B := gram q
    let U := upper s q a b
    let L := lower s q a b
    IsUnit U ∧
      QuaternionHermitianCocharacters.adjoint s.toAlgHom U * H * U = H ∧
      IsUnit L ∧ QuaternionHermitianCocharacters.adjoint s.toAlgHom L * H * L = H

/-- The three-factor identity in the ordered coordinates `e,w,f`. -/
def ThreeFactorInterchange : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
      (∀ x, conjugate s x = quaternionConjugate hB x) →
      ∀ (q : Fˣ) (a b : B), Admissible s q a b → b ≠ 0 →
        Admissible s q ((conjugate s b)⁻¹ * a) (conjugate s b)⁻¹ ∧
        Admissible s q (b⁻¹ * a) (conjugate s b)⁻¹ ∧
        lower s q ((conjugate s b)⁻¹ * a) (conjugate s b)⁻¹ * upper s q a b *
          lower s q (b⁻¹ * a) (conjugate s b)⁻¹ = interchange s q a b

/-- Every norm-one scalar is realized as the middle coordinate of an
admissible interchange. The identity uses a nonzero trace-zero parameter. -/
def NormOneMiddleEntries : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
      (∀ x, conjugate s x = quaternionConjugate hB x) →
      ∀ (q : Fˣ) (r : B), r * conjugate s r = 1 →
        ∃ a b : B, b ≠ 0 ∧ Admissible s q a b ∧
          interchange s q a b 1 1 = r ∧ (r = 1 → a = 0)

def TraceZeroRatios : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ t : Bˣ, ∃ b c : Bˣ, reducedTrace hB b = 0 ∧ reducedTrace hB c = 0 ∧ t = b * c⁻¹

/-- Nonzero trace functionals on the quaternion algebra detect a
norm-one quaternion, including in characteristic two. -/
def TraceOnNormOne : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
      (∀ x, conjugate s x = quaternionConjugate hB x) →
      ∀ c : B, c ≠ 0 → ∃ r : B, r * conjugate s r = 1 ∧ reducedTrace hB (c * r) ≠ 0

def planeUpper (b : B) : Matrix (Fin 2) (Fin 2) B := !![1, b; 0, 1]

def planeLower (b : B) : Matrix (Fin 2) (Fin 2) B := !![1, 0; b, 1]

def planeInterchange (b : B) : Matrix (Fin 2) (Fin 2) B :=
  planeUpper b * planeLower (-b⁻¹) * planeUpper b

/-- Interchange in the hyperbolic plane alone, including when the orthogonal
complement is zero. Its three parameters have reduced trace zero. -/
def PurePlaneWords : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
      (∀ x, conjugate s x = quaternionConjugate hB x) →
      (∀ b : Bˣ, reducedTrace hB b = 0 →
        reducedTrace hB (-(b : B)⁻¹) = 0 ∧
        planeInterchange (b : B) = !![0, (b : B); (conjugate s b)⁻¹, 0]) ∧
      ∀ t : Bˣ, ∃ b c : Bˣ, reducedTrace hB b = 0 ∧ reducedTrace hB c = 0 ∧
        planeInterchange (b : B) * planeInterchange (-(c : B)) =
          Matrix.diagonal ![(t : B), (conjugate s t)⁻¹]

/-- The raw matrix words supplied by the two opposite shear families. -/
def radicalWords (s : AntiAutomorphism F B) (q : Fˣ) :
    Submonoid (Matrix (Fin 3) (Fin 3) B) :=
  Submonoid.closure {g | ∃ a b, Admissible s q a b ∧ (g = upper s q a b ∨ g = lower s q a b)}

/-- The words realize independent hyperbolic-pair scales and norm-one
scales of the middle line. -/
def LineAndPairScaleWords : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
      (∀ x, conjugate s x = quaternionConjugate hB x) →
      ∀ (q : Fˣ) (t : Bˣ) (r : B), r * conjugate s r = 1 →
        Matrix.diagonal ![(t : B), r, (conjugate s t)⁻¹] ∈ radicalWords s q

section Hermitian

variable {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V]

/-- Right-linear automorphisms preserving the given quaternionic pairing. -/
def isometries {s : AntiAutomorphism F B} (h : HermitianPairing s V) :
    Subgroup (V ≃ₗ[Bᵐᵒᵖ] V) where
  carrier := {g | ∀ x y, h.value (g x) (g y) = h.value x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {g f} hg hf := fun x y => (hg (f x) (f y)).trans (hf x y)
  inv_mem' {g} hg := by
    intro x y
    change h.value (g.symm x) (g.symm y) = h.value x y
    simpa using (hg (g.symm x) (g.symm y)).symm

/-- Reflections may have any norm-one scale on a nonisotropic line. -/
def LineReflection {s : AntiAutomorphism F B} (h : HermitianPairing s V)
    (g : isometries h) : Prop :=
  ∃ (z : V) (r : B), h.value z z ≠ 0 ∧ r * conjugate s r = 1 ∧
    g.val z = op r • z ∧ ∀ x, h.value z x = 0 → g.val x = x

/-- The full isometry group of a nondegenerate quaternionic Hermitian space
is generated by scalings of its nonisotropic lines. -/
def ReflectionGeneration : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [Infinite F] [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B), (∀ x, conjugate s x = quaternionConjugate hB x) →
      ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] [Module.Finite Bᵐᵒᵖ V]
        (h : HermitianPairing s V),
        Subgroup.closure {g : isometries h | LineReflection h g} = ⊤

end Hermitian

section Approximation

open _root_.LinearAlgebraicGroups.Arithmetic _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Arithmetic.OppositeRadicals (IsNoncentral)
open Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Arithmetic.RelativeRayGeneration (unipotentGenerated)
open CharacterDescent (Cocharacter)
open IntegralModels (MatrixRealization)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open SymplecticDatumTorusAndBorel (HyperbolicIndex)
open SymplecticMatrixStructure (symplecticPoints)
open TypeCSplitRecognition (HasGeometricCartanTypeC)
open Unipotent (baseChangedAlgebraicGroup)

/-- The full point group of the split matrix model is generated by rational
parabolic radicals, including at a completion of a nonsplit global form. -/
def SplitLocalGeneration : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ) (G : AffineAlgebraicGroup F)
    (_ : (groupPointsFunctor F).obj G.val ≅ symplecticPoints F (HyperbolicIndex.{u} (n + 1))),
    unipotentGenerated G = ⊤

/-- The quaternionic local model is generated by rational parabolic radicals
as soon as its Hermitian form contains the specified hyperbolic plane. -/
def QuaternionLocalGeneration : Prop :=
  ∀ (F : Type u) [Field F] [Infinite F] (G : AffineAlgebraicGroup F)
    (_ : GeometricRadicals.IsReductive G)
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B), (∀ x, conjugate s x = quaternionConjugate hB x) →
      ∀ {r : ℕ} (H : (Matrix (Fin r) (Fin r) B)ˣ)
        (_ : SymplecticDivisionForms.dagger s H.val = H.val)
        (_ : (groupPointsFunctor F).obj G.val ≅
          QuaternionHermitianCocharacters.isometryPoints s.toAlgHom H.val),
        let h := QuaternionHermitianCocharacters.pairing s.toAlgHom H.val
        (∀ x, x ≠ 0 → ∃ y, h x y ≠ 0) →
        (∀ x, ∃ a : F, h x x = algebraMap F B a) →
        ∀ e f : Fin r → B, h e e = 0 → h f f = 0 → h e f = 1 → h f e = 1 →
          unipotentGenerated G = ⊤

/-- The local groups in the approximation reduction are those of the
actual scalar extensions of the given global group. -/
def ApproximationFromLocalGeneration : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → ∀ c : Cocharacter G.val, IsNoncentral c →
    ∀ (S : Finset D.Place), S.Nonempty →
      (∀ w : Outside D S, unipotentGenerated (baseChangedAlgebraicGroup (D.Completion w.1) G) = ⊤) →
      StrongApproximation D i S

/-- A globally isotropic, simply connected, absolutely almost simple
type C group has strong approximation outside every finite nonempty S. -/
def TypeCStrongApproximation : Prop :=
  ∀ {K E : Type u} [Field K] [Field E] [Algebra K E] [IsSepClosure K E]
    (D : GlobalFieldData.{u,v} K) (n : ℕ) (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G), IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G → HasGeometricCartanTypeC n G →
    ∀ c : Cocharacter G.val, IsNoncentral c →
      ∀ (S : Finset D.Place), S.Nonempty → StrongApproximation D i S

end Approximation

end LinearAlgebraicGroups.Specs.IsotropicTypeC
