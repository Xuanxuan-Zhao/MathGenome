import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.Group.Units.Opposite

open CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.UnitaryNormEquations

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Algebra.TensorProduct MulOpposite
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

variable {F E A R S : Type u} [Field F] [Field E] [Algebra F E]
  [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]

/-- The involution is an algebra isomorphism to the opposite over the ground
field. Its restriction to the centre is the nonidentity quadratic automorphism. -/
structure SecondKind (F E A : Type u) [Field F] [Field E] [Algebra F E]
    [Ring A] [Algebra F A] [Algebra E A] where
  conjugation : E ≃ₐ[F] E
  conjugation_ne : conjugation ≠ 1
  adjoint : A ≃ₐ[F] Aᵐᵒᵖ
  adjoint_adjoint : ∀ a, unop (adjoint (unop (adjoint a))) = a
  adjoint_centre : ∀ e, unop (adjoint (algebraMap E A e)) = algebraMap E A (conjugation e)

/-- Build the ground-field algebra involution from its ring form and its
restriction to the quadratic centre. -/
def SecondKind.ofRingEquiv (conjugation : E ≃ₐ[F] E) (hne : conjugation ≠ 1)
    (star : A ≃+* Aᵐᵒᵖ) (hsq : ∀ a, unop (star (unop (star a))) = a)
    (hc : ∀ c, unop (star (algebraMap E A c)) = algebraMap E A (conjugation c)) :
    SecondKind F E A :=
  ⟨conjugation, hne, AlgEquiv.ofRingEquiv (f := star) (by
    intro c
    apply MulOpposite.unop_injective
    change unop (star (algebraMap F A c)) = algebraMap F A c
    rw [IsScalarTower.algebraMap_apply F E A, hc, conjugation.commutes]), hsq, hc⟩

variable [CommRing R] [Algebra F R]

/-- The extension of the quadratic centre to the coefficient algebra. -/
abbrev Centre (F E R : Type u) [Field F] [Field E] [Algebra F E]
    [CommRing R] [Algebra F R] := R ⊗[F] E

local instance (priority := 2000) : Algebra E (Centre F E R) := Algebra.TensorProduct.rightAlgebra

/-- Associate the coefficient extension of the centre with that of the algebra. -/
def associateCentre : (R ⊗[F] A) ≃ₐ[F] (Centre F E R ⊗[E] A) :=
  (Algebra.TensorProduct.comm F R A).trans
    ((Algebra.TensorProduct.congr ((Algebra.TensorProduct.rid E E A).symm.restrictScalars F)
      (.refl : R ≃ₐ[F] R)).trans
    (((Algebra.TensorProduct.assoc F E E A E R).trans
      ((Algebra.TensorProduct.congr (.refl : A ≃ₐ[E] A)
        (Algebra.TensorProduct.commRight F E R)).trans
          (Algebra.TensorProduct.comm E A (Centre F E R)))).restrictScalars F))

@[simp] theorem associateCentre_tmul (r : R) (a : A) :
    associateCentre (E := E) (r ⊗ₜ[F] a) = (r ⊗ₜ[F] (1 : E)) ⊗ₜ[E] a := rfl

/-- The reduced norm after extension to a commutative ground-field algebra. -/
def unitaryNorm {ι : Type u} [Fintype ι] (hA : isCentralSimple E A)
    (b : Module.Basis ι E A) (x : R ⊗[F] A) : Centre F E R :=
  normAt hA b (associateCentre x)

/-- The coefficient extension of the adjoint, as an algebra map to the opposite. -/
def adjointEquiv (s : SecondKind F E A) : R ⊗[F] A ≃ₐ[R] (R ⊗[F] A)ᵐᵒᵖ :=
  (Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) s.adjoint).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.toOpposite R R) (.refl : Aᵐᵒᵖ ≃ₐ[F] Aᵐᵒᵖ)).trans
      (Algebra.TensorProduct.opAlgEquiv F R R A))

/-- The coefficient extension of the adjoint on elements. -/
def adjointAt (s : SecondKind F E A) (x : R ⊗[F] A) : R ⊗[F] A :=
  unop (adjointEquiv s x)

omit [IsScalarTower F E A] in
@[simp] theorem adjointAt_tmul (s : SecondKind F E A) (r : R) (a : A) :
    adjointAt s (r ⊗ₜ[F] a) = r ⊗ₜ[F] unop (s.adjoint a) := rfl

/-- The special unitary equations on units at an arbitrary test algebra. -/
def IsSpecialUnitary {ι : Type u} [Fintype ι] (hA : isCentralSimple E A)
    (b : Module.Basis ι E A) (s : SecondKind F E A) (x : (R ⊗[F] A)ˣ) : Prop :=
  adjointAt s x.val * x.val = 1 ∧ unitaryNorm hA b x.val = 1

open LinearAlgebraicGroups.Specs

/-- A finite-type affine group whose algebra-valued points are exactly the
units satisfying the special unitary equations, with the inherited group law
and natural coefficient maps. -/
def SpecialUnitaryRepresentability : Prop :=
  ∀ (F E A : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι E A) (s : SecondKind F E A),
    ∃ (G : AffineAlgebraicGroup F) (P : TestAlgebra F ⥤ GrpCat.{u})
      (_ : (groupPointsFunctor F).obj G.val ≅ P)
      (point : ∀ R : TestAlgebra F, P.obj R ≃ {x : (R ⊗[F] A)ˣ // IsSpecialUnitary hA b s x}),
      (∀ R, (point R 1).1 = 1) ∧
      (∀ R (x y : P.obj R), (point R (x * y)).1 = (point R x).1 * (point R y).1) ∧
      (∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : P.obj R),
        (point S (P.map f x)).1 =
          Units.map (map f.hom (AlgHom.id F A)).toMonoidHom (point R x).1)

section SplitCentre

variable [Algebra E R] [IsScalarTower F E R]

/-- Projection of the extended centre onto the factor of the chosen embedding. -/
def centreAugmentation : Centre F E R →ₐ[E] R :=
  { toRingHom := (lift (R := F) (S := R) (AlgHom.id R R) (IsScalarTower.toAlgHom F E R)
        (fun _ _ => Commute.all _ _)).toRingHom
    commutes' := fun e => by
      change (1 : R) * algebraMap E R e = _
      rw [one_mul] }

/-- Projection of the extended algebra onto the factor of the chosen embedding. -/
def factorProjection : (R ⊗[F] A) →ₐ[F] (R ⊗[E] A) :=
  (lift (R := F) (S := R) (includeLeft : R →ₐ[R] R ⊗[E] A)
    ((includeRight : A →ₐ[E] R ⊗[E] A).restrictScalars F)
    (fun _ _ => (Commute.one_right _).tmul (Commute.one_left _))).restrictScalars F

/-- The two factor coordinates use the given embedding for the first factor
and the conjugate embedding, followed by the adjoint, for the opposite factor. -/
def factorPair (s : SecondKind F E A) :
    (R ⊗[F] A) →ₐ[F] (R ⊗[E] A) × (R ⊗[E] A)ᵐᵒᵖ :=
  factorProjection.prod ((AlgHom.op factorProjection).comp
    ((adjointEquiv (R := R) s).toAlgHom.restrictScalars F))

/-- On any coefficient algebra above a splitting of the centre, projecting
to the chosen factor gives exactly the norm-one units. The other factor
in these coordinates is the opposite of the inverse. -/
def SplitCentreComparison : Prop :=
  ∀ {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι E A) (s : SecondKind F E A)
    {R : Type u} [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R],
    Function.Bijective (factorPair (R := R) s) ∧
    (∀ x : R ⊗[F] A, factorPair s (adjointAt s x) =
      (unop (factorPair s x).2, op (factorPair s x).1)) ∧
    ∃ e : {x : (R ⊗[F] A)ˣ // IsSpecialUnitary hA b s x} ≃
      {y : (R ⊗[E] A)ˣ // normAt hA b y.val = 1},
      (∀ x, (e x).1 = Units.map factorProjection.toMonoidHom x.1) ∧
      ∀ y, factorPair s (e.symm y).1.val = (y.1.val, op (y.1⁻¹).val)

/-- Naturality of the projection across morphisms respecting the chosen
embedding, including the test algebras of any field splitting the centre. -/
def SplitCentreNaturality : Prop :=
  ∀ {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    [Algebra E R] [Algebra E S] [IsScalarTower F E R] [IsScalarTower F E S]
    (f : R →ₐ[E] S) (x : R ⊗[F] A),
    factorProjection (map (f.restrictScalars F) (AlgHom.id F A) x) =
      map f (AlgHom.id E A) (factorProjection x)

/-- Restricting test algebras along an extension identifies the two stages of
scalar extension with the single extension from the centre. -/
def factorScalarExtension {L : Type u} [Field L] [Algebra E L]
    [Algebra L R] [IsScalarTower E L R] :
    (R ⊗[E] A) ≃ₐ[R] (R ⊗[L] (L ⊗[E] A)) :=
  (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L R R).symm
    (.refl : A ≃ₐ[E] A)).trans (Algebra.TensorProduct.assoc E L R R L A)

/-- The first coordinate is the norm of the actual factor over the splitting
field of the centre. This comparison does not require that factor to be a
split matrix algebra. -/
def FactorReducedNorm : Prop :=
  ∀ {E A L R : Type u} [Field E] [Field L] [Ring A] [Algebra E A]
    [Algebra E L] [CommRing R] [Algebra E R] [Algebra L R] [IsScalarTower E L R]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι] (b : Module.Basis ι E A),
    ∃ hL : isCentralSimple L (L ⊗[E] A),
      degree L (L ⊗[E] A) = degree E A ∧
      ∀ x : R ⊗[E] A, normAt hL (b.baseChange L) (factorScalarExtension x) =
        normAt hA b x

end SplitCentre

section MatrixComparison

variable {K : Type u} [Field K] [Algebra E K] [Algebra K R]

abbrev Mat (E A T : Type u) [Field E] [Ring A] [Algebra E A] :=
  Matrix (Fin (degree E A)) (Fin (degree E A)) T

/-- The matrix coordinate uses the projection for the specified embedding into
the splitting field and the extension of its given matrix splitting. -/
def matrixProjection [Algebra E R] [IsScalarTower F E R] [IsScalarTower E K R]
    (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K) :
    (R ⊗[F] A) →ₐ[F] Mat E A R :=
  let d : (R ⊗[E] A) →ₐ[E] Mat E A R :=
    (_root_.RM03.CSA.NormOneGroup.extendSplitting (R := R) e).toAlgHom.restrictScalars E
  (d.restrictScalars F).comp factorProjection

/-- Extend a coefficient-semilinear additive operator on the split matrix
algebra using its values on the matrix units. -/
def extendMatrixOperator {S : Type u} [CommRing S] [Algebra K S]
    (β : Mat E A K →+ Mat E A K) (f : R →+* S) (x : Mat E A R) : Mat E A S :=
  ∑ i, ∑ j, f (x i j) • (β (Matrix.single i j 1)).map (algebraMap K S)

/-- The given matrix comparison bijectively identifies the equations with
special linear matrices on each test algebra over the splitting field. -/
def MatrixComparison : Prop :=
  ∀ {F E A K : Type u} [Field F] [Field E] [Field K] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A] [Algebra E K]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι E A) (s : SecondKind F E A)
    (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K)
    {R : Type u} [CommRing R] [Algebra F R] [Algebra E R] [Algebra K R]
    [IsScalarTower F E R] [IsScalarTower E K R],
    ∃ c : {x : (R ⊗[F] A)ˣ // IsSpecialUnitary hA b s x} ≃
      Matrix.SpecialLinearGroup (Fin (degree E A)) R,
      ∀ x, (c x).val = matrixProjection e x.val.val

/-- An even operator fixes the embedded algebra and an odd operator restricts
to the adjoint. Under any coefficient map above the specified field
automorphism the projected matrix transforms by that operator on the
matrix of the point or on its inverse according to parity. -/
def MatrixSemilinearTransport : Prop :=
  ∀ {F E A K : Type u} [Field F] [Field E] [Field K] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι E A) (s : SecondKind F E A)
    (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K)
    (σ : K ≃ₐ[F] K) (odd : Bool) (β : Mat E A K →ₛₗ[σ.toRingHom] Mat E A K),
    (∀ c : E, σ (algebraMap E K c) =
      algebraMap E K (if odd then s.conjugation c else c)) →
    (∀ a : A, β (e (1 ⊗ₜ[E] a)) =
      e (1 ⊗ₜ[E] (if odd then unop (s.adjoint a) else a))) →
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      [Algebra E R] [Algebra E S] [Algebra K R] [Algebra K S]
      [IsScalarTower F E R] [IsScalarTower F E S] [IsScalarTower E K R] [IsScalarTower E K S]
      (f : R →ₐ[F] S), (∀ k : K, f (algebraMap K R k) = algebraMap K S (σ k)) →
      ∀ (x : (R ⊗[F] A)ˣ), IsSpecialUnitary hA b s x →
        matrixProjection e (map f (AlgHom.id F A) x.val) =
          extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom
            (matrixProjection e (if odd then (x⁻¹).val else x.val))

/-- Ordinary changes of coefficients intertwine the same matrix projection. -/
def MatrixNaturality : Prop :=
  ∀ {F E A K : Type u} [Field F] [Field E] [Field K] [Algebra F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A] [Algebra E K]
    (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    [Algebra E R] [Algebra E S] [Algebra K R] [Algebra K S]
    [IsScalarTower F E R] [IsScalarTower F E S] [IsScalarTower E K R] [IsScalarTower E K S]
    [Algebra F K] [IsScalarTower F K R] [IsScalarTower F K S]
    (f : R →ₐ[K] S) (x : R ⊗[F] A),
    matrixProjection e (map (f.restrictScalars F) (AlgHom.id F A) x) =
      (matrixProjection e x).map f

end MatrixComparison

end

end LinearAlgebraicGroups.UnitaryNormEquations
