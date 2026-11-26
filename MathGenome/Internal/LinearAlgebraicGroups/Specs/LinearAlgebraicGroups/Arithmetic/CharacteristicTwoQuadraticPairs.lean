import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import Mathlib.LinearAlgebra.Quotient.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.AbsoluteIsomorphism

open scoped RatFunc TensorProduct Matrix MatrixGroups
open CategoryTheory
open MulOpposite ValuativeRel
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels
  (AntiAutomorphism HermitianPairing quaternionConjugate)
open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)

universe u v w

namespace LinearAlgebraicGroups.Specs.Arithmetic.CharacteristicTwoQuadraticPairs

/-- The subfield of squares, with its inclusion into the original field. -/
abbrev SquareField (F : Type u) [Field F] [CharP F 2] : Subfield F :=
  (frobenius F 2).fieldRange

def GlobalSquareDegree : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {k : Type v} [Field k] [Finite k]
    [Algebra k⟮X⟯ F] [FiniteDimensional k⟮X⟯ F], Module.finrank (SquareField F) F = 2

def LocalSquareDegree : Prop :=
  ∀ (F : Type u) [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], Module.finrank (SquareField F) F = 2

/-- Squaring on the field of all square roots identifies it with the original field. -/
def IsSquareRootField (F : Type u) (E : Type v) [Field F] [Field E]
    [Algebra F E] (sq : E ≃+* F) : Prop :=
  ∀ x, algebraMap F E (sq x) = x ^ 2


section Brauer

open _root_.RM03.Brauer.ContinuousCohomology
open _root_.RM03.Brauer.ScalarObstruction
open _root_.Specs.RM03.Brauer.ContinuousCohomology (H2ContinuousValue)
open _root_.Specs.RM03.Brauer.ScalarObstruction (Presents RecordsDefect)
open _root_.Specs.RM03.Brauer (GroupLaws IsScalarExtension classOf)

/-- The comparison uses the prescribed scalar-defect normalization of the
continuous Brauer equivalence at every finite Galois stage. -/
def HasBrauerNormalization (F S : Type u) [Field F] [Field S] [Algebra F S]
    [AddCommGroup (BrauerGroup.{u,u} F)]
    (e : BrauerGroup.{u,u} F ≃+ Additive (H2ContinuousValue F S)) : Prop :=
  ∀ (J : Stage F S) (A : _root_.CSA.{u,u} F) {n : ℕ}, 0 < n →
    ∀ (p : (J ⊗[F] A) ≃ₐ[J] Matrix (Fin n) (Fin n) J) (g : Gal(J/F) → GL (Fin n) J),
      Presents p g → ∀ c : ScalarCocycle F J, RecordsDefect g c →
        e (classOf A) = Additive.ofMul (toContinuous J (cocycleClass F J c))

/-- Restriction and scalar extension of continuous Brauer cohomology for the
extension adjoining all square roots. Squaring identifies the new coefficients
with the original coefficients and sends the extended cocycle to the square
of the original cocycle. -/
def FrobeniusBrauerComparison : Prop :=
  ∀ (F E S T : Type u) [Field F] [CharP F 2] [Field E] [Algebra F E]
    [Field S] [Algebra F S] [IsSepClosure F S] [Field T] [Algebra E T] [IsSepClosure E T]
    (sq : E ≃+* F), IsSquareRootField F E sq →
    ∃ (sqSep : T ≃+* S) (i : S →+* T) (r : Gal(T/E) ≃* Gal(S/F)),
      (∀ x : E, sqSep (algebraMap E T x) = algebraMap F S (sq x)) ∧
      (∀ x : S, sqSep (i x) = x ^ 2) ∧
      (∀ a : F, i (algebraMap F S a) = algebraMap E T (algebraMap F E a)) ∧
      (∀ (σ : Gal(T/E)) (x : S), i (r σ x) = σ (i x)) ∧
      (∀ (σ : Gal(T/E)) (x : T), r σ (sqSep x) = sqSep (σ x)) ∧
      Continuous r ∧ Continuous r.symm ∧
      ∃ (C : continuousCocycles F S →* continuousCocycles E T)
        (H : H2ContinuousValue F S →* H2ContinuousValue E T),
        (∀ c σ τ, (C c).val.val (σ, τ) = Units.map i (c.val.val (r σ, r τ))) ∧
        (∀ c, H (continuousClass c) = continuousClass (C c)) ∧
      ∃ (gF : AddCommGroup (BrauerGroup.{u,u} F)) (gE : AddCommGroup (BrauerGroup.{u,u} E)),
        GroupLaws F gF ∧ GroupLaws E gE ∧
        letI := gF
        letI := gE
        ∃ (eF : BrauerGroup.{u,u} F ≃+ Additive (H2ContinuousValue F S))
          (eE : BrauerGroup.{u,u} E ≃+ Additive (H2ContinuousValue E T))
          (b : BrauerGroup.{u,u} F →+ BrauerGroup.{u,u} E),
          HasBrauerNormalization F S eF ∧ HasBrauerNormalization E T eE ∧
          IsScalarExtension F E b ∧
          ∀ x, eE (b x) = Additive.ofMul (H (eF x).toMul)

end Brauer


/-- A division factor splits over the field of all square roots and has degree
dividing two when the square field has index two. -/
def DivisionDegreeOverSquares : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2], Module.finrank (SquareField F) F = 2 →
    ∀ {A B : Type u} [Ring A] [Algebra F A] [DivisionRing B] [Algebra F B]
      (_hA : _root_.Specs.RM03.CSA.isCentralSimple F A)
      (_hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
      (m : ℕ), 0 < m → (A ≃ₐ[F] Matrix (Fin m) (Fin m) B) →
    ∀ (_σ : AntiAutomorphism F A),
      (∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (sq : E ≃+* F),
        IsSquareRootField F E sq ∧ Module.finrank F E = 2 ∧
        Nonempty ((E ⊗[F] A) ≃ₐ[E]
          Matrix (Fin (_root_.Specs.RM03.CSA.degree F A))
            (Fin (_root_.Specs.RM03.CSA.degree F A)) E) ∧
        Nonempty ((E ⊗[F] B) ≃ₐ[E]
          Matrix (Fin (_root_.Specs.RM03.CSA.degree F B))
            (Fin (_root_.Specs.RM03.CSA.degree F B)) E)) ∧
      _root_.Specs.RM03.CSA.degree F B ∣ 2


/-- The degree of a division algebra divides the degree of a finite splitting field. -/
def SplitDivisionDegree : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    (_hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    {E : Type w} [Field E] [Algebra F E] [FiniteDimensional F E]
    (_e : (E ⊗[F] B) ≃ₐ[E] Matrix (Fin (_root_.Specs.RM03.CSA.degree F B))
      (Fin (_root_.Specs.RM03.CSA.degree F B)) E),
    _root_.Specs.RM03.CSA.degree F B ∣ Module.finrank F E


section Semitrace

open NontrialitarianSpinModels (DescendedQuadraticPair symmetricPart)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

/-- Reduced trace on any central simple algebra, including the matrix algebra over
the quaternion division factor. -/
noncomputable def algebraReducedTrace {F : Type u} [Field F] {A : Type v}
    [Ring A] [Algebra F A] (hA : _root_.Specs.RM03.CSA.isCentralSimple F A) (x : A) : F :=
  -(_root_.Specs.RM03.CSA.reducedCharpoly hA x).coeff (_root_.Specs.RM03.CSA.degree F A - 1)

/-- The descended semitrace is represented by reduced trace against an element
whose sum with its adjoint is one. -/
def SemitraceRepresentative : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ),
    ∃ ell : ρ.fixedSubalgebra,
      ell + D.involution.toLinearMap ell = 1 ∧
      ∀ x : symmetricPart D.involution, D.semitrace x = algebraReducedTrace D.centralSimple (ell * x.val)

end Semitrace

section Refinement

variable {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
  {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V]

/-- The central scalar line in the quaternion algebra. -/
abbrev scalarLine (F : Type u) (B : Type v) [Field F] [Ring B] [Algebra F B] :
    Submodule F B :=
  LinearMap.range (Algebra.linearMap F B)

/-- The value space of the quaternionic generalized quadratic form. -/
abbrev ScalarClasses (F : Type u) (B : Type v) [Field F] [Ring B] [Algebra F B] :=
  B ⧸ scalarLine F B

abbrev scalarClass (F : Type u) {B : Type v} [Field F] [Ring B] [Algebra F B] :
    B →ₗ[F] ScalarClasses F B := (scalarLine F B).mkQ

/-- The quadratic form defined by an endomorphism representing the semitrace. -/
def refinement {s : AntiAutomorphism F B} (h : HermitianPairing s V)
    (ell : V →ₗ[Bᵐᵒᵖ] V) (x : V) : ScalarClasses F B :=
  scalarClass F (h.value x (ell x))

/-- The adjoint equation for an endomorphism with adjoint one minus ell. -/
def IsTraceOne {s : AntiAutomorphism F B} (h : HermitianPairing s V)
    (ell : V →ₗ[Bᵐᵒᵖ] V) : Prop :=
  ∀ x y, h.value (ell x) y + h.value x (ell y) = h.value x y

/-- Scaling, polarization, and the trace identity for the actual refinement. The
trace identity also asserts the existence of the reduced trace on the quotient. -/
def RefinementIdentities : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
    (∀ a, antiValue s a = quaternionConjugate hB a) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)
      (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell →
      (∀ x a, refinement h ell (op a • x) =
        scalarClass F (antiValue s a * h.value x (ell x) * a)) ∧
      (∀ a q q', scalarClass F q = scalarClass F q' →
        scalarClass F (antiValue s a * q * a) = scalarClass F (antiValue s a * q' * a)) ∧
      (∀ x y, refinement h ell (x + y) =
        refinement h ell x + refinement h ell y + scalarClass F (h.value x y)) ∧
      ∃ t : ScalarClasses F B →ₗ[F] F,
        (∀ a, t (scalarClass F a) = reducedTrace hB a) ∧
        ∀ x, algebraMap F B (t (refinement h ell x)) = h.value x x

/-- The specific orthogonal complement of the quaternionic hyperbolic plane. -/
def IsHyperbolicComplement {s : AntiAutomorphism F B} (h : HermitianPairing s V)
    (e f x : V) : Prop :=
  h.value e x = 0 ∧ h.value f x = 0

/-- An isotropic vector extends to a hyperbolic pair for the refinement. The
formula is in the coordinates of the orthogonal splitting off of that pair. -/
def RefinementHyperbolicPair : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (s : AntiAutomorphism F B),
    (∀ a, antiValue s a = quaternionConjugate hB a) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)
      (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell →
    ∀ e : V, e ≠ 0 → refinement h ell e = 0 →
      ∃ f : V, refinement h ell f = 0 ∧ h.value e e = 0 ∧ h.value f f = 0 ∧
        h.value e f = 1 ∧ h.value f e = 1 ∧
        (∀ x, ∃! t : B × V × B, IsHyperbolicComplement h e f t.2.1 ∧
          x = op t.1 • e + t.2.1 + op t.2.2 • f) ∧
        ∀ a b y, IsHyperbolicComplement h e f y →
          refinement h ell (op a • e + y + op b • f) =
            scalarClass F (antiValue s a * b) + refinement h ell y


/-- A quaternionic refinement in division dimension at least four is isotropic
when the center has square index two and the reduced norm is surjective. -/
def QuaternionRefinementIsotropy : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    Module.finrank (SquareField F) F = 2 →
    (∀ a : F, a ≠ 0 → ∃ b : Bˣ, _root_.Specs.RM03.CSA.reducedNorm hB (b : B) = a) →
    ∀ (s : AntiAutomorphism F B),
    (∀ a, antiValue s a = quaternionConjugate hB a) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)
      (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell → 4 ≤ Module.finrank Bᵐᵒᵖ V →
      ∃ x : V, x ≠ 0 ∧ refinement h ell x = 0

end Refinement

/-- A homogeneous scalar quadratic form in the split division-factor model
has a nonzero zero in its actual dimension in type D. -/
def SplitQuadraticIsotropy : Prop :=
  (∀ {F : Type u} [Field F] [CharP F 2] {k : Type v} [Field k] [Finite k]
    [Algebra k⟮X⟯ F] [FiniteDimensional k⟮X⟯ F] (n : ℕ), 4 ≤ n →
    ∀ q : MvPolynomial (Fin (2 * n)) F, q.IsHomogeneous 2 →
      ∃ x : Fin (2 * n) → F, x ≠ 0 ∧ MvPolynomial.eval x q = 0) ∧
  (∀ (F : Type u) [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 4 ≤ n →
    ∀ q : MvPolynomial (Fin (2 * n)) F, q.IsHomogeneous 2 →
      ∃ x : Fin (2 * n) → F, x ≠ 0 ∧ MvPolynomial.eval x q = 0)


section Models

open NontrialitarianSpinModels (DescendedQuadraticPair symmetricPart SpinModel)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticDivisionForms (dagger hermitianValue extendAnti intoTensor tensorMap)
open CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open AdjointCocharacters (powerOnGm)
open Matrix

variable {F K I : Type u} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}

/-- Preservation of the actual descended semitrace by conjugation. -/
def PreservesSemitrace (D : DescendedQuadraticPair ρ) (g : ρ.fixedSubalgebraˣ) : Prop :=
  ∀ s : symmetricPart D.involution, ∃ t : symmetricPart D.involution,
    t.val = g.val * s.val * g.inv ∧ D.semitrace t = D.semitrace s

/-- The quaternion-matrix model of the same descended pair. Its generalized
quadratic form is recovered from the semitrace representative, and the two
matrix realizations agree under scalar extension. -/
structure QuaternionPair (D : DescendedQuadraticPair ρ)
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (n : ℕ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B) where
  rank : n = Fintype.card I
  bar : SymplecticDivisionForms.Involution F B
  canonical : ∀ a, antiValue bar.anti a = quaternionConjugate hB a
  gram : (Matrix (Fin n) (Fin n) B)ˣ
  gramHermitian : dagger bar.anti gram.val = gram.val
  pairing : HermitianPairing bar.anti (Fin n → B)
  pairingFormula : pairing.value = hermitianValue bar.anti gram.val
  adjointFormula : ∀ a, e (D.involution.toLinearMap a) = gram.inv * dagger bar.anti (e a) * gram.val
  ell : ρ.fixedSubalgebra
  ellTraceOne : ell + D.involution.toLinearMap ell = 1
  semitraceFormula : ∀ a : symmetricPart D.involution,
    D.semitrace a = algebraReducedTrace D.centralSimple (ell * a.val)
  ellAction : (Fin n → B) →ₗ[Bᵐᵒᵖ] (Fin n → B)
  ellActionFormula : ∀ x, ellAction x = e ell *ᵥ x
  pairingTraceOne : IsTraceOne pairing ellAction
  refinementIndependent : ∀ (ell' : ρ.fixedSubalgebra),
    (∀ s : symmetricPart D.involution, D.semitrace s = algebraReducedTrace D.centralSimple (ell' * s.val)) →
    ∀ x, refinement pairing ellAction x = scalarClass F (pairing.value x (e ell' *ᵥ x))
  preserves : ∀ g : ρ.fixedSubalgebraˣ,
    (∀ x y, pairing.value (e g.val *ᵥ x) (e g.val *ᵥ y) = pairing.value x y) →
    ((∀ x, refinement pairing ellAction (e g.val *ᵥ x) = refinement pairing ellAction x) ↔
      PreservesSemitrace D g)
  scalarExtension : ∀ R : TestAlgebra F,
    (R ⊗[F] ρ.fixedSubalgebra) ≃ₐ[R] Matrix (Fin n) (Fin n) (R ⊗[F] B)
  scalarExtensionFormula : ∀ (R : TestAlgebra F) (r : R) (a : ρ.fixedSubalgebra),
    scalarExtension R (r ⊗ₜ[F] a) = r • (e a).map (intoTensor R B)
  scalarExtensionNatural : ∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : R ⊗[F] ρ.fixedSubalgebra),
    scalarExtension S (tensorMap ρ.fixedSubalgebra f.hom x) =
      (scalarExtension R x).map (tensorMap B f.hom)

def QuaternionPairRecovery : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ)
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (n : ℕ) (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B),
      Nonempty (QuaternionPair D hB n e)

/-- Recovery of the scalar quadratic form from the same semitrace in the
field division-factor case. -/
def SplitPairRecovery : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ)
    (n : ℕ) (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F),
    n = 2 * Fintype.card I ∧
    ∃ (H : (Matrix (Fin n) (Fin n) F)ˣ) (ell : ρ.fixedSubalgebra)
      (q : QuadraticForm F (Fin n → F)),
      (∀ x, e (D.involution.toLinearMap x) = H.inv * (e x).transpose * H.val) ∧
      ell + D.involution.toLinearMap ell = 1 ∧
      (∀ x : symmetricPart D.involution, D.semitrace x = algebraReducedTrace D.centralSimple (ell * x.val)) ∧
      (∀ x, q x = x ⬝ᵥ (H.val *ᵥ (e ell *ᵥ x))) ∧
      q.polarBilin = Matrix.toLinearMap₂' F H.val ∧ q.polarBilin.Nondegenerate ∧
      ∀ g : ρ.fixedSubalgebraˣ,
        (∀ x, q (e g.val *ᵥ x) = q x) ↔
          D.involution.toLinearMap g.val * g.val = 1 ∧ PreservesSemitrace D g

/-- The hyperbolic vectors and complement acted on by the scalar cocharacter,
with an actual lift through the spin cover after a positive multiple. -/
def HasQuaternionHyperbolicLift
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} (M : SpinModel G D)
    {B : Type u} [DivisionRing B] [Algebra F B] {hB : _root_.Specs.RM03.CSA.isCentralSimple F B}
    {n : ℕ} {e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B}
    (P : QuaternionPair D hB n e) : Prop :=
  ∃ x y : Fin n → B,
    x ≠ 0 ∧ refinement P.pairing P.ellAction x = 0 ∧ refinement P.pairing P.ellAction y = 0 ∧
    P.pairing.value x x = 0 ∧ P.pairing.value y y = 0 ∧
    P.pairing.value x y = 1 ∧ P.pairing.value y x = 1 ∧
    (∀ v, ∃! a : B × (Fin n → B) × B,
      IsHyperbolicComplement P.pairing x y a.2.1 ∧
      v = op a.1 • x + a.2.1 + op a.2.2 • y) ∧
    (∀ a b w, IsHyperbolicComplement P.pairing x y w →
      refinement P.pairing P.ellAction (op a • x + w + op b • y) =
        scalarClass F (antiValue P.bar.anti a * b) + refinement P.pairing P.ellAction w) ∧
    ∃ (c : Cocharacter M.neutral.val) (j : ℕ) (lift : Cocharacter G.val),
      c ≠ 0 ∧ 0 < j ∧ lift ≠ 0 ∧ lift ≫ M.projection = powerOnGm F j ≫ c ∧
      ∀ (R : TestAlgebra F) (t : Rˣ),
        let T := P.scalarExtension R
          (M.fullPoints R ((cocharacterPoint c R t) ≫ M.inclusion.hom.hom)).val
        let E := fun v : Fin n → B => fun i => (1 : R) ⊗ₜ[F] v i
        T *ᵥ E x = (t : R) • E x ∧
        T *ᵥ E y = (↑t⁻¹ : R) • E y ∧
        ∀ w, IsHyperbolicComplement P.pairing x y w → T *ᵥ E w = E w

/-- The two field hypotheses occurring in the characteristic-two case. -/
def IsCharacteristicTwoArithmeticField (F : Type u) [Field F] : Prop :=
  (∃ (k : Type v) (_ : Field k) (_ : Finite k) (_ : Algebra k⟮X⟯ F),
    FiniteDimensional k⟮X⟯ F) ∨
  (∃ (_ : ValuativeRel F) (_ : TopologicalSpace F), IsNonarchimedeanLocalField F)

/-- Quaternionic isotropy and its spin cocharacter over either of the
characteristic-two fields of the arithmetic proof. -/
def ArithmeticQuaternionIsotropy : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I], IsCharacteristicTwoArithmeticField.{u,v} F →
    ∀ {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
    {G : AffineAlgebraicGroup F} (M : SpinModel G D)
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ (n : ℕ), 4 ≤ n →
    ∀ (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B) (P : QuaternionPair D hB n e),
      HasQuaternionHyperbolicLift M P

/-- In the split division-factor case the actual recovered regular scalar
quadratic form is isotropic and gives a nonzero cocharacter of the spin group. -/
def ArithmeticSplitIsotropy : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I], IsCharacteristicTwoArithmeticField.{u,v} F →
    ∀ {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
    {G : AffineAlgebraicGroup F} (_M : SpinModel G D) (n : ℕ), n = 2 * Fintype.card I → 8 ≤ n →
    ∀ (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F)
      (H : (Matrix (Fin n) (Fin n) F)ˣ) (ell : ρ.fixedSubalgebra) (q : QuadraticForm F (Fin n → F)),
      (∀ x, e (D.involution.toLinearMap x) = H.inv * (e x).transpose * H.val) →
      ell + D.involution.toLinearMap ell = 1 →
      (∀ x : symmetricPart D.involution, D.semitrace x = algebraReducedTrace D.centralSimple (ell * x.val)) →
      (∀ x, q x = x ⬝ᵥ (H.val *ᵥ (e ell *ᵥ x))) →
      q.polarBilin = Matrix.toLinearMap₂' F H.val → q.polarBilin.Nondegenerate →
      (∃ x, x ≠ 0 ∧ q x = 0) ∧ ∃ c : Cocharacter G.val, c ≠ 0

/-- The assembled isotropy consequence for the original nontrialitarian group
of type D in characteristic two. -/
def NontrialitarianIsotropy : Prop :=
  ∀ (F : Type u) [Field F] [CharP F 2], IsCharacteristicTwoArithmeticField.{u,v} F →
    ∀ (G : AffineAlgebraicGroup F) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    SimplyConnectedLattice.GeometricallySimplyConnected G →
    NontrialitarianSpinModels.HasFixedVectorVertex G n →
    ∃ c : Cocharacter G.val, c ≠ 0

end Models

end LinearAlgebraicGroups.Specs.Arithmetic.CharacteristicTwoQuadraticPairs
