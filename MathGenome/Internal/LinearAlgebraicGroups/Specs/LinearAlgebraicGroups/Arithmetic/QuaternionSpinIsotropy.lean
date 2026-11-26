import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration

open CategoryTheory
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinIsotropy

open NontrialitarianSpinModels (SkewHermitianPairing)
open SymplecticDivisionForms (Involution antiValue)
open SymplecticInvolutionModels (quaternionConjugate)
open _root_.Specs.RM03.CSA (isCentralSimple degree)

/-- The involution is the canonical quaternion conjugation. -/
def IsCanonical {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (hB : isCentralSimple F B) (s : Involution F B) : Prop :=
  ∀ z, antiValue s.anti z = quaternionConjugate hB z

/-- The congruence orbit of a nonzero pure quaternion contains all its
nonzero scalar multiples. -/
def PureLine {F : Type u} {B : Type v} [Field F] [DivisionRing B] [Algebra F B]
    (s : Involution F B) : Prop :=
  ∀ (q : B), q ≠ 0 → antiValue s.anti q = -q →
    ∀ t : F, t ≠ 0 → ∃ a : Bˣ, antiValue s.anti (a : B) * q * (a : B) = t • q

/-- The pure-line assertion over nonarchimedean local fields of
characteristic different from two and over the reals. -/
def LocalPureLines : Prop :=
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ (B : Type v) [DivisionRing B] [Algebra F B]
      (hB : isCentralSimple F B), degree F B = 2 →
    ∀ s : Involution F B, IsCanonical hB s → PureLine s) ∧
  (∀ (B : Type v) [DivisionRing B] [Algebra ℝ B]
      (hB : isCentralSimple ℝ B), degree ℝ B = 2 →
    ∀ s : Involution ℝ B, IsCanonical hB s → PureLine s)

/-- A nonzero isotropic vector with a hyperbolic partner in a regular
skew-Hermitian space. -/
def HasHyperbolicPair {F : Type u} {B V : Type v} [Field F] [DivisionRing B]
    [Algebra F B] [AddCommGroup V] [Module Bᵐᵒᵖ V] {s : Involution F B}
    (h : SkewHermitianPairing (V := V) s) : Prop :=
  ∃ x y : V, x ≠ 0 ∧ h.value x x = 0 ∧ h.value x y = 1 ∧
    h.value y x = -1 ∧ h.value y y = 0

/-- The dimension-four isotropy bound for regular skew-Hermitian spaces
over the local quaternion division algebra. -/
def LocalSkewIsotropy : Prop :=
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ (B : Type v) [DivisionRing B] [Algebra F B]
      (hB : isCentralSimple F B), degree F B = 2 →
    ∀ (s : Involution F B), IsCanonical hB s →
    ∀ (V : Type v) [AddCommGroup V] [Module Bᵐᵒᵖ V],
      4 ≤ Module.finrank Bᵐᵒᵖ V →
    ∀ h : SkewHermitianPairing (V := V) s, HasHyperbolicPair h) ∧
  (∀ (B : Type v) [DivisionRing B] [Algebra ℝ B]
      (hB : isCentralSimple ℝ B), degree ℝ B = 2 →
    ∀ (s : Involution ℝ B), IsCanonical hB s →
    ∀ (V : Type v) [AddCommGroup V] [Module Bᵐᵒᵖ V],
      4 ≤ Module.finrank Bᵐᵒᵖ V →
    ∀ h : SkewHermitianPairing (V := V) s, HasHyperbolicPair h)


open NontrialitarianSpinModels (IsOrthogonal gramAdjoint)
open SymplecticDivisionForms (dagger hermitianValue)
open IsotropicSpinGeneration (IsIsotropic)

/-- An orthogonal involution of degree at least eight over a nonarchimedean local
field of characteristic different from two has either an isotropic regular
scalar quadratic model or a quaternionic skew-Hermitian model with a hyperbolic pair. -/
def FiniteModelIsotropy : Prop :=
  ∀ {F A : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Ring A] [Algebra F A],
    (2 : F) ≠ 0 → ∀ (_hA : isCentralSimple F A) (n : ℕ),
    4 ≤ n → degree F A = 2 * n →
    ∀ s : Involution F A, IsOrthogonal s →
    (∃ (r : ℕ) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F)
        (H : (Matrix (Fin r) (Fin r) F)ˣ) (q : QuadraticForm F (Fin r → F)),
      r = 2 * n ∧ H.val.transpose = H.val ∧
      q.polarBilin = Matrix.toLinearMap₂' F H.val ∧ q.polarBilin.Nondegenerate ∧
      (∀ z, e (antiValue s.anti z) = gramAdjoint H (e z)) ∧ IsIsotropic q) ∨
    (∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B)
        (hB : isCentralSimple F B) (r : ℕ) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B)
        (b : Involution F B) (H : (Matrix (Fin r) (Fin r) B)ˣ)
        (h : SkewHermitianPairing (V := Fin r → B) b),
      degree F B = 2 ∧ r = n ∧ IsCanonical hB b ∧ dagger b.anti H.val = -H.val ∧
      (∀ z, e (antiValue s.anti z) = H.inv * dagger b.anti (e z) * H.val) ∧
      h.value = hermitianValue b.anti H.val ∧ HasHyperbolicPair h)

open CharacterDescent (Cocharacter)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)

/-- Positive split rank of the actual spin group at any nonarchimedean
completion in characteristic different from two. The chosen vector model
is the descended orthogonal involution. -/
def FiniteSpinIsotropy : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (G : AffineAlgebraicGroup k) (D : DescendedQuadraticPair ρ), SpinModel G D →
    4 ≤ Fintype.card I →
    IsOrthogonal (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution D.involution) →
    ∀ (F : Type u) [Field F] [Algebra k F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
      ∃ c : Cocharacter ((groupBaseChange k F).obj G.val), c ≠ 0

/-- A compact real spin factor in this type-D range has a split algebra
with involution adjoint to a definite regular scalar quadratic form.
The real completion is identified with ℝ by the specified isomorphism. -/
def CompactRealModel : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
    (G : AffineAlgebraicGroup k) (D : DescendedQuadraticPair ρ), SpinModel G D →
    4 ≤ Fintype.card I →
    IsOrthogonal (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution D.involution) →
    ∀ (F : Type u) [Field F] [Algebra k F] (R : F ≃+* ℝ)
      (i : IntegralModels.MatrixRealization G),
      letI : TopologicalSpace F := TopologicalSpace.induced R inferInstance
      IsCompact (Set.univ : Set (_root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups.PointsIn i F)) →
      ∃ (r : ℕ) (e : (F ⊗[k] ρ.fixedSubalgebra) ≃ₐ[F] Matrix (Fin r) (Fin r) F)
        (H : (Matrix (Fin r) (Fin r) F)ˣ) (q : QuadraticForm F (Fin r → F)),
        r = 2 * Fintype.card I ∧ H.val.transpose = H.val ∧
        q.polarBilin = Matrix.toLinearMap₂' F H.val ∧ q.polarBilin.Nondegenerate ∧
        (∀ z, e ((D.involution.baseChange F).toLinearMap z) = gramAdjoint H (e z)) ∧
        ((∀ x, x ≠ 0 → 0 < R (q x)) ∨ (∀ x, x ≠ 0 → R (q x) < 0))

end LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinIsotropy
