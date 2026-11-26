import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

/-! The Clifford calculations for a hyperbolic pair in F12. -/

namespace LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration

open CliffordAlgebra

universe u v

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- A hyperbolic pair for the full polar form (q(x+y)-q(x)-q(y)). -/
structure HyperbolicPair (q : QuadraticForm R V) where
  e : V
  f : V
  q_e : q e = 0
  q_f : q f = 0
  polar_ef : q.polarBilin e f = 1

/-- The simultaneous perpendicular of the two isotropic vectors. -/
def HyperbolicPair.perpendicular {q : QuadraticForm R V} (h : HyperbolicPair q) :
    Submodule R V :=
  LinearMap.ker (q.polarBilin h.e) ⊓ LinearMap.ker (q.polarBilin h.f)

/-- The effect of the elementary lift attached to the isotropic vector (e). -/
def shearAction (q : QuadraticForm R V) (e w x : V) : V :=
  x + q.polarBilin w x • e - q.polarBilin e x • w -
    (q.polarBilin e x * q w) • e

/-- The shear is a norm-one even normalizer, and its action is the indicated
elementary orthogonal transformation. Using either vector of the pair gives
the two families of shears. -/
def ShearCalculation : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) (e w : V), q e = 0 → q.polarBilin e w = 0 →
    ∃ a : (CliffordAlgebra q)ˣ,
      (a : CliffordAlgebra q) = 1 + ι q e * ι q w ∧
      (↑a⁻¹ : CliffordAlgebra q) = 1 - ι q e * ι q w ∧
      (a : CliffordAlgebra q) ∈ evenOdd q 0 ∧ reverse (a : CliffordAlgebra q) * a = 1 ∧
      ∀ x : V, (a : CliffordAlgebra q) * ι q x * ↑a⁻¹ = ι q (shearAction q e w x)

open _root_.LinearAlgebraicGroups.Albert
open scoped TensorProduct

universe z j

/-- The elementary lifts in the precise represented normalizer, including on
nonreduced test algebras. The vector (e) may be either member of the pair. -/
def ScalarShears : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type j} [LinearOrder I] (q : QuadraticForm R V) (b : Module.Basis I R V)
    (S : Type z) [CommRing S] [Algebra R S],
    let Q := CliffordSpecification.coefficientForm S q b
    ∀ e w : S ⊗[R] V, Q e = 0 → Q.polarBilin e w = 0 →
      ∃ a ∈ SpinSpecification.spinUnits q S,
        (a : SpinSpecification.ScalarClifford q S) =
          1 + SpinSpecification.vectors q S e * SpinSpecification.vectors q S w ∧
        (↑a⁻¹ : SpinSpecification.ScalarClifford q S) =
          1 - SpinSpecification.vectors q S e * SpinSpecification.vectors q S w ∧
        ∀ x : S ⊗[R] V,
          SpinSpecification.conjugate q S a (SpinSpecification.vectors q S x) =
            SpinSpecification.vectors q S (shearAction Q e w x)

/-- The product of three shears realizing the rank-one Weyl interchange. -/
def WeylWordCalculation : Prop :=
  ∀ {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
    (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular),
    q w.val ≠ 0 →
    let E := ι q h.e
    let L := ι q h.f
    let z := ι q w.val
    (1 + E * z) * (1 + L * ι q ((q w.val)⁻¹ • w.val)) * (1 + E * z) =
      (E + ι q ((q w.val)⁻¹ • h.f)) * z

/-- Diagonal Clifford operators on the hyperbolic plane. The spin cocharacter
uses the coefficients ((s,s^{-1})), and the unnormalized lift of an
orthogonal plane scale uses ((t,1)). -/
def planeDiagonal (q : QuadraticForm R V) (h : HyperbolicPair q) (a b : R) : CliffordAlgebra q :=
  a • (ι q h.e * ι q h.f) + b • (ι q h.f * ι q h.e)

/-- The two plane idempotents are orthogonal, are exchanged by reversion,
and give the scaling and commutation rules for the vector generators. -/
def PlaneDiagonalCalculation : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) (h : HyperbolicPair q),
    let D := planeDiagonal q h
    let E := ι q h.e
    let L := ι q h.f
    D 1 1 = 1 ∧
    (∀ a b c d, D a b * D c d = D (a * c) (b * d)) ∧
    (∀ a b, reverse (D a b) = D b a) ∧
    (∀ a b, D a b ∈ evenOdd q 0) ∧
    ∀ a b, D a b * E = a • E ∧ E * D a b = b • E ∧
      D a b * L = b • L ∧ L * D a b = a • L ∧
      ∀ w : h.perpendicular, Commute (D a b) (ι q w.val)

/-- The spin diagonals multiply the e-shear parameter by (s^2) and the
f-shear parameter by (s^{-2}), over any test ring. -/
def PlaneScalingCalculation : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (q : QuadraticForm R V) (h : HyperbolicPair q) (s : Rˣ) (w : h.perpendicular),
    let d := planeDiagonal q h (s : R) (↑s⁻¹ : R)
    let d' := planeDiagonal q h (↑s⁻¹ : R) (s : R)
    d * (1 + ι q h.e * ι q w.val) * d' =
      1 + ι q h.e * ι q ((s : R) ^ 2 • w.val) ∧
    d * (1 + ι q h.f * ι q w.val) * d' =
      1 + ι q h.f * ι q ((↑s⁻¹ : R) ^ 2 • w.val)

section Field

variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]

/-- Regularity over the field, allowing the anisotropic polar radical line
in characteristic two. -/
def IsRegular (q : QuadraticForm F M) : Prop :=
  LinearMap.ker q.polarBilin = ⊥ ∨
    ∃ r : M, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = F ∙ r

/-- An isotropic quadratic form has a nonzero isotropic vector. -/
def IsIsotropic (q : QuadraticForm F M) : Prop :=
  ∃ e : M, e ≠ 0 ∧ q e = 0

/-- Every nonzero isotropic vector of a regular quadratic space extends to
a hyperbolic pair, in either characteristic. -/
def HyperbolicPairExistence : Prop :=
  ∀ {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    (q : QuadraticForm F M), IsRegular q → ∀ e : M, e ≠ 0 → q e = 0 →
      ∃ h : HyperbolicPair q, h.e = e

/-- Removing the hyperbolic plane preserves regularity, including the
possibility of a one-dimensional anisotropic polar radical. -/
def PerpendicularRegularity : Prop :=
  ∀ {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    (q : QuadraticForm F M) (h : HyperbolicPair q), IsRegular q →
      IsRegular (q.comp h.perpendicular.subtype)

/-- Reflection in a vector of nonzero norm, also called a symmetry in characteristic two. -/
def reflection (q : QuadraticForm F M) (w x : M) : M :=
  x - (q.polarBilin w x / q w) • w

/-- The conjugation action of the Weyl word, in multiplication form. -/
def WeylActionCalculation : Prop :=
  ∀ {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
    (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular),
    q w.val ≠ 0 →
    let n := ι q (h.e + (q w.val)⁻¹ • h.f) * ι q w.val
    n * ι q h.e = ι q (-(q w.val)⁻¹ • h.f) * n ∧
    n * ι q h.f = ι q (-q w.val • h.e) * n ∧
    ∀ x : h.perpendicular, n * ι q x.val = ι q (reflection q w.val x.val) * n

/-- The rank-one Weyl element as a Clifford element, indexed by its anisotropic vector. -/
def weylElement (q : QuadraticForm F M) (h : HyperbolicPair q) (w : M) : CliffordAlgebra q :=
  ι q (h.e + (q w)⁻¹ • h.f) * ι q w

/-- Ratios of the Weyl words give the spin scales and the scalar (-1). -/
def WeylScaleCalculation : Prop :=
  ∀ {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
    (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular),
    q w.val ≠ 0 →
    (∀ s : F, s ≠ 0 →
      weylElement q h (s • w.val) = planeDiagonal q h s s⁻¹ * weylElement q h w.val) ∧
    weylElement q h (-w.val) = -weylElement q h w.val

/-- For nonsingular polar form the graded vector centralizer is scalar.
This detects the parity of a Clifford word implementing an orthogonal action. -/
def GradedCentralizerCalculation : Prop :=
  ∀ {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    {I : Type j} [LinearOrder I] [Fintype I] (q : QuadraticForm F M)
    (_b : Module.Basis I F M), LinearMap.ker q.polarBilin = ⊥ →
      ∀ a : CliffordAlgebra q, (∀ v, ι q v * a = involute a * ι q v) →
        ∃ r : F, a = algebraMap F _ r

/-- Once the action on the perpendicular space is removed, a norm-one even
lift of a plane scale has square scale and is the spin diagonal for a unit. -/
def ScaleLiftCalculation : Prop :=
  ∀ {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    {I : Type j} [LinearOrder I] [Fintype I] (q : QuadraticForm F M)
    (_b : Module.Basis I F M) (h : HyperbolicPair q), IsRegular q →
    ∀ (t : Fˣ) (g : CliffordAlgebra q),
      g ∈ evenOdd q 0 → reverse g * g = 1 →
      g * ι q h.e = (t : F) • (ι q h.e * g) →
      g * ι q h.f = (↑t⁻¹ : F) • (ι q h.f * g) →
      (∀ w : h.perpendicular, Commute g (ι q w.val)) →
      ∃ s : Fˣ, g = planeDiagonal q h (s : F) (↑s⁻¹ : F) ∧ (t : F) = (s : F) ^ 2

end Field

section Scheme

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.CocharacterDynamics
open CharacterDescent (Cocharacter)
open AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open LinearAlgebraicGroups.Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open IntegralModels (MatrixRealization)
open SpinSpecification (ScalarClifford vectors IsSpinPointRepresentation)
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
variable {q : QuadraticForm F V} {G : AffineAlgebraicGroup F}

/-- The values of the spin cocharacter in the original representing scheme. -/
def HasSpinCocharacterFormula (h : HyperbolicPair q)
    (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
    (c : Cocharacter G.val) : Prop :=
  ∀ (R : TestAlgebra F) (s : Rˣ),
    let E := vectors q R (1 ⊗ₜ[F] h.e)
    let L := vectors q R (1 ⊗ₜ[F] h.f)
    (ρ R (cocharacterPoint c R s)).val = (s : R) • (E * L) + (↑s⁻¹ : R) • (L * E)

/-- The specified family of lift points for either isotropic vector of the
hyperbolic plane. The two polar equations are imposed in the test algebra. -/
def ShearPoint {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
    (h : HyperbolicPair q)
    (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
    (e : V) (R : TestAlgebra F) (g : GroupPoints G.val R) : Prop :=
  let Q := CliffordSpecification.coefficientForm R q b
  ∃ w : R ⊗[F] V, Q.polarBilin (1 ⊗ₜ[F] h.e) w = 0 ∧
    Q.polarBilin (1 ⊗ₜ[F] h.f) w = 0 ∧
    (ρ R g).val = 1 + vectors q R (1 ⊗ₜ[F] e) * vectors q R w

/-- The Levi action on the perpendicular space admits an even reflection
word. The definition uses the original vector inclusion on the field points. -/
def HasEvenPerpendicularAction (h : HyperbolicPair q)
    (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
    (c : Cocharacter G.val) : Prop :=
  ∀ p : GroupPoints G.val (CommAlgCat.of F F), Centralizes c p →
    ∃ l : List h.perpendicular, l.length % 2 = 0 ∧
      (∀ w ∈ l, q w.val ≠ 0) ∧
      ∀ x : h.perpendicular,
        let A := (ρ (CommAlgCat.of F F) p).val
        A * vectors q F (1 ⊗ₜ[F] x.val) =
          vectors q F (1 ⊗ₜ[F] (l.foldr (fun w z => reflection q w.val z) x.val)) * A

/-- The spin group of a regular isotropic form is generated by the two
opposite contracting radicals, over an infinite field and in particular
over each completion. -/
def LocalSpinGeneration : Prop :=
  ∀ {F : Type u} [Field F] [Infinite F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] [Fintype I] (q : QuadraticForm F V) (b : Module.Basis I F V)
    (G : AffineAlgebraicGroup F)
    (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ),
    IsSpinPointRepresentation q G.val ρ → IsRegular q → IsAbsolutelyAlmostSimple G →
    ∀ h : HyperbolicPair q, ∃ c : Cocharacter G.val,
      HasSpinCocharacterFormula h ρ c ∧ IsNoncentral c ∧
      HasEvenPerpendicularAction h ρ c ∧
      ∀ (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)),
        (∀ (R : TestAlgebra F) (g : GroupPoints G.val R),
          (ShearPoint b h ρ h.e R g → HasLimit c g 1) ∧
          (ShearPoint b h ρ h.f R g → HasLimit (oppositeCocharacter c) g 1)) ∧
        (∀ (_ : CharZero F) (R : TestAlgebra F) (g : GroupPoints G.val R),
          (HasLimit c g 1 → ShearPoint b h ρ h.e R g) ∧
          (HasLimit (oppositeCocharacter c) g 1 → ShearPoint b h ρ h.f R g)) ∧
        SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
          SubgroupSections E.contracting (𝟙_ (SchemeOver F)) = ⊤

/-- Strong approximation for the same global spin group, with the finite
nonempty omitted set and the local topology of F12. -/
def GlobalSpinApproximation : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    {V : Type u} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (q : QuadraticForm K V) (G : AffineAlgebraicGroup K)
    (ρ : ∀ R : TestAlgebra K, GroupPoints G.val R →* (ScalarClifford q R)ˣ),
    IsSpinPointRepresentation q G.val ρ → IsRegular q → IsIsotropic q →
    IsAbsolutelyAlmostSimple G → ∀ (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → StrongApproximation D i S

end Scheme

end LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration
