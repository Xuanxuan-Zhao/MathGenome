import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Basic

/-! Interfaces for unital composition algebras and octonion algebras. -/

namespace LinearAlgebraicGroups.Composition.Specification

open scoped TensorProduct

set_option linter.checkUnivs false

universe u v w
variable {R : Type u} {A : Type v} {S : Type w}

/-- Extend a quadratic form on a projective module by extending a bilinear representative.
The representative is obtained by retracting a free module onto the projective module. -/
noncomputable def normBaseChange [CommRing R] [AddCommGroup A] [Module R A]
    [Module.Projective R A] (S : Type w) [CommRing S] [Algebra R S]
    (n : QuadraticForm R A) : QuadraticForm S (S ⊗[R] A) :=
  let retraction := Finsupp.linearCombination R (id : A → A)
  let sectionMap := (Module.projective_def (R := R) (P := A)).mp inferInstance |>.choose
  let basis := Module.Free.chooseBasis R (A →₀ R)
  letI : LinearOrder (Module.Free.ChooseBasisIndex R (A →₀ R)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let representative := (n.comp retraction).toBilin basis
  (LinearMap.BilinForm.baseChange S
    (representative.compl₁₂ sectionMap sectionMap)).toQuadraticMap

def normBaseChangeType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [AddCommGroup A] [Module R A]
    [Module.Projective R A] (S : Type w) [CommRing S] [Algebra R S],
    QuadraticForm R A → QuadraticForm S (S ⊗[R] A)

def normBaseChangeOnTensors :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [AddCommGroup A] [Module R A]
    [Module.Projective R A] (S : Type w) [CommRing S] [Algebra R S]
    (n : QuadraticForm R A) (s : S) (x : A),
    normBaseChange S n (s ⊗ₜ x) = s * s * algebraMap R S (n x)

def polarBaseChange :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [AddCommGroup A] [Module R A]
    [Module.Projective R A] (S : Type w) [CommRing S] [Algebra R S]
    (n : QuadraticForm R A),
    (normBaseChange S n).polarBilin = LinearMap.BilinForm.baseChange S n.polarBilin

/-- In every characteristic, regularity means nondegeneracy of the full polar form. -/
structure FieldNormConditions [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (n : QuadraticForm R A) : Prop where
  finite : Module.Finite R A
  nontrivial : Nontrivial A
  nondegenerate : n.polarBilin.Nondegenerate
  multiplicative : ∀ x y, n (x * y) = n x * n y

def fieldNormType :=
  ∀ {R : Type u} {A : Type v} [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A],
    QuadraticForm R A → Prop

def fieldNormValue [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    QuadraticForm R A → Prop := FieldNormConditions

/-- Finite projective modules of constant stalk rank eight are finite locally free
of rank eight. Norm multiplicativity is required on scalar extensions. -/
structure OctonionNormConditions [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (n : QuadraticForm R A) : Prop where
  finite : Module.Finite R A
  projective : Module.Projective R A
  rank_eight : ∀ p : PrimeSpectrum R, Module.rankAtStalk A p = 8
  perfect : n.polarBilin.IsPerfPair
  multiplicative_after_baseChange :
    letI := projective
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] A),
      normBaseChange S n (x * y) = normBaseChange S n x * normBaseChange S n y

def octonionNormType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A],
    QuadraticForm R A → Prop

def octonionNormValue [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    QuadraticForm R A → Prop := OctonionNormConditions

def normCompositionAfterBaseChange :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module.Projective R A] (n : QuadraticForm R A),
    (∀ x y, n (x * y) = n x * n y) →
    ∀ (S : Type w) [CommRing S] [Algebra R S] (x y : S ⊗[R] A),
      normBaseChange S n (x * y) = normBaseChange S n x * normBaseChange S n y

def normCompositionBeforeBaseChange :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module.Projective R A] (n : QuadraticForm R A),
    (∀ x y : R ⊗[R] A,
      normBaseChange R n (x * y) = normBaseChange R n x * normBaseChange R n y) →
    ∀ x y, n (x * y) = n x * n y

def octonionNormOverField :=
  ∀ {R : Type u} {A : Type v} [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (n : QuadraticForm R A),
    OctonionNormConditions n ↔ FieldNormConditions n ∧ Module.finrank R A = 8

def fieldNormOne :=
  ∀ {R : Type u} {A : Type v} [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, FieldNormConditions n → n 1 = 1

def octonionNormMultiplicative :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, OctonionNormConditions n → ∀ x y, n (x * y) = n x * n y

def octonionNormOne :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, OctonionNormConditions n → n 1 = 1

def leftSimilarity :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, (∀ x y, n (x * y) = n x * n y) →
    ∀ x y z, n.polarBilin (x * y) (x * z) = n x * n.polarBilin y z

def rightSimilarity :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, (∀ x y, n (x * y) = n x * n y) →
    ∀ x y z, n.polarBilin (y * x) (z * x) = n x * n.polarBilin y z

def fullPolarFormula :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [AddCommGroup A] [Module R A]
    (n : QuadraticForm R A) (x y : A), n.polarBilin x y = n (x + y) - n x - n y

def scalarNormType := ∀ (R : Type u) [CommRing R], QuadraticForm R R

def scalarNorm (R : Type u) [CommRing R] : QuadraticForm R R := QuadraticMap.sq

def scalarConjugateType := ∀ (R : Type u) [CommRing R], R ≃ₗ[R] R

def scalarConjugate (R : Type u) [CommRing R] : R ≃ₗ[R] R := LinearEquiv.refl R R

def scalarModelLaws :=
  ∀ (R : Type u) [CommRing R],
    scalarNorm R 1 = 1 ∧
    (∀ x y, scalarNorm R (x * y) = scalarNorm R x * scalarNorm R y) ∧
    (∀ x, scalarConjugate R (scalarConjugate R x) = x ∧
      scalarNorm R (scalarConjugate R x) = scalarNorm R x) ∧
    (∀ x y, scalarConjugate R (x * y) = scalarConjugate R y * scalarConjugate R x)

def scalarPolar :=
  ∀ (R : Type u) [CommRing R] (x y : R),
    (scalarNorm R).polarBilin x y = 2 * x * y

def scalarPerfectIff :=
  ∀ (R : Type u) [CommRing R], (scalarNorm R).polarBilin.IsPerfPair ↔ IsUnit (2 : R)

def rankOneRequiresTwoNeZero :=
  ∀ {R : Type u} {A : Type v} [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A}, FieldNormConditions n → Module.finrank R A = 1 → (2 : R) ≠ 0

def isotropicType :=
  ∀ {R : Type u} {A : Type v} [Field R] [AddCommGroup A] [Module R A],
    QuadraticForm R A → Prop

def isotropic [Field R] [AddCommGroup A] [Module R A] (n : QuadraticForm R A) : Prop :=
  ∃ x, x ≠ 0 ∧ n x = 0

/-- Norm-preserving identification with an explicitly specified unital algebra model. -/
def hasModel [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {M : Type w}
    [AddCommGroup M] [Module R M] (n : QuadraticForm R A)
    (unit : M) (product : M → M → M) (norm : M → R) : Prop :=
  ∃ f : A ≃ₗ[R] M, f 1 = unit ∧
    (∀ x y, f (x * y) = product (f x) (f y)) ∧ (∀ x, n x = norm (f x))

/-- Coordinates of a Zorn vector matrix, ordered as the two diagonal scalars
with the upper and lower vectors between them. -/
abbrev ZornCoordinates (R : Type u) := R × (Fin 3 → R) × (Fin 3 → R) × R

def zornProduct [CommRing R] (x y : ZornCoordinates R) : ZornCoordinates R :=
  let (a, u, v, b) := x
  let (a', u', v', b') := y
  (a * a' + dotProduct u v', a • u' + b' • u - crossProduct v v',
    a' • v + b • v' + crossProduct u u', b * b' + dotProduct v u')

def zornUnit [CommRing R] : ZornCoordinates R := (1, 0, 0, 1)

def zornNorm [CommRing R] (x : ZornCoordinates R) : R :=
  let (a, u, v, b) := x
  a * b - dotProduct u v

def splitOctonion [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (n : QuadraticForm R A) : Prop :=
  hasModel n zornUnit zornProduct zornNorm

/-- Split models of ranks one, two, four and eight. The rank-one case is
available over all base rings independently of regularity of the polar form. -/
def split [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (n : QuadraticForm R A) : Prop :=
  hasModel n (1 : R) (· * ·) (scalarNorm R) ∨
  hasModel n (1 : R × R) (· * ·) (fun x : R × R => x.1 * x.2) ∨
  hasModel n (1 : Matrix (Fin 2) (Fin 2) R) (· * ·) Matrix.det ∨
  splitOctonion n

def splitOctonionType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A], QuadraticForm R A → Prop

def splitType :=
  ∀ {R : Type u} {A : Type v} [Field R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A], QuadraticForm R A → Prop

def perfectPolarAfterBaseChange :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [AddCommGroup A] [Module R A]
    [Module.Finite R A] [Module.Projective R A] (S : Type w) [CommRing S] [Algebra R S]
    (n : QuadraticForm R A), n.polarBilin.IsPerfPair → (normBaseChange S n).polarBilin.IsPerfPair

def octonionNormAfterBaseChange :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (h : OctonionNormConditions n)
    (S : Type w) [CommRing S] [Algebra R S],
    letI := h.projective
    OctonionNormConditions (normBaseChange S n)

end LinearAlgebraicGroups.Composition.Specification
