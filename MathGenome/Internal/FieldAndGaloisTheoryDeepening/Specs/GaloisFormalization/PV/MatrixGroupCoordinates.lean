import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Coordinate conventions for Picard–Vessiot matrix groups

The last variable records the inverse determinant. The coordinate ring of a set of
points is the quotient by all polynomials vanishing on those points. In particular
it incorporates the inverse determinant relation.
-/

namespace GaloisFormalization.PV.MatrixGroupCoordinates.Specs

universe u v w z

noncomputable section

/-- Variables for the matrix entries and the inverse determinant. -/
abbrev CoordinateVariable (n : ℕ) := (Fin n × Fin n) ⊕ Unit

/-- Polynomials before imposing any relations. -/
abbrev CoordinatePolynomial (C : Type u) [CommSemiring C] (n : ℕ) :=
  MvPolynomial (CoordinateVariable n) C

section Algebra

variable {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A]
variable {n : ℕ}

/-- The polynomial expressing that the last variable inverts the determinant. -/
def determinantRelation (C : Type u) [CommRing C] (n : ℕ) : CoordinatePolynomial C n :=
  let X : Matrix (Fin n) (Fin n) (CoordinatePolynomial C n) :=
    Matrix.of fun i j => MvPolynomial.X (Sum.inl (i, j))
  MvPolynomial.X (Sum.inr ()) * X.det - 1

/-- The inverse determinant over a commutative ring, defined using the unit determinant. -/
def inverseDeterminant (g : GL (Fin n) A) : A :=
  ↑((Matrix.GeneralLinearGroup.det g)⁻¹)

/-- Evaluate a polynomial in the entries and inverse determinant of an algebra-valued point. -/
def evalAt (g : GL (Fin n) A) : CoordinatePolynomial C n →ₐ[C] A :=
  MvPolynomial.aeval (Sum.elim (fun ij : Fin n × Fin n => g ij.1 ij.2)
    (fun _ => inverseDeterminant g))

/-- The common zero locus of a family of polynomials at base-ring points. -/
def zeroLocus (s : Set (CoordinatePolynomial C n)) : Set (GL (Fin n) C) :=
  {g | ∀ p ∈ s, evalAt g p = 0}

/-- The ideal of all polynomials whose restrictions to the set vanish. -/
def vanishingIdeal (S : Set (GL (Fin n) C)) : Ideal (CoordinatePolynomial C n) :=
  ⨅ g : S, RingHom.ker (evalAt (C := C) g.1)

/-- The algebra of polynomial coordinate functions on a set of points. -/
abbrev CoordinateRing (S : Set (GL (Fin n) C)) : Type u :=
  CoordinatePolynomial C n ⧸ vanishingIdeal S

/-- The restriction of polynomials to the coordinate ring. -/
def coordinateMap (S : Set (GL (Fin n) C)) : CoordinatePolynomial C n →ₐ[C] CoordinateRing S :=
  Ideal.Quotient.mkₐ C (vanishingIdeal S)

/-- Algebra-valued points of the coordinate ring. -/
abbrev Points (S : Set (GL (Fin n) C)) (A : Type v) [CommRing A] [Algebra C A] :=
  CoordinateRing S →ₐ[C] A

/-- Invertible matrices satisfying an ideal of polynomial relations over a test algebra. -/
abbrev MatrixSolutions (I : Ideal (CoordinatePolynomial C n)) (A : Type v)
    [CommRing A] [Algebra C A] :=
  {g : GL (Fin n) A // ∀ p ∈ I, evalAt (C := C) g p = 0}

/-- Regular scalar functions are the restrictions of coordinate polynomials. -/
def IsRegular {S : Set (GL (Fin n) C)} (f : S → C) : Prop :=
  ∃ p : CoordinatePolynomial C n, ∀ x : S, evalAt (C := C) x.1 p = f x

/-- A matrix-valued function is regular if each entry is regular. -/
def IsRegularMatrix {S : Set (GL (Fin n) C)} {ι : Type w} {κ : Type z}
    (f : S → Matrix ι κ C) : Prop :=
  ∀ i j, IsRegular (fun x => f x i j)

/-- A morphism to a general linear group has regular entries and regular inverse determinant. -/
def IsRegularGL {S : Set (GL (Fin n) C)} {m : ℕ} (f : S → GL (Fin m) C) : Prop :=
  IsRegularMatrix (fun x => (f x).val) ∧ IsRegular (fun x => inverseDeterminant (f x))

/-- Regular representations in a chosen finite-dimensional matrix basis. -/
def IsRegularRepresentation {H : Subgroup (GL (Fin n) C)} {m : ℕ}
    (ρ : H →* GL (Fin m) C) : Prop :=
  IsRegularGL (S := (H : Set (GL (Fin n) C))) ρ

end Algebra

section PointLaws

variable {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A]
variable {n : ℕ}

/-- A polynomial belongs to the ideal precisely when its restriction vanishes. -/
def MemVanishingIdeal : Prop :=
  ∀ {C : Type u} [CommRing C] {n : ℕ},
    ∀ (S : Set (GL (Fin n) C)) (p : CoordinatePolynomial C n),
      p ∈ vanishingIdeal S ↔ ∀ g : S, evalAt (C := C) g.1 p = 0

/-- The defining equation for the extra coordinate holds at every invertible matrix. -/
def EvalDeterminantRelation : Prop :=
  ∀ {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A] {n : ℕ},
    ∀ g : GL (Fin n) A, evalAt (C := C) g (determinantRelation C n) = 0

/-- Evaluating at an algebra-valued matrix with the prescribed relations gives an
algebra homomorphism on the quotient. -/
def evalSolution (I : Ideal (CoordinatePolynomial C n)) (g : MatrixSolutions I A) :
    (CoordinatePolynomial C n ⧸ I) →ₐ[C] A :=
  Ideal.Quotient.liftₐ I (evalAt g.1) g.2

/-- The quotient represents exactly the solutions of the relations, once the inverse
determinant relation is imposed. -/
def EvalSolutionBijective : Prop :=
  ∀ {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A] {n : ℕ},
    ∀ I : Ideal (CoordinatePolynomial C n), determinantRelation C n ∈ I →
      Function.Bijective (evalSolution (A := A) I)

/-- Evaluation of a coordinate function at a point of its defining set. -/
def evalCoordinate {S : Set (GL (Fin n) C)} (x : S) : Points S C :=
  evalSolution (vanishingIdeal S) ⟨x.1, fun _ hp =>
    RingHom.mem_ker.mp ((iInf_le _ x : vanishingIdeal S ≤ RingHom.ker (evalAt (C := C) x.1)) hp)⟩

/-- Regular scalar functions are evaluations of elements of the coordinate ring. -/
def RegularIffCoordinate : Prop :=
  ∀ {C : Type u} [CommRing C] {n : ℕ},
    ∀ (S : Set (GL (Fin n) C)) (f : S → C),
      IsRegular f ↔ ∃ a : CoordinateRing S, ∀ x : S, evalCoordinate x a = f x

/-- A coordinate function is determined by its values on the defining set. -/
def CoordinateExt : Prop :=
  ∀ {C : Type u} [CommRing C] {n : ℕ},
    ∀ (S : Set (GL (Fin n) C)) (a b : CoordinateRing S),
      (∀ x : S, evalCoordinate x a = evalCoordinate x b) → a = b

end PointLaws

section Topology

variable {C : Type u} [Field C] {n : ℕ}

/-- The kernel of evaluation at a base-field point, regarded as a prime. -/
def evaluationPrime (g : GL (Fin n) C) : PrimeSpectrum (CoordinatePolynomial C n) :=
  ⟨RingHom.ker (evalAt (C := C) g), RingHom.ker_isPrime _⟩

/-- The algebraic Zariski topology. The usual subtype topology gives its restriction to
any set or subgroup of points. -/
scoped instance (priority := high) zariskiTopology : TopologicalSpace (GL (Fin n) C) :=
  TopologicalSpace.induced evaluationPrime inferInstance

/-- Algebraic subgroups are the Zariski closed subgroups of the matrix group. -/
def IsAlgebraicSubgroup (H : Subgroup (GL (Fin n) C)) : Prop :=
  IsClosed (H : Set (GL (Fin n) C))

/-- The topology has exactly the polynomial zero loci as its closed subsets. -/
def IsClosedIffZeroLocus : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ},
    ∀ S : Set (GL (Fin n) C),
      IsClosed S ↔ ∃ s : Set (CoordinatePolynomial C n), S = zeroLocus s

/-- This characterization also applies to the topology induced on any subset. -/
def IsClosedSubtypeIffZeroLocus : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ},
    ∀ (S : Set (GL (Fin n) C)) (T : Set S),
      IsClosed T ↔ ∃ s : Set (CoordinatePolynomial C n), T = Subtype.val ⁻¹' zeroLocus s

/-- A closed subset is recovered from its vanishing ideal. -/
def ZeroLocusVanishingIdeal : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ},
    ∀ S : Set (GL (Fin n) C), IsClosed S → zeroLocus (vanishingIdeal S : Set _) = S

/-- The Zariski topology on the matrix group is Noetherian. -/
def ZariskiNoetherian : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ},
    TopologicalSpace.NoetherianSpace (GL (Fin n) C)

/-- A closed set is exactly the base-field points of its coordinate ring. -/
def EvalCoordinateBijective : Prop :=
  ∀ {C : Type u} [Field C] {n : ℕ},
    ∀ S : Set (GL (Fin n) C), IsClosed S → Function.Bijective (evalCoordinate (S := S))

end Topology

/-! ## Types of the shared definitions -/

section BindingTypes

-- These closed types retain the independent universes of the base ring, test algebra
-- and matrix index types.
set_option linter.checkUnivs false

def CoordinateVariableType := ℕ → Type

def CoordinatePolynomialType :=
  ∀ (C : Type u) [CommSemiring C], ℕ → Type u

def DeterminantRelationType :=
  ∀ (C : Type u) [CommRing C] (n : ℕ), CoordinatePolynomial C n

def InverseDeterminantType :=
  ∀ {A : Type v} [CommRing A] {n : ℕ}, GL (Fin n) A → A

def EvalAtType :=
  ∀ {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A] {n : ℕ},
    GL (Fin n) A → (CoordinatePolynomial C n →ₐ[C] A)

def ZeroLocusType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ}, Set (CoordinatePolynomial C n) → Set (GL (Fin n) C)

def VanishingIdealType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ}, Set (GL (Fin n) C) → Ideal (CoordinatePolynomial C n)

def CoordinateRingType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ}, Set (GL (Fin n) C) → Type u

def CoordinateMapType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ} (S : Set (GL (Fin n) C)),
    CoordinatePolynomial C n →ₐ[C] CoordinateRing S

def PointsType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ}, Set (GL (Fin n) C) →
    ∀ (A : Type v) [CommRing A] [Algebra C A], Type (max u v)

def MatrixSolutionsType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ}, Ideal (CoordinatePolynomial C n) →
    ∀ (A : Type v) [CommRing A] [Algebra C A], Type v

def IsRegularType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ} {S : Set (GL (Fin n) C)}, (S → C) → Prop

def IsRegularMatrixType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ} {S : Set (GL (Fin n) C)} {ι : Type w} {κ : Type z},
    (S → Matrix ι κ C) → Prop

def IsRegularGLType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ} {S : Set (GL (Fin n) C)} {m : ℕ},
    (S → GL (Fin m) C) → Prop

def IsRegularRepresentationType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ} {H : Subgroup (GL (Fin n) C)} {m : ℕ},
    (H →* GL (Fin m) C) → Prop

def ZariskiTopologyType :=
  ∀ {C : Type u} [Field C] {n : ℕ}, TopologicalSpace (GL (Fin n) C)

def IsAlgebraicSubgroupType :=
  ∀ {C : Type u} [Field C] {n : ℕ}, Subgroup (GL (Fin n) C) → Prop

def EvalSolutionType :=
  ∀ {C : Type u} [CommRing C] {A : Type v} [CommRing A] [Algebra C A] {n : ℕ}
    (I : Ideal (CoordinatePolynomial C n)), MatrixSolutions I A → ((CoordinatePolynomial C n ⧸ I) →ₐ[C] A)

def EvalCoordinateType :=
  ∀ {C : Type u} [CommRing C] {n : ℕ} {S : Set (GL (Fin n) C)}, S → Points S C

end BindingTypes

end

end GaloisFormalization.PV.MatrixGroupCoordinates.Specs
