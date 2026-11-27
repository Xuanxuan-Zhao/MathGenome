import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.NonpositiveAlgebras
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finsupp.Weight
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.SuccPred.Limit

open CategoryTheory

universe u v

namespace DerivedFormalization.Affine.Semifree

variable {k : Type u} [Field k] [CharZero k]

/-- A set of homogeneous generators in nonpositive cochain degrees. -/
structure Variables where
  Index : Type v
  degree : Index → ℤ
  nonpositive : ∀ x, degree x ≤ 0

namespace Variables

variable (V : Variables.{v})

abbrev Exponent := V.Index →₀ ℕ

/-- A monomial may contain any power of an even variable and at most one
copy of each odd variable. -/
def Admissible (m : V.Exponent) : Prop :=
  ∀ x, Odd (V.degree x) → m x ≤ 1

abbrev Monomial := {m : V.Exponent // V.Admissible m}

noncomputable def weight : V.Exponent →+ ℤ := Finsupp.weight V.degree

abbrev constant : V.Monomial := ⟨0, fun _ _ => Nat.zero_le _⟩

noncomputable def singleton (x : V.Index) : V.Monomial :=
  ⟨Finsupp.single x 1, by
    classical
    intro y _
    by_cases h : x = y <;> simp [h]⟩

/-- The order used to write monomials. Classical well-ordering makes the
construction available for every small type of generators. -/
noncomputable abbrev normalOrder : LinearOrder V.Index := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The exponent of the Koszul sign for sorting a concatenation of two
monomials written in normal order. -/
noncomputable def inversions (m n : V.Exponent) : ℤ := by
  letI := V.normalOrder
  exact m.sum fun x a => n.sum fun y b =>
    if y < x then (a : ℤ) * V.degree x * ((b : ℤ) * V.degree y) else 0

end Variables

section Terms

noncomputable section

variable (A : NonpositiveCDGA.{u,v} k) (V : Variables.{v})

/-- The coefficient of a monomial of weight w in degree n belongs to A^(n-w). -/
abbrev Coefficient (n : ℤ) (m : V.Monomial) : Type v :=
  A.complex.X (n - V.weight m.val)

/-- Homogeneous finite polynomials with coefficients on the left. -/
abbrev Polynomial (n : ℤ) := DirectSum V.Monomial (Coefficient A V n)

open Classical in
def term (n : ℤ) (m : V.Monomial) : Coefficient A V n m →ₗ[k] Polynomial A V n :=
  DirectSum.lof k _ _ m

/-- Reindex a graded module component along equality of degrees. -/
def castDegree (X : ℤ → ModuleCat.{v} k) {i j : ℤ} (h : i = j) : X i →ₗ[k] X j :=
  (eqToHom (congrArg X h)).hom

omit [CharZero k] in
@[simp] theorem castDegree_refl (X : ℤ → ModuleCat.{v} k) {i : ℤ} :
    castDegree X (rfl : i = i) = LinearMap.id := rfl

def coefficient (i : ℤ) : A.complex.X i →ₗ[k] Polynomial A V i :=
  (term A V i V.constant).comp (castDegree A.complex.X (by
    change i = i - V.weight 0
    rw [map_zero, sub_zero]))

def variableTerm (x : V.Index) : Polynomial A V (V.degree x) :=
  term A V _ (V.singleton x) (castDegree A.complex.X (by
    change 0 = V.degree x - V.weight (Finsupp.single x 1)
    rw [Variables.weight, Finsupp.weight_single, one_smul, sub_self]) A.one)

open Classical in
/-- The product of two monomial terms, including the coefficient crossing
and the signed sorting of the concatenation. An inadmissible exponent
represents the zero product. -/
def termProduct (i j n : ℤ) (h : i + j = n) (m p : V.Monomial) :
    Coefficient A V i m →ₗ[k] Coefficient A V j p →ₗ[k] Polynomial A V n :=
  if hp : V.Admissible (m.val + p.val) then
    ((A.mul _ _ _ (by
      change i - V.weight m.val + (j - V.weight p.val) =
        n - V.weight (m.val + p.val)
      rw [map_add]
      omega)).compr₂ (term A V n ⟨m.val + p.val, hp⟩)) |> fun f =>
      ((V.weight m.val * (j - V.weight p.val) + V.inversions m.val p.val).negOnePow : ℤˣ) • f
  else 0

open Classical in
/-- Extend monomial multiplication by bilinearity over the finite supports. -/
def polynomialMul (i j n : ℤ) (h : i + j = n) :
    Polynomial A V i →ₗ[k] Polynomial A V j →ₗ[k] Polynomial A V n :=
  DirectSum.toModule k _ _ fun m =>
    LinearMap.flip (DirectSum.toModule k _ _ fun p => (termProduct A V i j n h m p).flip)

@[simp] theorem polynomialMul_term (i j n : ℤ) (h : i + j = n)
    (m p : V.Monomial) (a : Coefficient A V i m) (b : Coefficient A V j p) :
    polynomialMul A V i j n h (term A V i m a) (term A V j p b) =
      termProduct A V i j n h m p a b := by
  classical
  simp [polynomialMul, term]


/-- Support of a polynomial is restricted to variables in the indicated set. -/
def UsesOnly (S : Set V.Index) {i : ℤ} (p : Polynomial A V i) : Prop :=
  ∀ m : V.Monomial, p m ≠ 0 → ∀ x ∈ m.val.support, x ∈ S

/-- The graded presentation compares multiplication, the unit, and the
specified map from the original base algebra. -/
structure Presentation {P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) where
  component : ∀ i, Polynomial A V i ≃ₗ[k] P.complex.X i
  map_one : component 0 (coefficient A V 0 A.one) = P.one
  map_mul (i j n : ℤ) (h : i + j = n) (x : Polynomial A V i) (y : Polynomial A V j) :
    component n (polynomialMul A V i j n h x y) =
      P.mul i j n h (component i x) (component j y)
  map_base (i : ℤ) (a : A.complex.X i) :
    component i (coefficient A V i a) = f.chainMap.f i a

/-- The strict predecessors of a stage form its earlier variables.
A stage can contain an arbitrary set of simultaneous generators. -/
structure Stages where
  Stage : Type v
  order : LinearOrder Stage
  wellFounded : WellFounded order.toLT.lt
  stage : V.Index → Stage

instance (S : Stages V) : LinearOrder S.Stage := S.order

def Stages.before {V : Variables.{v}} (S : Stages V) (a : S.Stage) : Set V.Index :=
  {x | S.stage x < a}

/-- The differential of a generator belongs to the algebra of earlier
variables in the chosen presentation. -/
structure StagedPresentation {P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P)
    extends Presentation A V f where
  stages : Stages V
  earlier (x : V.Index) :
    UsesOnly A V (stages.before (stages.stage x))
      ((component (V.degree x + 1)).symm
        (P.complex.d (V.degree x) (V.degree x + 1)
          (component (V.degree x) (variableTerm A V x))))

def IsSemifree {P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) : Prop :=
  ∃ V : Variables.{v}, Nonempty (StagedPresentation A V f)

/-- A linear, unital, multiplicative graded map out of the polynomial
algebra, over a given degree-preserving unital multiplicative map from A. -/
structure GradedLift (B : CommDGAlgebra.{u,v} k) (f : ∀ i, A.complex.X i →ₗ[k] B.complex.X i)
    (x : ∀ a, B.complex.X (V.degree a)) where
  component : ∀ i, Polynomial A V i →ₗ[k] B.complex.X i
  map_mul (i j n : ℤ) (h : i+j = n) (a : Polynomial A V i) (b : Polynomial A V j) :
    component n (polynomialMul A V i j n h a b) =
      B.mul i j n h (component i a) (component j b)
  map_base (i : ℤ) (a : A.complex.X i) : component i (coefficient A V i a) = f i a
  map_var (a : V.Index) : component (V.degree a) (variableTerm A V a) = x a

/-- A degree-one graded derivation on the monomial algebra extending the
base differential and having specified values on the variables. -/
structure Derivation (dx : ∀ x, Polynomial A V (V.degree x + 1)) where
  d : ∀ i, Polynomial A V i →ₗ[k] Polynomial A V (i+1)
  leibniz (i j n : ℤ) (h : i+j = n) (x : Polynomial A V i) (y : Polynomial A V j) :
    d n (polynomialMul A V i j n h x y) =
      polynomialMul A V (i+1) j (n+1) (by omega) (d i x) y +
        i.negOnePow • polynomialMul A V i (j+1) (n+1) (by omega) x (d j y)
  on_base (i : ℤ) (a : A.complex.X i) :
    d i (coefficient A V i a) = coefficient A V (i+1) (A.complex.d i (i+1) a)
  on_var (x : V.Index) : d (V.degree x) (variableTerm A V x) = dx x

/-- The cycle test at a stage uses the differential determined by the
values on the strictly earlier variables. -/
def EarlierCycles (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x + 1)) : Prop :=
  ∀ x (dy : ∀ y, Polynomial A V (V.degree y+1)) (D : Derivation A V dy),
    (∀ y ∈ S.before (S.stage x), dy y = dx y) → D.d (V.degree x+1) (dx x) = 0

end
end Terms

end DerivedFormalization.Affine.Semifree

namespace Specs.DerivedFormalization.Affine.SemifreeAlgebras

open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Semifree

set_option linter.checkUnivs false

abbrev CDGA := _root_.DerivedFormalization.Affine.NonpositiveCDGA

def PolynomialNonpositive : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i : ℤ), 0 < i → Subsingleton (Polynomial A V i)

def MonomialTermsInjective : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i : ℤ) (m : V.Monomial), Function.Injective (term A V i m)

def PolynomialFiniteSupport : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i : ℤ) (p : Polynomial A V i), {m | p m ≠ 0}.Finite

open Classical in
def MonomialExpansion : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i : ℤ) (p : Polynomial A V i), (∑ m ∈ p.support, term A V i m (p m)) = p

def PowersOfAVariable : Prop :=
  ∀ (V : Variables.{v}) (x : V.Index) (r : ℕ),
    V.Admissible (Finsupp.single x r) ↔ (Odd (V.degree x) → r ≤ 1)

def OddVariableSquare : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (x : V.Index), Odd (V.degree x) →
    polynomialMul A V (V.degree x) (V.degree x) (V.degree x+V.degree x) rfl
      (variableTerm A V x) (variableTerm A V x) = 0

def CoefficientMultiplication : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (b : A.complex.X j),
    polynomialMul A V i j n h (coefficient A V i a) (coefficient A V j b) =
      coefficient A V n (A.mul i j n h a b)

def PolynomialAssociative : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i j l : ℤ) (x : Polynomial A V i) (y : Polynomial A V j) (z : Polynomial A V l),
    polynomialMul A V (i+j) l (i+j+l) rfl (polynomialMul A V i j (i+j) rfl x y) z =
      polynomialMul A V i (j+l) (i+j+l) (add_assoc i j l).symm x
        (polynomialMul A V j l (j+l) rfl y z)

def PolynomialGradedCommutative : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i j n : ℤ) (h : i+j = n) (x : Polynomial A V i) (y : Polynomial A V j),
    polynomialMul A V i j n h x y =
      (i*j).negOnePow • polynomialMul A V j i n ((add_comm j i).trans h) y x

def PolynomialUnitalLeft : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i : ℤ) (x : Polynomial A V i),
    polynomialMul A V 0 i i (zero_add i) (coefficient A V 0 A.one) x = x

def PolynomialUnitalRight : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (i : ℤ) (x : Polynomial A V i),
    polynomialMul A V i 0 i (add_zero i) x (coefficient A V 0 A.one) = x

def GradedUniversalProperty : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (B : _root_.DerivedFormalization.Affine.CommDGAlgebra.{u,v} k)
    (f : ∀ i, A.complex.X i →ₗ[k] B.complex.X i),
    f 0 A.one = B.one →
    (∀ (i j n : ℤ) (h : i+j = n) (a : A.complex.X i) (b : A.complex.X j),
      f n (A.mul i j n h a b) = B.mul i j n h (f i a) (f j b)) →
    ∀ x : ∀ a, B.complex.X (V.degree a), Nonempty (Unique (GradedLift A V B f x))

def DerivationExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (dx : ∀ x, Polynomial A V (V.degree x + 1)),
    Nonempty (Unique (Derivation A V dx))

def DifferentialSquaresToZero : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (dx : ∀ x, Polynomial A V (V.degree x + 1)) (D : Derivation A V dx),
    (∀ x, D.d (V.degree x + 1) (dx x) = 0) →
    ∀ (i : ℤ) (p : Polynomial A V i), D.d (i+1) (D.d i p) = 0

def ContinuousStages : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (S : Stages V) (a : S.Stage),
    (∃ b : S.Stage, b < a) → (∀ x, S.stage x < a → ∃ b : S.Stage, S.stage x < b ∧ b < a) →
    ∀ (i : ℤ) (p : Polynomial A V i),
      UsesOnly A V (S.before a) p ↔ ∃ b : S.Stage, b < a ∧ UsesOnly A V (S.before b) p

def ContinuousLimitStages : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (S : Stages V) (a : S.Stage), Order.IsSuccLimit a →
    ∀ (i : ℤ) (p : Polynomial A V i),
      UsesOnly A V (S.before a) p ↔ ∃ b : S.Stage, b < a ∧ UsesOnly A V (S.before b) p

def DegreeZeroVariable : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (x : V.Index), V.degree x = 0 → ∀ p : Polynomial A V (V.degree x + 1), p = 0

def EmptyVariables : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A P : CDGA.{u,v} k} (f : A ⟶ P)
    (V : Variables.{v}) [IsEmpty V.Index],
    Presentation A V f → IsIso f

def GradedLiftUniqueness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (B : _root_.DerivedFormalization.Affine.CommDGAlgebra.{u,v} k)
    (f : ∀ i, A.complex.X i →ₗ[k] B.complex.X i)
    (x : ∀ a, B.complex.X (V.degree a)), Subsingleton (GradedLift A V B f x)

def DerivationUniqueness : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (dx : ∀ x, Polynomial A V (V.degree x + 1)), Subsingleton (Derivation A V dx)

def StageDifferential : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1)) (D : Derivation A V dx),
    (∀ x, UsesOnly A V (S.before (S.stage x)) (dx x)) →
    ∀ (a : S.Stage) (i : ℤ) (p : Polynomial A V i),
      UsesOnly A V (S.before a) p → UsesOnly A V (S.before a) (D.d i p)

def DerivationLocality : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (T : Set V.Index) (dx dy : ∀ x, Polynomial A V (V.degree x+1))
    (D : Derivation A V dx) (E : Derivation A V dy),
    (∀ x ∈ T, dx x = dy x) →
    ∀ (i : ℤ) (p : Polynomial A V i), UsesOnly A V T p → D.d i p = E.d i p

def StagedDifferentialExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CDGA.{u,v} k) (V : Variables.{v})
    (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1)),
    (∀ x, UsesOnly A V (S.before (S.stage x)) (dx x)) → EarlierCycles A V S dx →
    ∃! D : Derivation A V dx,
      (∀ (i : ℤ) (p : Polynomial A V i), D.d (i+1) (D.d i p) = 0) ∧
      ∃ (P : CDGA.{u,v} k) (f : A ⟶ P) (E : StagedPresentation A V f),
        E.stages = S ∧ ∀ (i : ℤ) (p : Polynomial A V i),
          E.component (i+1) (D.d i p) = P.complex.d i (i+1) (E.component i p)

def VariablesType := Type (v+1)
abbrev variablesModel := Variables.{v}

def MonomialType := Variables.{v} → Type v
abbrev monomialModel (V : Variables.{v}) := V.Monomial

def PolynomialType := ∀ {k : Type u} [Field k] [CharZero k],
  CDGA.{u,v} k → Variables.{v} → ℤ → Type v
abbrev polynomialModel {k : Type u} [Field k] [CharZero k]
    (A : CDGA.{u,v} k) (V : Variables.{v}) (i : ℤ) := Polynomial A V i

def StagesType := Variables.{v} → Type (v+1)
abbrev stagesModel (V : Variables.{v}) := Stages V

def PresentationType := ∀ {k : Type u} [Field k] [CharZero k] {A P : CDGA.{u,v} k},
  Variables.{v} → (A ⟶ P) → Type (v+1)
abbrev presentationModel {k : Type u} [Field k] [CharZero k] {A P : CDGA.{u,v} k}
    (V : Variables.{v}) (f : A ⟶ P) := StagedPresentation A V f

def IsSemifreeType := ∀ {k : Type u} [Field k] [CharZero k] {A P : CDGA.{u,v} k},
  (A ⟶ P) → Prop
abbrev isSemifree {k : Type u} [Field k] [CharZero k] {A P : CDGA.{u,v} k} (f : A ⟶ P) :=
  IsSemifree A f

end Specs.DerivedFormalization.Affine.SemifreeAlgebras
