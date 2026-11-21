import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientComplete

/-!
Independent specification of paper.tex, 9916–9923 (`fa2:p2:unitization`).
The input algebra need not have a unit and may be zero. Ideals are complex
linear subspaces absorbing multiplication on both sides. The quotient is the
original submodule quotient, with the distance norm fixed in Part 1.
No properness, commutativity, or norm-one hypothesis is imposed on the quotient.
-/

namespace Specs.ExpandedFA.BanachAlgebra.UnitizationQuotient

open Conventions

universe u

/-- The manuscript's order of coordinates is `(a, λ)`, whereas the native
unitization stores the scalar first. -/
def pair {A : Type u} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (a : A) (s : ℂ) :
    UnitizationValue A := WithLp.toLp 1 ⟨s, a⟩

/-- The actual direct-sum coordinates, product, identity, and sum norm. -/
def UnitizationFormulas : Prop :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A],
    Function.Bijective (fun p : A × ℂ => pair p.1 p.2) ∧
    (∀ (a b : A) (s t : ℂ),
      pair a s * pair b t = pair (a * b + s • b + t • a) (s * t)) ∧
    pair (0 : A) 1 = 1 ∧
    (∀ (a : A) (s : ℂ), ‖pair a s‖ = ‖a‖ + ‖s‖) ∧
    (∀ (a b : A) (s t : ℂ), pair a s + pair b t = pair (a + b) (s + t)) ∧
    (∀ (c : ℂ) (a : A) (s : ℂ), c • pair a s = pair (c • a) (c * s))

def UnitizationBanach : Prop :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A],
    IsBanachAlgebraValue A → IsUnitalBanachAlgebraValue (UnitizationValue A)

/-- Algebra ideals include scalar closure, also for nonunital algebras. -/
def IsTwoSidedIdeal {A : Type u} [NonUnitalRing A] [Module ℂ A]
    (I : Submodule ℂ A) : Prop :=
  (∀ (a b : A), b ∈ I → a * b ∈ I) ∧
    (∀ (a b : A), a ∈ I → a * b ∈ I)

/-- These laws refer to the fixed quotient addition, scalar action, and norm,
not to an arbitrarily chosen isomorphic replacement. -/
def QuotientAlgebraLaws {A : Type u} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    (I : Submodule ℂ A) (m : (A ⧸ I) → (A ⧸ I) → (A ⧸ I)) : Prop :=
  (∀ a b : A, m (I.mkQ a) (I.mkQ b) = I.mkQ (a * b)) ∧
  (∀ x y z, m (m x y) z = m x (m y z)) ∧
  (∀ x y z, m (x + y) z = m x z + m y z) ∧
  (∀ x y z, m x (y + z) = m x y + m x z) ∧
  (∀ x, m 0 x = 0 ∧ m x 0 = 0) ∧
  (∀ (c : ℂ) x y, m (c • x) y = c • m x y) ∧
  (∀ (c : ℂ) x y, m x (c • y) = c • m x y) ∧
  (∀ x y, ‖m x y‖ ≤ ‖x‖ * ‖y‖)

/-- A native ring structure with exactly the already fixed additive, metric,
and norm structures, and with the exhibited quotient multiplication. -/
def NativeQuotientRing {A : Type u} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    (I : Submodule ℂ A) (hI : IsClosed (I : Set A))
    (m : (A ⧸ I) → (A ⧸ I) → (A ⧸ I)) : Prop :=
  letI := ExpandedFA.P1.C02QuotientNorm.Spec.quotientNormedGroupValue ℂ A I hI
  ∃ R : NonUnitalNormedRing (A ⧸ I),
    R.toMul = (⟨m⟩ : Mul (A ⧸ I)) ∧
    R.toNorm = (inferInstance : Norm (A ⧸ I)) ∧
    R.toMetricSpace = (inferInstance : MetricSpace (A ⧸ I)) ∧
    R.toAddCommGroup = (inferInstance : AddCommGroup (A ⧸ I))

/-- Closed ideals give complete quotient algebras. The functional laws make
scalar compatibility explicit; the native ring witness fixes every inherited
operation and its metric. Completeness uses the very same quotient norm. -/
def QuotientBanach : Prop :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (I : Submodule ℂ A) (_hideal : IsTwoSidedIdeal I) (hclosed : IsClosed (I : Set A)),
    letI := ExpandedFA.P1.C02QuotientNorm.Spec.quotientNormedGroupValue ℂ A I hclosed
    IsBanachAlgebraValue A →
      (∃ m, QuotientAlgebraLaws I m ∧ NativeQuotientRing I hclosed m) ∧
      ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue (A ⧸ I) ∧
      (∀ a : A, ‖I.mkQ a‖ = sInf ((fun i : A => ‖a - i‖) '' (I : Set A)))

end Specs.ExpandedFA.BanachAlgebra.UnitizationQuotient
