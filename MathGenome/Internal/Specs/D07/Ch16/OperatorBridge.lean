import MathGenome.Internal.Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
import MathGenome.Internal.Specs.D07.Ch11.LinearAlgebraBridge
import Mathlib.RingTheory.Ideal.Colon

/-!
K07.16.operator_bridge, paper.tex:3330–3380. This final interface assembles
its two accepted prerequisite interfaces, using their canonical objects.
`AEval' T` has the evaluation action on the original vector space; `Cyclic f`
is literally F[X]/(f). Finite products are finite external direct sums.
The additional annihilator statements record the mechanism behind the
largest-factor formula, and the split criterion includes the converse.
No field extension, nonzero-space premise or splitting premise is imposed
on rational canonical form. Empty block families are allowed throughout.
-/
noncomputable section
universe u v w
namespace Specs.D07.Ch16.OperatorBridge
open Polynomial Module
open scoped BigOperators
open Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition

/-- Both directions of the correspondence, the entire action formula, and
identification of the actual underlying invertible intertwining maps. -/
def PolynomialCorrespondence : Prop :=
  OperatorBridgePolynomialModuleCorrespondence.OperatorToModule.{u,v} ∧
  OperatorBridgePolynomialModuleCorrespondence.ModuleToOperator.{u,v} ∧
  OperatorBridgePolynomialModuleCorrespondence.ActionFormula.{u,v} ∧
  OperatorBridgePolynomialModuleCorrespondence.EquivalenceCharacterization.{u,v,w} ∧
  OperatorBridgeRationalCanonicalDecomposition.EvaluationAction.{u,v}

/-- Finite generation and torsion for every finite-dimensional operator. -/
def FiniteTorsion : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.FiniteTorsion.{u,v}

/-- Every given finite field basis spans under the evaluation action too. -/
def BasisSpans : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (T : Module.End F V) (n : ℕ) (b : Basis (Fin n) F V),
    Submodule.span F[X] (Set.range (fun i => Module.AEval'.of T (b i))) = ⊤

/-- The d+1 iterates of each vector are dependent, and a nonzero polynomial
of degree at most d kills that vector. The zero space is included. -/
def VectorPowersDependent : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (x : V),
    (¬ LinearIndependent F (fun j : Fin (finrank F V + 1) => (T ^ j.val) x)) ∧
    ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ finrank F V ∧ aeval T p x = 0

/-- An algebraic operator on a space with an infinite basis need not have
finite-dimensional underlying space. -/
def InfiniteAlgebraicExample : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.InfiniteAlgebraicExample.{u}

/-- The free F[X] module cannot occur even as a submodule. -/
def NoFreePart : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V)
    (g : F[X] →ₗ[F[X]] Module.AEval' T), ¬ Function.Injective g

/-- Testing the generator 1 gives the actual annihilator ideal. Monicity,
positive degree and irreducibility are unnecessary for this identity. -/
def CyclicAnnihilator : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]),
    Module.annihilator F[X] (Cyclic f) = Ideal.span {f} ∧
    ∀ p : F[X], p • (1 : Cyclic f) = 0 ↔ f ∣ p

/-- The evaluated operator annihilator is the intersection of the cyclic
annihilators, for every actual quotient representation. -/
def IntersectionAnnihilator : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (T : Module.End F V) (s : ℕ) (f : Fin s → F[X]), HasFactors T f →
    Module.annihilator F[X] (Module.AEval' T) =
        Ch11.LinearAlgebraBridge.annihilator F V T ∧
    Ch11.LinearAlgebraBridge.annihilator F V T = ⨅ i, Ideal.span {f i}

/-- The ascending divisibility chain makes its intersection the last ideal;
the empty intersection is the whole polynomial ring. -/
def LargestAnnihilator : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (T : Module.End F V) (s : ℕ) (f : Fin s → F[X]),
    Normalized f → HasFactors T f →
    (s = 0 → Ch11.LinearAlgebraBridge.annihilator F V T = ⊤) ∧
    (∀ h : 0 < s, Ch11.LinearAlgebraBridge.annihilator F V T =
      Ideal.span {f ⟨s - 1, Nat.sub_lt h (by decide)⟩})

/-- The residue power basis is the prescribed companion basis, and each block
has characteristic polynomial f and annihilator (f). -/
def CompanionBlocks : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.CompanionQuotient.{u}

/-- Existence of one actual normalized representation, together with the
companion matrix, dimension, characteristic and minimal polynomial formulas.
The latter formulas hold for every representation in `AllBlockFormulas`. -/
def RationalCanonicalForm : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    ∃ (s : ℕ) (f : Fin s → F[X]), Normalized f ∧ HasFactors T f ∧
      (∃ b : Basis (Σ i, Fin (f i).natDegree) F V,
        LinearMap.toMatrix b b T = Matrix.blockDiagonal' (fun i => companion (f i))) ∧
      (∑ i, (f i).natDegree) = finrank F V ∧
      T.charpoly = ∏ i, f i ∧
      (s = 0 ↔ finrank F V = 0) ∧
      (∀ h : 0 < s, minpoly F T = f ⟨s - 1, Nat.sub_lt h (by decide)⟩)

def AllBlockFormulas : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.BlockFormulas.{u,v}

/-- Arbitrary normalized factor representations agree, and those factors
classify invertible field-linear intertwiners, also between different spaces. -/
def Classification : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.FactorUniqueness.{u,v} ∧
  OperatorBridgeRationalCanonicalDecomposition.SimilarityClassification.{u,v,w}

def ZeroSpace : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.ZeroSpace.{u,v}

/-- In each primary quotient use the reversed powers of X-λ; multiplication
by X is λI plus the superdiagonal shift. -/
def JordanQuotient : Prop :=
  OperatorBridgeRationalCanonicalDecomposition.JordanQuotient.{u}

/-- Splitting of the needed factors is equivalent to an actual primary
quotient representation with the indicated Jordan matrix in a field basis.
This includes dimension zero and uses the original coefficient field. -/
def JordanCriterion : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (s : ℕ) (f : Fin s → F[X]),
    Normalized f → HasFactors T f →
    ((∀ i, (f i).Splits) ↔
      ∃ (r : ℕ) (e : Fin r → ℕ) (lam : Fin r → F),
        (∀ i, 0 < e i) ∧ HasFactors T (fun i => (X - C (lam i)) ^ e i) ∧
        ∃ b : Basis (Σ i, Fin (e i)) F V,
          LinearMap.toMatrix b b T = Specs.D05.M10.JordanExistence.jordanMatrix e lam ∧
          (∑ i, e i) = finrank F V)

end Specs.D07.Ch16.OperatorBridge
