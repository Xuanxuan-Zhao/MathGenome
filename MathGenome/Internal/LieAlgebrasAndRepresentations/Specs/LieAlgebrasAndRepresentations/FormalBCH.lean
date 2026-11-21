import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalExpLog

/-! LA A08, notes/005/lie-algebras-and-representations.tex, lines 493–557.
All completions are the actual tensor-degree completion used by the preceding
primitive and exp/log results. Substitution allows arbitrary positive-degree
arguments, including in infinite-dimensional target spaces. -/
noncomputable section

namespace LieAlgebrasAndRepresentations.FormalBCH
open CompletedPrimitives FormalExpLog
universe u v w

/-- BCH on the tensor completion. Its intended inputs have zero constant term. -/
def bch (k : Type u) (V : Type v) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] (p q : Completion k V) : Completion k V :=
  logarithm (generators k V)
    (exponential (generators k V) p * exponential (generators k V) q)

/-- A vector as a homogeneous degree-one completed tensor. -/
def letter (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (x : V) : Completion k V :=
  ⟨PowerSeries.monomial 1 (TensorAlgebra.ι k x), by
    intro n
    rw [PowerSeries.coeff_monomial]
    split_ifs with h
    · subst n; simpa using LinearMap.mem_range_self (TensorAlgebra.ι k) x
    · exact (degree k V n).zero_mem⟩

/-- The vector space with the two universal generators. -/
abbrev Two (k : Type u) := Fin 2 → k

def X (k : Type u) [Field k] : Completion k (Two k) :=
  letter k (Two k) (Pi.single 0 1)

def Y (k : Type u) [Field k] : Completion k (Two k) :=
  letter k (Two k) (Pi.single 1 1)

/-- The universal formal series log(exp X exp Y). -/
def universalBCH (k : Type u) [Field k] [CharZero k] : Completion k (Two k) :=
  bch k (Two k) (X k) (Y k)

/-- The cubic Lie polynomial in an associative algebra, with the commutator
bracket written explicitly to avoid any alternate Lie structure. -/
def cubic {k B : Type*} [Field k] [Ring B] [Algebra k B] (x y : B) : B :=
  x + y + (2 : k)⁻¹ • (x*y-y*x) +
    (12 : k)⁻¹ • (x*(x*y-y*x)-(x*y-y*x)*x) +
    (12 : k)⁻¹ • (y*(y*x-x*y)-(y*x-x*y)*y)

/-- Degreewise extension of substitution. For positive f, only source degrees
at most n contribute to target degree n. The local finiteness assertion and
the algebra laws for this explicit formula are theorem obligations below. -/
def substitute {k : Type u} {V : Type v} {W : Type w} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] Completion k W) (p : Completion k V) : Completion k W :=
  ⟨PowerSeries.mk (fun n => ∑ m ∈ Finset.range (n+1),
      PowerSeries.coeff n ((TensorAlgebra.lift k f) (PowerSeries.coeff m p.val)).val), by
    intro n
    rw [PowerSeries.coeff_mk]
    exact Submodule.sum_mem _ (fun m _ =>
      ((TensorAlgebra.lift k f) (PowerSeries.coeff m p.val)).property n)⟩

/-- Linear assignment of the two generators to the chosen arguments. -/
def twoInputMap {k : Type u} {W : Type w} [Field k]
    [AddCommGroup W] [Module k W] (p q : Completion k W) :
    Two k →ₗ[k] Completion k W where
  toFun a := a 0 • p + a 1 • q
  map_add' a b := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c a := by simp [smul_add, mul_smul]

end LieAlgebrasAndRepresentations.FormalBCH

namespace Specs.LieAlgebrasAndRepresentations.FormalBCH
open _root_.LieAlgebrasAndRepresentations.CompletedPrimitives
open _root_.LieAlgebrasAndRepresentations.FormalExpLog
open _root_.LieAlgebrasAndRepresentations.FormalBCH
universe u v w

def bchExpectedType : Type (max (u+1) (v+1)) :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    Completion k V → Completion k V → Completion k V
def bchExpectedValue : bchExpectedType.{u,v} := bch

def universalExpectedType : Type (u+1) :=
  ∀ (k : Type u) [Field k] [CharZero k], Completion k (Two k)
def universalExpectedValue : universalExpectedType.{u} := universalBCH

/-- The universal result is a completed free Lie element, with no scalar part. -/
def lieExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    Positive k (Two k) (universalBCH k) ∧ InCompletedLie k (Two k) (universalBCH k)

/-- BCH also closes the entire completed free Lie algebra. -/
def closureExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (p q : Completion k V), InCompletedLie k V p → InCompletedLie k V q →
      Positive k V (bch k V p q) ∧ InCompletedLie k V (bch k V p q)

/-- The coefficients through degree three are exactly the displayed cubic
commutator expression, including its zero constant term. -/
def cubicExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ), n ≤ 3 →
    PowerSeries.coeff n (universalBCH k).val =
      PowerSeries.coeff n (cubic (k := k) (X k) (Y k)).val

/-- Full substitution in arbitrary positive-degree elements. This asserts local
finiteness independently of the chosen cutoff, constructs the unital algebra
homomorphism given by the explicit formula, and identifies the substituted
universal BCH with log(exp p exp q). -/
def substitutionExpected : Prop :=
  ∀ (k : Type u) (V : Type v) (W : Type w) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] Completion k W), (∀ x, Positive k W (f x)) →
    (∀ (m n : ℕ) (a : A k V), a ∈ degree k V m → n < m →
      PowerSeries.coeff n ((TensorAlgebra.lift k f) a).val = 0) ∧
    (∀ (p : Completion k V) (n N : ℕ), n < N →
      PowerSeries.coeff n (substitute f p).val =
        ∑ m ∈ Finset.range N,
          PowerSeries.coeff n ((TensorAlgebra.lift k f) (PowerSeries.coeff m p.val)).val) ∧
    (∃ s : Completion k V →ₐ[k] Completion k W,
      (∀ p, s p = substitute f p) ∧ (∀ x, s (letter k V x) = f x) ∧
      (∀ p, Positive k V p → Positive k W (s p)) ∧
      (∀ p, Positive k V p → s (exponential (generators k V) p) =
        exponential (generators k W) (s p)) ∧
      (∀ g, PowerSeries.coeff 0 g.val = 1 → s (logarithm (generators k V) g) =
        logarithm (generators k W) (s g)))

def evaluationExpected : Prop :=
  ∀ (k : Type u) (W : Type w) [Field k] [CharZero k]
    [AddCommGroup W] [Module k W] (p q : Completion k W),
    Positive k W p → Positive k W q →
      substitute (twoInputMap p q) (universalBCH k) = bch k W p q

/-- Associativity applies to all positive arguments, so in particular to
universal generators and to positive completed Lie elements. -/
def associativityExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (p q r : Completion k V), Positive k V p → Positive k V q → Positive k V r →
      bch k V (bch k V p q) r = bch k V p (bch k V q r)

end Specs.LieAlgebrasAndRepresentations.FormalBCH
