import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The first, simultaneous-root step of K07.12.algebraic_closure,
    paper.tex:3725. No ambient algebraically closed field is assumed. -/
universe u

namespace Specs.D07.Ch12.AlgebraicClosureSimultaneousRootField

open Polynomial

/-- One variable for every monic nonconstant polynomial over the base. -/
abbrev RootIndex (K : Type u) [Field K] :=
  {f : K[X] // f.Monic ∧ 0 < f.natDegree}

abbrev RootRing (K : Type u) [Field K] := MvPolynomial (RootIndex K) K

/-- The source's relation f(T_f), with coefficients embedded canonically. -/
noncomputable def relation {K : Type u} [Field K] (f : RootIndex K) : RootRing K :=
  aeval (MvPolynomial.X f) f.val

noncomputable def relationIdeal (K : Type u) [Field K] : Ideal (RootRing K) :=
  Ideal.span (Set.range (relation (K := K)))

/-- Finitely many defining equations can be evaluated simultaneously in a
finite extension obtained without an algebraically closed overfield. -/
def FiniteEvaluation : Prop :=
  ∀ (K : Type u) [Field K] (s : Finset (RootIndex K)),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧
      ∃ φ : RootRing K →ₐ[K] L, ∀ f ∈ s, φ (relation f) = 0

def IdealProper : Prop :=
  ∀ (K : Type u) [Field K], relationIdeal K ≠ ⊤

/-- Every maximal quotient containing these relations is an algebraic field
extension with the specified injective constant map and the root property. -/
def MaximalQuotientProperties : Prop :=
  ∀ (K : Type u) [Field K] (M : Ideal (RootRing K)),
    M.IsMaximal → relationIdeal K ≤ M →
    IsField (RootRing K ⧸ M) ∧
    Function.Injective (algebraMap K (RootRing K ⧸ M)) ∧
    Algebra.IsAlgebraic K (RootRing K ⧸ M) ∧
    ∀ f : K[X], 0 < f.natDegree →
      ∃ x : RootRing K ⧸ M, aeval x f = 0

/-- In particular an algebraic simultaneous-root extension exists in the same
universe as K, and is produced by a maximal quotient of the indicated ring. -/
def SimultaneousRootField : Prop :=
  ∀ (K : Type u) [Field K],
    ∃ (M : Ideal (RootRing K)), M.IsMaximal ∧ relationIdeal K ≤ M ∧
      IsField (RootRing K ⧸ M) ∧
      Function.Injective (algebraMap K (RootRing K ⧸ M)) ∧
      Algebra.IsAlgebraic K (RootRing K ⧸ M) ∧
      ∀ f : K[X], 0 < f.natDegree →
        ∃ x : RootRing K ⧸ M, aeval x f = 0

/-- The abstract field-extension form, with its specified scalar embedding. -/
def ExtensionExists : Prop :=
  ∀ (K : Type u) [Field K],
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Function.Injective (algebraMap K L) ∧ Algebra.IsAlgebraic K L ∧
      ∀ f : K[X], 0 < f.natDegree → ∃ x : L, aeval x f = 0

end Specs.D07.Ch12.AlgebraicClosureSimultaneousRootField
