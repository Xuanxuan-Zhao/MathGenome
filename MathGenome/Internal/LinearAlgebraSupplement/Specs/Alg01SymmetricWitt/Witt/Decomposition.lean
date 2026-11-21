import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Coordinates

namespace Specs.Alg01SymmetricWitt.Witt.Decomposition

open Coordinates (hyperbolicSum)

universe u v w

/-- The hyperbolic count of a decomposition with anisotropic remainder. The remainder
can be realized as a subspace with the restricted form. -/
def IsWittIndex {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) (r : ℕ) : Prop :=
  ∃ A : Submodule k V, (q.comp A.subtype).Anisotropic ∧
    q.Equivalent ((hyperbolicSum k r).prod (q.comp A.subtype))

set_option linter.checkUnivs false in
def IsWittIndexType :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V],
    QuadraticForm k V → ℕ → Prop

/-- A Witt decomposition exists, and all decompositions with anisotropic remainder
have the same hyperbolic count and isometric remainders. -/
def wittDecomposition : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [Invertible (2 : k)] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate →
    ∃ (r : ℕ) (A : Submodule k V),
      (q.comp A.subtype).Anisotropic ∧ (q.comp A.subtype).Nondegenerate ∧
      q.Equivalent ((hyperbolicSum k r).prod (q.comp A.subtype)) ∧
      ∀ {A' : Type w} [AddCommGroup A'] [Module k A'] [FiniteDimensional k A']
        (qA' : QuadraticForm k A') (s : ℕ), qA'.Anisotropic →
        q.Equivalent ((hyperbolicSum k s).prod qA') →
        r = s ∧ (q.comp A.subtype).Equivalent qA'

def existsUnique_wittIndex : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [Invertible (2 : k)] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate → ∃! r, IsWittIndex q r

/-- The hyperbolic count of any anisotropic decomposition characterizes the index. -/
def isWittIndex_iff : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [Invertible (2 : k)] [FiniteDimensional k V]
    {A : Type w} [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (q : QuadraticForm k V) (qA : QuadraticForm k A) (r s : ℕ),
    q.Nondegenerate → qA.Anisotropic → q.Equivalent ((hyperbolicSum k r).prod qA) →
    (IsWittIndex q s ↔ s = r)

def isWittIndex_equivalent : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [Invertible (2 : k)] [FiniteDimensional k V]
    {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (q : QuadraticForm k V) (q' : QuadraticForm k W) (r : ℕ),
    q.Nondegenerate → q'.Nondegenerate → q.Equivalent q' →
    (IsWittIndex q r ↔ IsWittIndex q' r)

def isWittIndex_zero_iff : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [Invertible (2 : k)] [FiniteDimensional k V]
    (q : QuadraticForm k V), q.Nondegenerate → (IsWittIndex q 0 ↔ q.Anisotropic)

def hyperbolicSumZero : Prop :=
  ∀ (k : Type u) [Field k], Subsingleton (Fin 0 → k × k) ∧ hyperbolicSum k 0 = 0

end Specs.Alg01SymmetricWitt.Witt.Decomposition
