import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.ZMod.Basic

/-! The shared structures for Definition 2.1 of *Topics in Lie Theory*. -/

namespace LieNotes.SuperRestricted

universe u v w z

/-- The sign for crossing elements of degrees `i` and `j`. -/
def paritySign (k : Type u) [Field k] (i j : ZMod 2) : k :=
  (-1 : k) ^ (i.val * j.val)

/-- A parity grading by an internal direct sum of subspaces. -/
structure Grading (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V] where
  piece : ZMod 2 → Submodule k V
  isInternal : DirectSum.IsInternal piece

section Bracket

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- A bilinear bracket adds degrees on homogeneous inputs. -/
def BracketGraded (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V) : Prop :=
  ∀ ⦃i j⦄ ⦃x y : V⦄, x ∈ G.piece i → y ∈ G.piece j → b x y ∈ G.piece (i + j)

/-- Skew symmetry with the parity sign. -/
def GradedSkew (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V) : Prop :=
  ∀ ⦃i j⦄ ⦃x y : V⦄, x ∈ G.piece i → y ∈ G.piece j →
    b x y = (-paritySign k i j) • b y x

/-- The adjoint map of a homogeneous element is a graded derivation of the bracket. -/
def GradedJacobi (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V) : Prop :=
  ∀ ⦃i j l⦄ ⦃x y t : V⦄, x ∈ G.piece i → y ∈ G.piece j → t ∈ G.piece l →
    b x (b y t) = b (b x y) t + paritySign k i j • b y (b x t)

/-- The additional identity on odd elements in characteristic three. -/
def OddTripleIdentity (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V) : Prop :=
  ∀ ⦃x : V⦄, x ∈ G.piece 1 → b x (b x x) = 0

end Bracket

/-- A Lie superalgebra on a vector space over a field of characteristic different from two. -/
structure LieSuperalgebra (k : Type u) (V : Type v) [Field k] [NeZero (2 : k)]
    [AddCommGroup V] [Module k V] where
  grading : Grading k V
  bracket : V →ₗ[k] V →ₗ[k] V
  bracket_mem : BracketGraded grading bracket
  skew : GradedSkew grading bracket
  jacobi : GradedJacobi grading bracket
  oddTriple_char_three : ringChar k = 3 → OddTripleIdentity grading bracket

/-- A graded action of a Lie superalgebra on a vector space with a fixed grading. -/
structure GradedModule {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)]
    [AddCommGroup V] [Module k V] (L : LieSuperalgebra k V)
    {M : Type w} [AddCommGroup M] [Module k M] (G : Grading k M) where
  act : V →ₗ[k] Module.End k M
  act_mem : ∀ ⦃i j⦄ ⦃x : V⦄ ⦃m : M⦄, x ∈ L.grading.piece i → m ∈ G.piece j →
    act x m ∈ G.piece (i + j)
  map_bracket : ∀ ⦃i j⦄ ⦃x y : V⦄, x ∈ L.grading.piece i → y ∈ L.grading.piece j →
    act (L.bracket x y) = act x * act y - paritySign k i j • (act y * act x)

/-- A parity-preserving linear intertwiner between graded actions. -/
structure GradedModule.Hom {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)]
    [AddCommGroup V] [Module k V] {L : LieSuperalgebra k V}
    {M : Type w} [AddCommGroup M] [Module k M] {G : Grading k M}
    {N : Type z} [AddCommGroup N] [Module k N] {H : Grading k N}
    (A : GradedModule L G) (B : GradedModule L H) where
  toLinearMap : M →ₗ[k] N
  map_piece : ∀ ⦃i⦄ ⦃m : M⦄, m ∈ G.piece i → toLinearMap m ∈ H.piece i
  intertwines : ∀ (x : V) (m : M), toLinearMap (A.act x m) = B.act x (toLinearMap m)

end LieNotes.SuperRestricted

namespace Specs.LieNotes.SuperRestricted.SuperLie

open _root_.LieNotes.SuperRestricted

universe u v w z

-- The types of the contract declarations only record the maximum universe.
set_option linter.checkUnivs false

def paritySignType := ∀ (k : Type u) [Field k], ZMod 2 → ZMod 2 → k

def paritySignValue (k : Type u) [Field k] (i j : ZMod 2) : k :=
  (-1 : k) ^ (i.val * j.val)

def gradingType := ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V], Type v

def gradingValue := @Grading

def lieSuperalgebraType := ∀ (k : Type u) (V : Type v) [Field k] [NeZero (2 : k)]
  [AddCommGroup V] [Module k V], Type v

def lieSuperalgebraValue := @LieSuperalgebra

def gradedModuleType := ∀ {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)]
  [AddCommGroup V] [Module k V] (_ : LieSuperalgebra k V)
  {M : Type w} [AddCommGroup M] [Module k M] (_ : Grading k M), Type (max v w)

def gradedModuleValue := @GradedModule

def gradedModuleHomType := ∀ {k : Type u} {V : Type v} [Field k] [NeZero (2 : k)]
  [AddCommGroup V] [Module k V] {L : LieSuperalgebra k V}
  {M : Type w} [AddCommGroup M] [Module k M] {G : Grading k M}
  {N : Type z} [AddCommGroup N] [Module k N] {H : Grading k N}
  (_ : GradedModule L G) (_ : GradedModule L H), Type (max w z)

def gradedModuleHomValue := @GradedModule.Hom

/-- The nonzero numeral used in the structures is equivalent to the source condition. -/
def charNeTwoType : Prop := ∀ (k : Type u) [Field k], (2 : k) ≠ 0 ↔ ringChar k ≠ 2

/-- The factor of three follows from degree compatibility, skew symmetry, and Jacobi. -/
def threeSmulOddTripleType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V),
    BracketGraded G b → GradedSkew G b → GradedJacobi G b →
    ∀ ⦃x : V⦄, x ∈ G.piece 1 → (3 : k) • b x (b x x) = 0

/-- Outside characteristic three, the odd triple identity needs no additional axiom. -/
def oddTripleOfCharNeThreeType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V),
    BracketGraded G b → GradedSkew G b → GradedJacobi G b →
    ringChar k ≠ 3 → OddTripleIdentity G b

/-- Every Lie superalgebra satisfies the odd triple identity. -/
def oddTripleType : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [NeZero (2 : k)]
    (L : LieSuperalgebra k V), OddTripleIdentity L.grading L.bracket

end Specs.LieNotes.SuperRestricted.SuperLie
