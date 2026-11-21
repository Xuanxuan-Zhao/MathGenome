import MathGenome.Internal.Specs.D07.Ch22.FreeDirectSums
import MathGenome.Internal.Specs.D07.Ch16.QuotientsIsomorphism
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
Independent specification of K07.22.tensor_construction, paper.tex:6727–6762.
The canonical tensor is related explicitly to the source's quotient of the
free abelian group `(M × N) →₀ ℤ` by exactly the three displayed families.
An abelian target has no R-action in the balanced universal property.
All rings are commutative and unital, including the zero ring, and modules
are arbitrary unital modules, with no basis or finiteness assumptions.
The quotient module structure must have the specified action on arbitrary
free representatives, not just an unspecified module structure.
-/

noncomputable section
universe u v w t
namespace Specs.D07.Ch22.TensorConstruction
open scoped TensorProduct

/-- The free abelian group supplied by the preceding free-module construction. -/
abbrev FreeAbelian (M : Type v) (N : Type w) := (M × N) →₀ ℤ

def symbol {M : Type v} {N : Type w} (m : M) (n : N) : FreeAbelian M N :=
  Finsupp.single (m, n) 1

/-- Evaluation of a function on the free generators, extended additively. -/
noncomputable def freeExtension {M : Type v} {N : Type w} {A : Type t}
    [AddCommGroup A] (b : M → N → A) : FreeAbelian M N →+ A :=
  (Finsupp.linearCombination ℤ (fun p : M × N => b p.1 p.2)).toAddMonoidHom

section Presentation
variable (R : Type u) [CommRing R] (M : Type v) (N : Type w)
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Precisely the source's additivity and balancing differences. -/
inductive DefiningRelation : FreeAbelian M N → Prop
  | addLeft (m m' : M) (n : N) :
      DefiningRelation (symbol (m + m') n - symbol m n - symbol m' n)
  | addRight (m : M) (n n' : N) :
      DefiningRelation (symbol m (n + n') - symbol m n - symbol m n')
  | balance (r : R) (m : M) (n : N) :
      DefiningRelation (symbol (r • m) n - symbol m (r • n))

def relationSubgroup : AddSubgroup (FreeAbelian M N) :=
  AddSubgroup.closure {x | DefiningRelation R M N x}

abbrev PresentedTensor := FreeAbelian M N ⧸ relationSubgroup R M N

def projection : FreeAbelian M N →+ PresentedTensor R M N :=
  QuotientAddGroup.mk' (relationSubgroup R M N)

def tensorClass (m : M) (n : N) : PresentedTensor R M N :=
  projection R M N (symbol m n)

/-- The free-group endomorphism sending [m,n] to [rm,n]. -/
noncomputable def freeScalar (r : R) : FreeAbelian M N →+ FreeAbelian M N :=
  freeExtension (fun m n => symbol (r • m) n)

/-- Biadditive and balanced, without a scalar action on A. -/
structure IsBalanced {A : Type t} [AddCommGroup A] (b : M → N → A) : Prop where
  add_left : ∀ m m' n, b (m + m') n = b m n + b m' n
  add_right : ∀ m n n', b m (n + n') = b m n + b m n'
  balance : ∀ (r : R) m n, b (r • m) n = b m (r • n)
end Presentation

/-- The elementary quotient classes satisfy precisely the balanced relations. -/
def QuotientBalanced : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    IsBalanced R M N (tensorClass R M N)

/-- A free-group map factors uniquely iff it kills the displayed generators. -/
def FactorCriterion : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Type t) [AddCommGroup A] (F : FreeAbelian M N →+ A),
    (∀ x, DefiningRelation R M N x → F x = 0) ↔
    ∃! f : PresentedTensor R M N →+ A, ∀ x, f (projection R M N x) = F x

/-- Balanced maps to every abelian group have a unique additive quotient lift. -/
def QuotientUniversalProperty : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Type t) [AddCommGroup A] (b : M → N → A), IsBalanced R M N b →
    ∃! F : PresentedTensor R M N →+ A, ∀ m n, F (tensorClass R M N m n) = b m n

/-- The quotient model and canonical library tensor agree on every generator. -/
def QuotientPresentation : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    ∃ e : PresentedTensor R M N ≃+ (M ⊗[R] N),
      ∀ m n, e (tensorClass R M N m n) = m ⊗ₜ[R] n

/-- Classes generate as an abelian group, not merely as an R-module. -/
def QuotientGenerators : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    AddSubgroup.closure {x | ∃ m n, tensorClass R M N m n = x} = ⊤

/-- The canonical tensor likewise represents balanced maps into abelian groups. -/
def BalancedUniversalProperty : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Type t) [AddCommGroup A] (b : M → N → A), IsBalanced R M N b →
    ∃! F : (M ⊗[R] N) →+ A, ∀ m n, F (m ⊗ₜ[R] n) = b m n

def TensorGenerators : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    AddSubgroup.closure {x : M ⊗[R] N | ∃ m n, m ⊗ₜ[R] n = x} = ⊤

/-- The free scalar endomorphism preserves the actual relation subgroup. -/
def ScalarRelationInvariant : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (x : FreeAbelian M N),
    x ∈ relationSubgroup R M N → freeScalar R M N r x ∈ relationSubgroup R M N

/-- Existence on the original quotient, its scalar descent on all representatives,
its elementary rule, and a compatible linear equivalence to the canonical tensor. -/
def QuotientModuleConstruction : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    ∃ inst : Module R (PresentedTensor R M N),
      letI := inst
      (∀ (r : R) x, r • projection R M N x = projection R M N (freeScalar R M N r x)) ∧
      (∀ (r : R) m n, r • tensorClass R M N m n = tensorClass R M N (r • m) n) ∧
      Ch16.Definition.ModuleLaws R (PresentedTensor R M N) ∧
      ∃ e : PresentedTensor R M N ≃ₗ[R] (M ⊗[R] N),
        ∀ m n, e (tensorClass R M N m n) = m ⊗ₜ[R] n

/-- The four module axioms on the whole tensor and the specified elementary rule. -/
def TensorModuleLaws : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    Ch16.Definition.ModuleLaws R (M ⊗[R] N) ∧
    ∀ (r : R) (m : M) (n : N), r • (m ⊗ₜ[R] n) = (r • m) ⊗ₜ[R] n

/-- Bilinear maps are balanced; scalar-linearity of their additive lift is explicit. -/
def BilinearBalanced : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P] (b : M →ₗ[R] N →ₗ[R] P),
    IsBalanced R M N (fun m n => b m n)

def AdditiveLiftLinear : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P] (b : M →ₗ[R] N →ₗ[R] P)
    (F : (M ⊗[R] N) →+ P),
    (∀ m n, F (m ⊗ₜ[R] n) = b m n) → ∀ (r : R) x, F (r • x) = r • F x

def LinearUniversalProperty : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P] (b : M →ₗ[R] N →ₗ[R] P),
    ∃! F : (M ⊗[R] N) →ₗ[R] P, ∀ m n, F (m ⊗ₜ[R] n) = b m n

/-- The Hom–bilinear correspondence, specifying the evaluation map. -/
def HomBilinearEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P],
    ∃ e : ((M ⊗[R] N) →ₗ[R] P) ≃ₗ[R] (M →ₗ[R] N →ₗ[R] P),
      ∀ F m n, e F m n = F (m ⊗ₜ[R] n)

end Specs.D07.Ch22.TensorConstruction
