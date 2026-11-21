import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import MathGenome.Internal.Specs.D07.Ch16.PidSubmodulesFinite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic

/-!
Independent specification of K07.16.torsion, paper.tex:3122–3144.
The general results use a commutative domain and arbitrary unital modules.
Only the common annihilator assertion assumes a PID and finite generation.
The zero module and an empty generating family are allowed. The canonical
library torsion submodule is explicitly identified with the source's
nonzero-annihilator predicate, rather than relying on its name.

The examples retain the actual quotient k[X]/(X) and the actual spans of
(1,0) and (1,[1]) in Z × Z/2Z. `IsCompl` asserts both trivial intersection
and generation of the ambient module; the linear equivalences to Z assert
that these complements are free of rank one.
-/

universe u v w

namespace Specs.D07.Ch16.Torsion

def TorsionMembership : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M] (x : M),
    x ∈ Submodule.torsion R M ↔ ∃ r : R, r ≠ 0 ∧ r • x = 0

def TorsionSubmodule : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M],
    ∃ T : Submodule R M, (T : Set M) = {x | ∃ r : R, r ≠ 0 ∧ r • x = 0}

def TorsionWitnessClosure : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (r s : R) (x y : M), r ≠ 0 → s ≠ 0 → r • x = 0 → s • y = 0 →
    r * s ≠ 0 ∧ (r * s) • (x + y) = 0 ∧ r • (-x) = 0 ∧
      ∀ a : R, r • (a • x) = 0

def QuotientTorsionFree : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M],
    Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)

/-- The quotient projection has precisely the torsion kernel, and all
linear maps induce maps of the canonical quotients with the expected formula. -/
def QuotientCanonical : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M],
    LinearMap.ker (Submodule.torsion R M).mkQ = Submodule.torsion R M ∧
    ∀ (N : Type w) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
      ∃ g : (M ⧸ Submodule.torsion R M) →ₗ[R] (N ⧸ Submodule.torsion R N),
        ∀ x : M, g ((Submodule.torsion R M).mkQ x) =
          (Submodule.torsion R N).mkQ (f x)

def CommonAnnihilator : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ Submodule.torsion R M, r • x = 0

def TorsionFinite : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    Module.Finite R (Submodule.torsion R M)

def ZeroTorsionAnnihilator : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M],
    Submodule.torsion R M = ⊥ →
      (1 : R) ≠ 0 ∧ ∀ x ∈ Submodule.torsion R M, (1 : R) • x = 0

abbrev PolynomialXQuotient (k : Type u) [Field k] :=
  Polynomial k ⧸ Ideal.span ({Polynomial.X} : Set (Polynomial k))

def PolynomialQuotientExample : Prop :=
  ∀ (k : Type u) [Field k],
    (Polynomial.X : Polynomial k) ≠ 0 ∧
    (∀ x : PolynomialXQuotient k, (Polynomial.X : Polynomial k) • x = 0) ∧
    (∀ x : PolynomialXQuotient k, ∃ r : Polynomial k, r ≠ 0 ∧ r • x = 0) ∧
    Nonempty (PolynomialXQuotient k ≃+* k) ∧
    (Infinite k → Infinite (PolynomialXQuotient k))

abbrev IntegerExample := ℤ × ZMod 2

def finitePart : Submodule ℤ IntegerExample :=
  LinearMap.ker (LinearMap.fst ℤ ℤ (ZMod 2))

def horizontal : Submodule ℤ IntegerExample :=
  Submodule.span ℤ {((1, 0) : IntegerExample)}

def diagonal : Submodule ℤ IntegerExample :=
  Submodule.span ℤ {((1, 1) : IntegerExample)}

def IntegerExampleTorsion : Prop :=
  Submodule.torsion ℤ IntegerExample = finitePart

def DistinctFreeComplements : Prop :=
  horizontal ≠ diagonal ∧
    IsCompl finitePart horizontal ∧ IsCompl finitePart diagonal ∧
    Nonempty (horizontal ≃ₗ[ℤ] ℤ) ∧ Nonempty (diagonal ≃ₗ[ℤ] ℤ)

end Specs.D07.Ch16.Torsion
