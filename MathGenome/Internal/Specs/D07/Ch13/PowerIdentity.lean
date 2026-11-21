import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Separable

/-!
Independent statements for K07.13.power_identity (paper.tex:3877–3890).

`F` is an arbitrary finite field, with its cardinality explicitly identified
with `q`. This includes every field of order q = p^r in the chapter's
convention and requires no choice of an abstract finite-field model.
The product and derivative are formal polynomial operations.
`Separable` expresses simplicity in a splitting field, while the final
statement gives the exact multiplicity of every element of F.
-/

universe u

namespace Specs.D07.Ch13.PowerIdentity

open Polynomial

def AllElementPower : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q → ∀ a : F, a ^ q = a

def NonzeroPowerIdentity : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q → ∀ a : F, a ≠ 0 → a ^ (q - 1) = 1

def Factorization : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q →
      (X ^ q - X : Polynomial F) = ∏ a : F, (X - C a)

def Derivative : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q → (X ^ q - X : Polynomial F).derivative = -1

def Separable : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q → (X ^ q - X : Polynomial F).Separable

def SimpleRoots : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (q : ℕ),
    Fintype.card F = q → ∀ a : F,
      (X ^ q - X : Polynomial F).rootMultiplicity a = 1

end Specs.D07.Ch13.PowerIdentity
