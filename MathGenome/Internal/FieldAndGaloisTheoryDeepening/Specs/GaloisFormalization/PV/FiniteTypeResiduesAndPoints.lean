import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType

/-!
Independent statements for the finite-extension and point consequences of PV04.
The residue field at a maximal ideal is represented by its quotient algebra.
-/

namespace GaloisFormalization.PV.Specs

universe u v

/-- A field of finite type as an algebra over an infinite field is finite and algebraic. -/
def finiteAlgebraicOfFiniteTypeType : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Infinite F] [Field E] [Algebra F E]
    [Algebra.FiniteType F E], Module.Finite F E ∧ Algebra.IsAlgebraic F E

/-- The residue field at every maximal ideal of a nonzero finite-type algebra is finite. -/
def maximalQuotientFiniteType : Prop :=
  ∀ (F : Type u) (B : Type v) [Field F] [Infinite F] [CommRing B] [Nontrivial B]
    [Algebra F B] [Algebra.FiniteType F B] (m : Ideal B),
    m.IsMaximal → Module.Finite F (B ⧸ m)

/-- Over an algebraically closed field, every such maximal quotient is the base algebra. -/
def maximalQuotientAlgEquivType : Prop :=
  ∀ (F : Type u) (B : Type v) [Field F] [IsAlgClosed F] [CommRing B] [Nontrivial B]
    [Algebra F B] [Algebra.FiniteType F B] (m : Ideal B),
    m.IsMaximal → Nonempty ((B ⧸ m) ≃ₐ[F] F)

/-- Any nonzero finite-type algebra over an algebraically closed field has a rational point. -/
def existsAlgHomType : Prop :=
  ∀ (F : Type u) (B : Type v) [Field F] [IsAlgClosed F] [CommRing B] [Nontrivial B]
    [Algebra F B] [Algebra.FiniteType F B], Nonempty (B →ₐ[F] F)

/-- Rational points detect every nonzero element of a reduced finite-type algebra. -/
def existsAlgHomOfNeZeroType : Prop :=
  ∀ (F : Type u) (B : Type v) [Field F] [IsAlgClosed F] [CommRing B] [Nontrivial B]
    [Algebra F B] [Algebra.FiniteType F B] [IsReduced B] (b : B),
    b ≠ 0 → ∃ f : B →ₐ[F] F, f b ≠ 0

end GaloisFormalization.PV.Specs
