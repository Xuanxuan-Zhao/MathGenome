import Mathlib.FieldTheory.AlgebraicClosure

/-!
Independent specification for K07.12.algebraic_closure,
paper.tex:3720–3729 (chapters/M07.12.tex:179–188).

Every field extension below includes its specified `Algebra` structure.
Algebraicity is the existence of a nonzero polynomial annihilator for each
element; `IsAlgClosed` says that every polynomial splits. No finiteness,
characteristic, or algebraically closed ambient field is assumed for existence.
Uniqueness allows closures in independent universes. In the final assertion,
the ambient extension may contain transcendental elements: only its canonical
intermediate field of algebraic elements is claimed to be an algebraic closure.
-/

universe u v w

namespace Specs.D07.Ch12.AlgebraicClosure

/-- An algebraic, algebraically closed extension exists, with an injective
structure map, in the same universe as the original field. -/
def Existence : Prop :=
  ∀ (K : Type u) [Field K],
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Function.Injective (algebraMap K L) ∧
      Algebra.IsAlgebraic K L ∧ IsAlgClosed L

/-- Any two algebraic closures are isomorphic over the specified base maps.
The extensions need not be finite, separable, or in the same universe. -/
def Uniqueness : Prop :=
  ∀ (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]
    [IsAlgClosed L] [IsAlgClosed M],
      Nonempty (L ≃ₐ[K] M)

/-- The algebraic elements in any algebraically closed extension form an
algebraic closure, using the canonical intermediate field and scalar maps. -/
def RelativeClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω],
      (∀ x : Ω, x ∈ algebraicClosure K Ω ↔
        ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.aeval x p = 0) ∧
      Algebra.IsAlgebraic K (algebraicClosure K Ω) ∧
      IsAlgClosed (algebraicClosure K Ω)

end Specs.D07.Ch12.AlgebraicClosure
