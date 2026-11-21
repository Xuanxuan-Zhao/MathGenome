import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic

/-! The dual-number example of paper.tex 3034–3046.  We use the explicit
`a + b ε` model of the ring; the statement also requires its polynomial
quotient presentation and the canonical residue-field identification. -/
namespace P103.Specs.Ch11.UniversalCoefficientsCounterexample
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.BalancedTensor
noncomputable section
universe u
variable (k : Type u) [Field k]
abbrev R := DualNumber k
instance (priority := 1100) regularRightModule : Module (R k)ᵐᵒᵖ (R k) :=
  Semiring.toOppositeModule
instance (priority := 1100) regularRightSMul : SMul (R k)ᵐᵒᵖ (R k) :=
  ⟨fun r x => x * r.unop⟩
instance residueAlgebra : Algebra (R k) k := TrivSqZeroExt.algebraBase k k
instance residueRightModule : Module (R k)ᵐᵒᵖ k := commRightModule (R k) k

def epsilon : R k := DualNumber.eps

def epsilonLeft : R k →ₗ[R k] R k := LinearMap.mulRight (R k) (epsilon k)
def epsilonRight : R k →ₗ[(R k)ᵐᵒᵖ] R k where
  toFun x := x * epsilon k
  map_add' x y := add_mul x y _
  map_smul' r x := by
    change (x * r.unop) * epsilon k = (x * epsilon k) * r.unop
    ring

/-- The left-module version used by Hom. -/
def C : ChainComplex (ModuleCat (R k)) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of (R k) (R k))
    (fun _ => ModuleCat.ofHom (epsilonLeft k)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (x * epsilon k) * epsilon k = 0
      simp [mul_assoc, epsilon])

/-- The same complex with the standard right regular action, used by tensor. -/
def Cright : ChainComplex (ModuleCat (R k)ᵐᵒᵖ) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of (R k)ᵐᵒᵖ (R k))
    (fun _ => ModuleCat.ofHom (epsilonRight k)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (x * epsilon k) * epsilon k = 0
      simp [mul_assoc, epsilon])

abbrev H (n : ℕ) := Homology (C k) n
abbrev Hr (n : ℕ) := Homology (Cright k) n
abbrev tensorC := tensorComplex (Cright k) k
abbrev homC := homComplex (C k) k

def counterexampleType : Prop := ∀ (k : Type u) [Field k],
  (∃ e : (Polynomial k ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))) ≃ₐ[k] R k,
    e (Ideal.Quotient.mk _ Polynomial.X) = epsilon k) ∧
  (∃ e : (R k ⧸ Ideal.span ({epsilon k} : Set (R k))) ≃+* k,
    ∀ x : R k, e (Ideal.Quotient.mk _ x) = x.fst) ∧
  (∀ i j l, ((C k).d j l).hom.comp ((C k).d i j).hom = 0) ∧
  (∀ n, ((C k).d (n+1) n).hom = epsilonLeft k ∧
    ((Cright k).d (n+1) n).hom = epsilonRight k) ∧
  (∀ j, (C k).d 0 j = 0 ∧ (Cright k).d 0 j = 0) ∧
  (∀ n, Module.Free (R k) ((C k).X n) ∧
    Module.Free (R k)ᵐᵒᵖ ((Cright k).X n)) ∧
  Nonempty (H k 0 ≃ₗ[R k] k) ∧ Nonempty (Hr k 0 ≃ₗ[(R k)ᵐᵒᵖ] k) ∧
  (∀ n, Subsingleton (H k (n+1)) ∧ Subsingleton (Hr k (n+1))) ∧
  (∀ i j, (tensorC k).d i j = 0 ∧ (homC k).d i j = 0) ∧
  (∀ n, Nonempty (Homology (tensorC k) n ≃+ k) ∧
    Nonempty (Homology (homC k) n ≃+ k) ∧
    Nontrivial (Homology (tensorC k) n) ∧ Nontrivial (Homology (homC k) n)) ∧
  (∀ n, 2 ≤ n →
    Subsingleton (Tensor (R k) (Hr k n) k) ∧
    (∀ P : LeftResolution (R k)ᵐᵒᵖ (Hr k (n-1)), P.IsProjective →
      Subsingleton (TorWith P k 1)) ∧
    (∀ P : LeftResolution (R k) (H k (n-1)), P.IsProjective →
      Subsingleton (ExtWith P k 1)) ∧
    Subsingleton (H k n →ₗ[R k] k) ∧
    (∀ (P : LeftResolution (R k)ᵐᵒᵖ (Hr k (n-1))), P.IsProjective →
      ∀ (f : Tensor (R k) (Hr k n) k →+ Homology (tensorC k) n)
        (g : Homology (tensorC k) n →+ TorWith P k 1), ¬ Function.Exact f g) ∧
    (∀ (P : LeftResolution (R k) (H k (n-1))), P.IsProjective →
      ∀ (f : ExtWith P k 1 →+ Homology (homC k) n)
        (g : Homology (homC k) n →+ (H k n →ₗ[R k] k)), ¬ Function.Exact f g))
end
end P103.Specs.Ch11.UniversalCoefficientsCounterexample
