import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.LinearGradedNormalization
import Mathlib.Algebra.Group.Action.Faithful

/-!
The faithful infinite-field step in paper.tex:1158–1164. Coefficients are
lengths over the actual degree-zero field, using the shared Laurent-series
identity. In particular, no dimension or growth certificate is an input.
-/
namespace P103.HilbertNormalizedGrowth

open P103.Graded P103.Specs.Ch06.LinearGradedNormalization

/-- The actual homogeneous vector space over the structural field. -/
def fieldComponent (k : Type*) {C M : Type*} [Field k] [CommRing C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G)
    (j : ℤ) : Submodule k M where
  __ := U.piece j
  smul_mem' a m hm := by
    have ha : algebraMap k C a ∈ G.piece 0 := (hzero _).mpr ⟨a, rfl⟩
    change a • m ∈ U.piece j
    rw [← IsScalarTower.algebraMap_smul C a m]
    simpa only [zero_vadd] using
      (SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) ha hm)

end P103.HilbertNormalizedGrowth

namespace Specs.P103.HilbertNormalizedGrowth

open _root_.P103.Graded _root_.P103.HilbertSerreLength
open _root_.P103.Specs.Ch06.LinearGradedNormalization

universe u v w

/-- Finite dimensionality is asserted before identifying the coefficients,
so `finrank` does not hide an infinite-dimensional component. -/
def finiteComponentsType : Prop :=
  ∀ (k : Type u) {C : Type v} {M : Type w}
    [Field k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    [Module.Finite C M] (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G), Specs.P103.Graded.standardValue G →
      (∀ j, Module.Finite k (_root_.P103.HilbertNormalizedGrowth.fieldComponent k G U hzero j)) ∧
      ∀ j, hilbertFunction G U j =
        (Module.finrank k (_root_.P103.HilbertNormalizedGrowth.fieldComponent k G U hzero j) : ℤ)

/-- The complete assigned conclusion, including exponent zero. -/
def normalizedGrowthType : Prop :=
  ∀ (k : Type u) {C : Type v} {M : Type w}
    [Field k] [Infinite k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Nontrivial M] [FaithfulSMul C M]
    [Module.Finite C M] (G : NonnegativeGrading C) (U : ModuleGrading G M),
    Connected k G → Specs.P103.Graded.standardValue G →
      ∀ (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
        RationalPresentation (hilbertFunction G U) b p e →
        (e = 0 ∨ p.eval 1 ≠ 0) → ringKrullDim C = (e : WithBot ℕ∞)

/-- The zero-dimensional implication is stated separately for partial work.
It does not require a faithful module or a nonzero module. -/
def dimensionZeroType : Prop :=
  ∀ (k : Type u) {C : Type v} {M : Type w}
    [Field k] [Infinite k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M),
    Connected k G → Specs.P103.Graded.standardValue G → ringKrullDim C = 0 →
      ∀ (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
        RationalPresentation (hilbertFunction G U) b p e →
        (e = 0 ∨ p.eval 1 ≠ 0) → e = 0

/-- Both directions of the exponent-zero boundary for faithful modules. -/
def exponentZeroType : Prop :=
  ∀ (k : Type u) {C : Type v} {M : Type w}
    [Field k] [Infinite k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Nontrivial M] [FaithfulSMul C M]
    [Module.Finite C M] (G : NonnegativeGrading C) (U : ModuleGrading G M),
    Connected k G → Specs.P103.Graded.standardValue G →
      ∀ (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
        RationalPresentation (hilbertFunction G U) b p e →
        (e = 0 ∨ p.eval 1 ≠ 0) → (e = 0 ↔ ringKrullDim C = 0)

end Specs.P103.HilbertNormalizedGrowth
