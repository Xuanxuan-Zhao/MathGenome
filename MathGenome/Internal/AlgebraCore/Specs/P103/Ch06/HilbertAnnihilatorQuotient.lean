import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.LinearGradedNormalization
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import Mathlib.Algebra.Module.Torsion.Basic

/-! The graded annihilator reduction in the proof of Theorem 6.10,
`paper.tex:1156`. The quotient action is Mathlib's descended action on the
original additive group, not an assumed faithful representation. -/
namespace P103.HilbertAnnihilatorQuotient
open P103.Graded P103.Specs.Ch06.LinearGradedNormalization
universe u v w

/-- The structural-field vector space on an actual homogeneous piece. -/
def fieldComponent (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Algebra k A] [AddCommGroup M]
    [Module A M] [Module k M] [IsScalarTower k A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G) (j : ℤ) : Submodule k M where
  __ := U.piece j
  smul_mem' a m hm := by
    rw [← IsScalarTower.algebraMap_smul A a m]
    have ha := (hzero (algebraMap k A a)).mpr ⟨a, rfl⟩
    simpa using (SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) ha hm)

end P103.HilbertAnnihilatorQuotient

namespace Specs.P103.HilbertAnnihilatorQuotient
open _root_.P103.Graded _root_.P103.HilbertSerreLength
open _root_.P103.Specs.Ch06.LinearGradedNormalization
open _root_.P103.Specs.Ch06.DimensionConventions
open _root_.P103.HilbertAnnihilatorQuotient
universe u v w

def annihilatorHomogeneousType : Prop :=
  ∀ {A : Type v} {M : Type w} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M),
    ∀ a ∈ Module.annihilator A M, ∀ i : ℤ,
      (DirectSum.decompose G.piece a i : A) ∈ Module.annihilator A M

/-- Full reduction, including exact representative and piece formulas.
The integer-indexed coefficient equality uses the actual degree-zero rings.
No infinite-field, domain, or reducedness hypotheses occur. -/
def quotientType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Nontrivial M] [Module.Finite A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M),
    Connected k G → _root_.Specs.P103.Graded.standardValue G →
    let C := A ⧸ Module.annihilator A M
    letI : Module C M := Module.quotientAnnihilator (R := A) (M := M)
    Nontrivial C ∧ FaithfulSMul C M ∧ Module.Finite C M ∧ IsScalarTower k C M ∧
    (∀ a : A, ∀ m : M, Ideal.Quotient.mk (Module.annihilator A M) a • m = a • m) ∧
    ∃ (GC : NonnegativeGrading C) (UC : ModuleGrading GC M),
      Connected k GC ∧ _root_.Specs.P103.Graded.standardValue GC ∧
      (∀ j, GC.piece j = (G.piece j).map
        (Ideal.Quotient.mk (Module.annihilator A M)).toAddMonoidHom) ∧
      (∀ j, UC.piece j = U.piece j) ∧
      hilbertFunction GC UC = hilbertFunction G U ∧
      ringKrullDim C = moduleDimensionValue A M

/-- Comparison with actual field dimension, with ordinary finiteness of every
piece asserted independently of `finrank`. Applies also to the quotient. -/
def finiteComponentsType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite A M] (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G), _root_.Specs.P103.Graded.standardValue G →
    ∀ j : ℤ, Module.Finite k (fieldComponent k G U hzero j) ∧
      hilbertFunction G U j = (Module.finrank k (fieldComponent k G U hzero j) : ℤ)

end Specs.P103.HilbertAnnihilatorQuotient
