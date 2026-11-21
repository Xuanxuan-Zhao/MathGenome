import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWOrdered
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Sum.Order
import Mathlib.Algebra.Module.Injective

/-! HA-A09, the enveloping-algebra and restriction step of the proof.
Right modules are represented by left modules over the opposite ring.
The complementary subspace need not be a Lie subalgebra. -/
namespace AdvancedHomologicalAlgebra.IdealEnveloping
open _root_.Shared.Lie _root_.Shared.Lie.PBW
universe u v w w'
attribute [local instance 100] LieRing.ofAssociativeRing
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]

/-- The induced homomorphism between the actual tensor-algebra quotients. -/
noncomputable def inducedMap (h : LieIdeal k g) : U k h →ₐ[k] U k g :=
  UniversalEnvelopingAlgebra.lift k ((inclusion k g).comp h.incl)

/-- `op r` acts as right multiplication by the image of `r`. -/
noncomputable abbrev rightModule (h : LieIdeal k g) : Module (U k h)ᵐᵒᵖ (U k g) :=
  Module.compHom (U k g) (inducedMap k g h).op.toRingHom

/-- A basis obtained by placing the complement before the ideal. -/
noncomputable def adaptedBasis (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h) :
    Module.Basis (ι ⊕ₗ κ) k g :=
  (bc.prod bh).map (c.prodEquivOfIsCompl h.toSubmodule hc)

/-- Ordered products of the complementary letters, including the empty product. -/
noncomputable def complementaryMonomial {c : Submodule k g} {ι : Type w} [LE ι]
    (bc : Module.Basis ι k c) (l : OrderedWord ι) : U k g :=
  word k g (l.val.map (fun i => (bc i : g)))

end AdvancedHomologicalAlgebra.IdealEnveloping

namespace Specs.AdvancedHomologicalAlgebra.IdealEnveloping
open _root_.Shared.Lie _root_.Shared.Lie.PBW
open _root_.AdvancedHomologicalAlgebra.IdealEnveloping
universe u v w w' z

/-- No injectivity assumption is made on the induced enveloping map. -/
def inclusionExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g), Function.Injective (inducedMap k g h)

/-- For every adapted pair of bases, the specified complementary words are
an actual right-module basis. This is independent of all choices of bases. -/
def orderedRightBasisExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (c : Submodule k g) (_hc : IsCompl c h.toSubmodule)
    (ι : Type w) (κ : Type w') [LinearOrder ι] [LinearOrder κ]
    (bc : Module.Basis ι k c) (_bh : Module.Basis κ k h),
    letI := rightModule k g h
    ∃ B : Module.Basis (OrderedWord ι) (U k h)ᵐᵒᵖ (U k g),
      ∀ l, B l = complementaryMonomial k g bc l

/-- Existence for every ideal, without supplied complement or basis. -/
def rightFreeExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g), letI := rightModule k g h; Module.Free (U k h)ᵐᵒᵖ (U k g)

/-- Restriction of every injective unital left U(g)-module is injective.
`Module.Injective` includes the extension property for every module and
injective linear map in the carrier's universe. -/
def restrictionExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : Type (max u v z)) [AddCommGroup M] [Module (U k g) M]
    [Module.Injective (U k g) M],
    letI := Module.compHom M (inducedMap k g h).toRingHom
    Module.Injective (U k h) M
end Specs.AdvancedHomologicalAlgebra.IdealEnveloping
