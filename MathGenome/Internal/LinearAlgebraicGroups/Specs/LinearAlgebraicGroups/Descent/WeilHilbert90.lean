import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LinearAlgebraicGroups.Specs.WeilHilbert90

open LinearAlgebraicGroups.Descent.NonabelianCohomology
open _root_.LinearAlgebraicGroups.WeilRestriction (extendedUnits)

universe u

/-- First Galois cohomology of the multiplicative Weil restriction is trivial. -/
def Vanishing : Prop :=
  ∀ (k E S : Type u) [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]
    [Module.Finite k E] [Algebra.IsSeparable k E] [IsSepClosure k S]
    (W : AffineAlgebraicGroup k),
    ((groupPointsFunctor k).obj W.val ≅ extendedUnits k E) →
    ∀ x : groupH1 k W.val.X S, x = groupBasepoint k W.val.X S

/-- First Galois cohomology of a finite product of multiplicative Weil restrictions
is trivial, including the empty product. -/
def ProductVanishing : Prop :=
  ∀ (k S : Type u) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (ι : Type u) [Finite ι] (E : ι → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra k (E i)] [∀ i, Module.Finite k (E i)]
    [∀ i, Algebra.IsSeparable k (E i)] (W : ι → AffineAlgebraicGroup k),
    (∀ i, (groupPointsFunctor k).obj (W i).val ≅ extendedUnits k (E i)) →
    ∀ (P : Fan (fun i => (W i).val)), IsLimit P →
      ∀ x : groupH1 k P.pt.X S, x = groupBasepoint k P.pt.X S

end LinearAlgebraicGroups.Specs.WeilHilbert90
