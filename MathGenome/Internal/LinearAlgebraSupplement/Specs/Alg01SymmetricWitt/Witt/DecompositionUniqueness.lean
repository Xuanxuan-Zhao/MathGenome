import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Coordinates

namespace Specs.Alg01SymmetricWitt.Witt.DecompositionUniqueness

open Specs.Alg01SymmetricWitt.Witt.Coordinates (hyperbolicSum)

universe u v w x

/-- In two Witt decompositions of the same space, the hyperbolic counts agree
and the anisotropic remainders are isometric. -/
def decompositionUnique : Prop :=
  ∀ {k : Type u} {V : Type v} {A : Type w} {A' : Type x}
    [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup A'] [Module k A'] [FiniteDimensional k A']
    (qV : QuadraticForm k V) (qA : QuadraticForm k A) (qA' : QuadraticForm k A')
    (r s : ℕ),
    qV.Nondegenerate → qA.Anisotropic → qA'.Anisotropic →
    qV.Equivalent ((hyperbolicSum k r).prod qA) →
    qV.Equivalent ((hyperbolicSum k s).prod qA') →
    r = s ∧ qA.Equivalent qA'

end Specs.Alg01SymmetricWitt.Witt.DecompositionUniqueness
