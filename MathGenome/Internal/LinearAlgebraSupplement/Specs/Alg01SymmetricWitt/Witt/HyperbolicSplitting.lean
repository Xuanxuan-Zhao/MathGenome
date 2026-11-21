import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.OrthogonalSplitting

namespace Specs.Alg01SymmetricWitt.Witt.HyperbolicSplitting

open Coordinates (hyperbolicPlane)
open OrthogonalSplitting (orthogonalComplement)

universe u v

/-- A specified isotropic vector is the first coordinate vector of a split hyperbolic plane. -/
def hyperbolicSplitting : Prop :=
  ∀ {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V) (_hq : q.Nondegenerate) (e : V),
    e ≠ 0 → q e = 0 →
    ∃ f : V, f ≠ 0 ∧ q f = 0 ∧ 2 * q.associated e f = 1 ∧
      let P := Submodule.span k ({e, f} : Set V)
      let W := orthogonalComplement q P
      (∃ i : (hyperbolicPlane k).IsometryEquiv (q.comp P.subtype),
        ∀ z : k × k, (i z : V) = z.1 • e + z.2 • f) ∧
      IsCompl P W ∧
      (∃ a : ((q.comp P.subtype).prod (q.comp W.subtype)).IsometryEquiv q,
        ∀ z : P × W, a z = (z.1 : V) + (z.2 : V)) ∧
      (q.comp W.subtype).Nondegenerate

end Specs.Alg01SymmetricWitt.Witt.HyperbolicSplitting
