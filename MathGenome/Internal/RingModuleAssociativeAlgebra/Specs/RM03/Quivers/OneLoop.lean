import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.BoundModuleEquivalence
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! The quiver with one vertex and one loop, and its square-zero quotient. -/

open Polynomial
open scoped Polynomial

namespace RM03.OneLoopSpec

open Quivers.AlgebraRepresentations

instance quiver : Quiver Unit := ⟨fun _ _ => Unit⟩

def loop : Quiver.Hom () () := ()

def walk : ℕ → Quiver.Path () ()
  | 0 => .nil
  | n + 1 => (walk n).cons loop

def path (n : ℕ) : Path Unit := Path.ofPath (walk n)

def PathEnumeration : Prop :=
  path 0 = Path.vertex () ∧ path 1 = Path.arrow loop ∧
    (∀ n, (path n).length = n) ∧ (∀ p : Path Unit, path p.length = p)

universe u v w t

variable (k : Type u) [Field k]

abbrev A := PathAlgebraSpec.Carrier k Unit

noncomputable def squareRelation : QuiverRelationSpec.Bundled k Unit :=
  ⟨(), (), Finsupp.single (walk 2) 1⟩

noncomputable def relations : Set (QuiverRelationSpec.Bundled k Unit) :=
  {squareRelation k}

section
attribute [local instance] QuiverRelationSpec.nonUnitalNonAssocRing

def IdealEqualsSquare : Prop :=
  ∀ (k : Type u) [Field k],
    QuiverRelationSpec.generatedIdeal (relations k) =
      QuiverRelationSpec.idealPower (QuiverRelationSpec.arrowIdeal k Unit) 2 ∧
    QuiverRelationSpec.admissible (QuiverRelationSpec.generatedIdeal (relations k))
end

noncomputable abbrev xSquared : Ideal k[X] := Ideal.span {X ^ 2}

/-- The action is on the original vector space and the operator is the action of the loop. -/
def ModuleDescription {B : Type v} [Ring B] [Algebra k B]
    (x : B) : Prop :=
  (∀ (V : Type w) [AddCommGroup V] [Module k V],
    ∃ e : CompatibleModule k B V ≃ {T : Module.End k V // T ^ 2 = 0},
      (∀ (M : CompatibleModule k B V) (z : V), (e M).1 z = M.act x z) ∧
      (∀ (T : {T : Module.End k V // T ^ 2 = 0}) (c μ : k) (z : V),
        (e.symm T).act (algebraMap k B c + algebraMap k B μ * x) z =
          c • z + μ • T.1 z)) ∧
  (∀ (V : Type w) (W : Type t) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (M : CompatibleModule k B V)
    (N : CompatibleModule k B W) (f : V →ₗ[k] W),
      IsModuleLinear M N f ↔ ∀ z, f (M.act x z) = N.act x (f z))

/-- The polynomial isomorphism descends along the two specified quotient maps. -/
def Construction : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (r : Ring (A k)) (a : @Algebra k (A k) _ r.toSemiring),
      PathOperatorsSpec.IsPathAlgebra r a ∧
      letI := r
      letI := a
      let I := QuiverBoundModuleEquivalenceSpec.quotientIdeal (relations k)
      let x := Ideal.Quotient.mk I (PathAlgebraSpec.arrow k Unit loop)
      ∃ (e : k[X] ≃ₐ[k] A k) (q : (k[X] ⧸ xSquared k) ≃ₐ[k] (A k ⧸ I))
        (b : Module.Basis (Fin 2) k (A k ⧸ I)),
        (∀ n : ℕ, e (X ^ n) = PathAlgebraSpec.ofPath k Unit (path n)) ∧
        (∀ p : k[X], q (Ideal.Quotient.mk (xSquared k) p) = Ideal.Quotient.mk I (e p)) ∧
        b 0 = 1 ∧ b 1 = x ∧ ModuleDescription.{u, u, w, t} k x

end RM03.OneLoopSpec
