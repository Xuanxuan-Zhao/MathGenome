import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperEnveloping
import Mathlib.LinearAlgebra.Basis.Basic

/-! The ordered super PBW words and their interpretation in the enveloping quotient. -/

namespace LieNotes.SuperRestricted.SuperPbwBasis

open SuperEnveloping.Construction

universe u v w

/-- Weakly increasing words with at most one occurrence of each odd letter. -/
abbrev OrderedWord {I : Type w} [LinearOrder I] (degree : I → ZMod 2) :=
  {l : List I // l.Pairwise (fun i j => i ≤ j ∧ (i = j → degree i ≠ 1))}

variable {k : Type u} {V : Type v} {I : Type w} [Field k] [AddCommGroup V] [Module k V]
  [NeZero (2 : k)]

/-- The ordered product of the images of the basis vectors in the actual quotient. -/
noncomputable def monomial (L : LieSuperalgebra k V) (b : Module.Basis I k V)
    (l : List I) : Enveloping L :=
  word (ι L) (l.map b)

/-- A choice of degrees certifying that every basis vector is homogeneous. -/
def Homogeneous (L : LieSuperalgebra k V) (b : Module.Basis I k V)
    (degree : I → ZMod 2) : Prop :=
  ∀ i, b i ∈ L.grading.piece (degree i)

end LieNotes.SuperRestricted.SuperPbwBasis

namespace Specs.LieNotes.SuperRestricted.SuperPbwBasis

open _root_.LieNotes.SuperRestricted
open _root_.LieNotes.SuperRestricted.SuperPbwBasis
open _root_.LieNotes.SuperRestricted.SuperEnveloping.Construction

universe u v w

/-- The specified products, including the empty product, form a basis. -/
def orderedBasisType : Prop :=
  ∀ {k : Type u} {V : Type v} {I : Type w} [Field k] [AddCommGroup V] [Module k V]
    [NeZero (2 : k)] [LinearOrder I] (L : LieSuperalgebra k V) (b : Module.Basis I k V)
    (degree : I → ZMod 2), Homogeneous L b degree →
      ∃ B : Module.Basis (OrderedWord degree) k (Enveloping L),
        ∀ l, B l = monomial L b l.val

/-- The filtration step consists of the span of the ordered products of the prescribed lengths. -/
def filtrationSpanType : Prop :=
  ∀ {k : Type u} {V : Type v} {I : Type w} [Field k] [AddCommGroup V] [Module k V]
    [NeZero (2 : k)] [LinearOrder I] (L : LieSuperalgebra k V) (b : Module.Basis I k V)
    (degree : I → ZMod 2), Homogeneous L b degree →
      ∀ n : ℤ, filtration L n = Submodule.span k
        (Set.range (fun l : {l : OrderedWord degree // (l.val.length : ℤ) ≤ n} =>
          monomial L b l.val.val))

end Specs.LieNotes.SuperRestricted.SuperPbwBasis
