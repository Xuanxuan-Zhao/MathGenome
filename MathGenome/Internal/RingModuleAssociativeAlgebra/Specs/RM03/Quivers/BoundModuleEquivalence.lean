import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.ModuleEquivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.QuotientModules
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Relations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The path algebra equivalence for an arbitrary set of relations. -/

open CategoryTheory
open scoped ModuleCat

namespace RM03.QuiverBoundModuleEquivalenceSpec

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

abbrev A := PathAlgebraSpec.Carrier k Q
abbrev Rep := QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q

/-- Representations in which every chosen endpointwise relation evaluates to zero. -/
def satisfying (S : Set (QuiverRelationSpec.Bundled k Q)) :
    ObjectProperty (Rep (k := k) (Q := Q)) :=
  fun V => ∀ r ∈ S, QuiverRelationSpec.satisfies V r.2.2

/-- The generated two-sided ideal viewed as the ideal for the ring quotient. -/
noncomputable abbrev quotientIdeal [Ring (A (k := k) (Q := Q))]
    (S : Set (QuiverRelationSpec.Bundled k Q)) : Ideal (A (k := k) (Q := Q)) :=
  (TwoSidedIdeal.span (QuiverRelationSpec.toElement '' S)).asIdeal

def RelationOperator : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (V : Rep.{u, v, w, d} (k := k) (Q := Q)) {i j : Q}
    (r : QuiverRelationSpec.Coefficients k i j),
    PathOperatorsSpec.linearExtension V (QuiverRelationSpec.inclusion i j r) =
      (PathOperatorsSpec.inclusion V j).comp
        ((QuiverRelationSpec.evaluate V i j r).comp (PathOperatorsSpec.projection V i))

/-- Exactness at the middle representation, tested on the component linear maps. -/
def vertexExact {V W X : Rep (k := k) (Q := Q)} (f : V ⟶ W) (g : W ⟶ X) : Prop :=
  ∀ i : Q, (QuiverRepresentationSpec.component f i).range =
    (QuiverRepresentationSpec.component g i).ker

/-- The equivalence with the full subcategory, its comparison with the path algebra
equivalence on both functors, and the exactness criterion on either side. -/
def Construction : Prop :=
  ∀ (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q]
    (S : Set (QuiverRelationSpec.Bundled k Q)),
    ∃ (r : Ring (A (k := k) (Q := Q))) (a : @Algebra k A _ r.toSemiring),
      PathOperatorsSpec.IsPathAlgebra r a ∧
      letI := r
      letI := a
      let I := quotientIdeal S
      let R := ModuleCat.restrictScalars.{d} (Ideal.Quotient.mk I)
      ∃ (E : ModuleCat.{d} A ≌ Rep.{u, v, w, d} (k := k) (Q := Q))
        (h : ∀ M, E.functor.obj M = ModuleVerticesSpec.representation M)
        (J : ∀ V, E.inverse.obj V ≃ₗ[k] PathOperatorsSpec.Total V)
        (B : ModuleCat.{d} (A ⧸ I) ≌ (satisfying S).FullSubcategory),
        QuiverModuleEquivalenceSpec.InverseFormula E.inverse J ∧
        (∀ {M N} (f : M ⟶ N) (i : Q),
          QuiverRepresentationSpec.component
            (eqToHom (h M).symm ≫ E.functor.map f ≫ eqToHom (h N)) i =
            ModuleVerticesSpec.restrictMap f i) ∧
        (∀ V, satisfying S V ↔ Quivers.QuotientModules.annihilated I (E.inverse.obj V)) ∧
        B.functor.Additive ∧ B.functor.Linear k ∧ B.inverse.Additive ∧ B.inverse.Linear k ∧
        B.functor ⋙ (satisfying S).ι = R ⋙ E.functor ∧
        B.inverse ⋙ R = (satisfying S).ι ⋙ E.inverse ∧
        (∀ {L M N : ModuleCat.{d} (A ⧸ I)} (f : L ⟶ M) (g : M ⟶ N),
          (∃ hz : f ≫ g = 0, (ShortComplex.mk f g hz).Exact) ↔
            vertexExact (B.functor.map f).hom (B.functor.map g).hom) ∧
        (∀ {V W X : (satisfying.{u, v, w, d} S).FullSubcategory} (f : V ⟶ W) (g : W ⟶ X),
          (∃ hz : f ≫ g = 0, (ShortComplex.mk f g hz).Exact) ↔ vertexExact f.hom g.hom)

end RM03.QuiverBoundModuleEquivalenceSpec
