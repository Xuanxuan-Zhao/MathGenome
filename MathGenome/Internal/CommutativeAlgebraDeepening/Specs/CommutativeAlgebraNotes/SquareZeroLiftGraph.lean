import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftDefinitions
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! The graph model for lifts with chosen polynomial generators. -/

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open Algebra.Extension

universe u v w t n l m

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  (p : Presentation e B σ) {c : e.CoefficientMap (B := B) N}

/-- A solution to the prescribed relation equation, with its full coefficient constraint. -/
def RelationMaps (c : e.CoefficientMap (B := B) N) :=
  {ρ : p.Conormal →ₗ[B] N // ∀ i : p.IP, ρ (p.toConormal i) = p.prescribed c i}

/-- A marked lift together with one element over each of the presented variables. -/
structure ChosenLift (c : e.CoefficientMap (B := B) N) where
  lift : Lift.{u,v,w,n,l} e c
  variableLifts : σ → lift.Ring
  overVariable : ∀ i, lift.map (variableLifts i) = p.map (MvPolynomial.X i)

namespace ChosenLift

variable {p}

/-- Isomorphisms of marked lifts carrying each chosen variable lift to its counterpart. -/
structure Iso (L : p.ChosenLift.{u,v,w,t,n,l} c) (M : p.ChosenLift.{u,v,w,t,n,m} c)
    extends L.lift.Iso M.lift where
  mapVariables : ∀ i, equiv (L.variableLifts i) = M.variableLifts i

def Iso.symm {L : p.ChosenLift.{u,v,w,t,n,l} c} {M : p.ChosenLift.{u,v,w,t,n,m} c}
    (f : L.Iso M) : M.Iso L :=
  ⟨f.toIso.symm, fun i => by rw [← f.mapVariables i]; exact f.equiv.symm_apply_apply _⟩

def Iso.trans {L : p.ChosenLift.{u,v,w,t,n,l} c} {M : p.ChosenLift.{u,v,w,t,n,m} c}
    {W : p.ChosenLift c} (f : L.Iso M) (g : M.Iso W) : L.Iso W :=
  ⟨f.toIso.trans g.toIso, fun i => by
    change g.equiv (f.equiv (L.variableLifts i)) = W.variableLifts i
    rw [f.mapVariables, g.mapVariables]⟩

def isoSetoid : Setoid (p.ChosenLift.{u,v,w,t,n,l} c) where
  r L M := Nonempty (L.Iso M)
  iseqv := ⟨fun L => ⟨⟨Lift.Iso.refl L.lift, fun _ => rfl⟩⟩,
    fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- The isomorphism classes of marked lifts with specified lifts of all variables. -/
def Classes (p : Presentation e B σ) (c : e.CoefficientMap (B := B) N) :=
  Quotient (isoSetoid (p := p) (c := c) : Setoid (p.ChosenLift.{u,v,w,t,n,l} c))

/-- Evaluation in a lift on the specified elements. -/
def evaluate (L : p.ChosenLift.{u,v,w,t,n,l} c) : p.extension.Ring →+* L.lift.Ring :=
  MvPolynomial.eval₂Hom (algebraMap A' L.lift.Ring) L.variableLifts

variable (L : p.ChosenLift.{u,v,w,t,n,l} c)

@[simp] theorem map_evaluate (x : p.extension.Ring) :
    L.lift.map (L.evaluate x) = p.ringHom x := by
  have h : L.lift.map.comp L.evaluate = p.map := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change L.lift.map (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) = _
      rw [MvPolynomial.eval₂Hom_C, L.lift.over, p.over]
    · intro i
      change L.lift.map (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.eval₂Hom_X']
      exact L.overVariable i
  exact DFunLike.congr_fun h x

/-- Evaluation of a relation in the square-zero kernel of the lift. -/
def evaluateKer (q : p.Q) : L.lift.ker :=
  ⟨L.evaluate q, (L.map_evaluate q).trans q.property⟩

/-- The relation map realized by evaluation in a chosen lift. -/
def Realizes (ρ : p.RelationMaps c) : Prop :=
  ∀ q : p.Q, ρ.val (Cotangent.mk q) = L.lift.marking (L.evaluateKer q)

end ChosenLift

/-- The canonical square-zero quotient of the polynomial ring. -/
abbrev InfRing := p.extension.infinitesimal.Ring

/-- Projection from the polynomial ring to its square-zero quotient. -/
abbrev infMk : p.extension.Ring →+* p.InfRing := p.extension.toInfinitesimal.toRingHom

/-- The presentation onto B after killing the square of the relation ideal. -/
abbrev infMap : p.InfRing →+* B := algebraMap p.InfRing B

instance infTargetModule : Module p.InfRing N := Module.compHom N p.infMap

instance infTargetOppositeModule : Module p.InfRingᵐᵒᵖ N :=
  Module.compHom N (p.infMap.comp (RingEquiv.toOpposite p.InfRing).symm.toRingHom)

instance infTargetCentralScalar : IsCentralScalar p.InfRing N := ⟨fun _ _ => rfl⟩

instance infTargetSMulCommClass : SMulCommClass p.InfRing p.InfRingᵐᵒᵖ N :=
  ⟨fun r s x => smul_comm (p.infMap r) (p.infMap s.unop) x⟩

/-- The trivial extension with the action on N pulled back from B. -/
abbrev Trivial (N : Type n) := TrivSqZeroExt p.InfRing N

/-- The reduction of the trivial extension to B. -/
def trivialMap : p.Trivial N →+* B :=
  p.infMap.comp (TrivSqZeroExt.fstHom p.InfRing p.InfRing N).toRingHom

/-- The map from P' into the trivial extension, through P'/Q². -/
def trivialMk : p.extension.Ring →+* p.Trivial N :=
  (TrivSqZeroExt.inlHom p.InfRing N).comp p.infMk

/-- Membership in the graph of the negative of the relation map. -/
def GraphMember (ρ : p.Conormal →ₗ[B] N) (x : p.Trivial N) : Prop :=
  ∃ q : p.Q, x.fst = p.infMk q ∧ x.snd = -ρ (Cotangent.mk q)

/-- The canonical conormal map induced by reduction modulo the coefficient ideal. -/
def conormalReduction : p.Conormal →ₗ[B] p.BarConormal :=
  Cotangent.map p.reductionHom

end CommutativeAlgebraNotes.SquareZeroLift.Presentation

namespace Specs.CommutativeAlgebraNotes.SquareZeroLiftGraph

open Algebra.Extension TrivSqZeroExt CommutativeAlgebraNotes.SquareZeroLift
open CommutativeAlgebraNotes.SquareZeroLift.Presentation

universe u v w t n l m

/-- Exactness and the isomorphism induced by reduction on the cokernel. -/
def conormalCokernelType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    {e : BaseExtension A' A} (p : Presentation e B σ),
      Function.Surjective p.conormalReduction ∧ LinearMap.ker p.conormalReduction = p.K ∧
        ∃ F : (p.Conormal ⧸ p.K) ≃ₗ[B] p.BarConormal,
          ∀ x : p.Conormal, F (p.K.mkQ x) = p.conormalReduction x

/-- The evaluation on relations in every marked lift is well defined and satisfies the constraint. -/
def evaluationType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {p : Presentation e B σ} {c : e.CoefficientMap (B := B) N}
    (L : p.ChosenLift.{u,v,w,t,n,l} c), ∃! ρ : p.RelationMaps c, L.Realizes ρ

/-- The quotient by the graph carries the prescribed lift, marking and chosen variables. -/
def graphConstructionType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {p : Presentation e B σ} {c : e.CoefficientMap (B := B) N}
    (ρ : p.RelationMaps c),
    ∃ (G : Ideal (p.Trivial N)) (L : p.ChosenLift.{u,v,w,t,n,max u t n} c)
      (F : (p.Trivial N ⧸ G) ≃+* L.lift.Ring),
      (∀ x, x ∈ G ↔ p.GraphMember ρ.val x) ∧
      (∀ a : A', F (Ideal.Quotient.mk G (p.trivialMk (p.polynomialEquiv (MvPolynomial.C a)))) =
        algebraMap A' L.lift.Ring a) ∧
      (∀ i : σ, F (Ideal.Quotient.mk G (p.trivialMk (p.polynomialEquiv (MvPolynomial.X i)))) =
        L.variableLifts i) ∧ L.Realizes ρ ∧
      ∃ hMap : ∀ x : p.Trivial N, L.lift.map (F (Ideal.Quotient.mk G x)) = p.trivialMap x,
        ∀ (x : p.Trivial N) (q : p.Q) (hq : x.fst = p.infMk q),
          L.lift.marking ⟨F (Ideal.Quotient.mk G x), by
            change L.lift.map (F (Ideal.Quotient.mk G x)) = 0
            rw [hMap, show p.trivialMap x = p.infMap x.fst from rfl, hq]
            exact q.property⟩ = ρ.val (Cotangent.mk q) + x.snd

/-- Evaluation gives precisely the graph as kernel of the surjection from the trivial extension. -/
def comparisonType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {p : Presentation e B σ} {c : e.CoefficientMap (B := B) N}
    (L : p.ChosenLift.{u,v,w,t,n,l} c) (ρ : p.RelationMaps c), L.Realizes ρ →
    ∃ f : p.Trivial N →+* L.lift.Ring, Function.Surjective f ∧
      (∀ r : p.extension.Ring, f (p.trivialMk r) = L.evaluate r) ∧
      (∀ a : N, f (inr a) = (L.lift.marking.symm a).val) ∧
      (∀ x : p.Trivial N, L.lift.map (f x) = p.trivialMap x) ∧
      (∀ x : p.Trivial N, x ∈ RingHom.ker f ↔ p.GraphMember ρ.val x)

/-- The correspondence on classes sends the class of each lift to its evaluated relation map. -/
def correspondenceType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {p : Presentation e B σ} {c : e.CoefficientMap (B := B) N},
    ∃ E : ChosenLift.Classes.{u,v,w,t,n,max u t n} p c ≃ p.RelationMaps c,
      ∀ L : p.ChosenLift.{u,v,w,t,n,max u t n} c,
        L.Realizes (E (Quotient.mk (ChosenLift.isoSetoid (p := p)) L))

/-- Equality of evaluated relation maps characterizes the isomorphism relation in any universes. -/
def isomorphismType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {p : Presentation e B σ} {c : e.CoefficientMap (B := B) N}
    (L : p.ChosenLift.{u,v,w,t,n,l} c) (M : p.ChosenLift.{u,v,w,t,n,m} c)
    (ρ τ : p.RelationMaps c), L.Realizes ρ → M.Realizes τ →
      (Nonempty (L.Iso M) ↔ ρ = τ)

end Specs.CommutativeAlgebraNotes.SquareZeroLiftGraph
