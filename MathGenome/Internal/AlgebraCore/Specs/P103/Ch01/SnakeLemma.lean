import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.ModuleExactness

/-! Snake lemma, paper.tex 142–184. Rings may be noncommutative or zero.
A right R-module means a left Rᵐᵒᵖ-module; all statements below can be
instantiated over that ring, without changing any hypothesis. -/

namespace P103.Specs.Ch01.SnakeLemma

universe u v w
variable {R : Type u} [Ring R]

/-- The two rows, their vertical maps, and exactly the snake-lemma hypotheses. -/
structure Diagram (R : Type u) [Ring R] where
  A : Type v
  B : Type v
  C : Type v
  A' : Type v
  B' : Type v
  C' : Type v
  [addA : AddCommGroup A]
  [addB : AddCommGroup B]
  [addC : AddCommGroup C]
  [addA' : AddCommGroup A']
  [addB' : AddCommGroup B']
  [addC' : AddCommGroup C']
  [modA : Module R A]
  [modB : Module R B]
  [modC : Module R C]
  [modA' : Module R A']
  [modB' : Module R B']
  [modC' : Module R C']
  i : A →ₗ[R] B
  p : B →ₗ[R] C
  i' : A' →ₗ[R] B'
  p' : B' →ₗ[R] C'
  a : A →ₗ[R] A'
  b : B →ₗ[R] B'
  c : C →ₗ[R] C'
  left : b.comp i = i'.comp a
  right : c.comp p = p'.comp b
  top : Function.Exact i p
  bottom : Function.Exact i' p'
  onto : Function.Surjective p
  mono : Function.Injective i'

attribute [instance] Diagram.addA Diagram.addB Diagram.addC
  Diagram.addA' Diagram.addB' Diagram.addC' Diagram.modA Diagram.modB
  Diagram.modC Diagram.modA' Diagram.modB' Diagram.modC'

section InducedMaps
variable {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup M'] [AddCommGroup N'] [Module R M] [Module R N]
  [Module R M'] [Module R N']

/-- Restriction of a commutative square to kernels. -/
def kerMap (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (s : M →ₗ[R] M') (t : N →ₗ[R] N') (h : t.comp f = g.comp s) :
    LinearMap.ker f →ₗ[R] LinearMap.ker g :=
  (s.comp (LinearMap.ker f).subtype).codRestrict (LinearMap.ker g) (by
    intro x
    change g (s x) = 0
    have hx := DFunLike.congr_fun h (x : M)
    change t (f x) = g (s x) at hx
    rw [show f x = 0 from x.property, map_zero] at hx
    exact hx.symm)

/-- The quotient map induced by a commutative square on cokernels. -/
def cokerMap (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (s : M →ₗ[R] M') (t : N →ₗ[R] N') (h : t.comp f = g.comp s) :
    (N ⧸ LinearMap.range f) →ₗ[R] (N' ⧸ LinearMap.range g) :=
  (LinearMap.range f).mapQ (LinearMap.range g) t (by
    rintro _ ⟨x, rfl⟩
    exact ⟨s x, (DFunLike.congr_fun h x).symm⟩)
end InducedMaps

namespace Diagram
variable (D : Diagram.{u,v} R)

def kerFirst := kerMap D.a D.b D.i D.i' D.left.symm

def kerSecond := kerMap D.b D.c D.p D.p' D.right.symm

def cokerFirst := cokerMap D.a D.b D.i D.i' D.left.symm

def cokerSecond := cokerMap D.b D.c D.p D.p' D.right.symm

/-- Formula on every pair of lifts; in particular this asserts independence
of all choices of representatives. -/
def Connecting (δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a)) : Prop :=
  ∀ (z : LinearMap.ker D.c) (y : D.B) (x' : D.A'),
    D.p y = z.val → D.i' x' = D.b y → δ z = (LinearMap.range D.a).mkQ x'

/-- All four interior exactness assertions and the two conditional endpoints. -/
def SequenceExact (δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a)) : Prop :=
  Function.Exact D.kerFirst D.kerSecond ∧
  Function.Exact D.kerSecond δ ∧
  Function.Exact δ D.cokerFirst ∧
  Function.Exact D.cokerFirst D.cokerSecond ∧
  (Function.Injective D.i → Function.Injective D.kerFirst) ∧
  (Function.Surjective D.p' → Function.Surjective D.cokerSecond)

/-- A map of diagrams: all seven relevant squares commute. -/
structure Hom (E : Diagram.{u,w} R) where
  a : D.A →ₗ[R] E.A
  b : D.B →ₗ[R] E.B
  c : D.C →ₗ[R] E.C
  a' : D.A' →ₗ[R] E.A'
  b' : D.B' →ₗ[R] E.B'
  c' : D.C' →ₗ[R] E.C'
  topLeft : b.comp D.i = E.i.comp a
  topRight : c.comp D.p = E.p.comp b
  bottomLeft : b'.comp D.i' = E.i'.comp a'
  bottomRight : c'.comp D.p' = E.p'.comp b'
  verticalLeft : a'.comp D.a = E.a.comp a
  verticalMiddle : b'.comp D.b = E.b.comp b
  verticalRight : c'.comp D.c = E.c.comp c

end Diagram

def snakeType : Prop := ∀ (R : Type u) [Ring R] (D : Diagram.{u,v} R),
  ∃! δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a),
    D.Connecting δ ∧ D.SequenceExact δ

/-- The right-module specialization, with the scalar ring explicitly opposite. -/
def snakeRightType : Prop := ∀ (R : Type u) [Ring R] (D : Diagram.{u,v} Rᵐᵒᵖ),
  ∃! δ : LinearMap.ker D.c →ₗ[Rᵐᵒᵖ] (D.A' ⧸ LinearMap.range D.a),
    D.Connecting δ ∧ D.SequenceExact δ

/-- Naturality of the entire six-term sequence, including its connecting arrow. -/
def naturalityType : Prop := ∀ (R : Type u) [Ring R]
    (D : Diagram.{u,v} R) (E : Diagram.{u,w} R) (h : D.Hom E)
    (δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a))
    (ε : LinearMap.ker E.c →ₗ[R] (E.A' ⧸ LinearMap.range E.a)),
    D.Connecting δ → E.Connecting ε →
    (kerMap D.b E.b h.b h.b' h.verticalMiddle).comp D.kerFirst =
      E.kerFirst.comp (kerMap D.a E.a h.a h.a' h.verticalLeft) ∧
    (kerMap D.c E.c h.c h.c' h.verticalRight).comp D.kerSecond =
      E.kerSecond.comp (kerMap D.b E.b h.b h.b' h.verticalMiddle) ∧
    (cokerMap D.a E.a h.a h.a' h.verticalLeft).comp δ =
      ε.comp (kerMap D.c E.c h.c h.c' h.verticalRight) ∧
    (cokerMap D.b E.b h.b h.b' h.verticalMiddle).comp D.cokerFirst =
      E.cokerFirst.comp (cokerMap D.a E.a h.a h.a' h.verticalLeft) ∧
    (cokerMap D.c E.c h.c h.c' h.verticalRight).comp D.cokerSecond =
      E.cokerSecond.comp (cokerMap D.b E.b h.b h.b' h.verticalMiddle)

end P103.Specs.Ch01.SnakeLemma
