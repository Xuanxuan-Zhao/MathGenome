import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! Canonical models for paper.tex, §1.1. No connectedness or separation assumptions.
`Path.trans a b` traverses `a` first. Mathlib's `End` multiplication has the
opposite order, so the paper's fundamental group is its multiplicative opposite.
A homotopy is written with time as its first coordinate (the transpose of the
paper's `X × I` convention). -/
namespace P202Specs.Topology

open CategoryTheory
open scoped unitInterval

universe u v w

noncomputable section

abbrev SourcePath {X : Type u} [TopologicalSpace X] (x y : X) := Path x y
abbrev PathHomotopy {X : Type u} [TopologicalSpace X] {x y : X}
    (a b : SourcePath x y) := Path.Homotopy a b
abbrev PathClass {X : Type u} [TopologicalSpace X] (x y : X) :=
  Path.Homotopic.Quotient x y
abbrev PathGroupoid (X : Type u) [TopologicalSpace X] := FundamentalGroupoid X

abbrev Pi1 (X : Type u) [TopologicalSpace X] (x : X) :=
  (FundamentalGroup X x)ᵐᵒᵖ

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The underlying endpoint-fixed path class of an element of the paper's group. -/
def pathClass {x : X} (b : Pi1 X x) : PathClass x x := b.unop.asHom
/-- The inverse conversion, with no change of path or orientation. -/
def ofClass {x : X} (b : PathClass x x) : Pi1 X x := MulOpposite.op (.of b)
def loopClass {x : X} (a : SourcePath x x) : Pi1 X x :=
  ofClass (Path.Homotopic.Quotient.mk a)

/-- Transport a homomorphism through the explicit opposite convention. -/
def oppositeHom {A : Type*} {B : Type*} [Monoid A] [Monoid B]
    (f : A →* B) : Aᵐᵒᵖ →* Bᵐᵒᵖ where
  toFun a := MulOpposite.op (f a.unop)
  map_one' := congrArg MulOpposite.op f.map_one
  map_mul' a b := congrArg MulOpposite.op (f.map_mul b.unop a.unop)

/-- Transport an isomorphism through the same convention. -/
def oppositeEquiv {A : Type*} {B : Type*} [Mul A] [Mul B]
    (f : A ≃* B) : Aᵐᵒᵖ ≃* Bᵐᵒᵖ where
  toFun a := MulOpposite.op (f a.unop)
  invFun b := MulOpposite.op (f.symm b.unop)
  left_inv a := congrArg MulOpposite.op (f.symm_apply_apply a.unop)
  right_inv b := congrArg MulOpposite.op (f.apply_symm_apply b.unop)
  map_mul' a b := congrArg MulOpposite.op (f.map_mul b.unop a.unop)

/-- All continuous pointed maps, with arbitrary basepoints and no extra hypotheses. -/
structure PointedMap (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) where
  map : C(X, Y)
  point : map x = y

namespace PointedMap

def id (x : X) : PointedMap X X x x := ⟨ContinuousMap.id X, rfl⟩
def comp {x : X} {y : Y} {z : Z} (g : PointedMap Y Z y z)
    (f : PointedMap X Y x y) : PointedMap X Z x z :=
  ⟨g.map.comp f.map, (congrArg g.map f.point).trans g.point⟩

def induced {x : X} {y : Y} (f : PointedMap X Y x y) : Pi1 X x →* Pi1 Y y :=
  oppositeHom (FundamentalGroup.mapOfEq f.map f.point)

abbrev BasedHomotopy {x : X} {y : Y} (f g : PointedMap X Y x y) :=
  ContinuousMap.HomotopyRel f.map g.map {x}

end PointedMap

/-- A pointed homotopy equivalence includes a pointed inverse and both based homotopies. -/
structure PointedHomotopyEquivalence (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y) where
  forward : PointedMap X Y x y
  backward : PointedMap Y X y x
  left : (backward.comp forward).BasedHomotopy (.id x)
  right : (forward.comp backward).BasedHomotopy (.id y)

/-- Transpose a continuous square in the paper's coordinate order into a library homotopy. -/
def squareHomotopy (f g : C(X, Y)) (F : C(X × unitInterval, Y))
    (h0 : ∀ x, F (x, 0) = f x) (h1 : ∀ x, F (x, 1) = g x) : f.Homotopy g where
  toFun p := F (p.2, p.1)
  continuous_toFun := F.continuous.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left := h0
  map_one_left := h1

/-- This is the path `d(t) = F(x,t)` in the source. -/
def squareTrace (f g : C(X, Y)) (F : C(X × unitInterval, Y))
    (h0 : ∀ x, F (x, 0) = f x) (h1 : ∀ x, F (x, 1) = g x) (x : X) :
    SourcePath (f x) (g x) := (squareHomotopy f g F h0 h1).evalAt x

/-- The direction is contravariant in the basepoint path, as in the paper. -/
noncomputable def changeBasepoint {x y : X} (d : SourcePath x y) : Pi1 X y ≃* Pi1 X x :=
  oppositeEquiv (FundamentalGroup.fundamentalGroupMulEquivOfPath d).symm

/-! Independent full proposition types for the implementation. -/
namespace Expected

-- The concrete half-interval formula and reversal fix the source conventions.
def pathOperations : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x y z : X) (a : SourcePath x y)
    (b : SourcePath y z),
    (∀ t : unitInterval, a.symm t = a (unitInterval.symm t)) ∧
    (∀ t : unitInterval, (a.trans b) t =
      if h : (t : ℝ) ≤ 1 / 2 then
        a ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else b ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩)

def classEquality : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x y : X) (a b : SourcePath x y),
    Path.Homotopic.Quotient.mk a = Path.Homotopic.Quotient.mk b ↔
      Nonempty (PathHomotopy a b)

def groupoidLaws : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x y z w : X)
    (a : PathClass x y) (b : PathClass y z) (c : PathClass z w),
    (a.trans b).trans c = a.trans (b.trans c) ∧
    (Path.Homotopic.Quotient.refl x).trans a = a ∧
    a.trans (Path.Homotopic.Quotient.refl y) = a ∧
    a.trans a.symm = Path.Homotopic.Quotient.refl x ∧
    a.symm.trans a = Path.Homotopic.Quotient.refl y

def groupConvention : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x : X),
    (∀ a b : SourcePath x x, loopClass (a.trans b) = loopClass a * loopClass b) ∧
    loopClass (Path.refl x) = 1 ∧
    (∀ a : SourcePath x x, loopClass a.symm = (loopClass a)⁻¹) ∧
    Function.Bijective (pathClass : Pi1 X x → PathClass x x)

def inducedFormula : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f : PointedMap X Y x y) (a : SourcePath x x),
    f.induced (loopClass a) = loopClass ((a.map f.map.continuous).cast f.point.symm f.point.symm)

def functoriality : Prop :=
  (∀ (X : Type u) [TopologicalSpace X] (x : X),
    (PointedMap.id x).induced = MonoidHom.id (Pi1 X x)) ∧
  (∀ (X : Type u) (Y : Type v) (Z : Type w)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (x : X) (y : Y) (z : Z) (f : PointedMap X Y x y) (g : PointedMap Y Z y z),
    (g.comp f).induced = g.induced.comp f.induced)

def basedHomotopy : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f g : PointedMap X Y x y),
    Nonempty (f.BasedHomotopy g) → f.induced = g.induced

def pointedEquivalence : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (e : PointedHomotopyEquivalence X Y x y),
    ∃ E : Pi1 X x ≃* Pi1 Y y, (∀ a, E a = e.forward.induced a) ∧
      (∀ b, E.symm b = e.backward.induced b)

def basepointFormula : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x y : X) (d : SourcePath x y) (b : Pi1 X y),
    pathClass (changeBasepoint d b) =
      ((Path.Homotopic.Quotient.mk d).trans (pathClass b)).trans
        (Path.Homotopic.Quotient.mk d.symm)

def basepointInner : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x y : X) (d d' : SourcePath x y) (b : Pi1 X y),
    changeBasepoint d' b =
      loopClass (d'.trans d.symm) * changeBasepoint d b * (loopClass (d'.trans d.symm))⁻¹

def unbasedHomotopy : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (F : f.Homotopy g) (x : X) (a : SourcePath x x),
    loopClass (a.map f.continuous) =
      changeBasepoint (F.evalAt x) (loopClass (a.map g.continuous))

/-- The unbased formula with the original square and the explicit concatenated loop. -/
def unbasedSquare : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (F : C(X × unitInterval, Y))
    (h0 : ∀ x, F (x, 0) = f x) (h1 : ∀ x, F (x, 1) = g x)
    (x : X) (a : SourcePath x x),
    loopClass (a.map f.continuous) =
      loopClass (((squareTrace f g F h0 h1 x).trans (a.map g.continuous)).trans
        (squareTrace f g F h0 h1 x).symm)

end Expected
end
end P202Specs.Topology
