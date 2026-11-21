import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerCounting

/-!
Independent specification of `K07.05.burnside` (paper.tex:911–924).
The orbit space is the upstream quotient by the orbit relation; fixed
points are written explicitly as the subtype satisfying `g • x = x`.
Only finiteness of G and X is assumed. In particular X may be empty,
and the action need not be faithful, free, or transitive.
-/

namespace Specs.D07.Ch05.Burnside

universe u v

/-- Burnside's counting identity in natural-number cardinalities. -/
def CountingIdentity : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] [Finite X],
    letI := Fintype.ofFinite G
    Nat.card G * Nat.card (MulAction.orbitRel.Quotient G X) =
      ∑ g : G, Nat.card {x : X // g • x = x}

/-- The divisor in the orbit average is positive, since a group has an identity. -/
def GroupOrderPositive : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], 0 < Nat.card G

/-- The fixed-point sum is exactly divisible by the group order. -/
def GroupOrderDividesFixedPointSum : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] [Finite X],
    letI := Fintype.ofFinite G
    Nat.card G ∣ ∑ g : G, Nat.card {x : X // g • x = x}

/-- The displayed average is an exact natural-number quotient. -/
def OrbitCountEqDiv : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] [Finite X],
    letI := Fintype.ofFinite G
    Nat.card (MulAction.orbitRel.Quotient G X) =
      (∑ g : G, Nat.card {x : X // g • x = x}) / Nat.card G

end Specs.D07.Ch05.Burnside
