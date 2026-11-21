import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.JacobsonRadical
import Mathlib.RingTheory.Artinian.Defs

/-!
Independent statements for the radical and semisimple-quotient assertions of
paper.tex, Theorem 3.3, lines 652–676, with the conventions at line 47.
The other conclusions of Theorem 3.3 are allocated to separate goals.

`IsArtinianRing R` means the descending chain condition on LEFT ideals.
`radical R` is the upstream intersection of maximal left ideals. It is
two-sided, so both its ideal powers and its quotient ring are available.
`IsNilpotent` means that some natural-number power is zero; zero for an
ideal is the bottom ideal. `IsSemisimpleModule Q Q` refers to the canonical
left regular action of the quotient ring Q on itself.

A right R-module is a left Rᵐᵒᵖ-module. Thus the right regular ring and
quotient are represented by Rᵐᵒᵖ and Rᵐᵒᵖ / J(Rᵐᵒᵖ). On representatives,
right multiplication by r is multiplication on the left by `op r`.
The explicit `op_mem_radicalType` identifies the radical used there with
the SAME radical J(R) under `op`. No commutativity, nontriviality,
Noetherianity, or finite-generation assumption is imposed on R.
-/

universe u

namespace P103.Specs.Ch03.ArtinianRadical

open P103.Specs.Ch03.JacobsonRadical (radical)

def nilpotentType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing R], IsNilpotent (radical R)

def quotient_semisimpleType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing R],
    IsSemisimpleModule (R ⧸ radical R) (R ⧸ radical R)

def op_mem_radicalType : Prop :=
  ∀ (R : Type u) [Ring R] (x : R),
    MulOpposite.op x ∈ radical Rᵐᵒᵖ ↔ x ∈ radical R

def right_nilpotentType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing Rᵐᵒᵖ],
    IsNilpotent (radical Rᵐᵒᵖ)

def right_quotient_semisimpleType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing Rᵐᵒᵖ],
    IsSemisimpleModule (Rᵐᵒᵖ ⧸ radical Rᵐᵒᵖ) (Rᵐᵒᵖ ⧸ radical Rᵐᵒᵖ)

end P103.Specs.Ch03.ArtinianRadical
