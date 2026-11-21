import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition

/-!
Absolute continuity of real and complex functions as in Chapter 12.
Functions on `[a,b]` are represented by ambient functions `ℝ → 𝕂`; only
their values on that interval are tested. No continuity, measurability or
bounded-variation hypothesis is part of the definition.
-/

namespace D11.Ch12

/-- Absolute continuity on a real domain, tested by finite families of
pairwise disjoint open intervals whose endpoints belong to that domain.
Disjoint open intervals may share endpoints.
-/
def AbsolutelyContinuousOn {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂) (s : Set ℝ) : Prop :=
  Specs.D11.Ch12.absolutelyContinuousOnValue F s

/-- Absolute continuity on the finite closed interval `[a,b]` (used for `a < b`
in the source). Values at both endpoints participate in the definition.
-/
def AbsolutelyContinuousOnInterval {𝕂 : Type*} [RCLike 𝕂]
    (F : ℝ → 𝕂) (a b : ℝ) : Prop :=
  AbsolutelyContinuousOn F (Set.Icc a b)

/-- Uniform absolute continuity on `ℝ`: a single positive `δ` works for
every finite disjoint family of bounded open intervals anywhere in `ℝ`.
-/
def AbsolutelyContinuous {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂) : Prop :=
  AbsolutelyContinuousOn F Set.univ

end D11.Ch12
