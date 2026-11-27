import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.Algebra.Exact.Basic

namespace GaloisFormalization.GH.Model

universe u v₁ v₂ v₃

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Type v₁) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable (B : Type v₂) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable (C : Type v₃) [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]

/-- An equivariant short exact sequence of discrete continuous coefficients. -/
structure ShortExactCoefficients where
  i : A →+ B
  p : B →+ C
  i_equivariant : ∀ (g : G) (a : A), i (g • a) = g • i a
  p_equivariant : ∀ (g : G) (b : B), p (g • b) = g • p b
  i_injective : Function.Injective i
  exact : Function.Exact i p
  p_surjective : Function.Surjective p

variable {G A B C}

namespace ShortExactCoefficients

variable (S : ShortExactCoefficients G A B C)

abbrev cochainI (n : ℕ) :=
  continuousCochainMap (MonoidHom.id G) continuous_id S.i n

abbrev cochainP (n : ℕ) :=
  continuousCochainMap (MonoidHom.id G) continuous_id S.p n

abbrev cohomologyI (n : ℕ) :=
  continuousCohomologyMap (MonoidHom.id G) continuous_id S.i S.i_equivariant n

abbrev cohomologyP (n : ℕ) :=
  continuousCohomologyMap (MonoidHom.id G) continuous_id S.p S.p_equivariant n

abbrev ConnectingFamily :=
  ∀ n : ℕ, ContinuousH G C n →ₗ[ℤ] ContinuousH G A (n + 1)

/-- The lift-and-differentiate rule for any representative and any continuous lift.
The A-valued cochain over the differential is unique and is a cocycle. -/
def ConnectingFormula (δ : ConnectingFamily (G := G) (A := A) (C := C)) : Prop :=
  ∀ (n : ℕ) (c : continuousCocycles G C n) (b : continuousCochains G B n),
    S.cochainP n b = c.val →
    ∃ a : continuousCocycles G A (n + 1),
      S.cochainI (n + 1) a.val = continuousDifferential G B n b ∧
      δ n (continuousClass G C n c) = continuousClass G A (n + 1) a ∧
      ∀ a' : continuousCochains G A (n + 1),
        S.cochainI (n + 1) a' = continuousDifferential G B n b → a' = a.val

/-- Exactness at every term, including the first term after zero. -/
structure IsLongExact (δ : ConnectingFamily (G := G) (A := A) (C := C)) : Prop where
  cochain_lift : ∀ n : ℕ, Function.Surjective (S.cochainP n)
  initial : Function.Injective (S.cohomologyI 0)
  exact_middle : ∀ n : ℕ, Function.Exact (S.cohomologyI n) (S.cohomologyP n)
  exact_right : ∀ n : ℕ, Function.Exact (S.cohomologyP n) (δ n)
  exact_left : ∀ n : ℕ, Function.Exact (δ n) (S.cohomologyI (n + 1))
  connecting_formula : S.ConnectingFormula δ

end ShortExactCoefficients

end GaloisFormalization.GH.Model

namespace GaloisFormalization.GH.Specification

open Model

/-- GH05 for profinite groups. The discrete lifting argument in fact works for
any topological group, so no compactness or separation assumption is needed. -/
def ContinuousCohomologyLongExact.{u, v₁, v₂, v₃} : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type v₁} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A]
    {B : Type v₂} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [DistribMulAction G B] [ContinuousSMul G B]
    {C : Type v₃} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
      [DistribMulAction G C] [ContinuousSMul G C]
    (S : ShortExactCoefficients G A B C),
    ∃ δ, S.IsLongExact δ

end GaloisFormalization.GH.Specification
