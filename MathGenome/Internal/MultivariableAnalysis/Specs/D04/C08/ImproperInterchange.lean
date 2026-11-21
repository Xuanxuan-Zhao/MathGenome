import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.UniformTailsContinuity

/-! `d04:08:improper-interchange`. The compact parameter box uses its
native Darboux integral. Truncations use the shared region integrals, and
improper values are tied to the specified regular exhaustion. Ambient
extensions of f outside A × Ω are ignored. All dimensions are allowed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology
namespace Specs.D04.C08.ImproperInterchange.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model

def leftBlock {p q : ℕ} (z : E (p + q)) : E p :=
  WithLp.toLp 2 (fun i => z (finSumFinEquiv (Sum.inl i)))
def rightBlock {p q : ℕ} (z : E (p + q)) : E q :=
  WithLp.toLp 2 (fun i => z (finSumFinEquiv (Sum.inr i)))

/-- Zero extension in the second block, on a product of containing boxes. -/
def productExtension {p q : ℕ} {V : Type} [Zero V]
    (S : Set (E q)) (f : E p → E q → V) (z : E (p + q)) : V :=
  if rightBlock z ∈ S then f (leftBlock z) (rightBlock z) else 0

/-- The same coordinate integral as `vectorIntegral`, displayed without a
proof argument; the theorems establish its integrability. -/
def boxIntegral {p k : ℕ} (A : Box p) (f : E p → E k) : E k :=
  WithLp.toLp 2 (fun i => lowerIntegral (fun x => f x i) A)
end Specs.D04.C08.ImproperInterchange.Model

namespace Specs.D04.C08.ImproperInterchange
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model
open Specs.D04.C06.SubdivisionUniformVector.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model
open Specs.D04.C06.AbsoluteConvergence.Model
open Specs.D04.C08.UniformTailsContinuity.Model Model

/-- Both ordinary iterated integrals, including product zero-extension
integrability, on each compact Jordan truncation. -/
def proper_fubiniType : Prop := ∀ {p q k} (A : Box p) {S : Set (E q)},
  IsCompact S → Jordan S → ∀ f : E p → E q → E k,
  ContinuousOn (Function.uncurry f) (carrier A ×ˢ S) →
  VectorIntegrable (productExtension S f) (productBox A (enclosingBox S)) ∧
  (∀ x ∈ carrier A, VectorRegionIntegrable (fun y : S => f x y)) ∧
  VectorIntegrable (fun x => vectorRegionIntegral (fun y : S => f x y)) A ∧
  VectorRegionIntegrable (fun y : S => boxIntegral A (fun x => f x y)) ∧
  boxIntegral A (fun x => vectorRegionIntegral (fun y : S => f x y)) =
    vectorRegionIntegral (fun y : S => boxIntegral A (fun x => f x y))

/-- Uniform convergence is the only improper convergence assumption.
The output supplies a continuous Riemann-integrable limit, pointwise improper
integrals, the proper equalities, and existence and value of the reverse
improper integral along K. No exhaustion independence is asserted. -/
def improper_interchangeType : Prop := ∀ {p q k} (A : Box p)
  {Ω : Set (E q)} {K : ℕ → Set (E q)} (f : E p → E q → E k),
  IsOpen Ω → RegularExhaustion Ω K →
  ContinuousOn (Function.uncurry f) (carrier A ×ˢ Ω) →
  UniformImproperConverges K (fun y x => f x y) (carrier A) →
  ∃ H : E p → E k,
    TendstoUniformlyOn (fun j x => vectorRegionIntegral (fun y : K j => f x y))
      H atTop (carrier A) ∧
    ContinuousOn H (carrier A) ∧ VectorIntegrable H A ∧
    (∀ x ∈ carrier A, HasVectorIntegralAlong (f x) K (H x) ∧
      H x = exhaustionIntegral K (f x)) ∧
    (∀ j, VectorIntegrable (productExtension (K j) f)
      (productBox A (enclosingBox (K j))) ∧
      VectorRegionIntegrable (fun y : K j => boxIntegral A (fun x => f x y)) ∧
      boxIntegral A (fun x => vectorRegionIntegral (fun y : K j => f x y)) =
        vectorRegionIntegral (fun y : K j => boxIntegral A (fun x => f x y))) ∧
    LocallyVectorRiemannIntegrable Ω (fun y => boxIntegral A (fun x => f x y)) ∧
    HasVectorIntegralAlong (fun y => boxIntegral A (fun x => f x y)) K
      (boxIntegral A H) ∧
    exhaustionIntegral K (fun y => boxIntegral A (fun x => f x y)) = boxIntegral A H

/-- The real-valued specialization uses real Riemann integrals throughout. -/
def scalar_interchangeType : Prop := ∀ {p q} (A : Box p)
  {Ω : Set (E q)} {K : ℕ → Set (E q)} (f : E p → E q → ℝ),
  IsOpen Ω → RegularExhaustion Ω K →
  ContinuousOn (Function.uncurry f) (carrier A ×ˢ Ω) →
  (∃ H : E p → ℝ, TendstoUniformlyOn
    (fun j x => regionIntegral (fun y : K j => f x y)) H atTop (carrier A)) →
  ∃ H : E p → ℝ,
    TendstoUniformlyOn (fun j x => regionIntegral (fun y : K j => f x y))
      H atTop (carrier A) ∧
    ContinuousOn H (carrier A) ∧ Integrable H A ∧
    (∀ x ∈ carrier A, HasIntegralAlong (f x) K (H x)) ∧
    (∀ j, Integrable (productExtension (K j) f) (productBox A (enclosingBox (K j))) ∧
      RegionIntegrable (fun y : K j => lowerIntegral (fun x => f x y) A)) ∧
    LocallyRiemannIntegrable Ω (fun y => lowerIntegral (fun x => f x y) A) ∧
    HasIntegralAlong (fun y => lowerIntegral (fun x => f x y) A) K (lowerIntegral H A)
end Specs.D04.C08.ImproperInterchange
