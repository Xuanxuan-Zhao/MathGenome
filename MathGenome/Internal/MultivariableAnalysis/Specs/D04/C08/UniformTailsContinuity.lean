import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.AbsoluteConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Cauchy

/-! Chapter 8, `d04:08:uniform-tails` and `d04:08:improper-continuity`.
All proper integrals are the shared, coordinatewise Darboux integrals of zero
extensions. The value `exhaustionIntegral` retains its chosen exhaustion,
including for conditional convergence. Uniform tail predicates use the usual
ε formulation with the parameter quantified after the truncation index.
The separate supremum characterization includes a uniform bound strictly below
ε, avoiding the real `sSup` convention for unbounded sets. Limits of parameters
are stated for a nontrivial filter eventually in B; this includes punctured
relative limits at accumulation points, as required by Chapter 1. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C08.UniformTailsContinuity.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model

def truncatedIntegral {n m k : ℕ} (K : ℕ → Set (E n))
    (f : E n → E m → E k) (j : ℕ) (p : E m) : E k :=
  vectorRegionIntegral (fun x : K j => f x p)

def tailIntegral {n m k : ℕ} (K : ℕ → Set (E n))
    (f : E n → E m → E k) (j l : ℕ) (p : E m) : E k :=
  vectorRegionIntegral (fun x : (K l \ K j : Set (E n)) => f x p)

def exhaustionIntegral {n k : ℕ} (K : ℕ → Set (E n)) (f : E n → E k) : E k :=
  limUnder atTop (fun j => vectorRegionIntegral (fun x : K j => f x))

def UniformImproperConverges {n m k : ℕ} (K : ℕ → Set (E n))
    (f : E n → E m → E k) (B : Set (E m)) : Prop :=
  ∃ F : E m → E k, TendstoUniformlyOn (truncatedIntegral K f) F atTop B

def UniformCauchyTails {n m k : ℕ} (K : ℕ → Set (E n))
    (f : E n → E m → E k) (B : Set (E m)) : Prop :=
  ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ l ≥ j, ∀ p ∈ B,
    ‖tailIntegral K f j l p‖ < ε

def UniformAbsoluteTails {n m k : ℕ} (K : ℕ → Set (E n))
    (f : E n → E m → E k) (B : Set (E m)) : Prop :=
  ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ l ≥ j, ∀ p ∈ B,
    regionIntegral (fun x : (K l \ K j : Set (E n)) => ‖f x p‖) < ε

/-- Each singular endpoint has its own tail; cancellation between endpoints is
not a convergence criterion. `r = 0` is permitted. -/
def EndpointwiseUniformTails {n m k r : ℕ} (K : Fin r → ℕ → Set (E n))
    (f : Fin r → E n → E m → E k) (B : Set (E m)) : Prop :=
  ∀ e, UniformCauchyTails (K e) (f e) B
/-- Absolute tails, separately at every singular endpoint. -/
def EndpointwiseUniformAbsoluteTails {n m k r : ℕ} (K : Fin r → ℕ → Set (E n))
    (f : Fin r → E n → E m → E k) (B : Set (E m)) : Prop :=
  ∀ e, UniformAbsoluteTails (K e) (f e) B
end Specs.D04.C08.UniformTailsContinuity.Model

namespace Specs.D04.C08.UniformTailsContinuity
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model
open Specs.D04.C06.AbsoluteConvergence.Model Model

abbrev truncatedIntegralType := {n m k : ℕ} → (ℕ → Set (E n)) → (E n → E m → E k) → ℕ → E m → E k
def truncatedIntegralValue : truncatedIntegralType := @Model.truncatedIntegral

abbrev tailIntegralType := {n m k : ℕ} → (ℕ → Set (E n)) → (E n → E m → E k) → ℕ → ℕ → E m → E k
def tailIntegralValue : tailIntegralType := @Model.tailIntegral

abbrev exhaustionIntegralType := {n k : ℕ} → (ℕ → Set (E n)) → (E n → E k) → E k
def exhaustionIntegralValue : exhaustionIntegralType := @Model.exhaustionIntegral

abbrev UniformImproperConvergesType := {n m k : ℕ} → (ℕ → Set (E n)) → (E n → E m → E k) → Set (E m) → Prop
def UniformImproperConvergesValue : UniformImproperConvergesType := @Model.UniformImproperConverges

abbrev UniformCauchyTailsType := {n m k : ℕ} → (ℕ → Set (E n)) → (E n → E m → E k) → Set (E m) → Prop
def UniformCauchyTailsValue : UniformCauchyTailsType := @Model.UniformCauchyTails

abbrev UniformAbsoluteTailsType := {n m k : ℕ} → (ℕ → Set (E n)) → (E n → E m → E k) → Set (E m) → Prop
def UniformAbsoluteTailsValue : UniformAbsoluteTailsType := @Model.UniformAbsoluteTails

abbrev EndpointwiseUniformTailsType := {n m k r : ℕ} → (Fin r → ℕ → Set (E n)) → (Fin r → E n → E m → E k) → Set (E m) → Prop
def EndpointwiseUniformTailsValue : EndpointwiseUniformTailsType := @Model.EndpointwiseUniformTails

abbrev EndpointwiseUniformAbsoluteTailsType := {n m k r : ℕ} →
  (Fin r → ℕ → Set (E n)) → (Fin r → E n → E m → E k) → Set (E m) → Prop
def EndpointwiseUniformAbsoluteTailsValue : EndpointwiseUniformAbsoluteTailsType :=
  @Model.EndpointwiseUniformAbsoluteTails

def tail_differenceType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k}, IsOpen Ω → RegularExhaustion Ω K →
  ∀ p, LocallyVectorRiemannIntegrable Ω (fun x => f x p) → ∀ j l, j ≤ l →
  tailIntegral K f j l p = truncatedIntegral K f l p - truncatedIntegral K f j p

def convergence_iff_cauchyType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)},
  IsOpen Ω → RegularExhaustion Ω K →
  (∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
  (UniformImproperConverges K f B ↔ UniformCauchyTails K f B)

/-- An exact supremum formulation: the parameter norms admit a common bound
strictly smaller than ε. This is equivalent to their supremum being < ε,
with supremum zero for the empty parameter set. -/
def supremum_tailsType : Prop := ∀ {n m k} (K : ℕ → Set (E n))
  (f : E n → E m → E k) (B : Set (E m)), UniformCauchyTails K f B ↔
  ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ l ≥ j,
    ∃ c : ℝ, 0 ≤ c ∧ c < ε ∧ ∀ p ∈ B, ‖tailIntegral K f j l p‖ ≤ c

def absolute_implies_signedType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)},
  IsOpen Ω → RegularExhaustion Ω K →
  (∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
  UniformAbsoluteTails K f B → UniformCauchyTails K f B

def uniform_limit_continuousType : Prop := ∀ {n m k}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)} {F : E m → E k},
  (∀ j, ContinuousOn (truncatedIntegral K f j) B) →
  TendstoUniformlyOn (truncatedIntegral K f) F atTop B → ContinuousOn F B

def uniform_converges_to_integralType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)},
  IsOpen Ω → RegularExhaustion Ω K →
  (∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
  UniformCauchyTails K f B →
  TendstoUniformlyOn (truncatedIntegral K f)
    (fun p => exhaustionIntegral K (fun x => f x p)) atTop B

def improper_integral_continuousType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)},
  IsOpen Ω → RegularExhaustion Ω K →
  (∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
  (∀ j, ContinuousOn (truncatedIntegral K f j) B) →
  UniformCauchyTails K f B →
  ContinuousOn (fun p => exhaustionIntegral K (fun x => f x p)) B

def improper_limitType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)}
  {g : E n → E k} (l : Filter (E m)), NeBot l → B ∈ l →
  IsOpen Ω → RegularExhaustion Ω K →
  (∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
  (∀ j, TendstoUniformlyOn (fun p x => f x p) g l (K j)) →
  UniformCauchyTails K f B →
  LocallyVectorRiemannIntegrable Ω g ∧
  (∀ j, VectorRegionIntegrable (fun x : K j => g x)) ∧
  HasVectorIntegralAlong g K (exhaustionIntegral K g) ∧
  (∀ p ∈ B, HasVectorIntegralAlong (fun x => f x p) K
    (exhaustionIntegral K (fun x => f x p))) ∧
  Tendsto (fun p => exhaustionIntegral K (fun x => f x p)) l
    (𝓝 (exhaustionIntegral K g))

def domination_absolute_tailsType : Prop := ∀ {n m k} {Ω : Set (E n)}
  {K : ℕ → Set (E n)} {f : E n → E m → E k} {B : Set (E m)},
  IsOpen Ω → RegularExhaustion Ω K →
  (∀ p ∈ B, LocallyVectorRiemannIntegrable Ω (fun x => f x p)) →
  ∀ {M : E n → ℝ}, AbsolutelyConvergent Ω M → (∀ x ∈ Ω, 0 ≤ M x) →
  (∀ p ∈ B, ∀ x ∈ Ω, ‖f x p‖ ≤ M x) → UniformAbsoluteTails K f B

def endpointwise_common_thresholdType : Prop := ∀ {n m k r}
  (K : Fin r → ℕ → Set (E n)) (f : Fin r → E n → E m → E k) (B : Set (E m)),
  EndpointwiseUniformTails K f B ↔
  ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ e, ∀ j ≥ j₀, ∀ l ≥ j, ∀ p ∈ B,
    ‖tailIntegral (K e) (f e) j l p‖ < ε

def endpointwise_absolute_common_thresholdType : Prop := ∀ {n m k r}
  (K : Fin r → ℕ → Set (E n)) (f : Fin r → E n → E m → E k) (B : Set (E m)),
  EndpointwiseUniformAbsoluteTails K f B ↔
  ∀ ε > (0 : ℝ), ∃ j₀ : ℕ, ∀ e, ∀ j ≥ j₀, ∀ l ≥ j, ∀ p ∈ B,
    regionIntegral (fun x : (K e l \ K e j : Set (E n)) => ‖f e x p‖) < ε

def scalar_tail_identityType : Prop := ∀ {n m} (K : ℕ → Set (E n))
  (v : E n → E m → ℝ) (j l : ℕ) (p : E m),
  ‖tailIntegral K (fun x p => WithLp.toLp 2 (fun _ : Fin 1 => v x p)) j l p‖ =
    |regionIntegral (fun x : (K l \ K j : Set (E n)) => v x p)|
end Specs.D04.C08.UniformTailsContinuity
