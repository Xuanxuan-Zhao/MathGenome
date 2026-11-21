import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.CircleLift
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Connected.PathConnected

/-!
Independent statement of paper.tex, Lemma d13:21:collar.

The oriented Euclidean plane is represented by ℂ, regarded throughout as a
real vector space. Smoothness on ℝ/ℤ uses its canonical covering coordinates:
a map is C¹ precisely when its pullback by ℝ → ℝ/ℤ is C¹. The inverse collar
condition below likewise asks for C¹ real lifts locally in the target. Thus
no differentiability structure on the quotient is inferred from its topology.
-/
namespace Specs.D13Unified.Ch21.Collar

noncomputable section
open Set Filter
open scoped Topology

abbrev Circle := Specs.D13Unified.Ch15.CircleLift.Circle
abbrev q := Specs.D13Unified.Ch15.CircleLift.quotientMap

/-- The standard orientation: det(u,v)=u.re*v.im-u.im*v.re. -/
def det (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

def realLift (γ : Circle → ℂ) : ℝ → ℂ := fun t => γ (q t)

/-- C¹ in the canonical real covering coordinates of the circle. -/
def CircleC1 (γ : Circle → ℂ) : Prop := ContDiff ℝ 1 (realLift γ)

/-- No injectivity as a function on ℝ is required. -/
def RegularEmbeddedLoop (γ : Circle → ℂ) : Prop :=
  CircleC1 γ ∧ Function.Injective γ ∧ ∀ t : ℝ, deriv (realLift γ) t ≠ 0

def collarMap (γ v : Circle → ℂ) : Circle × ℝ → ℂ :=
  fun p => γ p.1 + p.2 • v p.1

def cylinder (a : ℝ) : Set (Circle × ℝ) := univ ×ˢ Ioo (-a) a

def positiveSide (γ v : Circle → ℂ) (a : ℝ) : Set ℂ :=
  collarMap γ v '' (univ ×ˢ Ioo 0 a)

def negativeSide (γ v : Circle → ℂ) (a : ℝ) : Set ℂ :=
  collarMap γ v '' (univ ×ˢ Ioo (-a) 0)

/-- C¹ inverse in covering coordinates, with a local representative of its
circle coordinate. The equality is on an actual neighborhood of each point. -/
def InverseC1 (e : OpenPartialHomeomorph (Circle × ℝ) ℂ) : Prop :=
  ∀ y ∈ e.target, ∃ g : ℂ → ℝ × ℝ,
    ContDiffAt ℝ 1 g y ∧
    ∀ᶠ z in 𝓝 y, (q (g z).1, (g z).2) = e.symm z

/-- Full collar conclusion, including the open image, trace, inverse regularity,
and both path-connected sides in the complement. -/
def IsCollar (γ v : Circle → ℂ) (a : ℝ) : Prop :=
  0 < a ∧ CircleC1 v ∧
  (∀ t : ℝ, 0 < det (deriv (realLift γ) t) (v (q t))) ∧
  ∃ e : OpenPartialHomeomorph (Circle × ℝ) ℂ,
    e.source = cylinder a ∧
    (∀ p, e p = collarMap γ v p) ∧
    range γ ⊆ e.target ∧
    ContDiff ℝ 1 (fun p : ℝ × ℝ => realLift γ p.1 + p.2 • realLift v p.1) ∧
    InverseC1 e ∧
    Disjoint (positiveSide γ v a) (negativeSide γ v a) ∧
    IsPathConnected (positiveSide γ v a) ∧
    IsPathConnected (negativeSide γ v a) ∧
    positiveSide γ v a ⊆ (range γ)ᶜ ∧
    negativeSide γ v a ⊆ (range γ)ᶜ

def collar_existsStatement : Prop :=
  ∀ γ : Circle → ℂ, RegularEmbeddedLoop γ →
    ∃ (v : Circle → ℂ) (a : ℝ), IsCollar γ v a

def lift_periodicStatement : Prop :=
  ∀ γ : Circle → ℂ, Function.Periodic (realLift γ) 1

def lift_eq_iffStatement : Prop :=
  ∀ (γ : Circle → ℂ), Function.Injective γ → ∀ t u : ℝ,
    realLift γ t = realLift γ u ↔ ∃ k : ℤ, t - u = (k : ℝ)

def lift_traceStatement : Prop :=
  ∀ γ : Circle → ℂ, range (realLift γ) = range γ

def regularity_bridgeStatement : Prop :=
  ∀ γ : Circle → ℂ, RegularEmbeddedLoop γ ↔
    ContDiff ℝ 1 (realLift γ) ∧
    (∀ t u : ℝ, realLift γ t = realLift γ u ↔ ∃ k : ℤ, t - u = (k : ℝ)) ∧
    ∀ t : ℝ, deriv (realLift γ) t ≠ 0

/-- Covering-coordinate smoothness agrees with smoothness in actual open
quotient charts, rather than just a condition on a chosen fundamental interval. -/
def coveringC1_bridgeStatement : Prop :=
  ∀ γ : Circle → ℂ, CircleC1 γ ↔ ∀ t : ℝ, ∃ U : Set ℝ,
    IsOpen U ∧ t ∈ U ∧ Topology.IsOpenEmbedding (U.domRestrict q) ∧
    ContDiffOn ℝ 1 (realLift γ) U

/-- A genuine construction from the curve hypotheses, not a certificate
assumed as an extra hypothesis of the collar theorem. -/
def transverse_existsStatement : Prop :=
  ∀ γ : Circle → ℂ, RegularEmbeddedLoop γ → ∃ v : Circle → ℂ,
    CircleC1 v ∧ ∀ t : ℝ, 0 < det (deriv (realLift γ) t) (v (q t))

end
end Specs.D13Unified.Ch21.Collar
