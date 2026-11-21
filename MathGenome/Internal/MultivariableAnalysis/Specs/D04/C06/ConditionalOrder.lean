import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ImproperExhaustions
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.SlicingAndMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The concrete improper Riemann example of paper.tex, d04:06:conditional-order.
Proper integrals use the shared Darboux construction. The scalar improper
limits below control each endpoint separately; symmetric truncations are also
recorded. No Lebesgue convention is used. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C06.ConditionalOrder.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model
open Specs.D04.C06.SlicingAndMoments.Model

def kernel (x y : ℝ) : ℝ := (x^2-y^2)/(x^2+y^2)^2
def integrand (z : E 2) : ℝ := kernel (z 0) (z 1)
def domain : Set (E 2) := {z | ∀ i, z i ∈ Ioo 0 1}
def properIntegral (g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  lowerIntegral (fun z : E 1 => g (z 0)) (intervalBox (min a b) (max a b) min_le_max)
def HasUnitImproperIntegral (g : ℝ → ℝ) (I : ℝ) : Prop :=
  (∀ a b : ℝ, 0 < a → ∀ (hab : a ≤ b), b < 1 →
    Integrable (fun z : E 1 => g (z 0)) (intervalBox a b hab)) ∧
  Tendsto (fun δ => properIntegral g δ (1-δ)) (𝓝[>] (0 : ℝ)) (𝓝 I) ∧
  ∃ L R : ℝ,
    Tendsto (fun δ => properIntegral g δ (1/2)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
    Tendsto (fun δ => properIntegral g (1/2) (1-δ)) (𝓝[>] (0 : ℝ)) (𝓝 R) ∧ I = L+R
def truncationBox (δ : ℝ) : Box 2 :=
  productBox (intervalBox δ (max δ (1-δ)) (le_max_left _ _))
    (intervalBox δ (max δ (1-δ)) (le_max_left _ _))
def truncation (δ : ℝ) : Set (E 2) := carrier (truncationBox δ)
/-- The lower artificial edge stays strictly above y=0, so this is a proper
compact Jordan triangle inside Ω whenever 0 < δ < 1/2. -/
def triangle (δ : ℝ) : Set (E 2) :=
  between (carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)))
    (fun _ => δ/4) (fun x => x 0/2)
def triangleMinorant (z : E 2) : ℝ := 12/(25*(z 0)^2)
end Specs.D04.C06.ConditionalOrder.Model

namespace Specs.D04.C06.ConditionalOrder
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model Model

def local_integrabilityType : Prop := LocallyRiemannIntegrable domain integrand

def inner_integralsType : Prop := ∀ x : ℝ, 0 < x →
  Integrable (fun z : E 1 => kernel x (z 0)) (intervalBox 0 1 (by norm_num)) ∧
  properIntegral (kernel x) 0 1 = 1/(1+x^2) ∧
  HasUnitImproperIntegral (kernel x) (1/(1+x^2)) ∧
  Integrable (fun z : E 1 => kernel (z 0) x) (intervalBox 0 1 (by norm_num)) ∧
  properIntegral (fun t => kernel t x) 0 1 = -1/(1+x^2) ∧
  HasUnitImproperIntegral (fun t => kernel t x) (-1/(1+x^2))

def iterated_integralsType : Prop :=
  HasUnitImproperIntegral (fun x => properIntegral (kernel x) 0 1) (Real.pi/4) ∧
  HasUnitImproperIntegral (fun y => properIntegral (fun x => kernel x y) 0 1) (-Real.pi/4)

def square_integralsType : Prop := ∀ δ : ℝ, 0 < δ → δ < 1/2 →
  Integrable integrand (truncationBox δ) ∧
  lowerIntegral integrand (truncationBox δ) = 0 ∧
  RegionIntegrable (fun z : truncation δ => integrand z) ∧
  regionIntegral (fun z : truncation δ => integrand z) = 0

def regular_exhaustionType : Prop := ∀ δ : ℕ → ℝ,
  (∀ j, 0 < δ j ∧ δ j < 1/2) → StrictAnti δ → Tendsto δ atTop (𝓝 0) →
  RegularExhaustion domain (fun j => truncation (δ j))

def quantitative_boundType : Prop := ∀ x y : ℝ, 0 < x → 0 < y → y ≤ x/2 →
  12/(25*x^2) ≤ kernel x y

/-- Both proper slicing and a logarithmic lower bound on the original
integrand's absolute integral are retained, including all artificial edges. -/
def trianglesType : Prop := ∀ δ : ℝ, 0 < δ → δ < 1/2 →
  CompactJordanSubset domain (triangle δ) ∧
  RegionIntegrable (fun z : triangle δ => |integrand z|) ∧
  RegionIntegrable (fun z : triangle δ => triangleMinorant z) ∧
  RegionIntegrable (fun x : carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)) =>
    (12/(25*(x.val 0)^2)) * (x.val 0/2-δ/4)) ∧
  regionIntegral (fun z : triangle δ => triangleMinorant z) =
    regionIntegral (fun x : carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)) =>
      (12/(25*(x.val 0)^2)) * (x.val 0/2-δ/4)) ∧
  (3/25)*(Real.log (1/2)-Real.log δ) ≤
    regionIntegral (fun z : triangle δ => |integrand z|)

def triangle_divergenceType : Prop :=
  Tendsto (fun δ => regionIntegral (fun z : triangle δ => |integrand z|))
    (𝓝[>] (0 : ℝ)) atTop

def not_absoluteType : Prop := absoluteMass domain integrand = ⊤ ∧
  ¬ AbsolutelyConvergent domain integrand

def conditional_limitType : Prop := ∀ δ : ℕ → ℝ,
  (∀ j, 0 < δ j ∧ δ j < 1/2) → StrictAnti δ → Tendsto δ atTop (𝓝 0) →
  ConditionalConvergesAlong domain integrand (fun j => truncation (δ j)) 0
end Specs.D04.C06.ConditionalOrder
