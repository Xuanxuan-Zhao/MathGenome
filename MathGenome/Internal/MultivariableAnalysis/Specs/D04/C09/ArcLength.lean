import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.PathsLength
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.FtcFirst

/-! Independent specifications for paper.tex, `d04:09:arclength`.
The velocity on a closed piece is continuous and is a within-derivative at
both endpoints. Functions outside their displayed intervals are immaterial.
The integral is the shared proper scalar Riemann integral. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C09.ArcLength
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.SingleVariableAnalysis.Ch09.FtcFirst
open Specs.SingleVariableAnalysis.Ch08.Integral
open SingleVariableAnalysis.Riemann
namespace Model

/-- An inverse on two closed intervals, represented by ambient functions. -/
def IntervalInverse (s r : ℝ → ℝ) (a b c d : ℝ) : Prop :=
  MapsTo r (Icc c d) (Icc a b) ∧
  (∀ t ∈ Icc a b, r (s t) = t) ∧
  (∀ u ∈ Icc c d, s (r u) = u) ∧ ContinuousOn r (Icc c d)

/-- The complete regular conclusion, including continuous one-sided inverse
and reparametrized derivatives on the entire closed interval. -/
def RegularConclusion {n} (γ v : ℝ → E n) (s : ℝ → ℝ) (a b : ℝ) : Prop :=
  s a = 0 ∧ 0 < s b ∧ length γ a b = ENNReal.ofReal (s b) ∧ StrictMonoOn s (Icc a b) ∧
  BijOn s (Icc a b) (Icc 0 (s b)) ∧ ContinuousOn s (Icc a b) ∧
  (∀ t ∈ Icc a b, HasDerivWithinAt s ‖v t‖ (Icc a b) t) ∧
  ∃ r : ℝ → ℝ, IntervalInverse s r a b 0 (s b) ∧
    ContinuousOn (fun u => ‖v (r u)‖⁻¹) (Icc 0 (s b)) ∧
    (∀ u ∈ Icc 0 (s b),
      HasDerivWithinAt r ‖v (r u)‖⁻¹ (Icc 0 (s b)) u) ∧
    ContinuousOn (γ ∘ r) (Icc 0 (s b)) ∧
    C1Piece (γ ∘ r) (fun u => ‖v (r u)‖⁻¹ • v (r u)) 0 (s b) ∧
    ∀ u ∈ Icc 0 (s b), ‖‖v (r u)‖⁻¹ • v (r u)‖ = 1

/-- The cumulative lengths are the images of the original joins. Derivatives
and unit speed are asserted separately on each closed image piece, so no
equality between the two tangents at a join is imposed. -/
def PiecewiseConclusion {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ)
    (h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ)) : Prop :=
  ∃ s r : ℝ → ℝ, s a = 0 ∧ 0 < s b ∧ s b = piecewiseSpeedIntegral d h ∧
    length γ a b = ENNReal.ofReal (s b) ∧
    StrictMonoOn s (Icc a b) ∧ BijOn s (Icc a b) (Icc 0 (s b)) ∧
    ContinuousOn s (Icc a b) ∧ IntervalInverse s r a b 0 (s b) ∧
    ContinuousOn (γ ∘ r) (Icc 0 (s b)) ∧
    ∀ i, let l := d.partition.point i.castSucc
         let u := d.partition.point i.succ
      realAccumulationOn (fun t => ‖d.velocity i t‖) (fun t => s t - s l) l u ∧
      ContinuousOn (fun x => ‖d.velocity i (r x)‖⁻¹) (Icc (s l) (s u)) ∧
      (∀ x ∈ Icc (s l) (s u),
        HasDerivWithinAt r ‖d.velocity i (r x)‖⁻¹ (Icc (s l) (s u)) x) ∧
      C1Piece (γ ∘ r) (fun x => ‖d.velocity i (r x)‖⁻¹ • d.velocity i (r x))
        (s l) (s u) ∧
      ∀ x ∈ Icc (s l) (s u), ‖‖d.velocity i (r x)‖⁻¹ • d.velocity i (r x)‖ = 1
end Model
open Model

def regular_arc_lengthType : Prop := ∀ {n a b} (γ : IntervalPath n a b)
  (v : ℝ → E n), a < b → C1Piece γ v a b →
  (∀ t ∈ Icc a b, v t ≠ 0) →
  ∀ s : ℝ → ℝ, realAccumulationOn (fun t => ‖v t‖) s a b →
    RegularConclusion γ v s a b

def arc_length_accumulation_existsType : Prop := ∀ {n a b} (γ : IntervalPath n a b)
  (v : ℝ → E n), C1Piece γ v a b →
  ∃ s : ℝ → ℝ, realAccumulationOn (fun t => ‖v t‖) s a b

def piecewise_arc_lengthType : Prop := ∀ {n a b} (γ : IntervalPath n a b)
  (d : PiecewiseC1Data γ), a < b →
  (∀ i, ∀ t ∈ Icc (d.partition.point i.castSucc) (d.partition.point i.succ),
    d.velocity i t ≠ 0) →
  ∀ h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
    (d.partition.point i.castSucc) (d.partition.point i.succ), PiecewiseConclusion d h

/-- The source's existential notion of piecewise regularity, with the
integrability witnesses supplied in the conclusion. -/
def piecewise_regular_arc_lengthType : Prop := ∀ {n a b} (γ : IntervalPath n a b),
  a < b → PiecewiseRegular γ → ∃ (d : PiecewiseC1Data γ)
    (h : ∀ i, realIntegrableValue (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ)), PiecewiseConclusion d h

/-- The degenerate case asserts only the zero-length convention. -/
def arc_length_degenerateType : Prop := ∀ {n a} (γ : IntervalPath n a a),
  length γ a a = 0

end Specs.D04.C09.ArcLength
