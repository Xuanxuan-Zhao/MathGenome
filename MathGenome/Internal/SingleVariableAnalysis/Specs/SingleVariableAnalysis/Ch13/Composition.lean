import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Recentering
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic

/-!
Independent specifications for K03.13.composition (paper.tex:1432–1446).
The centers remain real. Complex inner values need not be real. Ordered
numerical sums are the upstream predicates; summability is used only for
absolute majorants. The finite indices l encode the ordered tuple
(l 0,...,l (m-1)), whose entries are positive and whose sum is k.
The empty tuple supplies c₀₀=1. The local radius is produced existentially.
-/
noncomputable section
open scoped BigOperators ENNReal Topology
namespace Specs.SingleVariableAnalysis.Ch13.Composition

def positivePartValue {K : Type*} [Zero K] (b : ℕ → K) (j : ℕ) : K :=
  if j = 0 then 0 else b j

def powerCoefficientValue {K : Type*} [CommSemiring K] (b : ℕ → K) (m k : ℕ) : K :=
  PowerSeries.coeff k ((PowerSeries.mk (positivePartValue b)) ^ m)

def coefficientValue {K : Type*} [CommSemiring K] (A b : ℕ → K) (k : ℕ) : K :=
  ∑ m ∈ Finset.range (k+1), A m * powerCoefficientValue b m k

def majorantValue {K : Type*} [SeminormedAddCommGroup K] (b : ℕ → K) (r : ℝ) : ℝ :=
  ∑' j, ‖positivePartValue b j‖ * r^j

/-- The full binomial recentering coefficient, also at nonreal values. -/
def recenteredValue {K : Type*} [RCLike K] (a : ℕ → K) (w : K) (k : ℕ) : K :=
  ∑' n, (n.choose k : K) * a n * w^(n-k)

def positivePartType := {K : Type*} → [Zero K] → (ℕ → K) → ℕ → K
def powerCoefficientType := {K : Type*} → [CommSemiring K] → (ℕ → K) → ℕ → ℕ → K
def coefficientType := {K : Type*} → [CommSemiring K] → (ℕ → K) → (ℕ → K) → ℕ → K
def majorantType := {K : Type*} → [SeminormedAddCommGroup K] → (ℕ → K) → ℝ → ℝ

def coefficient_formulaSpec : Prop :=
  ∀ {K : Type*} [CommSemiring K] (A b : ℕ → K) (k : ℕ),
    coefficientValue A b k = ∑ m ∈ Finset.range (k+1), A m *
      ∑ l ∈ (Finset.finsuppAntidiag (Finset.range m) k).filter
        (fun l => ∀ i ∈ Finset.range m, 0 < l i), ∏ i ∈ Finset.range m, b (l i)

def powerCoefficient_formulaSpec : Prop :=
  ∀ {K : Type*} [CommSemiring K] (b : ℕ → K) (m k : ℕ),
    powerCoefficientValue b m k =
      ∑ l ∈ (Finset.finsuppAntidiag (Finset.range m) k).filter
        (fun l => ∀ i ∈ Finset.range m, 0 < l i), ∏ i ∈ Finset.range m, b (l i)

def powerCoefficient_belowSpec : Prop :=
  ∀ {K : Type*} [CommSemiring K] (b : ℕ → K)
    (m k : ℕ) (hk : k < m),
    powerCoefficientValue b m k = 0

def majorant_leSpec : Prop :=
  ∀ {K : Type*} [RCLike K] (b : ℕ → K) {s r : ℝ}
    (hs : 0 < s) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hb : Summable (fun j => ‖b j‖ * s^j)),
    majorantValue b r ≤ (r/s) * majorantValue b s

def exists_small_majorantSpec : Prop :=
  ∀ {K : Type*} [RCLike K] (b : ℕ → K) {s ε : ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hb : Summable (fun j => ‖b j‖ * s^j)),
    ∃ r : ℝ, 0 < r ∧ r ≤ s ∧ majorantValue b r < ε

def double_majorantSpec : Prop :=
  ∀ {K : Type*} [RCLike K] (A b : ℕ → K) {r : ℝ}
    (hr : 0 ≤ r) (hb : Summable (fun j => ‖positivePartValue b j‖ * r^j))
    (hA : Summable (fun m => ‖A m‖ * majorantValue b r ^ m)),
    Summable (fun p : ℕ × ℕ => ‖A p.1‖ *
      powerCoefficientValue (fun j => ‖b j‖) p.1 p.2 * r^p.2) ∧
    (∑' p : ℕ × ℕ, ‖A p.1‖ *
      powerCoefficientValue (fun j => ‖b j‖) p.1 p.2 * r^p.2) =
      ∑' m, ‖A m‖ * majorantValue b r ^ m

def local_composeSpec : Prop :=
  ∀ {K : Type*} [RCLike K] (a b : ℕ → K) (w : K)
    (s t : ℝ) (hs : 0 < s) (hw : ‖w‖ < t)
    (hb : Summable (fun j => ‖b j‖ * s^j))
    (ha : Summable (fun n => ‖a n‖ * t^n)),
    let A := recenteredValue a w
    ∃ r : ℝ, 0 < r ∧ r ≤ s ∧ ‖w‖ + majorantValue b r < t ∧
      Summable (fun m => ‖A m‖ * majorantValue b r ^ m) ∧
      Summable (fun k => ‖coefficientValue A b k‖ * r^k) ∧
      ∀ h : K, ‖h‖ ≤ r → ∃ v S : K,
        ‖v‖ ≤ majorantValue b r ∧ HasSum (fun j => b j * h^j) (b 0 + v) ∧
        HasSum (fun n => a n * (w+v)^n) S ∧
        HasSum (fun k => coefficientValue A b k * h^k) S ∧
        Summable (fun k => ‖coefficientValue A b k * h^k‖)

def real_compositionSpec : Prop :=
  ∀ (a b : ℕ → ℝ) (c d : ℝ)
    (hb : 0 < PowerSeries.realPowerSeriesRadiusValue b)
    (ha : ENNReal.ofReal |b 0-d| < PowerSeries.realPowerSeriesRadiusValue a),
    let A := Recentering.realRecenteredCoefficientValue a d (b 0)
    let C := coefficientValue A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < PowerSeries.realPowerSeriesRadiusValue b ∧
      ENNReal.ofReal r ≤ PowerSeries.realPowerSeriesRadiusValue C ∧
      Summable (fun m => |A m| * majorantValue b r ^ m) ∧
      Summable (fun k => |C k| * r^k) ∧
      ∀ h : ℝ, |h| ≤ r → ∃ G S : ℝ,
        ENNReal.ofReal |G-d| < PowerSeries.realPowerSeriesRadiusValue a ∧ PowerSeries.RealPowerSeriesHasSumValue b c (c+h) G ∧
        PowerSeries.RealPowerSeriesHasSumValue a d G S ∧
        PowerSeries.RealPowerSeriesHasSumValue C c (c+h) S ∧
        PowerSeries.RealPowerSeriesAbsolutelyConvergesValue C c (c+h)

def complex_compositionSpec : Prop :=
  ∀ (a b : ℕ → ℂ) (c d : ℝ)
    (hb : 0 < PowerSeries.complexPowerSeriesRadiusValue b)
    (ha : ENNReal.ofReal ‖b 0-(d : ℂ)‖ < PowerSeries.complexPowerSeriesRadiusValue a),
    let A := recenteredValue a (b 0-(d : ℂ))
    let C := coefficientValue A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < PowerSeries.complexPowerSeriesRadiusValue b ∧
      ENNReal.ofReal r ≤ PowerSeries.complexPowerSeriesRadiusValue C ∧
      Summable (fun m => ‖A m‖ * majorantValue b r ^ m) ∧
      Summable (fun k => ‖C k‖ * r^k) ∧
      ∀ h : ℂ, ‖h‖ ≤ r → ∃ G S : ℂ,
        ENNReal.ofReal ‖G-(d : ℂ)‖ < PowerSeries.complexPowerSeriesRadiusValue a ∧ PowerSeries.ComplexPowerSeriesHasSumValue b c ((c : ℂ)+h) G ∧
        PowerSeries.ComplexPowerSeriesHasSumValue a d G S ∧
        PowerSeries.ComplexPowerSeriesHasSumValue C c ((c : ℂ)+h) S ∧
        PowerSeries.ComplexPowerSeriesAbsolutelyConvergesValue C c ((c : ℂ)+h)

def real_composition_functionsSpec : Prop :=
  ∀ (a b : ℕ → ℝ) (c d : ℝ) (g F : ℝ → ℝ)
    (hb : 0 < PowerSeries.realPowerSeriesRadiusValue b)
    (hg : ∃ ε : ℝ, 0 < ε ∧ ∀ x, |x-c| < ε →
      PowerSeries.RealPowerSeriesHasSumValue b c x (g x))
    (hF : ∀ y, ENNReal.ofReal |y-d| < PowerSeries.realPowerSeriesRadiusValue a →
      PowerSeries.RealPowerSeriesHasSumValue a d y (F y))
    (ha : ENNReal.ofReal |g c-d| < PowerSeries.realPowerSeriesRadiusValue a),
    let A := Recentering.realRecenteredCoefficientValue a d (g c)
    let C := coefficientValue A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ PowerSeries.realPowerSeriesRadiusValue C ∧
      Summable (fun m => |A m| * majorantValue b r ^ m) ∧
      Summable (fun k => |C k| * r^k) ∧
      ∀ x : ℝ, |x-c| < r → PowerSeries.RealPowerSeriesHasSumValue C c x (F (g x))

def complex_composition_functionsSpec : Prop :=
  ∀ (a b : ℕ → ℂ) (c d : ℝ) (g F : ℂ → ℂ)
    (hb : 0 < PowerSeries.complexPowerSeriesRadiusValue b)
    (hg : ∃ ε : ℝ, 0 < ε ∧ ∀ z, ‖z-(c : ℂ)‖ < ε →
      PowerSeries.ComplexPowerSeriesHasSumValue b c z (g z))
    (hF : ∀ y, ENNReal.ofReal ‖y-(d : ℂ)‖ < PowerSeries.complexPowerSeriesRadiusValue a →
      PowerSeries.ComplexPowerSeriesHasSumValue a d y (F y))
    (ha : ENNReal.ofReal ‖g (c : ℂ)-(d : ℂ)‖ < PowerSeries.complexPowerSeriesRadiusValue a),
    let A := recenteredValue a (g (c : ℂ)-(d : ℂ))
    let C := coefficientValue A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ PowerSeries.complexPowerSeriesRadiusValue C ∧
      Summable (fun m => ‖A m‖ * majorantValue b r ^ m) ∧
      Summable (fun k => ‖C k‖ * r^k) ∧
      ∀ z : ℂ, ‖z-(c : ℂ)‖ < r → PowerSeries.ComplexPowerSeriesHasSumValue C c z (F (g z))

def complex_real_composition_functionsSpec : Prop :=
  ∀ (a b : ℕ → ℂ) (c d : ℝ) (g : ℝ → ℂ) (F : ℂ → ℂ)
    (hb : 0 < PowerSeries.complexPowerSeriesRadiusValue b)
    (hg : ∃ ε : ℝ, 0 < ε ∧ ∀ x, |x-c| < ε →
      PowerSeries.ComplexPowerSeriesHasSumValue b c (x : ℂ) (g x))
    (hF : ∀ y, ENNReal.ofReal ‖y-(d : ℂ)‖ < PowerSeries.complexPowerSeriesRadiusValue a →
      PowerSeries.ComplexPowerSeriesHasSumValue a d y (F y))
    (ha : ENNReal.ofReal ‖g c-(d : ℂ)‖ < PowerSeries.complexPowerSeriesRadiusValue a),
    let A := recenteredValue a (g c-(d : ℂ))
    let C := coefficientValue A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ PowerSeries.complexPowerSeriesRadiusValue C ∧
      Summable (fun m => ‖A m‖ * majorantValue b r ^ m) ∧
      Summable (fun k => ‖C k‖ * r^k) ∧
      ∀ x : ℝ, |x-c| < r → PowerSeries.ComplexPowerSeriesHasSumValue C c (x : ℂ) (F (g x))

end Specs.SingleVariableAnalysis.Ch13.Composition
