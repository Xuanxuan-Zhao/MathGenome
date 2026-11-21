import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.EReal.Operations

/-! Common conventions for paper.tex, Chapter 8, especially lines 3655–3664 and
3768–3785. All integrands are finite (real-valued). The exceptional set in the
continuity clause is independent of the finite-dimensional argument. The metric
and second-countability assumptions below include all finite-dimensional real
state spaces and finite products of fibers, without choosing coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace VariationalNotes.Sobolev.CaratheodorySpecs

variable {S E : Type*} [MeasurableSpace S] [TopologicalSpace E]

/-- Independent model of measurable sections and continuity outside one common null set. -/
def Caratheodory (μ : Measure S) (F : S → E → ℝ) : Prop :=
  (∀ y, Measurable (fun x => F x y)) ∧ ∀ᵐ x ∂μ, Continuous (F x)

/-- The ordinary integrability condition on the negative part. -/
def NegativePartIntegrable (μ : Measure S) (f : S → ℝ) : Prop :=
  Integrable (fun x => max (-f x) 0) μ

/-- Extended Lebesgue integral, used when the negative part is integrable.
Unlike the totalized real Bochner integral this retains a possible value `⊤`. -/
def extendedIntegral (μ : Measure S) (f : S → ℝ) : EReal :=
  (∫⁻ x, ENNReal.ofReal (f x) ∂μ : ℝ≥0∞) -
    (∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ℝ≥0∞)

/-- Integral energy on representatives; the theorems establish descent modulo a.e. equality. -/
def integralEnergy (μ : Measure S) (F : S → E → ℝ) (y : S → E) : EReal :=
  extendedIntegral μ (fun x => F x (y x))

/-- State and variable finite product of independent fiber arguments. In particular,
`A = EuclideanSpace ℝ (Fin m)` and `B i = EuclideanSpace ℝ (Fin (d i))`
recover the state and mixed-exponent fibers in the source. -/
def MixedCaratheodory {A ι : Type*} {B : ι → Type*}
    [TopologicalSpace A] [∀ i, TopologicalSpace (B i)]
    (μ : Measure S) (F : S → A → (∀ i, B i) → ℝ) : Prop :=
  Caratheodory μ (fun x (v : A × (∀ i, B i)) => F x v.1 v.2)

/-- Energy on an `Lp` class, evaluated on its a.e. representative. -/
def lpIntegralEnergy {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (μ : Measure S) (F : S → E → ℝ) (y : Lp E p μ) : EReal :=
  integralEnergy μ F y

end VariationalNotes.Sobolev.CaratheodorySpecs

/-! Independent expected interfaces. Each theorem specification is its full universally
quantified proposition, and each definition specification includes its full expected value.
These declarations import no implementation. The finite-coordinate specializations below
make explicit the applicability to arbitrary state dimensions and variable finite fibers.
The energy specifications impose no upper growth bound and retain positive infinity. -/
namespace VariationalNotes.Sobolev.CaratheodorySpecs
universe u_1 u_2 u_3 u_4 u_5

/-- Expected definition interface for `VariationalNotes.Sobolev.Caratheodory`. -/
def Caratheodory_type : Type _ :=
  {S : Type u_1} →
    {E : Type u_2} → [MeasurableSpace S] → [TopologicalSpace E] → MeasureTheory.Measure S → (S → E → Real) → Prop

def Caratheodory_value : Caratheodory_type :=
  fun {S} {E} [MeasurableSpace S] [TopologicalSpace E] μ F =>
    And (∀ (y : E), Measurable fun x => F x y) (Filter.Eventually (fun x => Continuous (F x)) (MeasureTheory.ae μ))

/-- Expected theorem interface for `VariationalNotes.Sobolev.Caratheodory.aemeasurable_lp_substitution`. -/
def Caratheodory_aemeasurable_lp_substitution_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {μ : MeasureTheory.Measure S} {p : ENNReal} {F : S → E → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ F →
      ∀ (y : Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp E p μ) x),
        AEMeasurable (fun x => F x (y.val.cast x)) μ

/-- Expected theorem interface for `VariationalNotes.Sobolev.Caratheodory.aemeasurable_substitution`. -/
def Caratheodory_aemeasurable_substitution_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [MeasurableSpace E] [PseudoMetricSpace E]
    [SecondCountableTopology E] [BorelSpace E] [Nonempty E] {μ : MeasureTheory.Measure S} {F : S → E → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ F → ∀ {y : S → E}, AEMeasurable y μ → AEMeasurable (fun x => F x (y x)) μ

/-- Expected theorem interface for `VariationalNotes.Sobolev.Caratheodory.exists_regularization`. -/
def Caratheodory_exists_regularization_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [PseudoMetricSpace E] {μ : MeasureTheory.Measure S}
    {F : S → E → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ F →
      Exists fun (N : Set S) =>
        Exists fun (G : S → E → ℝ) =>
          And (MeasurableSet N)
            (And (Eq (MeasureTheory.Measure.instFunLike.coe μ N) 0)
              (And (∀ (x : S), Not (Set.instMembership.mem N x) → ∀ (y : E), Eq (G x y) (F x y))
                (And (∀ (x : S), Set.instMembership.mem N x → ∀ (y : E), Eq (G x y) 0)
                  (And (∀ (y : E), Measurable fun x => G x y) (∀ (x : S), Continuous (G x))))))

/-- Expected theorem interface for `VariationalNotes.Sobolev.Caratheodory.lpIntegralEnergy_ne_bot`. -/
def Caratheodory_lpIntegralEnergy_ne_bot_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {μ : MeasureTheory.Measure S} {p : ENNReal} {F : S → E → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ F →
      ∀ (y : Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp E p μ) x),
        (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (y.val.cast x)) →
          Ne (VariationalNotes.Sobolev.CaratheodorySpecs.lpIntegralEnergy μ F y) instBotEReal.bot

/-- Expected theorem interface for `VariationalNotes.Sobolev.Caratheodory.measurable_substitution`. -/
def Caratheodory_measurable_substitution_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [MeasurableSpace E] [PseudoMetricSpace E]
    [SecondCountableTopology E] [BorelSpace E] [Nonempty E] {μ : MeasureTheory.Measure S} [μ.IsComplete]
    {F : S → E → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ F → ∀ {y : S → E}, Measurable y → Measurable fun x => F x (y x)

/-- Expected definition interface for `VariationalNotes.Sobolev.MixedCaratheodory`. -/
def MixedCaratheodory_type : Type _ :=
  {S : Type u_1} →
    [MeasurableSpace S] →
      {A : Type u_3} →
        {ι : Type u_4} →
          {B : ι → Type u_5} →
            [TopologicalSpace A] →
              [(i : ι) → TopologicalSpace (B i)] → MeasureTheory.Measure S → (S → A → ((i : ι) → B i) → Real) → Prop

def MixedCaratheodory_value : MixedCaratheodory_type :=
  fun {S} [MeasurableSpace S] {A} {ι} {B} [TopologicalSpace A] [(i : ι) → TopologicalSpace (B i)] μ F =>
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ fun x (v : A × (∀ i, B i)) => F x v.fst v.snd

/-- Expected theorem interface for `VariationalNotes.Sobolev.MixedCaratheodory.ae_continuous_fiber`. -/
def MixedCaratheodory_ae_continuous_fiber_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {A : Type u_3} {ι : Type u_4} {B : ι → Type u_5}
    [PseudoMetricSpace A] [(i : ι) → PseudoMetricSpace (B i)] {μ : MeasureTheory.Measure S}
    {F : S → A → ((i : ι) → B i) → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.MixedCaratheodory μ F →
      ∀ (s : S → A), Filter.Eventually (fun x => Continuous (F x (s x))) (MeasureTheory.ae μ)

/-- Expected theorem interface for `VariationalNotes.Sobolev.MixedCaratheodory.aemeasurable_lp_substitution`. -/
def MixedCaratheodory_aemeasurable_lp_substitution_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {A : Type u_3} {ι : Type u_4} {B : ι → Type u_5} [Fintype ι]
    [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [(i : ι) → NormedAddCommGroup (B i)] [(i : ι) → MeasurableSpace (B i)] [∀ (i : ι), BorelSpace (B i)]
    [∀ (i : ι), SecondCountableTopology (B i)] {μ : MeasureTheory.Measure S} {q : ENNReal} {r : ι → ENNReal}
    {F : S → A → ((i : ι) → B i) → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.MixedCaratheodory μ F →
      ∀ (s : Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp A q μ) x)
        (z : (i : ι) → Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp (B i) (r i) μ) x),
        AEMeasurable (fun x => F x (s.val.cast x) fun i => (z i).val.cast x) μ

/-- Expected theorem interface for `VariationalNotes.Sobolev.MixedCaratheodory.aemeasurable_state_section`. -/
def MixedCaratheodory_aemeasurable_state_section_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {A : Type u_3} {ι : Type u_4} {B : ι → Type u_5} [Fintype ι]
    [MeasurableSpace A] [PseudoMetricSpace A] [SecondCountableTopology A] [BorelSpace A] [Nonempty A]
    [(i : ι) → MeasurableSpace (B i)] [(i : ι) → PseudoMetricSpace (B i)]
    [∀ (i : ι), SecondCountableTopology (B i)] [∀ (i : ι), BorelSpace (B i)] [∀ (i : ι), Nonempty (B i)]
    {μ : MeasureTheory.Measure S} {F : S → A → ((i : ι) → B i) → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.MixedCaratheodory μ F →
      ∀ {s : S → A}, AEMeasurable s μ → ∀ (z : (i : ι) → B i), AEMeasurable (fun x => F x (s x) z) μ

/-- Expected theorem interface for `VariationalNotes.Sobolev.MixedCaratheodory.aemeasurable_substitution`. -/
def MixedCaratheodory_aemeasurable_substitution_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {A : Type u_3} {ι : Type u_4} {B : ι → Type u_5} [Fintype ι]
    [MeasurableSpace A] [PseudoMetricSpace A] [SecondCountableTopology A] [BorelSpace A] [Nonempty A]
    [(i : ι) → MeasurableSpace (B i)] [(i : ι) → PseudoMetricSpace (B i)]
    [∀ (i : ι), SecondCountableTopology (B i)] [∀ (i : ι), BorelSpace (B i)] [∀ (i : ι), Nonempty (B i)]
    {μ : MeasureTheory.Measure S} {F : S → A → ((i : ι) → B i) → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.MixedCaratheodory μ F →
      ∀ {s : S → A} {z : (i : ι) → S → B i},
        AEMeasurable s μ → (∀ (i : ι), AEMeasurable (z i) μ) → AEMeasurable (fun x => F x (s x) fun i => z i x) μ

/-- Expected theorem interface for `VariationalNotes.Sobolev.MixedCaratheodory.measurable_substitution`. -/
def MixedCaratheodory_measurable_substitution_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {A : Type u_3} {ι : Type u_4} {B : ι → Type u_5} [Fintype ι]
    [MeasurableSpace A] [PseudoMetricSpace A] [SecondCountableTopology A] [BorelSpace A] [Nonempty A]
    [(i : ι) → MeasurableSpace (B i)] [(i : ι) → PseudoMetricSpace (B i)]
    [∀ (i : ι), SecondCountableTopology (B i)] [∀ (i : ι), BorelSpace (B i)] [∀ (i : ι), Nonempty (B i)]
    {μ : MeasureTheory.Measure S} {F : S → A → ((i : ι) → B i) → Real} [μ.IsComplete],
    VariationalNotes.Sobolev.CaratheodorySpecs.MixedCaratheodory μ F →
      ∀ {s : S → A} {z : (i : ι) → S → B i},
        Measurable s → (∀ (i : ι), Measurable (z i)) → Measurable fun x => F x (s x) fun i => z i x

/-- Expected definition interface for `VariationalNotes.Sobolev.NegativePartIntegrable`. -/
def NegativePartIntegrable_type : Type _ :=
  {S : Type u_1} → [MeasurableSpace S] → MeasureTheory.Measure S → (S → Real) → Prop

def NegativePartIntegrable_value : NegativePartIntegrable_type :=
  fun {S} [MeasurableSpace S] μ f => MeasureTheory.Integrable (fun x => Real.instMax.max (Real.instNeg.neg (f x)) 0) μ

/-- Expected definition interface for `VariationalNotes.Sobolev.extendedIntegral`. -/
def extendedIntegral_type : Type _ :=
  {S : Type u_1} → [MeasurableSpace S] → MeasureTheory.Measure S → (S → Real) → EReal

def extendedIntegral_value : extendedIntegral_type :=
  fun {S} [MeasurableSpace S] μ f =>
    instHSub.hSub (MeasureTheory.lintegral μ fun x => ENNReal.ofReal (f x)).toEReal
      (MeasureTheory.lintegral μ fun x => ENNReal.ofReal (Real.instNeg.neg (f x))).toEReal

/-- Expected theorem interface for `VariationalNotes.Sobolev.extendedIntegral_congr_ae`. -/
def extendedIntegral_congr_ae_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f g : S → Real},
    (MeasureTheory.ae μ).EventuallyEq f g →
      Eq (VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ f) (VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ g)

/-- Expected theorem interface for `VariationalNotes.Sobolev.extendedIntegral_eq_integral`. -/
def extendedIntegral_eq_integral_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f : S → Real},
    MeasureTheory.Integrable f μ →
      Eq (VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ f) (MeasureTheory.integral μ fun x => f x).toEReal

/-- Expected theorem interface for `VariationalNotes.Sobolev.extendedIntegral_eq_top_iff`. -/
def extendedIntegral_eq_top_iff_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f : S → Real},
    AEMeasurable f μ →
      VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ f →
        Iff (Eq (VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ f) instTopEReal.top)
          (Eq (MeasureTheory.lintegral μ fun x => ENNReal.ofReal (f x)) ENNReal.instTop.top)

/-- Expected theorem interface for `VariationalNotes.Sobolev.extendedIntegral_ne_bot`. -/
def extendedIntegral_ne_bot_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f : S → Real},
    AEMeasurable f μ →
      VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ f →
        Ne (VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ f) instBotEReal.bot

/-- Expected theorem interface for `VariationalNotes.Sobolev.extendedIntegral_of_nonneg`. -/
def extendedIntegral_of_nonneg_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f : S → Real},
    Filter.Eventually (fun x => Real.instLE.le 0 (f x)) (MeasureTheory.ae μ) →
      Eq (VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ f) (MeasureTheory.lintegral μ fun x => ENNReal.ofReal (f x)).toEReal

/-- Expected theorem interface for `VariationalNotes.Sobolev.finiteDimensional_substitution`. -/
def finiteDimensional_substitution_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {n : Nat} {F : S → (Fin n → Real) → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.Caratheodory μ F →
      ∀ {y : S → Fin n → Real}, AEMeasurable y μ → AEMeasurable (fun x => F x (y x)) μ

/-- Expected definition interface for `VariationalNotes.Sobolev.integralEnergy`. -/
def integralEnergy_type : Type _ :=
  {S : Type u_1} →
    {E : Type u_2} → [MeasurableSpace S] → MeasureTheory.Measure S → (S → E → Real) → (S → E) → EReal

def integralEnergy_value : integralEnergy_type :=
  fun {S} {E} [MeasurableSpace S] μ F y => VariationalNotes.Sobolev.CaratheodorySpecs.extendedIntegral μ fun x => F x (y x)

/-- Expected theorem interface for `VariationalNotes.Sobolev.integralEnergy_congr_ae`. -/
def integralEnergy_congr_ae_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {F : S → E → Real}
    {y y' : S → E},
    (MeasureTheory.ae μ).EventuallyEq y y' →
      And (Eq (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ F y) (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ F y'))
        (Iff (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (y x))
          (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (y' x)))

/-- Expected theorem interface for `VariationalNotes.Sobolev.integralEnergy_congr_integrand_ae`. -/
def integralEnergy_congr_integrand_ae_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {F G : S → E → Real},
    Filter.Eventually (fun x => ∀ (y : E), Eq (F x y) (G x y)) (MeasureTheory.ae μ) →
      ∀ (y : S → E),
        And (Eq (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ F y) (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ G y))
          (Iff (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (y x))
            (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => G x (y x)))

/-- Expected definition interface for `VariationalNotes.Sobolev.lpIntegralEnergy`. -/
def lpIntegralEnergy_type : Type _ :=
  {S : Type u_1} →
    [MeasurableSpace S] →
      {E : Type u_3} →
        [NormedAddCommGroup E] →
          {p : ENNReal} →
            (μ : MeasureTheory.Measure S) →
              (S → E → Real) → (Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp E p μ) x) → EReal

def lpIntegralEnergy_value : lpIntegralEnergy_type :=
  fun {S} [MeasurableSpace S] {E} [NormedAddCommGroup E] {_p} μ F y =>
    VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ F y.val.cast

/-- Expected theorem interface for `VariationalNotes.Sobolev.lpIntegralEnergy_toLp`. -/
def lpIntegralEnergy_toLp_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [NormedAddCommGroup E] {μ : MeasureTheory.Measure S}
    {p : ENNReal} {F : S → E → Real} {y : S → E} (hy : MeasureTheory.MemLp y p μ),
    And
      (Eq (VariationalNotes.Sobolev.CaratheodorySpecs.lpIntegralEnergy μ F (MeasureTheory.MemLp.toLp y hy))
        (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ F y))
      (Iff (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x ((MeasureTheory.MemLp.toLp y hy).val.cast x))
        (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (y x)))

/-- Expected theorem interface for `VariationalNotes.Sobolev.measurable_simple_substitution`. -/
def measurable_simple_substitution_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [Nonempty E] {F : S → E → Real},
    (∀ (y : E), Measurable fun x => F x y) →
      ∀ (y : MeasureTheory.SimpleFunc S E), Measurable fun x => F x (MeasureTheory.SimpleFunc.instFunLike.coe y x)

/-- Expected theorem interface for `VariationalNotes.Sobolev.measurable_substitution`. -/
def measurable_substitution_type : Prop :=
  ∀ {S : Type u_1} {E : Type u_2} [MeasurableSpace S] [MeasurableSpace E] [PseudoMetricSpace E]
    [SecondCountableTopology E] [BorelSpace E] [Nonempty E] {F : S → E → Real},
    (∀ (y : E), Measurable fun x => F x y) →
      (∀ (x : S), Continuous (F x)) → ∀ {y : S → E}, Measurable y → Measurable fun x => F x (y x)

/-- Expected theorem interface for `VariationalNotes.Sobolev.mixed_finiteDimensional_lp_substitution`. -/
def mixed_finiteDimensional_lp_substitution_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {m k : Nat} {d : Fin k → Nat} {q : ENNReal}
    {r : Fin k → ENNReal} {F : S → (Fin m → Real) → ((i : Fin k) → Fin (d i) → Real) → Real},
    VariationalNotes.Sobolev.CaratheodorySpecs.MixedCaratheodory μ F →
      ∀ (s : Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp (Fin m → Real) q μ) x)
        (z : (i : Fin k) → Subtype fun x => SetLike.instMembership.mem (MeasureTheory.Lp (Fin (d i) → Real) (r i) μ) x),
        AEMeasurable (fun x => F x (s.val.cast x) fun i => (z i).val.cast x) μ

/-- Expected theorem interface for `VariationalNotes.Sobolev.mixed_integralEnergy_congr_ae`. -/
def mixed_integralEnergy_congr_ae_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {A : Type u_3} {ι : Type u_4} {B : ι → Type u_5} [Fintype ι]
    {μ : MeasureTheory.Measure S} {F : S → A → ((i : ι) → B i) → Real} {s s' : S → A} {z z' : (i : ι) → S → B i},
    (MeasureTheory.ae μ).EventuallyEq s s' →
      (∀ (i : ι), (MeasureTheory.ae μ).EventuallyEq (z i) (z' i)) →
        And
          (Eq
            (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ (fun x (v : A × (∀ i, B i)) => F x v.fst v.snd) fun x =>
              (s x, fun i => z i x))
            (VariationalNotes.Sobolev.CaratheodorySpecs.integralEnergy μ (fun x (v : A × (∀ i, B i)) => F x v.fst v.snd) fun x =>
              (s' x, fun i => z' i x)))
          (Iff (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (s x) fun i => z i x)
            (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ fun x => F x (s' x) fun i => z' i x))

/-- Expected theorem interface for `VariationalNotes.Sobolev.negativePartIntegrable_congr_ae`. -/
def negativePartIntegrable_congr_ae_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f g : S → Real},
    (MeasureTheory.ae μ).EventuallyEq f g →
      Iff (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ f) (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ g)

/-- Expected theorem interface for `VariationalNotes.Sobolev.negativePartIntegrable_iff`. -/
def negativePartIntegrable_iff_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f : S → Real},
    AEMeasurable f μ →
      Iff (VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ f)
        (Ne (MeasureTheory.lintegral μ fun x => ENNReal.ofReal (Real.instNeg.neg (f x))) ENNReal.instTop.top)

/-- Expected theorem interface for `VariationalNotes.Sobolev.negativePartIntegrable_of_lower_bound`. -/
def negativePartIntegrable_of_lower_bound_type : Prop :=
  ∀ {S : Type u_1} [MeasurableSpace S] {μ : MeasureTheory.Measure S} {f : S → Real},
    AEMeasurable f μ →
      ∀ {a : S → Real},
        MeasureTheory.Integrable a μ →
          Filter.Eventually (fun x => Real.instLE.le (Real.instNeg.neg (a x)) (f x)) (MeasureTheory.ae μ) →
            VariationalNotes.Sobolev.CaratheodorySpecs.NegativePartIntegrable μ f

end VariationalNotes.Sobolev.CaratheodorySpecs
