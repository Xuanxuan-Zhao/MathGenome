import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-!
Independent statements for paper.tex:165–203 (d12:01-01-rules).
The domain of a punctured limit is arbitrary, and sequences are required to
stay in that domain and avoid the center. Holomorphic sets are open but may
be empty or disconnected. All derivatives use the shared increment definition.
-/

open scoped Topology
open Filter

namespace Specs.D12Complex.Ch01.LimitsCalculus
open _root_.D12Complex

def complex_tendsto_iff_coordinates_type : Prop :=
  ∀ (ι : Type) (l : Filter ι) (f : ι → ℂ) (L : ℂ),
    Tendsto f l (𝓝 L) ↔
      Tendsto (fun z => (f z).re) l (𝓝 L.re) ∧
      Tendsto (fun z => (f z).im) l (𝓝 L.im)

def puncturedLimitWithin_iff_coordinates_type : Prop :=
  ∀ (s : Set ℂ) (f : ℂ → ℂ) (a L : ℂ),
    PuncturedLimitWithin s f a L ↔
      Tendsto (fun z => (f z).re) (𝓝[s \ {a}] a) (𝓝 L.re) ∧
      Tendsto (fun z => (f z).im) (𝓝[s \ {a}] a) (𝓝 L.im)

def puncturedLimitWithin_iff_sequences_type : Prop :=
  ∀ (s : Set ℂ) (f : ℂ → ℂ) (a L : ℂ),
    PuncturedLimitWithin s f a L ↔
      ∀ u : ℕ → ℂ, (∀ n, u n ∈ s ∧ u n ≠ a) →
        Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 L)

def puncturedLimit_iff_sequences_type : Prop :=
  ∀ (f : ℂ → ℂ) (a L : ℂ),
    PuncturedLimit f a L ↔
      ∀ u : ℕ → ℂ, (∀ n, u n ≠ a) →
        Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 L)

def complexDifferentiableAt_continuous_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ),
    ComplexDifferentiableAt f a → ContinuousAtPoint f a

def hasComplexDerivativeAt_linear_type : Prop :=
  ∀ (f g : ℂ → ℂ) (A B a α β : ℂ),
    HasComplexDerivativeAt f A a → HasComplexDerivativeAt g B a →
    HasComplexDerivativeAt (fun z => α * f z + β * g z) (α * A + β * B) a

def hasComplexDerivativeAt_mul_type : Prop :=
  ∀ (f g : ℂ → ℂ) (A B a : ℂ),
    HasComplexDerivativeAt f A a → HasComplexDerivativeAt g B a →
    HasComplexDerivativeAt (fun z => f z * g z) (A * g a + f a * B) a

def hasComplexDerivativeAt_div_type : Prop :=
  ∀ (f g : ℂ → ℂ) (A B a : ℂ),
    HasComplexDerivativeAt f A a → HasComplexDerivativeAt g B a → g a ≠ 0 →
    HasComplexDerivativeAt (fun z => f z / g z)
      ((A * g a - f a * B) / (g a) ^ 2) a

def hasComplexDerivativeAt_comp_type : Prop :=
  ∀ (f g : ℂ → ℂ) (A B a : ℂ),
    HasComplexDerivativeAt f A a → HasComplexDerivativeAt g B (f a) →
    HasComplexDerivativeAt (g ∘ f) (B * A) a

def complexDifferentiableAt_nonzero_near_type : Prop :=
  ∀ (g : ℂ → ℂ) (a : ℂ), ComplexDifferentiableAt g a → g a ≠ 0 →
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - a‖ < r → g z ≠ 0

def holomorphicOn_linear_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ) (α β : ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g →
    HolomorphicOn Ω (fun z => α * f z + β * g z)

def holomorphicOn_mul_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g →
    HolomorphicOn Ω (fun z => f z * g z)

def holomorphicOn_div_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g → (∀ z ∈ Ω, g z ≠ 0) →
    HolomorphicOn Ω (fun z => f z / g z)

def holomorphicOn_div_nonzeroSet_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g →
    HolomorphicOn {z ∈ Ω | g z ≠ 0} (fun z => f z / g z)

def holomorphicOn_div_local_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ) (a : ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g → a ∈ Ω → g a ≠ 0 →
    ∃ U : Set ℂ, a ∈ U ∧ U ⊆ Ω ∧ (∀ z ∈ U, g z ≠ 0) ∧
      HolomorphicOn U (fun z => f z / g z)

def holomorphicOn_comp_type : Prop :=
  ∀ (Ω V : Set ℂ) (f g : ℂ → ℂ),
    HolomorphicOn Ω f → HolomorphicOn V g → Set.MapsTo f Ω V →
    HolomorphicOn Ω (g ∘ f)

end Specs.D12Complex.Ch01.LimitsCalculus
