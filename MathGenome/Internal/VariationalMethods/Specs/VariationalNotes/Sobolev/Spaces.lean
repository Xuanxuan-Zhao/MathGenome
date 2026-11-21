import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.EReal.Basic

/-! Canonical definitions for paper.tex, Chapter 8, §8.1.
The domain is an arbitrary open set, so the same definitions apply to the
whole space and to the empty set. Boundedness is needed by subsequent results,
not by these definitions. Both finite dimensional fibers have their Euclidean
norm, including the flattened m-by-d matrix fiber. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal InnerProductSpace

namespace VariationalNotes.Sobolev

/-- A finite real exponent in the source's range. -/
structure Exponent where
  real : ℝ
  one_le : 1 ≤ real

namespace Exponent
def ennreal (p : Exponent) : ℝ≥0∞ := ENNReal.ofReal p.real
instance (p : Exponent) : Fact (1 ≤ p.ennreal) :=
  ⟨by simpa [ennreal] using (ENNReal.ofReal_le_ofReal p.one_le)⟩
@[simp] theorem toReal (p : Exponent) : p.ennreal.toReal = p.real :=
  ENNReal.toReal_ofReal (le_trans zero_le_one p.one_le)
theorem pos (p : Exponent) : 0 < p.real := lt_of_lt_of_le zero_lt_one p.one_le
def two : Exponent := ⟨2, by norm_num⟩
end Exponent

abbrev Domain (d : ℕ) := P102.U4.Space d
abbrev Vector (m : ℕ) := EuclideanSpace ℝ (Fin m)
/-- Entries are indexed by (target coordinate, domain coordinate). -/
abbrev Gradient (m d : ℕ) := EuclideanSpace ℝ (Fin m × Fin d)
def frobenius {m d : ℕ} (A B : Gradient m d) : ℝ := ⟪A, B⟫_ℝ
abbrev domainMeasure {d : ℕ} (Ω : Opens (Domain d)) := volume.restrict (Ω : Set (Domain d))
abbrev ValueLp {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :=
  Lp (Vector m) p.ennreal (domainMeasure Ω)
abbrev GradientLp {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :=
  Lp (Gradient m d) p.ennreal (domainMeasure Ω)
abbrev GraphAmbient {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :=
  WithLp p.ennreal (ValueLp Ω m p × GradientLp Ω m p)

/-- Coordinate extraction on genuine Lp equivalence classes. -/
def coordinateLp {ι : Type*} [Fintype ι] {d : ℕ} (Ω : Opens (Domain d))
    (p : Exponent) (i : ι) :
    Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω) →L[ℝ]
      P102.U4.DomainLp ℝ Ω p.ennreal :=
  (PiLp.proj 2 (fun _ : ι => ℝ) i).compLpL p.ennreal (domainMeasure Ω)

def graphValue {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    GraphAmbient Ω m p →L[ℝ] ValueLp Ω m p := WithLp.fstL ..
def graphGradient {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    GraphAmbient Ω m p →L[ℝ] GradientLp Ω m p := WithLp.sndL ..

/-- The distributional identity ∫(D_j u_i)φ + ∫u_i(D_j φ) = 0. -/
def derivativeEquation {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent)
    (i : Fin m) (j : Fin d) (φ : P102.U4.TestSpace ℝ Ω) :
    GraphAmbient Ω m p →L[ℝ] ℝ :=
  (P102.U4.lpTestPairing Ω p.ennreal φ).comp
      ((coordinateLp Ω p (i,j)).comp (graphGradient Ω m p)) +
    (P102.U4.lpTestPairing Ω p.ennreal (P102.U4.testPartialWord Ω [j] φ)).comp
      ((coordinateLp Ω p i).comp (graphValue Ω m p))

def weakDerivativeGraph {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    Submodule ℝ (GraphAmbient Ω m p) :=
  ⨅ (i : Fin m) (j : Fin d) (φ : P102.U4.TestSpace ℝ Ω),
    (derivativeEquation Ω m p i j φ).ker

/-- W^{1,p} is the weak-derivative graph with the exact full source norm. -/
abbrev W1p {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :=
  ↥(weakDerivativeGraph Ω m p)
def value {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    W1p Ω m p →L[ℝ] ValueLp Ω m p :=
  (graphValue Ω m p).comp (weakDerivativeGraph Ω m p).subtypeL
def gradient {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    W1p Ω m p →L[ℝ] GradientLp Ω m p :=
  (graphGradient Ω m p).comp (weakDerivativeGraph Ω m p).subtypeL

/-- The intrinsic distributional membership condition on a value Lp class. -/
def HasWeakGradient {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent)
    (u : ValueLp Ω m p) : Prop :=
  ∃ V : GradientLp Ω m p, ∀ (i : Fin m) (j : Fin d),
    P102.U4.distributionPartial {j}
      (P102.U4.regularDistribution Ω (coordinateLp Ω p i u)) =
    P102.U4.regularDistribution Ω (coordinateLp Ω p (i,j) V)

/-- Genuine vector-valued smooth functions compactly supported inside Ω. -/
abbrev VectorTest {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) :=
  TestFunction Ω (Vector m) ⊤

def testToValueLp {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    VectorTest Ω m →ₗ[ℝ] ValueLp Ω m p where
  toFun φ := (φ.continuous.memLp_of_hasCompactSupport (p := p.ennreal) φ.hasCompactSupport).toLp φ
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

/-- Finite coordinate families of scalar compactly supported smooth tests are
exactly compactly supported smooth vector functions. -/
def smoothSubmodule {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    Submodule ℝ (W1p Ω m p) :=
  ⨅ i : Fin m, (LinearMap.range (P102.U4.testToDomainLp Ω p.ennreal)).comap
    ((coordinateLp Ω p i).comp (value Ω m p)).toLinearMap
def zeroSubmodule {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :
    Submodule ℝ (W1p Ω m p) := (smoothSubmodule Ω m p).topologicalClosure
abbrev W1pZero {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent) :=
  ↥(zeroSubmodule Ω m p)
def affineClass {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent)
    (u₀ : W1p Ω m p) : Set (W1p Ω m p) :=
  {u | u - u₀ ∈ zeroSubmodule Ω m p}
abbrev H1 {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) := W1p Ω m Exponent.two
abbrev H1Zero {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) := W1pZero Ω m Exponent.two

def WeaklyConverges {d : ℕ} {Ω : Opens (Domain d)} {m : ℕ} {p : Exponent}
    (u : ℕ → W1p Ω m p) (v : W1p Ω m p) : Prop :=
  ∀ ℓ : W1p Ω m p →L[ℝ] ℝ, Filter.Tendsto (fun n => ℓ (u n)) Filter.atTop (nhds (ℓ v))

/-- Signed extended integral. On energies with integrable negative part this
is the usual well-defined real-or-+∞ energy, including nonintegrable positive part. -/
def energyOnFields {d m : ℕ} (Ω : Opens (Domain d))
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (u : Domain d → Vector m) (V : Domain d → Gradient m d) : EReal :=
  (∫⁻ x, ENNReal.ofReal (F x (u x) (V x)) ∂domainMeasure Ω).toEReal -
    (∫⁻ x, ENNReal.ofReal (-F x (u x) (V x)) ∂domainMeasure Ω).toEReal
def energy {d : ℕ} (Ω : Opens (Domain d)) (m : ℕ) (p : Exponent)
    (F : Domain d → Vector m → Gradient m d → ℝ) (u : W1p Ω m p) : EReal :=
  energyOnFields Ω F (value Ω m p u) (gradient Ω m p u)


namespace Expected

def SpaceType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → Type
def SpaceValue : SpaceType := @W1p

def ZeroSpaceType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → Type
def ZeroSpaceValue : ZeroSpaceType := @W1pZero

def H1SpaceType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → Type
def H1SpaceValue : H1SpaceType := @H1

def H1ZeroSpaceType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → Type
def H1ZeroSpaceValue : H1ZeroSpaceType := @H1Zero

def ValueMapType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → W1p Ω m p →L[ℝ] ValueLp Ω m p
def ValueMapValue : ValueMapType := @value

def GradientMapType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → W1p Ω m p →L[ℝ] GradientLp Ω m p
def GradientMapValue : GradientMapType := @gradient

def ZeroBoundarySubmoduleType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → Submodule ℝ (W1p Ω m p)
def ZeroBoundarySubmoduleValue : ZeroBoundarySubmoduleType := @zeroSubmodule

def AffineClassType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → W1p Ω m p → Set (W1p Ω m p)
def AffineClassValue : AffineClassType := @affineClass

def WeakConvergenceType := {d : ℕ} → {Ω : Opens (Domain d)} → {m : ℕ} → {p : Exponent} → (ℕ → W1p Ω m p) → W1p Ω m p → Prop
def WeakConvergenceValue : WeakConvergenceType := @WeaklyConverges

def EnergyType := {d : ℕ} → (Ω : Opens (Domain d)) → (m : ℕ) → (p : Exponent) → (Domain d → Vector m → Gradient m d → ℝ) → W1p Ω m p → EReal
def EnergyValue : EnergyType := @energy

def MatrixPairingType := {m d : ℕ} → Gradient m d → Gradient m d → ℝ
def MatrixPairingValue : MatrixPairingType := @frobenius

/-- Full source norm, not the inherited scalar coordinate sum norm. -/
def NormFormula : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (u : W1p Ω m p),
    ‖u‖ = (‖value Ω m p u‖ ^ p.real + ‖gradient Ω m p u‖ ^ p.real) ^ (1 / p.real)

def ValueInjective : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent), Function.Injective (value Ω m p)

def ValueRange : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
    Set.range (value Ω m p) = {u | HasWeakGradient Ω m p u}

def DerivativeDistribution : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (u : W1p Ω m p)
    (i : Fin m) (j : Fin d),
    P102.U4.distributionPartial {j} (P102.U4.regularDistribution Ω (coordinateLp Ω p i (value Ω m p u))) =
      P102.U4.regularDistribution Ω (coordinateLp Ω p (i,j) (gradient Ω m p u))

def ZeroClosure : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
    (zeroSubmodule Ω m p : Set (W1p Ω m p)) =
      closure {u | ∃ φ : VectorTest Ω m, value Ω m p u = testToValueLp Ω m p φ}

def SmoothInclusion : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (φ : VectorTest Ω m),
    ∃ u : W1p Ω m p, value Ω m p u = testToValueLp Ω m p φ

/-- The coordinate linear identification respects values, derivatives, topology,
zero-boundary closure and weak convergence. -/
def CoordinateBridge : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent),
    ∃ e : W1p Ω m p ≃L[ℝ] (Fin m → P102.U4.Sobolev ℝ Ω 1 p.ennreal),
      (∀ u i, P102.U4.sobolevUnderlying (e u i) = coordinateLp Ω p i (value Ω m p u)) ∧
      (∀ u i j, P102.U4.sobolevDerivative (e u i) ⟨{j}, by simp⟩ =
        coordinateLp Ω p (i,j) (gradient Ω m p u)) ∧
      (∀ A : Set (W1p Ω m p), e '' closure A = closure (e '' A)) ∧
      (∀ u, u ∈ zeroSubmodule Ω m p ↔
        ∀ i, e u i ∈ P102.U4.sobolevZeroSubmodule ℝ Ω 1 p.ennreal) ∧
      (∀ (u : ℕ → W1p Ω m p) v, WeaklyConverges u v ↔
        ∀ (i : Fin m) (ℓ : P102.U4.Sobolev ℝ Ω 1 p.ennreal →L[ℝ] ℝ),
          Filter.Tendsto (fun n => ℓ (e (u n) i)) Filter.atTop (nhds (ℓ (e v i))))

def FrobeniusFormula : Prop :=
  (∀ {m d : ℕ} (A B : Gradient m d),
    frobenius A B = ∑ i : Fin m, ∑ j : Fin d, A (i,j) * B (i,j)) ∧
  (∀ {m d : ℕ} (A : Gradient m d),
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin d, (A (i,j)) ^ 2))

def MeasurableRepresentatives : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (u : W1p Ω m p),
    StronglyMeasurable (value Ω m p u : Domain d → Vector m) ∧
      StronglyMeasurable (gradient Ω m p u : Domain d → Gradient m d)

def CompositionCongr : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (F : Domain d → Vector m → Gradient m d → ℝ)
    {u v : Domain d → Vector m} {U V : Domain d → Gradient m d},
    u =ᵐ[domainMeasure Ω] v → U =ᵐ[domainMeasure Ω] V →
      (fun x => F x (u x) (U x)) =ᵐ[domainMeasure Ω] fun x => F x (v x) (V x)

def EnergyCongr : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (F : Domain d → Vector m → Gradient m d → ℝ)
    {u v : Domain d → Vector m} {U V : Domain d → Gradient m d},
    u =ᵐ[domainMeasure Ω] v → U =ᵐ[domainMeasure Ω] V →
      energyOnFields Ω F u U = energyOnFields Ω F v V

def CompositionMeasurable : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (F : Domain d → Vector m → Gradient m d → ℝ),
    (∀ s Z, AEMeasurable (fun x => F x s Z) (domainMeasure Ω)) →
    (∀ᵐ x ∂domainMeasure Ω, Continuous (fun y : Vector m × Gradient m d => F x y.1 y.2)) →
    ∀ (u : Domain d → Vector m) (V : Domain d → Gradient m d),
      AEMeasurable u (domainMeasure Ω) → AEMeasurable V (domainMeasure Ω) →
      AEMeasurable (fun x => F x (u x) (V x)) (domainMeasure Ω)

end Expected
end VariationalNotes.Sobolev
