import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! Independent statements for d04:02:segment-ftc. The integral below is a
finite tuple of scalar Darboux integrals, not a measure integral. Intervals
are ordered (including singletons); both Euclidean dimensions may be zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C02.SegmentFTC
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
namespace Model
open Specs.SingleVariableAnalysis.Ch08.Integral

def VectorRiemannIntegrable {m : ℕ} (v : ℝ → E m) (a b : ℝ) : Prop :=
  ∀ i : Fin m, realIntegrableValue (fun t => v t i) a b

/-- Each component is the admitted proper scalar Riemann integral. -/
def vectorRiemannIntegral {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hv : VectorRiemannIntegrable v a b) : E m :=
  WithLp.toLp 2 (fun i => realIntegralValue (fun t => v t i) (hv i))
end Model
open Model
open Specs.SingleVariableAnalysis.Ch08.Integral

def VectorRiemannIntegrableType := {m : ℕ} → (ℝ → E m) → ℝ → ℝ → Prop
def VectorRiemannIntegrableValue : VectorRiemannIntegrableType := @Model.VectorRiemannIntegrable

def vectorRiemannIntegralType := {m : ℕ} → (v : ℝ → E m) → {a b : ℝ} →
  VectorRiemannIntegrable v a b → E m
def vectorRiemannIntegralValue : vectorRiemannIntegralType := @Model.vectorRiemannIntegral

def continuous_vector_riemann_integrableType : Prop :=
  ∀ {m : ℕ} (v : ℝ → E m) {a b : ℝ}, a ≤ b →
    ContinuousOn v (Icc a b) → VectorRiemannIntegrable v a b

def vectorRiemannIntegral_applyType : Prop :=
  ∀ {m : ℕ} (v : ℝ → E m) {a b : ℝ} (hv : VectorRiemannIntegrable v a b)
    (i : Fin m), vectorRiemannIntegral v hv i = realIntegralValue (fun t => v t i) (hv i)

def vectorRiemannIntegral_innerType : Prop :=
  ∀ {m : ℕ} (v : ℝ → E m) {a b : ℝ} (hab : a ≤ b)
    (hv : VectorRiemannIntegrable v a b) (w : E m),
    ∃ hw : realIntegrableValue (fun t => inner ℝ w (v t)) a b,
      realIntegralValue _ hw = inner ℝ w (vectorRiemannIntegral v hv)

def vectorRiemannIntegral_addType : Prop :=
  ∀ {m : ℕ} (v w : ℝ → E m) {a b : ℝ}
    (hv : VectorRiemannIntegrable v a b) (hw : VectorRiemannIntegrable w a b),
    ∃ h : VectorRiemannIntegrable (fun t => v t + w t) a b,
      vectorRiemannIntegral _ h = vectorRiemannIntegral v hv + vectorRiemannIntegral w hw

def vectorRiemannIntegral_smulType : Prop :=
  ∀ {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hv : VectorRiemannIntegrable v a b) (c : ℝ),
    ∃ h : VectorRiemannIntegrable (fun t => c • v t) a b,
      vectorRiemannIntegral _ h = c • vectorRiemannIntegral v hv

def norm_vectorRiemannIntegral_leType : Prop :=
  ∀ {m : ℕ} (v : ℝ → E m) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn v (Icc a b)) (hv : VectorRiemannIntegrable v a b),
    ∃ hn : realIntegrableValue (fun t => ‖v t‖) a b,
      ‖vectorRiemannIntegral v hv‖ ≤ realIntegralValue _ hn

def segment_integrand_continuousType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a h : E n)
    (hf : CrOn 1 U f) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U),
    ContinuousOn (fun t : ℝ => totalDerivative f (a + t • h) h) (Icc 0 1)

def segment_ftcType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a h : E n)
    (hU : IsOpen U) (hf : CrOn 1 U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U),
    ∃ hv : VectorRiemannIntegrable (fun t : ℝ => totalDerivative f (a + t • h) h) 0 1,
      f (a + h) - f a = vectorRiemannIntegral _ hv

end Specs.D04.C02.SegmentFTC
