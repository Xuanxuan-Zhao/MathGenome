import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WindingIndex
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! d12:19-07, first assertions. Germ relations are equations in the actual
neighborhood quotient. The paths for continuation are arbitrary continuous
paths; the integral assertions use the canonical piecewise C1 contours on
any compact interval, including a degenerate interval. -/
open Filter Set
open scoped Topology
noncomputable section

namespace D12Complex.LogarithmRootMonodromy

def IsLogarithmGerm {a : ℂ} (φ : HolomorphicGerm a) : Prop :=
  φ.val.map Complex.exp = ((fun z : ℂ => z) : Germ (𝓝 a) ℂ)

def IsRootGerm (n : ℕ) {a : ℂ} (φ : HolomorphicGerm a) : Prop :=
  φ.val.map (fun w => w ^ n) = ((fun z : ℂ => z) : Germ (𝓝 a) ℂ)

/-- Affine normalization retains both endpoints and allows constant contours. -/
def normalizedPath (γ : PiecewiseC1Path) (t : unitInterval) : ℂ :=
  γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))

/-- The canonical index of the chain consisting of this one traversal.
The monodromy assertions use it only for closed contours avoiding zero. -/
def pathIndex (γ : PiecewiseC1Path) : ℂ :=
  IntegralChain.index (Finsupp.single γ 1) 0

end D12Complex.LogarithmRootMonodromy

namespace Specs.D12Complex.Ch19.LogarithmRootMonodromy
open _root_.D12Complex _root_.D12Complex.LogarithmRootMonodromy

def IsLogarithmGerm_type := ∀ {a : ℂ}, HolomorphicGerm a → Prop
def IsLogarithmGerm_value : IsLogarithmGerm_type := @IsLogarithmGerm

def IsRootGerm_type := ℕ → ∀ {a : ℂ}, HolomorphicGerm a → Prop
def IsRootGerm_value : IsRootGerm_type := @IsRootGerm

def normalizedPath_type := PiecewiseC1Path → unitInterval → ℂ
def normalizedPath_value : normalizedPath_type := normalizedPath

def pathIndex_type := PiecewiseC1Path → ℂ
def pathIndex_value : pathIndex_type := pathIndex

/-- The relation remains a relation of germs, at every parameter. -/
def logarithm_continues_type : Prop :=
  ∀ (γ : unitInterval → ℂ), Continuous γ → (∀ t, γ t ≠ 0) →
    ∀ φ : HolomorphicGerm (γ 0), IsLogarithmGerm φ →
      ∃ Φ : GermFamily γ, IsContinuation {z : ℂ | z ≠ 0} γ φ Φ ∧
        ∀ t, IsLogarithmGerm (Φ t)

def root_continues_type : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (γ : unitInterval → ℂ),
    Continuous γ → (∀ t, γ t ≠ 0) →
    ∀ φ : HolomorphicGerm (γ 0), IsRootGerm n φ →
      ∃ Φ : GermFamily γ, IsContinuation {z : ℂ | z ≠ 0} γ φ Φ ∧
        ∀ t, IsRootGerm n (Φ t)

/-- The integral equality also fixes the sign and normalization of the index. -/
def logarithm_monodromy_type : Prop :=
  ∀ (γ : PiecewiseC1Path), γ.IsClosed → 0 ∉ γ.trace →
    ∀ (φ : HolomorphicGerm (normalizedPath γ 0)) (Φ : GermFamily (normalizedPath γ)),
      IsLogarithmGerm φ →
      IsContinuation {z : ℂ | z ≠ 0} (normalizedPath γ) φ Φ →
      (Φ 1).value - φ.value = γ.integral (fun z => 1 / z) ∧
      (Φ 1).value - φ.value = 2 * (Real.pi : ℂ) * Complex.I * pathIndex γ

/-- Equality on a neighborhood states the terminal *germ* identity. The
representatives f,g are arbitrary. HEq identifies the endpoint fibres using
closedness, and the integer k is tied to the integral-defined index. -/
def root_monodromy_type : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (γ : PiecewiseC1Path), γ.IsClosed → 0 ∉ γ.trace →
    ∀ (φ : HolomorphicGerm (normalizedPath γ 0)) (Φ : GermFamily (normalizedPath γ)),
      IsRootGerm n φ →
      IsContinuation {z : ℂ | z ≠ 0} (normalizedPath γ) φ Φ →
      ∃ k : ℤ, pathIndex γ = (k : ℂ) ∧
        (∀ (f g : ℂ → ℂ), φ.val = (f : Germ (𝓝 (normalizedPath γ 0)) ℂ) →
          (Φ 1).val = (g : Germ (𝓝 (normalizedPath γ 1)) ℂ) →
          g =ᶠ[𝓝 (normalizedPath γ 0)]
            (fun z => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / n) * f z)) ∧
        (HEq (Φ 1) φ ↔ (n : ℤ) ∣ k)

end Specs.D12Complex.Ch19.LogarithmRootMonodromy
