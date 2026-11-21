import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Data.Set.Function
import Mathlib.Topology.Compactness.Compact

/-! Independent statements for the Joukowski part of paper.tex:2354–2361.
The segment is the closed real segment, including both endpoints. The square
root is constructed from the inverse; no square-root certificate is assumed.
The asymptotic assertion means squareRoot(w)/w → 1 as |w| → ∞. -/
noncomputable section
open scoped Topology

namespace D12Complex.Joukowski

def map (z : ℂ) : ℂ := (z + z⁻¹) / 2

def exterior : Set ℂ := {z | 1 < ‖z‖}

def slitPlane : Set ℂ := {w | ¬(w.im = 0 ∧ -1 ≤ w.re ∧ w.re ≤ 1)}

noncomputable def inverse : ℂ → ℂ := Function.invFunOn map exterior

def squareRoot (w : ℂ) : ℂ := inverse w - w

end D12Complex.Joukowski

namespace Specs.D12Complex.Ch10.Joukowski
open _root_.D12Complex
open _root_.D12Complex.Joukowski

def map_type := ℂ → ℂ
def map_value : map_type := fun z => (z + z⁻¹) / 2

def exterior_type := Set ℂ
def exterior_value : exterior_type := {z | 1 < ‖z‖}

def slitPlane_type := Set ℂ
def slitPlane_value : slitPlane_type := {w | ¬(w.im = 0 ∧ -1 ≤ w.re ∧ w.re ≤ 1)}

def inverse_type := ℂ → ℂ
def inverse_value : inverse_type := Function.invFunOn map exterior

def squareRoot_type := ℂ → ℂ
def squareRoot_value : squareRoot_type := fun w => inverse w - w

def biholomorphic_pair_type : Prop :=
  BiholomorphicPair exterior slitPlane map inverse

def unique_quadratic_root_type : Prop :=
  ∀ w ∈ slitPlane, 1 < ‖inverse w‖ ∧
    (inverse w)^2 - 2*w*inverse w + 1 = 0 ∧
    ∀ z : ℂ, 1 < ‖z‖ → z^2 - 2*w*z + 1 = 0 → z = inverse w

def inverse_squareRoot_type : Prop :=
  HolomorphicOn slitPlane squareRoot ∧
    (∀ w ∈ slitPlane, (squareRoot w)^2 = w^2 - 1 ∧
      inverse w = w + squareRoot w) ∧
    Filter.Tendsto (fun w => squareRoot w / w) (Filter.cocompact ℂ) (𝓝 1)

end Specs.D12Complex.Ch10.Joukowski
