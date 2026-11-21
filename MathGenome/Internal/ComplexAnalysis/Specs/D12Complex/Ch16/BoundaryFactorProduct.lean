import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.CanonicalFactors
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.HolomorphicProducts
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Boundary factors in the proof of D12.16.05, paper.tex:2808–2818.
A sequence is indexed from zero; its n-th factor is E_(n+1), corresponding
exactly to the source's indexing from one. Local finiteness counts indices,
so repeated points retain their prescribed finite multiplicities. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace Specs.D12Complex.Ch16.BoundaryFactorProduct
open _root_.D12Complex

def Admissible_type := Set ℂ → (ℕ → ℂ) → Prop
def Admissible_value : Admissible_type := fun G z =>
  IsOpen G ∧ (∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, R < ‖w‖ → w ∈ G) ∧
  IsCompact Gᶜ ∧ Gᶜ.Nonempty ∧ Bornology.IsBounded (range z) ∧
  (∀ n, z n ∈ G) ∧
  (∀ K : Set ℂ, IsCompact K → K ⊆ G → {n : ℕ | z n ∈ K}.Finite)

def Nearest_type := Set ℂ → (ℕ → ℂ) → (ℕ → ℂ) → Prop
def Nearest_value : Nearest_type := fun G z b =>
  ∀ n, b n ∈ Gᶜ ∧ dist (z n) (b n) = infDist (z n) Gᶜ

def boundaryFactor_type := (ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℂ → ℂ
def boundaryFactor_value : boundaryFactor_type := fun z b n w =>
  CanonicalFactors.factor_value (n+1) ((z n - b n) / (w - b n))
def product_type := (ℕ → ℂ) → (ℕ → ℂ) → ℂ → ℂ
def product_value : product_type := fun z b w => ∏' n, boundaryFactor_value z b n w

def exists_nearest_type : Prop :=
  ∀ G z, Admissible_value G z → ∃ b, Nearest_value G z b

def distances_tendsto_zero_type : Prop :=
  ∀ G z, Admissible_value G z → Tendsto (fun n => infDist (z n) Gᶜ) atTop (𝓝 0)

def nearest_distances_tendsto_zero_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b →
    Tendsto (fun n => ‖z n - b n‖) atTop (𝓝 0)

def nearest_bounded_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b → Bornology.IsBounded (range b)

def normal_product_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b →
    HolomorphicProducts.NormalProductCondition_value G (boundaryFactor_value z b)

def product_holomorphic_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b →
    TendstoLocallyUniformlyOn (fun N w => ∏ n ∈ Finset.range N, boundaryFactor_value z b n w)
      (product_value z b) atTop G ∧ HolomorphicOn G (product_value z b)

def product_zeros_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b →
    ∀ a ∈ G, (product_value z b a = 0 ↔ ∃ n, z n = a)

def product_multiplicity_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b → ∀ a ∈ G,
    {n : ℕ | z n = a}.Finite ∧
    analyticOrderAt (product_value z b) a = ∑' n : ℕ, (if z n = a then 1 else 0 : ℕ∞) ∧
    analyticOrderAt (product_value z b) a ≠ ⊤

/-- Uniform exterior limit of the full product, not limits of individual factors. -/
def product_limit_at_infinity_type : Prop :=
  ∀ G z b, Admissible_value G z → Nearest_value G z b →
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ w : ℂ, R < ‖w‖ → w ∈ G ∧ ‖product_value z b w - 1‖ < ε
end Specs.D12Complex.Ch16.BoundaryFactorProduct
