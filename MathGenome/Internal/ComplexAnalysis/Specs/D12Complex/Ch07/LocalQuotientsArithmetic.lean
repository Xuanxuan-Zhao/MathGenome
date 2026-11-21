import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Meromorphic
import Mathlib.Analysis.Meromorphic.NormalForm

/-! Interfaces for the local quotient and filled arithmetic proposition,
paper.tex:1741–1770. Normalization fills removable cancellations. Negative
order, rather than the representative's value, determines a pole. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects
open _root_.D12Complex

/-- The sphere value of a meromorphic germ, with its removable value restored. -/
def fill (f : ℂ → ℂ) (a : ℂ) : RiemannSphere :=
  if meromorphicOrderAt f a < 0 then sphereInfty
  else sphereFinite (toMeromorphicNFAt f a a)

/-- A local quotient uses weak holomorphy and a genuinely nonzero denominator
on a disk. Equality includes all filled values at the denominator's zeros. -/
def LocalQuotientsOn (Ω : Set ℂ) (F : ℂ → RiemannSphere) : Prop :=
  IsOpen Ω ∧ ∀ a ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ Ω ∧
    ∃ p q : ℂ → ℂ, HolomorphicOn (Metric.ball a r) p ∧
      HolomorphicOn (Metric.ball a r) q ∧
      ¬ EqOn q (fun _ => 0) (Metric.ball a r) ∧
      EqOn F (fill (p / q)) (Metric.ball a r)

/-- Arithmetic is applied to punctured representatives and then filled. -/
def add (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F + scalarFinitePart G)
def neg (F : ℂ → RiemannSphere) := fill (-scalarFinitePart F)
def sub (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F - scalarFinitePart G)
def mul (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F * scalarFinitePart G)
def inv (F : ℂ → RiemannSphere) := fill (scalarFinitePart F)⁻¹
def div (F G : ℂ → RiemannSphere) := fill (scalarFinitePart F / scalarFinitePart G)

/-- Actual scalar functions on Ω, represented with the fixed value zero outside Ω.
The outside normalization makes equality exactly equality on Ω. -/
def ScalarFunction (Ω : Set ℂ) :=
  {F : ℂ → RiemannSphere // ScalarMeromorphicOn Ω F ∧
    ∀ a ∉ Ω, F a = sphereFinite 0}

end Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects

namespace Specs.D12Complex.Ch07.LocalQuotientsArithmetic
open _root_.D12Complex
open Objects

def fill_type := (ℂ → ℂ) → ℂ → RiemannSphere
def fill_value : fill_type := fun f a =>
  if meromorphicOrderAt f a < 0 then sphereInfty
  else sphereFinite (toMeromorphicNFAt f a a)

def LocalQuotientsOn_type := Set ℂ → (ℂ → RiemannSphere) → Prop
def LocalQuotientsOn_value : LocalQuotientsOn_type := fun Ω F =>
  IsOpen Ω ∧ ∀ a ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ Ω ∧
    ∃ p q : ℂ → ℂ, HolomorphicOn (Metric.ball a r) p ∧
      HolomorphicOn (Metric.ball a r) q ∧
      ¬ EqOn q (fun _ => 0) (Metric.ball a r) ∧
      EqOn F (fill (p / q)) (Metric.ball a r)

def scalar_meromorphicAt_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
    ∀ a ∈ Ω, MeromorphicAt (scalarFinitePart F) a

def fill_congr_type : Prop :=
  ∀ (f g : ℂ → ℂ) (a : ℂ), f =ᶠ[𝓝[≠] a] g → fill f a = fill g a

def scalar_eq_fill_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
    EqOn F (fill (scalarFinitePart F)) Ω

def scalar_order_mul_germ_type : Prop :=
  ∀ (Ω : Set ℂ) (F G : ℂ → RiemannSphere),
    ScalarMeromorphicOn Ω F → ScalarMeromorphicOn Ω G →
    ∀ a ∈ Ω, ∀ m n : ℤ, scalarSignedOrder F a = some m →
      scalarSignedOrder G a = some n →
      meromorphicOrderAt (scalarFinitePart F * scalarFinitePart G) a = some (m + n)

def scalar_order_div_germ_type : Prop :=
  ∀ (Ω : Set ℂ) (F G : ℂ → RiemannSphere),
    ScalarMeromorphicOn Ω F → ScalarMeromorphicOn Ω G →
    ∀ a ∈ Ω, ∀ m n : ℤ, scalarSignedOrder F a = some m →
      scalarSignedOrder G a = some n →
      meromorphicOrderAt (scalarFinitePart F / scalarFinitePart G) a = some (m - n)


/-- The field uses the displayed filled operations on actual functions on Ω.
A fixed zero extension outside Ω avoids quotienting by irrelevant values. -/
def field_exists_type : Prop := ∀ Ω : Set ℂ, IsDomain Ω →
  ∃ I : Field (ScalarFunction Ω), (letI := I;
    EqOn (0 : ScalarFunction Ω).val (fun _ => sphereFinite 0) Ω ∧
    EqOn (1 : ScalarFunction Ω).val (fun _ => sphereFinite 1) Ω ∧
    (∀ F G : ScalarFunction Ω, EqOn (F + G).val (add F.val G.val) Ω) ∧
    (∀ F G : ScalarFunction Ω, EqOn (F * G).val (mul F.val G.val) Ω) ∧
    (∀ F : ScalarFunction Ω, EqOn (-F).val (neg F.val) Ω) ∧
    (∀ F : ScalarFunction Ω, EqOn (F⁻¹).val (inv F.val) Ω) ∧
    (∀ F G : ScalarFunction Ω, EqOn (F - G).val (sub F.val G.val) Ω) ∧
    (∀ F G : ScalarFunction Ω, EqOn (F / G).val (div F.val G.val) Ω))


def add_type := (ℂ → RiemannSphere) → (ℂ → RiemannSphere) → ℂ → RiemannSphere
def add_value : add_type := fun F G => fill (scalarFinitePart F + scalarFinitePart G)

def neg_type := (ℂ → RiemannSphere) → ℂ → RiemannSphere
def neg_value : neg_type := fun F => fill (-scalarFinitePart F)

def sub_type := (ℂ → RiemannSphere) → (ℂ → RiemannSphere) → ℂ → RiemannSphere
def sub_value : sub_type := fun F G => fill (scalarFinitePart F - scalarFinitePart G)

def mul_type := (ℂ → RiemannSphere) → (ℂ → RiemannSphere) → ℂ → RiemannSphere
def mul_value : mul_type := fun F G => fill (scalarFinitePart F * scalarFinitePart G)

def inv_type := (ℂ → RiemannSphere) → ℂ → RiemannSphere
def inv_value : inv_type := fun F => fill ((scalarFinitePart F)⁻¹)

def div_type := (ℂ → RiemannSphere) → (ℂ → RiemannSphere) → ℂ → RiemannSphere
def div_value : div_type := fun F G => fill (scalarFinitePart F / scalarFinitePart G)

def ScalarFunction_type := Set ℂ → Type
def ScalarFunction_value : ScalarFunction_type := fun Ω => {F : ℂ → RiemannSphere // ScalarMeromorphicOn Ω F ∧ ∀ a ∉ Ω, F a = sphereFinite 0}

def scalarMeromorphicOn_fill_type : Prop :=
  ∀ (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ)
    (hf : MeromorphicOn f Ω),
  ScalarMeromorphicOn Ω (fill f)

def scalar_iff_filled_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere),
  ScalarMeromorphicOn Ω F ↔ IsOpen Ω ∧ MeromorphicOn (scalarFinitePart F) Ω ∧
      EqOn F (fill (scalarFinitePart F)) Ω

def scalar_iff_localQuotients_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere),
  ScalarMeromorphicOn Ω F ↔ LocalQuotientsOn Ω F

def arithmetic_closed_type : Prop :=
  ∀ (Ω : Set ℂ) (F G : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) (hG : ScalarMeromorphicOn Ω G),
  ScalarMeromorphicOn Ω (add F G) ∧ ScalarMeromorphicOn Ω (neg F) ∧
    ScalarMeromorphicOn Ω (sub F G) ∧ ScalarMeromorphicOn Ω (mul F G) ∧
    ScalarMeromorphicOn Ω (inv F) ∧ ScalarMeromorphicOn Ω (div F G)

def signedOrder_mul_div_type : Prop :=
  ∀ (Ω : Set ℂ) (F G : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) (hG : ScalarMeromorphicOn Ω G)
    (a : ℂ) (ha : a ∈ Ω) (m n : ℤ)
    (hm : scalarSignedOrder F a = some m) (hn : scalarSignedOrder G a = some n),
  scalarSignedOrder (mul F G) a = some (m + n) ∧
    scalarSignedOrder (div F G) a = some (m - n)

def signedOrder_rules_type : Prop :=
  ∀ (Ω : Set ℂ) (F G : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F) (hG : ScalarMeromorphicOn Ω G)
    (a : ℂ) (ha : a ∈ Ω) (hf0 : ¬ scalarZeroGerm F a) (hg0 : ¬ scalarZeroGerm G a),
  ∃ m n : ℤ, scalarSignedOrder F a = some m ∧ scalarSignedOrder G a = some n ∧
      scalarSignedOrder (mul F G) a = some (m + n) ∧
      scalarSignedOrder (div F G) a = some (m - n)

def finite_order_of_componentwise_nonzero_type : Prop :=
  ∀ {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F)
    (hn : ∀ a ∈ Ω, ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a))
    (a : ℂ) (ha : a ∈ Ω),
  meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤

def reciprocal_law_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F)
    (hn : ∀ a ∈ Ω, ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a)),
  ScalarMeromorphicOn Ω (inv F) ∧ EqOn (mul F (inv F)) (fun _ => sphereFinite 1) Ω

def local_arithmetic_formulas_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (hr : 0 < r)
    (F G : ℂ → RiemannSphere) (p q u v : ℂ → ℂ)
    (hp : HolomorphicOn (Metric.ball a r) p) (hq : HolomorphicOn (Metric.ball a r) q)
    (hu : HolomorphicOn (Metric.ball a r) u) (hv : HolomorphicOn (Metric.ball a r) v)
    (hq0 : ¬ EqOn q (fun _ => 0) (Metric.ball a r))
    (hv0 : ¬ EqOn v (fun _ => 0) (Metric.ball a r))
    (hF : EqOn F (fill (p / q)) (Metric.ball a r))
    (hG : EqOn G (fill (u / v)) (Metric.ball a r)),
  ¬ EqOn (q * v) (fun _ => 0) (Metric.ball a r) ∧
    EqOn (add F G) (fill ((p * v + u * q) / (q * v))) (Metric.ball a r) ∧
    EqOn (sub F G) (fill ((p * v - u * q) / (q * v))) (Metric.ball a r) ∧
    EqOn (mul F G) (fill ((p * u) / (q * v))) (Metric.ball a r)

def local_reciprocal_formula_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (F : ℂ → RiemannSphere)
    (p q : ℂ → ℂ) (hp : HolomorphicOn (Metric.ball a r) p)
    (hq : HolomorphicOn (Metric.ball a r) q)
    (hF : EqOn F (fill (p / q)) (Metric.ball a r)),
  EqOn (inv F) (fill (q / p)) (Metric.ball a r)

def scalarFunction_restrict_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn Ω F),
  ∃ G : ScalarFunction Ω, EqOn G.val F Ω

def scalarFunction_ext_type : Prop :=
  ∀ (Ω : Set ℂ) (F G : ScalarFunction Ω),
  EqOn F.val G.val Ω ↔ F = G

end Specs.D12Complex.Ch07.LocalQuotientsArithmetic
