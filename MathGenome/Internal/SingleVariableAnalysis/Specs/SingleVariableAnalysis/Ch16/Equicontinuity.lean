import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.SupSpace
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
Independent specification of K03.16.equicontinuity (paper.tex:3831–3840).
The family consists of canonical continuous maps on a real subset, equipped
with its induced metric. Instantiating `E` with ℝ or ℂ gives precisely the
two scalar cases of the manuscript; the same statements make sense for any
normed additive commutative group. No scalar order is used.

The nonnegative real bound formulation means a finite common bound, including
empty families and empty domains. It does not use the total real `sSup` of an
empty or unbounded set. A pointwise bound may depend on the domain point;
a uniform bound and a uniform equicontinuity radius may not.
-/
namespace Specs.SingleVariableAnalysis.Ch16.Equicontinuity

universe u


def pointwiseEquicontinuousFamilyType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E], (K : Set ℝ) → Set C(K, E) → Prop

def pointwiseEquicontinuousFamilyValue : pointwiseEquicontinuousFamilyType :=
  fun {_E} _ K F => ∀ x : K, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ y : K, dist y x < δ → ∀ f ∈ F, ‖f y - f x‖ < ε

def uniformlyEquicontinuousFamilyType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E], (K : Set ℝ) → Set C(K, E) → Prop

def uniformlyEquicontinuousFamilyValue : uniformlyEquicontinuousFamilyType :=
  fun {_E} _ K F => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : K, dist x y < δ → ∀ f ∈ F, ‖f x - f y‖ < ε

def pointwiseBoundedFamilyType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E], (K : Set ℝ) → Set C(K, E) → Prop

def pointwiseBoundedFamilyValue : pointwiseBoundedFamilyType :=
  fun {_E} _ K F => ∀ x : K, ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ F, ‖f x‖ ≤ M

def uniformlyBoundedFamilyType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E], (K : Set ℝ) → Set C(K, E) → Prop

def uniformlyBoundedFamilyValue : uniformlyBoundedFamilyType :=
  fun {_E} _ K F => ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ F, ∀ x : K, ‖f x‖ ≤ M

/-- Bridges specify the meaning of the indexed Mathlib predicates as well. -/
def pointwiseEquicontinuousFamilyIff : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E], ∀ (K : Set ℝ) (F : Set C(K, E)),
    pointwiseEquicontinuousFamilyValue K F ↔ Equicontinuous (fun f : F => (f.val : K → E))

def uniformlyEquicontinuousFamilyIff : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E], ∀ (K : Set ℝ) (F : Set C(K, E)),
    uniformlyEquicontinuousFamilyValue K F ↔
      UniformEquicontinuous (fun f : F => (f.val : K → E))

def compactUniformEquicontinuity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E], ∀ (K : Set ℝ), IsCompact K → ∀ F : Set C(K, E),
    pointwiseEquicontinuousFamilyValue K F → uniformlyEquicontinuousFamilyValue K F

def compactUniformBoundedness : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E], ∀ (K : Set ℝ), IsCompact K → ∀ F : Set C(K, E),
    pointwiseEquicontinuousFamilyValue K F → pointwiseBoundedFamilyValue K F →
      uniformlyBoundedFamilyValue K F

end Specs.SingleVariableAnalysis.Ch16.Equicontinuity
