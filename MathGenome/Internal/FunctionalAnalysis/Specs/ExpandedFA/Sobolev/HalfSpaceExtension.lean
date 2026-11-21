import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Even reflection on the coordinate upper half-space from
`fa2:p4:sobolev-extension`. Boundary values are assigned zero in the raw
formula; only almost-everywhere classes are used. The same formula is used
for every exponent, including infinity, and over both scalar fields. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions

/-- The chosen normal coordinate exists only in positive dimension. -/
def upper {d : ℕ} (i : Fin d) : Opens (Domain d) :=
  ⟨{x | 0 < x i}, isOpen_lt continuous_const (continuous_apply i)⟩

/-- Reflection in the boundary hyperplane. -/
def reflect {d : ℕ} (i : Fin d) (x : Domain d) : Domain d :=
  fun j => if j = i then -x j else x j

/-- Odd reflection is used for the normal weak derivative; even reflection
is used for the function and for all tangential weak derivatives. -/
def reflection {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (i : Fin d) (odd : Bool)
    (f : Domain d → 𝕜) (x : Domain d) : 𝕜 :=
  (upper i : Set (Domain d)).indicator f x +
    if odd then -((upper i : Set (Domain d)).indicator f (reflect i x))
    else (upper i : Set (Domain d)).indicator f (reflect i x)

/-- The normal derivative is the only degree-one multi-index that is odd. -/
def normalParity {d : ℕ} (i : Fin d) (α : DerivativeIndex d 1) : Bool :=
  decide (natIndex α i = 1)

/-- At p = infinity, toReal infinity = 0, so this factor is one. -/
def reflectionFactor (p : ℝ≥0∞) : ℝ := (2 : ℝ) ^ (1 / p.toReal)

/-- An affine coordinate map on the manuscript's Euclidean domain. -/
def affineMap {d : ℕ} (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (x : Domain d) : Domain d := A x + b

/-- Pullback of an open domain under affine coordinates. -/
def affinePreimage {d : ℕ} (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (Ω : Opens (Domain d)) : Opens (Domain d) :=
  ⟨affineMap A b ⁻¹' (Ω : Set (Domain d)),
    Ω.isOpen.preimage (A.continuous.add continuous_const)⟩

/-- Every affine half-space with a nonzero normal is included in the theorem. -/
def affineHalfSpace {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : Opens (Domain d) :=
  ⟨{x | c < ∑ j, a j * x j}, isOpen_lt continuous_const
    (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))⟩

/-- The degree-one index in the j-th coordinate. -/
def affineCoordinateIndex {d : ℕ} (j : Fin d) : DerivativeIndex d 1 :=
  ⟨Pi.single j 1, by
    classical
    have h : (fun k => ((Pi.single j (1 : Fin 2) : Fin d → Fin 2) k).val) = (Pi.single j 1 : Fin d → ℕ) := by
      funext k
      by_cases hk : k = j <;> simp [Pi.single_apply, hk]
    rw [h]
    simp⟩

/-- A chart-independent bound for the sum norm of a pulled back first jet.
No exponent occurs in this constant. -/
def affineJetBound {d : ℕ} (A : Domain d ≃L[ℝ] Domain d) : ℝ :=
  Fintype.card (DerivativeIndex d 1) * (1 + ∑ j, ∑ k, |A (coordinateVector j) k|)

end ExpandedFA.Sobolev.HalfSpace

namespace Specs.ExpandedFA.Sobolev.HalfSpaceExtension
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.HalfSpace

/-- Lp well-definedness must hold at both endpoints as well. -/
def ReflectionMemLp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool) (u : DomainLp 𝕜 (upper i) p),
  MemLp (reflection i odd u) p volume

/-- The finite-p power integral doubles, also for the odd normal component. -/
def ReflectionIntegral : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool) (u : DomainLp 𝕜 (upper i) p)
  (q : ℝ) (hq : 0 < q),
  (∫⁻ x, ‖reflection i odd u x‖ₑ ^ q) =
    2 * ∫⁻ x in (upper i : Set (Domain d)), ‖u x‖ₑ ^ q

/-- One norm formula includes p=infinity without a density argument. -/
def ReflectionNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool) (u : DomainLp 𝕜 (upper i) p),
  eLpNorm (reflection i odd u) p volume =
    (2 : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm u p (volume.restrict (upper i : Set (Domain d)))

/-- The boundary compatibility obligation: reflecting a function evenly and
its weak derivatives with the appropriate sign creates no boundary measure.
The representatives on the full space are arbitrary Lp classes with the stated
a.e. formulas, so no choice of boundary values is built into this statement. -/
def WeakReflection : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 (upper i) p)
  (g : Fin d → DomainLp 𝕜 (upper i) p),
  _root_.ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives u g →
  ∀ (v : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (h : Fin d → DomainLp 𝕜 (⊤ : Opens (Domain d)) p),
    (v =ᵐ[volume] reflection i false u) →
    (∀ j, h j =ᵐ[volume] reflection i (decide (j = i)) (g j)) →
    _root_.ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives v h

/-- Full required extension statement on the upper half-space. The derivative
rule is on the actual canonical graph, not an auxiliary choice of derivatives.
Its raw formula is independent of p. The component power integrals and the
infinity estimates are included explicitly. -/
def ExtensionExists : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
  (p : ℝ≥0∞) [Fact (1 ≤ p)],
  ∃ E : WeakDerivativeSpaces.SpaceValue 𝕜 d (upper i) 1 p →L[𝕜]
      WeakDerivativeSpaces.SpaceValue 𝕜 d ⊤ 1 p,
    (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume]
      reflection i false (u.val (zeroIndex d 1))) ∧
    (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
      u.val (zeroIndex d 1)) ∧
    (∀ u α, (E u).val α =ᵐ[volume]
      reflection i (normalParity i α) (u.val α)) ∧
    (∀ u, ‖E u‖ = reflectionFactor p * ‖u‖) ∧
    ‖E‖ ≤ reflectionFactor p ∧
    (p ≠ ∞ → ∀ u α,
      (∫⁻ x, ‖(E u).val α x‖ₑ ^ p.toReal) =
        2 * ∫⁻ x in (upper i : Set (Domain d)), ‖u.val α x‖ₑ ^ p.toReal) ∧
    (p = ∞ → ∀ u α, eLpNorm ((E u).val α) ∞ volume =
      eLpNorm (u.val α) ∞ (volume.restrict (upper i : Set (Domain d))))

/-- The affine bridge acts on the original canonical graph and includes the
actual weak chain rule. Volume-preserving affine coordinates suffice for all
half-spaces. In particular this proposition includes p = infinity directly. -/
def AffinePullback : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
  (hA : MeasurePreserving (affineMap A b) volume volume)
  (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  ∃ P : WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p →L[𝕜]
      WeakDerivativeSpaces.SpaceValue 𝕜 d (affinePreimage A b Ω) 1 p,
    (∀ u, (P u).val (zeroIndex d 1) =ᵐ[volume.restrict
      (affinePreimage A b Ω : Set (Domain d))]
      fun x => u.val (zeroIndex d 1) (affineMap A b x)) ∧
    (∀ u (j : Fin d), (P u).val (affineCoordinateIndex j) =ᵐ[volume.restrict
      (affinePreimage A b Ω : Set (Domain d))]
      fun x => ∑ k, (A (coordinateVector j) k) •
        u.val (affineCoordinateIndex k) (affineMap A b x)) ∧
    ‖P‖ ≤ affineJetBound A

/-- A single affine coordinate choice gives the extension formula for both
scalar fields and every exponent, including infinity. The normal may be tilted
and the boundary hyperplane need not pass through the origin. The quantitative
bound uses the manuscript's sum norm, which need not be rotation invariant. -/
def AffineExtensionExists : Prop := ∀ (d : ℕ) (a : Fin d → ℝ) (ha : a ≠ 0) (c : ℝ),
  ∃ (i : Fin d) (A : Domain d ≃L[ℝ] Domain d) (b : Domain d),
    MeasurePreserving (affineMap A b) volume volume ∧
    affinePreimage A b (upper i) = affineHalfSpace a c ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ E : WeakDerivativeSpaces.SpaceValue 𝕜 d (affineHalfSpace a c) 1 p →L[𝕜]
        WeakDerivativeSpaces.SpaceValue 𝕜 d ⊤ 1 p,
      (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume]
        fun x => reflection i false
          (fun y => u.val (zeroIndex d 1) (A.symm (y - b))) (affineMap A b x)) ∧
      (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume.restrict
        (affineHalfSpace a c : Set (Domain d))] u.val (zeroIndex d 1)) ∧
      ‖E‖ ≤ affineJetBound A * reflectionFactor p * affineJetBound A.symm

end Specs.ExpandedFA.Sobolev.HalfSpaceExtension
