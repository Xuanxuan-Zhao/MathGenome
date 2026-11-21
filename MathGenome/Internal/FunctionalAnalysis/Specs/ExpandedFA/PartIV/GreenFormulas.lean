import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent scope of the two Green identities in `fa2:p4:second-trace`.
The separate second-jet surjectivity assertion is allocated to SecondTrace.
All derivatives below are components of the shared distributional graph;
boundary integrals use the shared, normalized Euclidean surface measure.
The existence of a geometric outward normal and of an actual L² trace is
included in the conclusion, rather than assumed as an analytic certificate. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ExpandedFA.PartIV.GreenFormulas
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- C² boundary charts with the same geometric convention as IsC1Domain. -/
def IsC2Domain {d : ℕ} (Ω : Opens (Domain d)) : Prop :=
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
      x ∈ Φ.source ∧ Φ x i = 0 ∧
      ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
      ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i

/-- A coordinate weakPartial of an ambient real defining function. -/
def definingPartial {d : ℕ} (r : Domain d → ℝ) (j : Fin d) (x : Domain d) : ℝ :=
  fderiv ℝ r x (coordinateVector j)

/-- The outward normal is the normalized gradient of a local defining
function negative on the domain. Measurability and the coordinate bound
are included in the construction obligation, not postulated of Ω.
Only surface-a.e. values matter, and dimension zero is retained. -/
def IsOutwardUnitNormal {d : ℕ} (Ω : Opens (Domain d))
    (ν : Fin d → Domain d → ℝ) : Prop :=
  (∀ j, AEStronglyMeasurable (ν j) (surfaceMeasure Ω)) ∧
  (∀ j, ∀ᵐ x ∂surfaceMeasure Ω, |ν j x| ≤ 1) ∧
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (U : Opens (Domain d)) (r : Domain d → ℝ),
      x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      0 < ∑ k, (definingPartial r k x) ^ 2 ∧
      ∀ j, ν j x = definingPartial r j x /
        Real.sqrt (∑ k, (definingPartial r k x) ^ 2)

/-- A canonical bounded multi-index, also usable without any candidate module. -/
def indexOfNat {d m : ℕ} (a : Fin d → ℕ) (ha : (∑ j, a j) ≤ m) :
    DerivativeIndex d m :=
  ⟨fun j => ⟨a j, Nat.lt_succ_of_le
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans ha)⟩,
    ha⟩

def firstIndex {d m : ℕ} (hm : 1 ≤ m) (j : Fin d) : DerivativeIndex d m :=
  indexOfNat (Pi.single j 1) (by classical simpa using hm)

def secondIndex {d : ℕ} (j k : Fin d) : DerivativeIndex d 2 :=
  indexOfNat (fun i => (Pi.single j 1 : Fin d → ℕ) i + (Pi.single k 1 : Fin d → ℕ) i)
    (by classical simp [Finset.sum_add_distrib])

abbrev H1 (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  SpaceValue 𝕜 d Ω 1 2
abbrev H2 (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  SpaceValue 𝕜 d Ω 2 2

abbrev value {𝕜 : Type} [RCLike 𝕜] {d m : ℕ} {Ω : Opens (Domain d)}
    (u : SpaceValue 𝕜 d Ω m 2) := u.val (zeroIndex d m)
abbrev weakPartial {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : H1 𝕜 Ω) (j : Fin d) := u.val (firstIndex (by rfl) j)

/-- Compatibility identifies the H¹ derivatives of an H² element with its
already prescribed first and second weak derivatives, including mixed ones. -/
def IsDerivativeFamily {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : H2 𝕜 Ω) (g : Fin d → H1 𝕜 Ω) : Prop :=
  (∀ j, value (g j) = u.val (firstIndex (by decide) j)) ∧
  ∀ j k, weakPartial (g j) k = u.val (secondIndex j k)

/-- The weak Laplacian, without replacing u by a smooth representative. -/
def laplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : H2 𝕜 Ω) : Domain d → 𝕜 := fun x => ∑ j, u.val (secondIndex j j) x

/-- The normal derivative is the contraction of the L² traces of all weak
first derivatives with the outward real normal. -/
def normalDerivative {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2)
    (ν : Fin d → Domain d → ℝ) (g : Fin d → H1 𝕜 Ω) : Domain d → 𝕜 :=
  fun x => ∑ j, (T (g j)) x * (ν j x : 𝕜)

/-- The source's first-order identity, with both conjugations explicit. -/
def FirstIdentity {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2)
    (ν : Fin d → Domain d → ℝ) (u v : H1 𝕜 Ω) (j : Fin d) : Prop :=
  (∫ x in (Ω : Set (Domain d)),
    value u x * conj (weakPartial v j x) + weakPartial u j x * conj (value v x)) =
  ∫ x, (T u) x * conj ((T v) x) * (ν j x : 𝕜) ∂surfaceMeasure Ω

/-- The source's second identity. The gradient product is the finite
coordinate sum, and the normal derivative uses precisely the same trace. -/
def SecondIdentity {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2)
    (ν : Fin d → Domain d → ℝ) (u : H2 𝕜 Ω) (v : H1 𝕜 Ω)
    (g : Fin d → H1 𝕜 Ω) : Prop :=
  -(∫ x in (Ω : Set (Domain d)), laplacian u x * conj (value v x)) =
  (∫ x in (Ω : Set (Domain d)),
    ∑ j, u.val (firstIndex (by decide) j) x * conj (weakPartial v j x)) -
  ∫ x, normalDerivative T ν g x * conj ((T v) x) ∂surfaceMeasure Ω

end ExpandedFA.PartIV.GreenFormulas

namespace Specs.ExpandedFA.PartIV.GreenFormulas
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev.Trace
open _root_.ExpandedFA.PartIV.GreenFormulas

/-- Trace and normal existence make the identity a statement about actual
boundary data, including empty and zero-dimensional domains. -/
def FirstOrderGreen : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
    (∃ ν, IsOutwardUnitNormal Ω ν) ∧
    (∃! T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2, IsTrace T) ∧
    ∀ (ν : Fin d → Domain d → ℝ), IsOutwardUnitNormal Ω ν →
    ∀ (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2), IsTrace T →
    ∀ (u v : H1 𝕜 Ω) (j : Fin d), FirstIdentity T ν u v j

/-- No H² boundary density is assumed: derivative representatives and the
second identity are conclusions for every element of the shared H² graph. -/
def SecondGreen : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
    ∀ (ν : Fin d → Domain d → ℝ), IsOutwardUnitNormal Ω ν →
    ∀ (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2), IsTrace T →
    ∀ (u : H2 𝕜 Ω) (v : H1 𝕜 Ω),
      ∃ g, IsDerivativeFamily u g ∧ SecondIdentity T ν u v g

end Specs.ExpandedFA.PartIV.GreenFormulas
