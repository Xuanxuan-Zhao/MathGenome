import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevCompleteness
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.ContinuousMap.Basic

/-!
The first paragraph of `fa2:p3:confining-potential` (paper.tex 16022ff).
The real line is represented in the upstream Sobolev coordinates `Fin 1 → ℝ`;
its coordinate is `x 0`. Scalars range over both ℝ and ℂ. The space is the
actual graph of multiplication by √p over H¹, with the ℓ² product norm.
No coercivity or density certificate is included in its definition.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

attribute [local instance 2000] NormedAddCommGroup.toSeminormedAddCommGroup

namespace ExpandedFA.Models.WeightedConfiningEnergySpace
open ExpandedFA.Sobolev ExpandedFA.Distributions

/-- Exactly the continuous nonnegative potentials on the real line. -/
structure Potential where
  toContinuousMap : C(ℝ, ℝ)
  nonneg : ∀ x, 0 ≤ toContinuousMap x

abbrev Line := Domain 1
abbrev lineMeasure := volume.restrict ((⊤ : Opens Line) : Set Line)
abbrev L2 (𝕜 : Type) [RCLike 𝕜] : Type := DomainLp 𝕜 (⊤ : Opens Line) 2
abbrev H1 (𝕜 : Type) [RCLike 𝕜] : Type := hilbertDerivativeGraph 𝕜 (⊤ : Opens Line) 1
abbrev Ambient (𝕜 : Type) [RCLike 𝕜] := WithLp 2 (H1 𝕜 × L2 𝕜)

def firstIndex : DerivativeIndex 1 1 := ⟨fun _ => 1, by simp⟩

def weight (𝕜 : Type) [RCLike 𝕜] (p : Potential) (x : Line) : 𝕜 :=
  (Real.sqrt (p.toContinuousMap (x 0)) : 𝕜)

/-- No regularity or boundedness of p beyond continuity is assumed. -/
def weightedGraph (𝕜 : Type) [RCLike 𝕜] (p : Potential) : Submodule 𝕜 (Ambient 𝕜) where
  carrier := {z | z.snd =ᵐ[lineMeasure]
    fun x => weight 𝕜 p x * (z.fst.val (zeroIndex 1 1)) x}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero 𝕜 2 lineMeasure] with x hx
    simp
  add_mem' := by
    intro z t hz ht
    filter_upwards [hz, ht, Lp.coeFn_add z.snd t.snd,
      Lp.coeFn_add (z.fst.val (zeroIndex 1 1)) (t.fst.val (zeroIndex 1 1))]
      with x hz ht h₁ h₂
    change (z.snd + t.snd) x = weight 𝕜 p x *
      ((z.fst.val (zeroIndex 1 1) + t.fst.val (zeroIndex 1 1)) : L2 𝕜) x
    simp only [h₁, h₂, Pi.add_apply, hz, ht, mul_add]
  smul_mem' := by
    intro c z hz
    filter_upwards [hz, Lp.coeFn_smul c z.snd,
      Lp.coeFn_smul c (z.fst.val (zeroIndex 1 1))] with x hz h₁ h₂
    change (c • z.snd) x = weight 𝕜 p x *
      ((c • z.fst.val (zeroIndex 1 1)) : L2 𝕜) x
    simp only [h₁, h₂, Pi.smul_apply, hz, smul_eq_mul, mul_left_comm]

abbrev Space (𝕜 : Type) [RCLike 𝕜] (p : Potential) : Type := weightedGraph 𝕜 p

/-- The canonical inherited inner product, recorded explicitly to keep the
normed and seminormed product instances aligned. -/
instance spaceInnerProductSpace (𝕜 : Type) [RCLike 𝕜] (p : Potential) :
    InnerProductSpace 𝕜 (Space 𝕜 p) := (weightedGraph 𝕜 p).innerProductSpace

def value {𝕜 : Type} [RCLike 𝕜] {p : Potential} (u : Space 𝕜 p) : L2 𝕜 :=
  u.val.fst.val (zeroIndex 1 1)
def derivative {𝕜 : Type} [RCLike 𝕜] {p : Potential} (u : Space 𝕜 p) : L2 𝕜 :=
  u.val.fst.val firstIndex
def weighted {𝕜 : Type} [RCLike 𝕜] {p : Potential} (u : Space 𝕜 p) : L2 𝕜 := u.val.snd

/-- Conjugate-linear in the test, linear in the unknown. -/
def energyForm {𝕜 : Type} [RCLike 𝕜] {p : Potential} (v u : Space 𝕜 p) : 𝕜 :=
  ⟪derivative v, derivative u⟫_𝕜 + ⟪weighted v, weighted u⟫_𝕜

def SmoothMembers (𝕜 : Type) [RCLike 𝕜] (p : Potential) : Set (Space 𝕜 p) :=
  {u | ∃ φ : Tests 𝕜 (⊤ : Opens Line), value u =ᵐ[lineMeasure] φ}

/-- The hypothesis in the source, without requiring p to tend to infinity. -/
def PositiveAtInfinity (p : Potential) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → δ ≤ p.toContinuousMap x

end ExpandedFA.Models.WeightedConfiningEnergySpace

namespace Specs.ExpandedFA.Models.WeightedConfiningEnergySpace
open _root_.ExpandedFA.Models.WeightedConfiningEnergySpace
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions

def SpaceType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential), Type

/-- Independent value of the primary type-valued construction. -/
def SpaceValue : SpaceType := fun 𝕜 _ p => Space 𝕜 p

/-- Identifies exactly the H¹ functions with the required weighted L² condition. -/
def Membership : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential) (h : H1 𝕜),
  (∃ u : Space 𝕜 p, u.val.fst = h) ↔
    MemLp (fun x => weight 𝕜 p x * h.val (zeroIndex 1 1) x) 2 lineMeasure

def UnderlyingInjective : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential),
  Function.Injective (value (𝕜 := 𝕜) (p := p))

def Hilbert : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential),
  CompleteSpace (Space 𝕜 p) ∧ SeparableSpace (Space 𝕜 p)

def NormFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential) (u : Space 𝕜 p),
  ‖u‖ ^ 2 = ‖derivative u‖ ^ 2 + ‖value u‖ ^ 2 + ‖weighted u‖ ^ 2

/-- Inner product inherited from the three genuine L² components. -/
def InnerFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential) (v u : Space 𝕜 p),
  ⟪v, u⟫_𝕜 = ⟪derivative v, derivative u⟫_𝕜 +
    ⟪value v, value u⟫_𝕜 + ⟪weighted v, weighted u⟫_𝕜

def SmoothInclusion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential)
  (φ : Tests 𝕜 (⊤ : Opens Line)), ∃ u : Space 𝕜 p, value u =ᵐ[lineMeasure] φ

def SmoothDensity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential),
  Dense (SmoothMembers 𝕜 p)

/-- The potential integral agrees with the weighted L² inner product; in
particular the form is the source's integral, not an unrelated abstract form. -/
def FormIntegral : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential) (v u : Space 𝕜 p),
  Integrable (fun x => conj (derivative v x) * derivative u x +
    (p.toContinuousMap (x 0) : 𝕜) * conj (value v x) * value u x) lineMeasure ∧
  energyForm v u = ∫ x, conj (derivative v x) * derivative u x +
    (p.toContinuousMap (x 0) : 𝕜) * conj (value v x) * value u x ∂lineMeasure

def FormBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential) (v u : Space 𝕜 p),
  ‖energyForm v u‖ ≤ ‖v‖ * ‖u‖

def Coercivity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential),
  PositiveAtInfinity p → ∃ α : ℝ, 0 < α ∧
    ∀ u : Space 𝕜 p, α * ‖u‖ ^ 2 ≤ RCLike.re (energyForm u u)

def VariationalSolvability : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential),
  PositiveAtInfinity p → ∀ f : L2 𝕜, ∃! u : Space 𝕜 p,
    ∀ v : Space 𝕜 p, energyForm v u = ⟪value v, f⟫_𝕜

end Specs.ExpandedFA.Models.WeightedConfiningEnergySpace
