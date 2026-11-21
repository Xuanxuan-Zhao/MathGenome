import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertBesselParseval

/-!
Independent statements for paper.tex 7465–7486, arbitrary orthonormal bases.
Maximality means maximality of the range among orthonormal subsets, not
maximality among families with a fixed index type. All index types are allowed.
The separate cardinality/unitary classification is allocated to
HilbertCardinalityClassification. The partial sums are the shared conjugate-first
Fourier sums; HasSum and the explicit Tendsto statements use all finite subsets.
-/

noncomputable section
open scoped InnerProductSpace
open Filter Topology

namespace ExpandedFA.Hilbert.OrthonormalExpansion.Spec
universe u v w

def IsMaximalOrthonormalType :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], (ι → H) → Prop

def IsMaximalOrthonormalValue : IsMaximalOrthonormalType.{u, v, w} :=
  fun 𝕜 H _ _ _ _ e => Orthonormal 𝕜 e ∧
    ∀ S : Set H, Set.range e ⊆ S →
      Orthonormal 𝕜 (Subtype.val : S → H) → S = Set.range e

def ExistsMaximalOrthonormalSubset : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ∃ S : Set H, IsMaximalOrthonormalValue 𝕜 H S (Subtype.val : S → H)

def ExistsMaximalOrthonormalFamily : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ∃ (ι : Type v) (e : ι → H), IsMaximalOrthonormalValue 𝕜 H ι e

def MaximalIffTotal : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H), Orthonormal 𝕜 e →
    (IsMaximalOrthonormalValue 𝕜 H ι e ↔
      (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤)

def Expansion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H), IsMaximalOrthonormalValue 𝕜 H ι e → ∀ x : H,
    HasSum (fun i => ⟪e i, x⟫_𝕜 • e i) x ∧
      x = ∑' i, ⟪e i, x⟫_𝕜 • e i

def FiniteSubsetNetExpansion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H), IsMaximalOrthonormalValue 𝕜 H ι e → ∀ x : H,
    Tendsto (PreHilbertBesselParseval.fourierPartialSum 𝕜 e x) atTop (𝓝 x)

def Parseval : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H), IsMaximalOrthonormalValue 𝕜 H ι e → ∀ x : H,
    HasSum (fun i => ‖⟪e i, x⟫_𝕜‖ ^ 2) (‖x‖ ^ 2) ∧
      ‖x‖ ^ 2 = ∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2

/-- Countability holds even for a nonmaximal family in an incomplete space. -/
def CountableCoefficientSupport : Prop :=
  PreHilbertBesselParseval.Spec.CountableCoefficientSupport.{u, v, w}

/-- An empty index type gives a basis exactly for the zero space. -/
def EmptyBasisIffZero : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [IsEmpty ι] (e : ι → H),
    IsMaximalOrthonormalValue 𝕜 H ι e ↔ Subsingleton H

/-- Every orthonormal family in finite dimension has finite index type. -/
def FiniteIndexInFiniteDimension : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    (e : ι → H), Orthonormal 𝕜 e → Finite ι

def ExistsFiniteBasis : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [FiniteDimensional 𝕜 H],
    ∃ S : Set H, S.Finite ∧ IsMaximalOrthonormalValue 𝕜 H S (Subtype.val : S → H)

/-- On finite bases the net formulas specialize to ordinary finite sums. -/
def FiniteExpansionAndParseval : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Fintype ι] (e : ι → H), IsMaximalOrthonormalValue 𝕜 H ι e → ∀ x : H,
    x = ∑ i, ⟪e i, x⟫_𝕜 • e i ∧ ‖x‖ ^ 2 = ∑ i, ‖⟪e i, x⟫_𝕜‖ ^ 2

end ExpandedFA.Hilbert.OrthonormalExpansion.Spec
