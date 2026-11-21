import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Separation.CompletelyRegular

/-! Characters in concrete function algebras, paper.tex:9958–10015.
The character carrier is the shared algebraic nonzero multiplicative complex
linear functionals. Its topology is the initial topology of all evaluations.
No local compactness, measurability, or nonemptiness assumption is imposed. -/
noncomputable section
open scoped BoundedContinuousFunction
namespace ExpandedFA.BanachAlgebra.StoneCech.Spec
universe u v

abbrev Space (S : Type u) [TopologicalSpace S] :=
  Specs.ExpandedFA.BanachAlgebra.Conventions.CharacterValue ℂ (S →ᵇ ℂ)

instance (S : Type u) [TopologicalSpace S] : TopologicalSpace (Space S) :=
  Specs.ExpandedFA.BanachAlgebra.Characters.CharacterTopologyValue (S →ᵇ ℂ)

/-- Point evaluation, with its original algebraic character laws. -/
def evaluation {S : Type u} [TopologicalSpace S] (x : S) : Space S :=
  ⟨{ toFun := fun f => f x
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl }, by
    refine ⟨?_, fun _ _ => rfl⟩
    intro h
    have hh := LinearMap.congr_fun h (1 : S →ᵇ ℂ)
    exact one_ne_zero hh⟩

/-- The Gelfand transform, on the actual character space. -/
def gelfandExtension {S : Type u} [TopologicalSpace S] (f : S →ᵇ ℂ) :
    C(Space S, ℂ) :=
  ⟨fun χ => χ.val f,
    (continuous_apply f).comp continuous_induced_dom⟩

def CompactHausdorff : Prop :=
  ∀ (S : Type u) [TopologicalSpace S], CompactSpace (Space S) ∧ T2Space (Space S)

def NativeIdentification : Prop :=
  ∀ (S : Type u) [TopologicalSpace S],
    ∃ e : _root_.StoneCech S ≃ₜ Space S,
      ∀ x : S, e (stoneCechUnit x) = evaluation x

def EvaluationDenseEmbedding : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [CompletelyRegularSpace S] [T2Space S],
    Topology.IsEmbedding (evaluation : S → Space S) ∧
      DenseRange (evaluation : S → Space S)

def ScalarExtension : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [CompletelyRegularSpace S] [T2Space S]
    (f : S →ᵇ ℂ),
    (∀ x : S, gelfandExtension f (evaluation x) = f x) ∧
    ∀ F : C(Space S, ℂ), (∀ x : S, F (evaluation x) = f x) → F = gelfandExtension f

/-- Each continuous map into any compact Hausdorff space extends uniquely.
The target universe is independent of the universe of S. -/
def UniversalProperty : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [CompletelyRegularSpace S] [T2Space S]
    (K : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : C(S, K)), ∃! F : C(Space S, K),
      ∀ x : S, F (evaluation x) = f x

def EmptyCase : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [IsEmpty S],
    Subsingleton (S →ᵇ ℂ) ∧ IsEmpty (Space S)

def CompactCharactersAreEvaluations : Prop :=
  Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters.CompactCharactersAreEvaluations.{u}

def EmptyCompactCase : Prop :=
  Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters.EmptyCompactCase.{u}

def DiskCharacters : Prop :=
  Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters.DiskCharacters

def PolydiskCharacters : Prop :=
  Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters.HolomorphicPolydiskCharacters

end ExpandedFA.BanachAlgebra.StoneCech.Spec
