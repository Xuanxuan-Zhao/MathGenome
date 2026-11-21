import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalEmbeddings
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MorreyWhole
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL

/-! Independent scope of paper.tex:1830–1881. All domains are the shared
bounded Lipschitz open sets, including the empty and disconnected cases.
The representative is unique on the closure, with no constraint on values
outside it. The two constants in `HolderNormBound` control the supremum and
seminorm and their sum controls the full Hölder norm. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace P102.Sobolev.IntegerEmbeddings
open P102.U4

def RepresentsOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) (f : Space d → 𝕜) : Prop :=
  (sobolevUnderlying u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] f

def HolderNormBound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space d → 𝕜) (S : Set (Space d)) (a M : ℝ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B ≤ M ∧
    (∀ x ∈ S, ‖f x‖ ≤ A) ∧
    ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ B * ‖x - y‖ ^ a

namespace Expected

def Critical : Prop :=
  ∀ (m : ℕ), 2 ≤ m + 1 →
  ∀ (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    letI : Fact (1 ≤ ((m + 1 : ℕ) : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ m + 1 by omega)⟩
    ∀ (q : ℝ≥0) (hq : 1 ≤ q),
      letI : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
      ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜],
        (∀ u : Sobolev 𝕜 Ω 1 (m + 1 : ℕ),
          MemLp (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space (m + 1)))) ∧
          eLpNorm (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space (m + 1)))) ≤
            (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) ∧
        HasSobolevInclusion 𝕜 Ω (m + 1 : ℕ) q

def Finite : Prop :=
  ∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
      ((m + 1 : ℕ) : ℝ≥0∞) < p → p ≠ ⊤ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Sobolev 𝕜 Ω 1 p,
        ∃ f : Space (m + 1) → 𝕜,
          ContinuousOn f (closure (Ω : Set (Space (m + 1)))) ∧ RepresentsOn u f ∧
          HolderNormBound f (closure (Ω : Set (Space (m + 1))))
            (1 - ((m + 1 : ℕ) : ℝ) / p.toReal) (C * ‖u‖) ∧
          ∀ g : Space (m + 1) → 𝕜,
            ContinuousOn g (closure (Ω : Set (Space (m + 1)))) → RepresentsOn u g →
            EqOn g f (closure (Ω : Set (Space (m + 1))))

def Infinity : Prop :=
  ∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜],
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Sobolev 𝕜 Ω 1 ⊤,
        ∃ f : Space (m + 1) → 𝕜,
          ContinuousOn f (closure (Ω : Set (Space (m + 1)))) ∧ RepresentsOn u f ∧
          HolderNormBound f (closure (Ω : Set (Space (m + 1)))) 1 (C * ‖u‖) ∧
          ∀ g : Space (m + 1) → 𝕜,
            ContinuousOn g (closure (Ω : Set (Space (m + 1)))) → RepresentsOn u g →
            EqOn g f (closure (Ω : Set (Space (m + 1))))

/-- Every nondegenerate interval whose interior lies in the one-dimensional
open set includes each closed component interval. No connectedness is imposed.
Absolute continuity is on the closed interval, including its endpoints. -/
def DimensionOne : Prop :=
  ∀ (e : GraphPieces.Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient 0)) →
    ∀ (𝕜 : Type) [RCLike 𝕜],
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Sobolev 𝕜 Ω 1 1,
        ∃ f : Space 1 → 𝕜,
          ContinuousOn f (closure (Ω : Set (Space 1))) ∧ RepresentsOn u f ∧
          (∀ x ∈ closure (Ω : Set (Space 1)), ‖f x‖ ≤ C * ‖u‖) ∧
          (∀ a b : ℝ, a < b → Ioo a b ⊆ ACL.fiber Ω 0 0 →
            AbsolutelyContinuousOnInterval (fun t => f (ACL.line 0 0 t)) a b) ∧
          ∀ g : Space 1 → 𝕜, ContinuousOn g (closure (Ω : Set (Space 1))) →
            RepresentsOn u g → EqOn g f (closure (Ω : Set (Space 1)))

end Expected
end P102.Sobolev.IntegerEmbeddings
