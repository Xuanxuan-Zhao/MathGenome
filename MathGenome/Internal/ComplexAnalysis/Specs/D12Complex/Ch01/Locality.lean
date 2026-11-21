import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-!
Independent statements for the restriction and gluing assertions of
paper.tex:268–279 (D12.01.05). We reuse weak holomorphy from the Basic Spec.
Functions on open sets are represented by total functions. Thus uniqueness
means equality on the covered open set; values outside it are immaterial.
-/

namespace Specs.D12Complex.Ch01.Locality

open _root_.D12Complex

def holomorphicOn_restrict_type : Prop :=
  ∀ (Ω U : Set ℂ) (f : ℂ → ℂ),
    HolomorphicOn Ω f → IsOpen U → U ⊆ Ω → HolomorphicOn U f

/-- An arbitrary compatible family on an open cover has a holomorphic gluing,
unique as a function on Ω. The index type can be empty and of any universe. -/
def holomorphicOn_glue_type.{u} : Prop :=
  ∀ (ι : Type u) (Ω : Set ℂ) (U : ι → Set ℂ) (f : ι → ℂ → ℂ),
    (⋃ i, U i) = Ω →
    (∀ i, HolomorphicOn (U i) (f i)) →
    (∀ i j, Set.EqOn (f i) (f j) (U i ∩ U j)) →
    ∃ F : ℂ → ℂ, HolomorphicOn Ω F ∧
      (∀ i, Set.EqOn F (f i) (U i)) ∧
      ∀ G : ℂ → ℂ, (∀ i, Set.EqOn G (f i) (U i)) → Set.EqOn G F Ω

end Specs.D12Complex.Ch01.Locality
