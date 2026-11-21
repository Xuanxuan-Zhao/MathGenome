import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Equicontinuity

/-!
K03.16.ascoli, paper.tex:3842–3861: compactness of a scalar family in
the canonical sup norm. The subsequence assertion is specified upstream.
These statements keep pointwise equicontinuity in the characterization;
necessity also supplies the stronger common radius for every pair of points.
CompactSpace K refers to the induced topology of the real subset K, and
requires neither K nor the family to be nonempty.
-/
namespace Specs.SingleVariableAnalysis.Ch16.Ascoli

/-- Compactness provides internal finite nets in the actual sup norm. -/
def compactFamilyFiniteNet : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] (K : Set ℝ) [CompactSpace K]
    (F : Set C(K, E)), IsCompact F →
    ∀ ε : ℝ, 0 < ε → ∃ t : Finset C(K, E),
      (∀ h ∈ t, h ∈ F) ∧ ∀ f ∈ F, ∃ h ∈ t, ‖f - h‖ < ε

/-- A radius-1 finite net yields a finite common bound on all values. -/
def boundedFamilyOfFiniteNet : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] (K : Set ℝ) [CompactSpace K]
    (F : Set C(K, E)),
    (∃ t : Finset C(K, E), ∀ f ∈ F, ∃ h ∈ t, ‖f - h‖ < 1) →
    Equicontinuity.uniformlyBoundedFamilyValue K F

/-- Finitely many uniformly continuous centers produce a common modulus. -/
def equicontinuousFamilyOfFiniteNets : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] (K : Set ℝ) [CompactSpace K]
    (F : Set C(K, E)),
    (∀ ε : ℝ, 0 < ε → ∃ t : Finset C(K, E),
      ∀ f ∈ F, ∃ h ∈ t, ‖f - h‖ < ε) →
    Equicontinuity.uniformlyEquicontinuousFamilyValue K F

def realAscoliCompactIff : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : Set C(K, ℝ)),
    IsCompact F ↔ IsClosed F ∧
      Equicontinuity.uniformlyBoundedFamilyValue K F ∧
      Equicontinuity.pointwiseEquicontinuousFamilyValue K F

def complexAscoliCompactIff : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : Set C(K, ℂ)),
    IsCompact F ↔ IsClosed F ∧
      Equicontinuity.uniformlyBoundedFamilyValue K F ∧
      Equicontinuity.pointwiseEquicontinuousFamilyValue K F

end Specs.SingleVariableAnalysis.Ch16.Ascoli
