import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethFreeSplitting

/-! The one-free splitting conclusion of paper.tex 3050–3069, 3135–3168.
All complexes are nonnegative, and freeness has arbitrary rank. The natural
sequence retains its specified cycle injection and normalized Tor surjection.
No naturality is imposed on the choice of section. -/
namespace P103.Specs.Ch11.KunnethSplitting
open CategoryTheory
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.KunnethSequence
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.KunnethFreeSplitting
noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Either complex may be free; no hypothesis is imposed on the rank. -/
def OneFree {R : Type u} [Ring R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R) : Prop :=
  (∀ p, Module.Free Rᵐᵒᵖ (C.X p)) ∨ (∀ q, Module.Free R (D.X q))

/-- A section of the actual surjection, with the corresponding direct-product
coordinates fixing the actual injection. Coefficient linearity is expressed
using the established scalar endomorphisms on the integer-linear models. -/
def SplitsOver {R : Type u} [CommRing R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (P : HomologyModels C) (T : TorMaps.{u,v,w} R 1) (n : ℕ)
    (S : DegreeSequence C D P n) : Prop :=
  ∃ s : TorDiagonal C D P n →ₗ[ℤ] Homology (ordinaryTotal C D) n,
    S.β.comp s = LinearMap.id ∧
    (∀ r, (totalScalar C D n r).comp s = s.comp (torScalar C D P T n r)) ∧
    ∃ e : (TensorDiagonal C D n × TorDiagonal C D P n) ≃ₗ[ℤ]
        Homology (ordinaryTotal C D) n,
      (∀ a t, e (a,t) = S.α a + s t) ∧
      (∀ a t, S.β (e (a,t)) = t)

/-- Retain existence and simultaneous naturality of the normalized sequence.
Under the original first-factor flatness hypotheses, every normalized choice
splits over a PID as soon as either complex is degreewise free. -/
def right_splittingType : Prop :=
  right_sequenceType.{u,v,w} ∧ normalized_naturalType.{u,v,w} ∧
  scalar_compatibilityType.{u,v,w} ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
    P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,v,w} C →
    OneFree C D → ∀ (P : HomologyModels C) (T : TorMaps.{u,v,w} R 1)
      (n : ℕ) (S : NormalizedDegreeSequence C D P n),
      SplitsOver C D P T n S.toDegreeSequence

/-- The analogous assertion for the simultaneous second-factor family,
including its opposite-ring normalization and the same right-left Tor terms. -/
def left_splittingType : Prop :=
  left_natural_sequenceType.{u,v,w} ∧ scalar_compatibilityType.{u,v,w} ∧
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (L : LeftSequenceFamily.{u,v,w} R)
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R)
    (hD : LeftFlatTermsAndBoundaries.{u,v,w} D),
    OneFree C D → ∀ (P : HomologyModels C) (T : TorMaps.{u,v,w} R 1) (n : ℕ),
      SplitsOver C D P T n (L.sequence C D hD P n)

end
end P103.Specs.Ch11.KunnethSplitting
