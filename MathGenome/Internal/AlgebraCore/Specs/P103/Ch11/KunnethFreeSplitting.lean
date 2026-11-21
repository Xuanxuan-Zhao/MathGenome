import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.KunnethSequence
import Mathlib.RingTheory.PrincipalIdealDomain

/-! The both-free splitting assertion of paper.tex 3110–3133, with the
commutative coefficient convention of 2577–2582. The actual sequence exists
and is normalized by the shared positive connector and canonical Tor kernel
identification. Splitting applies to every such prescribed sequence, at every
rank and for every projective model. No splitting is asserted natural. -/
namespace P103.Specs.Ch11.KunnethFreeSplitting
open CategoryTheory
open P103.Specs.Ch11.KunnethSequence
open P103.Specs.Ch11.TorBalance P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A section of the actual last arrow, and a splitting fixing both ends. -/
def Splits {R : Type u} [Ring R]
    {C : RightComplex.{u,v} R} {D : LeftComplex.{u,w} R}
    {P : HomologyModels C} {n : ℕ} (S : DegreeSequence C D P n) : Prop :=
  ∃ s : TorDiagonal C D P n →ₗ[ℤ] Homology (ordinaryTotal C D) n,
    S.β.comp s = LinearMap.id ∧
    ∃ e : (TensorDiagonal C D n × TorDiagonal C D P n) ≃ₗ[ℤ]
        Homology (ordinaryTotal C D) n,
      (∀ a t, e (a,t) = S.α a + s t) ∧
      (∀ a t, S.β (e (a,t)) = t)

/-- For arbitrary-rank free complexes over a PID the normalized Künneth
sequence exists, and every sequence with its prescribed injection splits.
In particular the section belongs to the actual normalized surjection. -/
def splittingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
    (∀ p, Module.Free Rᵐᵒᵖ (C.X p)) → (∀ q, Module.Free R (D.X q)) →
    ∀ (P : HomologyModels C) (n : ℕ),
      Nonempty (NormalizedDegreeSequence C D P n) ∧
      ∀ S : DegreeSequence C D P n, Splits S

/-- The scalar endomorphism of a complex of left modules. -/
def scalarChainMap {R : Type u} [CommRing R] (D : LeftComplex.{u,w} R) (r : R) :
    D ⟶ D where
  f q := scalarMap (D.X q) r
  comm' q q' _ := scalarMap_naturality (D.d q q') r

/-- The actual coefficient action on total homology. -/
def totalScalar {R : Type u} [CommRing R] (C : RightComplex.{u,v} R)
    (D : LeftComplex.{u,w} R) (n : ℕ) (r : R) :
    Homology (ordinaryTotal C D) n →ₗ[ℤ] Homology (ordinaryTotal C D) n :=
  (homologyMap (ordinaryTotalMap (𝟙 C) (scalarChainMap D r)) n).toAddMonoidHom.toIntLinearMap

/-- The same coefficient action on the chosen Tor diagonal. -/
def torScalar {R : Type u} [CommRing R] (C : RightComplex.{u,v} R)
    (D : LeftComplex.{u,w} R) (P : HomologyModels C)
    (T : TorMaps.{u,v,w} R 1) (n : ℕ) (r : R) :
    TorDiagonal C D P n →ₗ[ℤ] TorDiagonal C D P n :=
  torDiagonalMap (𝟙 C) (scalarChainMap D r) P P T n

/-- R-linearity of a section is stated using the actual coefficient actions,
without choosing unrelated module structures on the integer-linear models. -/
def ScalarSplits {R : Type u} [CommRing R]
    {C : RightComplex.{u,v} R} {D : LeftComplex.{u,w} R}
    {P : HomologyModels C} {n : ℕ} (S : DegreeSequence C D P n)
    (T : TorMaps.{u,v,w} R 1) : Prop :=
  ∃ s : TorDiagonal C D P n →ₗ[ℤ] Homology (ordinaryTotal C D) n,
    S.β.comp s = LinearMap.id ∧
    ∀ r, (totalScalar C D n r).comp s = s.comp (torScalar C D P T n r)

/-- The normalized sequence exists and every normalized choice admits an
R-linear section. No sequence or scalar compatibility certificate is assumed. -/
def scalar_splittingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : RightComplex.{u,v} R) (D : LeftComplex.{u,w} R),
    (∀ p, Module.Free Rᵐᵒᵖ (C.X p)) → (∀ q, Module.Free R (D.X q)) →
    ∀ (P : HomologyModels C) (n : ℕ) (T : TorMaps.{u,v,w} R 1),
      Nonempty (NormalizedDegreeSequence C D P n) ∧
      ∀ S : NormalizedDegreeSequence C D P n, ScalarSplits S.toDegreeSequence T

end
end P103.Specs.Ch11.KunnethFreeSplitting
