import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.DualSystems
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair

/-!
Nondegenerate normed dual systems, algebraic paired adjoints, and transport
of conjugate-linear-first systems to bilinear ones. Pairings are linear maps,
not continuous linear maps; the normed spaces may be incomplete.
-/

namespace ExpandedFA.Fredholm

universe u v u₁ v₁ u₂ v₂
noncomputable section

abbrev DualSystem (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] : Type (max u v) :=
  DualSystemsSpec.DualSystemData X Y

abbrev SesquilinearSystem (X : Type u) (Y : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] : Type (max u v) :=
  DualSystemsSpec.SesquilinearSystemData X Y

/-- Same additive normed group, with `a •conj x = conj a • x`. -/
abbrev ConjugateSpace (X : Type u) : Type u := DualSystemsSpec.ConjugateSpaceData X

section OneSystem

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The bracket order in the manuscript is X first, Y second. -/
def dualSystemBracket (D : DualSystem X Y) (x : X) (y : Y) : ℂ := D.pairing y x

/-- Construct a dual system from the same algebraic bilinear-map type used
for the weak dual-pair topology, and separation in each variable. -/
def dualSystemOfPairing (B : Y →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (hX : ∀ x, (∀ y, B y x = 0) → x = 0)
    (hY : ∀ y, (∀ x, B y x = 0) → y = 0) : DualSystem X Y :=
  ⟨B, hX, hY⟩

theorem dualSystem_separation : DualSystemsSpec.Separation (X := X) (Y := Y) := by
  intro D
  constructor
  · intro x
    exact ⟨D.separatesLeft x, fun h y => by simp [h]⟩
  · intro y
    exact ⟨D.separatesRight y, fun h x => by simp [h]⟩

/-- Use the accepted initial topology of exactly this pairing. -/
def dualSystemWeakTopology (D : DualSystem X Y) : TopologicalSpace X :=
  ExpandedFA.P1.dualPairTopology ℂ X Y D.pairing

theorem dualSystemWeakTopology_compatibility :
    DualSystemsSpec.WeakTopologyCompatibility (X := X) (Y := Y) := by
  intro D
  rfl

/-- Interchanging the two spaces preserves nondegeneracy. -/
def dualSystemFlip (D : DualSystem X Y) : DualSystem Y X :=
  ⟨D.pairing.flip, D.separatesRight, D.separatesLeft⟩

/-- Conjugate the scalar structure on the conjugate-linear argument.
All pairing values are preserved. In particular, no estimate on the pairing
is needed to construct the transported nondegenerate bilinear system. -/
def sesquilinearToDualSystem (S : SesquilinearSystem X Y) :
    DualSystem (ConjugateSpace X) Y where
  pairing := {
    toFun := fun y => {
      toFun := fun x => S.pairing y (x : X)
      map_add' := fun x z => (S.pairing y).map_add x z
      map_smul' := fun a (x : X) => by
        change S.pairing y (star a • x) = a • S.pairing y x
        simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star] }
    map_add' := fun y z => by
      ext x
      exact LinearMap.congr_fun (S.pairing.map_add y z) (x : X)
    map_smul' := fun a y => by
      ext x
      exact LinearMap.congr_fun (S.pairing.map_smul a y) (x : X) }
  separatesLeft := S.separatesLeft
  separatesRight := S.separatesRight

theorem sesquilinearToDualSystem_apply :
    DualSystemsSpec.SesquilinearTransportEvaluation (X := X) (Y := Y) := by
  intro S x y
  rfl

end OneSystem

section Conjugation

variable {X : Type u₁} {Z : Type u₂}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem conjugateSpace_smul : DualSystemsSpec.ConjugateScalarAction (X := X) := by
  intro a x
  rfl

theorem conjugateSpace_norm : DualSystemsSpec.ConjugateNorm (X := X) := by
  intro x
  rfl

/-- The same underlying map is linear between the conjugated spaces. -/
def conjugateLinearMap (T : X →ₗ[ℂ] Z) : ConjugateSpace X →ₗ[ℂ] ConjugateSpace Z where
  toFun := fun x => T (x : X)
  map_add' := fun x z => T.map_add x z
  map_smul' := fun a x => T.map_smul (star a) (x : X)

/-- Conjugation also preserves continuity: the additive normed group and
the underlying function are unchanged. -/
def conjugateContinuousLinearMap (T : X →L[ℂ] Z) :
    ConjugateSpace X →L[ℂ] ConjugateSpace Z :=
  { conjugateLinearMap T.toLinearMap with cont := T.cont }

theorem conjugateMap_apply : DualSystemsSpec.ConjugateMapEvaluation (X := X) (Z := Z) := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end Conjugation

section Adjoint

variable {X₁ : Type u₁} {Y₁ : Type v₁} {X₂ : Type u₂} {Y₂ : Type v₂}
  [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
  [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂]

/-- `[Tx,y]₂ = [x,U y]₁`. This is a relation, not a claim that every map
admits an adjoint in an arbitrary algebraic dual system. -/
def isPairedAdjoint (D₁ : DualSystem X₁ Y₁) (D₂ : DualSystem X₂ Y₂)
    (T : X₁ →ₗ[ℂ] X₂) (U : Y₂ →ₗ[ℂ] Y₁) : Prop :=
  ∀ x y, D₂.pairing y (T x) = D₁.pairing (U y) x

theorem isPairedAdjoint_iff :
    DualSystemsSpec.PairedAdjointEquation
      (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) := by
  intro D₁ D₂ T U
  rfl

/-- Separation in Y₁ makes an existing paired adjoint unique. -/
theorem pairedAdjoint_unique :
    DualSystemsSpec.PairedAdjointUnique
      (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) := by
  intro D₁ D₂ T U V hU hV
  ext y
  have hzero : U y - V y = 0 := D₁.separatesRight _ (fun x => by
    simp only [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr ((hU x y).symm.trans (hV x y)))
  exact sub_eq_zero.mp hzero

/-- Under the explicitly conjugated scalar action the sesquilinear
adjoint equation is exactly the bilinear adjoint equation. -/
theorem sesquilinear_pairedAdjoint_iff :
    DualSystemsSpec.SesquilinearAdjointTransport
      (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) := by
  intro S₁ S₂ T U
  rfl

end Adjoint
end
end ExpandedFA.Fredholm
