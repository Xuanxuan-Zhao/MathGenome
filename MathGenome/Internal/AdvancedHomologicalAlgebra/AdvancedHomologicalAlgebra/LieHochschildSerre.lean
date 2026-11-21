import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieHochschildSerre
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckEdges
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.LieQuotientCohomologyAction
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtExactSequences

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Shared.Lie

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w r

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

/-- The induced algebra map sends each Lie generator to its quotient class. -/
@[simp] theorem envelopingQuotient_inclusion (h : LieIdeal k g) (y : g) :
    envelopingQuotient h (inclusion k g y) =
      inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h y) :=
  UniversalEnvelopingAlgebra.lift_ι_apply _ _ y

/-- Augmenting after passage to the quotient gives the ambient augmentation. -/
theorem augmentation_quotient (h : LieIdeal k g) :
    Shared.Lie.augmentation k g =
      (Shared.Lie.augmentation k (g ⧸ h)).comp (envelopingQuotient h) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext y
  change Shared.Lie.augmentation k g (inclusion k g y) =
    Shared.Lie.augmentation k (g ⧸ h) (envelopingQuotient h (inclusion k g y))
  rw [envelopingQuotient_inclusion, (augmentation_properties k g).1,
    (augmentation_properties k (g ⧸ h)).1]

/-- The composite of the two invariant functors is ambient invariants. -/
def compositionInvariantsIso (h : LieIdeal k g) :
    idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h ≅ lieInvariants.{u,v,w} k g := by
  let f := (envelopingQuotient h).toRingHom
  let t := (Shared.Lie.augmentation k (g ⧸ h)).toRingHom
  let aug := (Shared.Lie.augmentation k g).toRingHom
  have ha : aug = t.comp f := congrArg AlgHom.toRingHom (augmentation_quotient h)
  let e := ModuleCat.restrictScalarsComp'.{max u v w} f t aug ha
  let af := ModuleCat.restrictCoextendScalarsAdj.{w, max u v, max u v} f
  let atq := ModuleCat.restrictCoextendScalarsAdj.{max v w, max u v, u} t
  let ag := ModuleCat.restrictCoextendScalarsAdj.{max v w, max u v, u} aug
  exact ((atq.comp af).ofNatIsoLeft e.symm).rightAdjointUniq ag

/-- Coextension along a ring map preserves injectives because restriction of
scalars preserves monomorphisms. -/
theorem coextend_injective {R : Type*} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
    (I : ModuleCat.{max v w} R) (hI : Injective I) :
    Injective ((ModuleCat.coextendScalars f).obj I) :=
  (ModuleCat.restrictCoextendScalarsAdj f).map_injective I hI

/-- Apply the object form of the Grothendieck spectral sequence to the two
coextensions defined by the Lie quotient and its augmentation. -/
theorem derived_spectral_sequence : DerivedStatement.{u,v,w} := by
  intro k g _ _ _ h
  let A := ModuleCat.{max u v w} (U k g)
  let B := ModuleCat.{max u v w} (U k (g ⧸ h))
  let C := ModuleCat.{max u v w} k
  letI := HasDerivedCategory.standard A
  letI := HasDerivedCategory.standard B
  letI := HasDerivedCategory.standard C
  let F := idealInvariants.{u,v,w} h
  let G := quotientInvariants.{u,v,w} h
  letI : F.Additive := inferInstanceAs ((idealInvariants.{u,v,w} h).Additive)
  letI : G.Additive := inferInstanceAs ((quotientInvariants.{u,v,w} h).Additive)
  letI : F.IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{w, max u v, max u v}
      (envelopingQuotient h).toRingHom).isRightAdjoint
  letI : G.IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max v w, max u v, u}
      (Shared.Lie.augmentation k (g ⧸ h)).toRingHom).isRightAdjoint
  letI : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (idealInvariants.{u,v,w} h))
  letI : PreservesFiniteLimits G :=
    inferInstanceAs (PreservesFiniteLimits (quotientInvariants.{u,v,w} h))
  refine GrothendieckEdges.grothendieck_edges A B C F G ?_
  intro I hI
  letI hFI : Injective (F.obj I) := coextend_injective.{max u v,w} _ I hI
  exact (AcyclicTermComparison.rightVanishing B C G (F.obj I)).mpr
    (ClassicalDerivedValues.rightInjectiveVanishing B C G (F.obj I))


section InvariantEvaluation

open LieQuotientAction

theorem envelopingQuotient_surjective (h : LieIdeal k g) :
    Function.Surjective (envelopingQuotient h) := by
  intro z
  induction z using Shared.Lie.enveloping_induction k (g ⧸ h) with
  | scalar r => exact ⟨algebraMap k (U k g) r, (envelopingQuotient h).commutes r⟩
  | generator z =>
    induction z using Submodule.Quotient.induction_on with | _ y =>
    exact ⟨inclusion k g y, envelopingQuotient_inclusion h y⟩
  | mul a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' * b', map_mul _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩

variable (h : LieIdeal k g) (M : ModuleCat.{max u v w} (U k g))

@[simp] theorem coefficientRepresentation_apply (y : g) (m : (underlying k g).obj M) :
    coefficientRepresentation k g M y m = inclusion k g y • m := rfl

/-- Linearity over the ambient enveloping algebra determines a coextended
map's values on quotient images from its value at one. -/
theorem idealCoextend_apply (t : (idealInvariants.{u,v,w} h).obj M) (a : U k g) :
    t (envelopingQuotient h a) = a • t (1 : U k (g ⧸ h)) := by
  have he := (ModuleCat.CoextendScalars.equiv (envelopingQuotient h).toRingHom M t).map_smul
    a (1 : U k (g ⧸ h))
  change t (envelopingQuotient h a * 1) = a • t (1 : U k (g ⧸ h)) at he
  erw [mul_one] at he
  exact he

/-- The quotient action on ideal invariants agrees with the ambient
enveloping action, tested on every algebra element and invariant vector. -/
theorem quotientAction_compatible
    (a : U k g) (m : invariants h (coefficientRepresentation k g M)) :
    (representationEquiv k (g ⧸ h) _
      (invariantQuotient h (coefficientRepresentation k g M)) (envelopingQuotient h a) m).val =
      a • m.val := by
  induction a using Shared.Lie.enveloping_induction k g generalizing m with
  | scalar r =>
    rw [(envelopingQuotient h).commutes, AlgHom.commutes]
    rfl
  | generator y =>
    rw [envelopingQuotient_inclusion,
      (representation_properties k (g ⧸ h) _).1]
    exact invariantQuotient_formula h (coefficientRepresentation k g M) y m
  | mul a b ha hb =>
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, ha, hb, mul_smul]
  | add a b ha hb =>
    rw [map_add, map_add]
    simp only [LinearMap.add_apply, Submodule.coe_add, ha, hb, add_smul]

/-- Evaluation on the unit gives the original ideal-invariant space. -/
def idealInvariantEval : (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M)
    →ₗ[k] invariants h (coefficientRepresentation k g M) where
  toFun t :=
    let t' : (idealInvariants.{u,v,w} h).obj M := t
    ⟨t' (1 : U k (g ⧸ h)), fun a => by
    erw [coefficientRepresentation_apply, ← idealCoextend_apply h M t',
      envelopingQuotient_inclusion]
    have ha : quotientMap k g h (a : g) = 0 :=
      (Submodule.Quotient.mk_eq_zero h.toSubmodule).mpr a.property
    erw [ha, map_zero]
    exact (ModuleCat.CoextendScalars.equiv (envelopingQuotient h).toRingHom M t').map_zero⟩
  map_add' _ _ := rfl
  map_smul' r t := by
    apply Subtype.ext
    let t' : (idealInvariants.{u,v,w} h).obj M := t
    change t' (1 * algebraMap k (U k (g ⧸ h)) r) = algebraMap k (U k g) r • t' (1 : U k (g ⧸ h))
    erw [one_mul, ← (envelopingQuotient h).commutes, idealCoextend_apply]

/-- The inverse evaluates the quotient action at an invariant vector. -/
def idealInvariantLift (m : invariants h (coefficientRepresentation k g M)) :
    (idealInvariants.{u,v,w} h).obj M :=
  (ModuleCat.CoextendScalars.equiv (envelopingQuotient h).toRingHom M).symm
    { toFun := fun a => (representationEquiv k (g ⧸ h) _
        (invariantQuotient h (coefficientRepresentation k g M)) a m).val
      map_add' := fun a b => by
        change (representationEquiv k (g ⧸ h) _
          (invariantQuotient h (coefficientRepresentation k g M)) ((a : U k (g ⧸ h)) + (b : U k (g ⧸ h))) m).val = _
        erw [map_add]
        rfl
      map_smul' := fun a b => by
        change (representationEquiv k (g ⧸ h) _
          (invariantQuotient h (coefficientRepresentation k g M))
          (envelopingQuotient h a * (show U k (g ⧸ h) from b)) m).val = _
        rw [map_mul]
        simp only [Module.End.mul_apply]
        exact quotientAction_compatible h M a _ }

def idealInvariantEquiv :
    (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M) ≃ₗ[k]
      invariants h (coefficientRepresentation k g M) :=
  LinearEquiv.ofBijective (idealInvariantEval h M) ⟨by
    intro s t hst
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := envelopingQuotient_surjective h z
    let s' : (idealInvariants.{u,v,w} h).obj M := s
    let t' : (idealInvariants.{u,v,w} h).obj M := t
    change s' (envelopingQuotient h a) = t' (envelopingQuotient h a)
    rw [idealCoextend_apply, idealCoextend_apply]
    exact congrArg (a • ·) (congrArg Subtype.val hst), by
    intro m
    refine ⟨idealInvariantLift h M m, ?_⟩
    apply Subtype.ext
    change (representationEquiv k (g ⧸ h) _
      (invariantQuotient h (coefficientRepresentation k g M)) 1 m).val = m.val
    rw [map_one]
    rfl⟩

theorem ideal_invariants_evaluation : IdealInvariantsStatement.{u,v,w} := by
  intro k g _ _ _ h M
  refine ⟨idealInvariantEquiv h M, fun _ => rfl, ?_⟩
  intro y t
  let t' : (idealInvariants.{u,v,w} h).obj M := t
  change t' (1 * inclusion k (g ⧸ h) (quotientMap k g h y)) = inclusion k g y • t' (1 : U k (g ⧸ h))
  erw [one_mul, ← envelopingQuotient_inclusion, idealCoextend_apply]

end InvariantEvaluation

section AugmentationEvaluation

variable (M : ModuleCat.{max u v w} (U k g))

theorem lieCoextend_apply (t : (lieInvariants.{u,v,w} k g).obj M) (a : U k g) :
    t (Shared.Lie.augmentation k g a) = a • t (1 : k) := by
  have hs := (ModuleCat.CoextendScalars.equiv (Shared.Lie.augmentation k g).toRingHom M t).map_smul
    a (1 : k)
  change t (Shared.Lie.augmentation k g a * 1) = a • t (1 : k) at hs
  erw [mul_one] at hs
  exact hs

/-- The coefficient map used to forget quotient invariance on the column edge. -/
def lieInvariantEval :
    (lieInvariants.{u,v,w} k g).obj M ⟶ (underlying k g).obj M :=
  ModuleCat.ofHom (X := (lieInvariants.{u,v,w} k g).obj M) (Y := (underlying k g).obj M)
    { toFun := fun t => t (1 : k)
      map_add' := fun _ _ => rfl
      map_smul' := fun r t => by
        change t (1 * r) = algebraMap k (U k g) r • t (1 : k)
        have hr : Shared.Lie.augmentation k g (algebraMap k (U k g) r) = r :=
          (Shared.Lie.augmentation k g).commutes r
        erw [one_mul]
        exact (congrArg (fun s : k => t s) hr).symm.trans (lieCoextend_apply M t _) }

private theorem smul_of_lie_invariant (m : (underlying k g).obj M)
    (hm : ∀ y, coefficientRepresentation k g M y m = 0) (a : U k g) :
    a • (m : M) = algebraMap k (U k g) (Shared.Lie.augmentation k g a) • (m : M) := by
  induction a using Shared.Lie.enveloping_induction k g with
  | scalar r =>
    rw [(Shared.Lie.augmentation k g).commutes]
    rfl
  | generator y =>
    rw [(augmentation_properties k g).1, map_zero, zero_smul]
    exact hm y
  | mul a b ha hb =>
    have hcentral := Algebra.commutes (R := k) (A := U k g) (Shared.Lie.augmentation k g b) a
    rw [map_mul, map_mul, mul_smul, hb, ← mul_smul, ← hcentral, mul_smul, ha, ← mul_smul]
    rw [Algebra.commutes (Shared.Lie.augmentation k g b)
      (algebraMap k (U k g) (Shared.Lie.augmentation k g a))]
  | add a b ha hb => rw [map_add, map_add, add_smul, add_smul, ha, hb]

/-- Evaluation at one identifies the augmentation Hom with the original
invariant vectors, naturally in the coefficient module. -/
def lieInvariantInclusion (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] :
    InvariantInclusion.{u,v,w} k g where
  evaluation :=
    { app := lieInvariantEval.{u,v,w}
      naturality := by
        intro X Y a
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro t
        rfl }
  formula _ _ := rfl
  injective M := by
    intro t s hs
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro r
    change t (r : k) = s (r : k)
    have hr : Shared.Lie.augmentation k g (algebraMap k (U k g) (r : k)) = r :=
      (Shared.Lie.augmentation k g).commutes r
    erw [← hr, lieCoextend_apply, lieCoextend_apply]
    exact congrArg ((algebraMap k (U k g) r) • ·) hs
  range M m := by
    constructor
    · rintro ⟨t, rfl⟩ y
      change inclusion k g y • t (1 : k) = 0
      erw [← lieCoextend_apply M t, (augmentation_properties k g).1]
      exact (ModuleCat.CoextendScalars.equiv (Shared.Lie.augmentation k g).toRingHom M t).map_zero
    · intro hm
      let t : (lieInvariants.{u,v,w} k g).obj M :=
        (ModuleCat.CoextendScalars.equiv (Shared.Lie.augmentation k g).toRingHom M).symm
          { toFun := fun r => (algebraMap k (U k g) (r : k)) • (m : M)
            map_add' := fun r s => by
              change (algebraMap k (U k g) ((r : k) + (s : k))) • (m : M) = _
              rw [map_add, add_smul]
            map_smul' := fun a r => by
              let r' : k := r
              change (algebraMap k (U k g) (Shared.Lie.augmentation k g a * r')) • (m : M) =
                a • ((algebraMap k (U k g) r') • (m : M))
              rw [mul_comm (Shared.Lie.augmentation k g a) r', map_mul, mul_smul,
                ← smul_of_lie_invariant M m hm, ← mul_smul, Algebra.commutes r' a, mul_smul] }
      refine ⟨t, ?_⟩
      change (algebraMap k (U k g) (1 : k)) • (m : M) = m
      rw [map_one, one_smul]

theorem lie_invariants_evaluation : LieInvariantsStatement.{u,v,w} := by
  intro k g _ _ _
  exact ⟨lieInvariantInclusion k g⟩

end AugmentationEvaluation

section Pullback

variable {L : Type*} [LieRing L] [LieAlgebra k L]
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  (f : L →ₗ⁅k⁆ g) (a : M →ₗ[k] N)

@[simp] theorem pullback_wedge (n : ℕ) (t : CE.W k g n →ₗ[k] M) (x : Fin n → L) :
    pullback f a n t (CE.wedge k L n x) = a (t (CE.wedge k g n (f ∘ x))) := by
  change a (t (exteriorPower.map n f.toLinearMap _)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

theorem pullback_bracketSum (n : ℕ) (t : CE.W k g n →ₗ[k] M) (x : Fin (n+1) → L) :
    CE.cochainBracketSum k L N n (pullback f a n t) x =
      a (CE.cochainBracketSum k g M n t (f ∘ x)) := by
  cases n with
  | zero => simp [CE.cochainBracketSum]
  | succ n =>
    simp only [CE.cochainBracketSum, map_sum, map_zsmul, pullback_wedge]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 4
    funext b
    refine Fin.cases ?_ (fun _ => ?_) b
    · simpa only [Function.comp_apply, Fin.cons_zero] using f.map_lie (x i.castSucc) (x j.succ)
    · rfl

theorem pullback_commutes : PullbackStatement.{u,v,w} := by
  intro k g L _ _ _ _ _ M N _ _ _ _ ρ τ f a ha d e hd he n t
  apply exteriorPower.linearMap_ext
  ext x
  change e n (pullback f a n t) (CE.wedge k L (n+1) x) =
    pullback f a (n+1) (d n t) (CE.wedge k L (n+1) x)
  rw [he, pullback_wedge, hd, map_add, pullback_bracketSum]
  congr 1
  simp only [map_sum, map_zsmul, pullback_wedge, ha, Function.comp_apply]
  rfl

end Pullback

section ChevalleyEilenberg

variable (k g)

private instance coefficientTower (M : ModuleCat.{max u v w} (U k g)) :
    IsScalarTower k (U k g) ((underlying k g).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The actual CE coboundary on a bundled coefficient module. -/
def ceDifferential (M : ModuleCat.{max u v w} (U k g)) (n : ℕ) :=
  CE.coboundary k g ((underlying k g).obj M) (CE.boundary k g) n

theorem ceDifferential_formula (M : ModuleCat.{max u v w} (U k g)) :
    IsCEDifferential (coefficientRepresentation k g M) (ceDifferential k g M) :=
  CE.coboundary_formula k g ((underlying k g).obj M)
    (CE.boundary k g) (CE.boundary_formula k g)

/-- The module-valued CE complex uses precisely the HA-A06 coboundary. -/
def chevalleyEilenberg : CochainTheory.{u,v,w} k g where
  d := ceDifferential k g
  formula := ceDifferential_formula k g
  square M := CE.coboundary_squared k g ((underlying k g).obj M)
    (CE.boundary k g) (CE.boundary_squared k g)
  natural {M N} a := by
    refine pullback_commutes k g g _ _ (coefficientRepresentation k g M)
      (coefficientRepresentation k g N) (LieHom.id : g →ₗ⁅k⁆ g)
      ((underlying k g).map a).hom ?_ _ _
      (ceDifferential_formula k g M) (ceDifferential_formula k g N)
    intro y m
    exact a.hom.map_smul (inclusion k g y) m

end ChevalleyEilenberg

section EdgeMaps

open LieQuotientAction

variable (h : LieIdeal k g) (M : ModuleCat.{max u v w} (U k g))

/-- The inclusion of the ideal-invariant coefficient vectors. -/
def inflationCoefficient :
    (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M) ⟶ (underlying k g).obj M :=
  ModuleCat.ofHom
    (X := (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M))
    (Y := (underlying k g).obj M)
    { toFun := fun t =>
        (show (idealInvariants.{u,v,w} h).obj M from t) (1 : U k (g ⧸ h))
      map_add' := fun t s => congrArg Subtype.val
        ((idealInvariantEval.{u,v,w} h M).map_add t s)
      map_smul' := fun r t => congrArg Subtype.val
        ((idealInvariantEval.{u,v,w} h M).map_smul r t) }

@[simp] theorem inflationCoefficient_apply
    (m : (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M)) :
    (inflationCoefficient.{u,v,w} h M).hom m =
      (show (idealInvariants.{u,v,w} h).obj M from m) (1 : U k (g ⧸ h)) := rfl

theorem inflationCoefficient_intertwines (y : g)
    (m : (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M)) :
    (inflationCoefficient.{u,v,w} h M).hom (coefficientRepresentation k (g ⧸ h)
      ((idealInvariants.{u,v,w} h).obj M) (quotientMap k g h y) m) =
      coefficientRepresentation k g M y ((inflationCoefficient.{u,v,w} h M).hom m) := by
  rw [coefficientRepresentation_apply, coefficientRepresentation_apply,
    inflationCoefficient_apply, inflationCoefficient_apply]
  let m' : (idealInvariants.{u,v,w} h).obj M := m
  change m' ((1 : U k (g ⧸ h)) * inclusion k (g ⧸ h) (quotientMap k g h y)) =
    inclusion k g y • m' (1 : U k (g ⧸ h))
  erw [one_mul, ← envelopingQuotient_inclusion, idealCoextend_apply]

/-- Restriction does not change the coefficient vector. The identity on
vectors is linear because the enveloping inclusion respects base scalars. -/
def restrictionCoefficient :
    (underlying k g).obj M ⟶ (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) :=
  ModuleCat.ofHom (X := (underlying k g).obj M)
    (Y := (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M))
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change (algebraMap k (U k g) r) • (m : M) =
          IdealEnveloping.inducedMap k g h (algebraMap k (U k h) r) • (m : M)
        rw [AlgHom.commutes] }

theorem restrictionCoefficient_intertwines (y : h) (m : (underlying k g).obj M) :
    (restrictionCoefficient.{u,v,w} h M).hom (coefficientRepresentation k g M (h.incl y) m) =
      coefficientRepresentation k h ((restrictIdeal.{u,v,w} h).obj M) y
        ((restrictionCoefficient.{u,v,w} h M).hom m) := by
  rw [coefficientRepresentation_apply, coefficientRepresentation_apply]
  change inclusion k g (y : g) • (m : M) =
    IdealEnveloping.inducedMap k g h (inclusion k h y) • (m : M)
  rw [IdealEnveloping.inducedMap_inclusion]

/-- Pullback along the quotient Lie map with invariant coefficients. -/
def inflationCochain :
    (chevalleyEilenberg.{u,v,w} k (g ⧸ h)).complex ((idealInvariants.{u,v,w} h).obj M) ⟶
      (chevalleyEilenberg.{u,v,w} k g).complex M :=
  (chevalleyEilenberg.{u,v,w} k (g ⧸ h)).map (chevalleyEilenberg.{u,v,w} k g)
    (quotientMap k g h) (inflationCoefficient.{u,v,w} h M)
    (pullback_commutes k (g ⧸ h) g _ _ _ _ _ _ (inflationCoefficient_intertwines.{u,v,w} h M)
      _ _ ((chevalleyEilenberg.{u,v,w} k (g ⧸ h)).formula _)
      ((chevalleyEilenberg.{u,v,w} k g).formula _))

/-- Pullback along the ideal inclusion with the original coefficient vectors. -/
def restrictionCochain :
    (chevalleyEilenberg.{u,v,w} k g).complex M ⟶
      (chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M) :=
  (chevalleyEilenberg.{u,v,w} k g).map (chevalleyEilenberg.{u,v,w} k h)
    h.incl (restrictionCoefficient.{u,v,w} h M)
    (pullback_commutes k g h _ _ _ _ _ _ (restrictionCoefficient_intertwines.{u,v,w} h M)
      _ _ ((chevalleyEilenberg.{u,v,w} k g).formula _)
      ((chevalleyEilenberg.{u,v,w} k h).formula _))

/-- Inflation, as a transformation of the actual cochain functors. -/
def inflationCochainNat :
    idealInvariants.{u,v,w} h ⋙ (chevalleyEilenberg.{u,v,w} k (g ⧸ h)).functor ⟶
      (chevalleyEilenberg.{u,v,w} k g).functor where
  app M := inflationCochain.{u,v,w} h M
  naturality M N a := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro x
    let tq : CE.W k (g ⧸ h) n →ₗ[k]
        (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M) := t
    let mapq := exteriorPower.map n (quotientMap k g h).toLinearMap
    change a ((show (idealInvariants.{u,v,w} h).obj M from tq
      (exteriorPower.map n (LinearMap.id (R := k)) (mapq x))) (1 : U k (g ⧸ h))) =
      a ((show (idealInvariants.{u,v,w} h).obj M from tq
        (mapq (exteriorPower.map n (LinearMap.id (R := k)) x))) (1 : U k (g ⧸ h)))
    simp

/-- Restriction, as a transformation of the actual cochain functors. -/
def restrictionCochainNat :
    (chevalleyEilenberg.{u,v,w} k g).functor ⟶
      restrictIdeal.{u,v,w} h ⋙ (chevalleyEilenberg.{u,v,w} k h).functor where
  app M := restrictionCochain.{u,v,w} h M
  naturality M N a := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro x
    let tg : CE.W k g n →ₗ[k] (underlying k g).obj M := t
    let mapi := exteriorPower.map n h.incl.toLinearMap
    change a (tg (exteriorPower.map n (LinearMap.id (R := k)) (mapi x))) =
      a (tg (mapi (exteriorPower.map n (LinearMap.id (R := k)) x)))
    simp

def edgeCochains :
    EdgeCochains h (chevalleyEilenberg.{u,v,w} k g)
      (chevalleyEilenberg.{u,v,w} k h) (chevalleyEilenberg.{u,v,w} k (g ⧸ h)) where
  inflation := inflationCochainNat.{u,v,w} h
  restriction := restrictionCochainNat.{u,v,w} h
  inflation_formula M n t x := by
    exact pullback_wedge (quotientMap k g h) (inflationCoefficient.{u,v,w} h M).hom n t x
  restriction_formula M n t x := by
    exact pullback_wedge h.incl (restrictionCoefficient.{u,v,w} h M).hom n t x

theorem edge_cochains : EdgeCochainsStatement.{u,v,w} := by
  intro k g _ _ _ h
  exact ⟨chevalleyEilenberg k g, chevalleyEilenberg k h, chevalleyEilenberg k (g ⧸ h),
    ⟨edgeCochains.{u,v,w} h⟩⟩

end EdgeMaps

section ResolutionComparison

open LieQuotientAction P103.Specs.Ch10.Comparison

/-- The categorical injective resolution gives the same augmented module
resolution used in the Chevalley–Eilenberg balance comparison. -/
def moduleInjectiveResolution {R : Type r} [Ring R] {X : ModuleCat.{max r w} R}
    (I : CategoryTheory.InjectiveResolution X) :
    P103.Specs.Ch10.Comparison.InjectiveResolution R X := by
  let e := HomologicalComplex.singleObjXSelf (.up ℕ) 0 X
  let a := e.inv ≫ I.ι.f 0
  have hz : a ≫ I.cocomplex.d 0 1 = 0 := by simp [a]
  let S := ShortComplex.mk a (I.cocomplex.d 0 1) hz
  have hlim : IsLimit (KernelFork.ofι a hz) :=
    IsLimit.ofIsoLimit I.isLimitKernelFork
      (Fork.ext e (by simp [a]))
  exact
    { complex := I.cocomplex
      injectiveTerm := fun n =>
        (Module.injective_iff_injective_object R (I.cocomplex.X n)).mpr (I.injective n)
      η := a.hom
      injective_η := (ModuleCat.mono_iff_injective a).mp (by dsimp [a]; infer_instance)
      exact_zero := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
        (S.exact_of_f_is_kernel hlim)
      exact_succ := fun n =>
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (I.exact_succ n) }

variable (h : LieIdeal k g) (M : ModuleCat.{max u v w} (U k g))

/-- Restriction to the ideal preserves the actual injective modules. -/
theorem restrictIdeal_injective (hM : Injective M) :
    Injective ((restrictIdeal.{u,v,w} h).obj M) := by
  letI : Module.Injective (U k g) M :=
    (Module.injective_iff_injective_object (U k g) M).mpr hM
  exact (Module.injective_iff_injective_object (U k h)
    ((restrictIdeal.{u,v,w} h).obj M)).mp
    (IdealEnveloping.restriction_spec.{u,v,w} k g h M)

/-- The underlying complex of categorical ideal invariants is the same
complex used by the upstream comparison for the quotient action. -/
def idealResolutionIso (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) :
    (((idealInvariants.{u,v,w} h ⋙ underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).obj
      I.complex) ≅ invariantResolutionComplex h I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (idealInvariantEquiv.{u,v,w} h (I.complex.X n)).toModuleIso)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      apply Subtype.ext
      simp only [invariantResolutionComplex, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      rfl)

end ResolutionComparison

end AdvancedHomologicalAlgebra.LieHochschildSerre

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.Category
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

section ResolutionValues

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

open HomologicalComplex

/-- Extension by zero commutes with applying an additive functor termwise. -/
def mapExtendIso (F : A ⥤ B) [F.Additive]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (K : HomologicalComplex A c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅ ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents
    (fun j' => by
      classical
      by_cases hj' : ∃ j, e.f j = j'
      · exact F.mapIso (K.extendXIso e hj'.choose_spec) ≪≫
          (((F.mapHomologicalComplex c).obj K).extendXIso e hj'.choose_spec).symm
      · exact (F.map_isZero (K.isZero_extend_X e j' (fun j h => hj' ⟨j, h⟩))).iso
          (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j' (fun j h => hj' ⟨j, h⟩)))
    (by
      classical
      intro i' j' hij'
      by_cases hi' : ∃ i, e.f i = i'
      · by_cases hj' : ∃ j, e.f j = j'
        · simp only [dite_eq_left hi', dite_eq_left hj', Iso.trans_hom, Iso.symm_hom,
            Functor.mapIso_hom, extend_d_eq _ _ hi'.choose_spec
              hj'.choose_spec, Category.assoc, Iso.inv_hom_id_assoc]
          simp only [Functor.mapHomologicalComplex_obj_d, extend_d_eq K e hi'.choose_spec
            hj'.choose_spec, Functor.map_comp, Category.assoc]
          rw [← F.map_comp_assoc (K.extendXIso e hj'.choose_spec).inv
            (K.extendXIso e hj'.choose_spec).hom, Iso.inv_hom_id, F.map_id, id_comp]
        · simp only [dite_eq_right hj']
          apply (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j'
            (fun j h => hj' ⟨j, h⟩)).eq_of_tgt
      · apply (F.map_isZero (K.isZero_extend_X e i' (fun i h => hi' ⟨i, h⟩))).eq_of_src)

lemma mapExtendIso_hom_f (F : A ⥤ B) [F.Additive]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (K : HomologicalComplex A c) {i : ι} {i' : ι'} (hi : e.f i = i') :
    (mapExtendIso F e K).hom.f i' = F.map (K.extendXIso e hi).hom ≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e hi).inv := by
  classical
  have h : ∃ j, e.f j = i' := ⟨i, hi⟩
  have h' : h.choose = i := e.injective_f (h.choose_spec.trans hi.symm)
  subst i
  simp [mapExtendIso, h]

@[reassoc]
lemma mapExtendIso_natural (F : A ⥤ B) [F.Additive]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    {K L : HomologicalComplex A c} (f : K ⟶ L) :
    (F.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso F e L).hom =
      (mapExtendIso F e K).hom ≫ extendMap ((F.mapHomologicalComplex c).map f) e := by
  apply HomologicalComplex.hom_ext
  intro i'
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    simp only [HomologicalComplex.comp_f, mapExtendIso_hom_f F e _ hi,
      Functor.mapHomologicalComplex_map_f, extendMap_f _ e hi, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp_assoc (L.extendXIso e hi).inv
      (L.extendXIso e hi).hom, Iso.inv_hom_id, F.map_id, id_comp]
  · apply (F.map_isZero (K.isZero_extend_X e i' (fun i h => hi ⟨i,h⟩))).eq_of_src

variable [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

abbrev resolutionEmbedding := ComplexShape.embeddingUpNat

/-- The bounded-below complex of an ordinary injective resolution. -/
def resolutionPlus {X : A} (I : InjectiveResolution X) : CochainComplex.Plus A :=
  ⟨I.cocomplex.extend resolutionEmbedding, 0, inferInstance⟩

instance resolutionPlus_injective {X : A} (I : InjectiveResolution X) (n : ℤ) :
    Injective ((resolutionPlus I).obj.X n) := by
  letI : ∀ n, Injective (I.cocomplex.X n) := I.injective
  exact inferInstanceAs (Injective ((I.cocomplex.extend resolutionEmbedding).X n))

instance resolutionPlus_unit_isIso (F : A ⥤ B) [F.Additive] {X : A} (I : InjectiveResolution X) :
    IsIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I)) := by
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

/-- The ordinary resolution augmentation, in integer degrees. -/
def resolutionAugmentation {X : A} (I : InjectiveResolution X) :
    (⟨(CochainComplex.singleFunctor A 0).obj X, 0, inferInstance⟩ : CochainComplex.Plus A) ⟶ resolutionPlus I :=
  (CochainComplex.plus A).homMk
    ((extendSingleIso resolutionEmbedding X 0 0 rfl).inv ≫
      extendMap I.ι resolutionEmbedding)

instance resolutionAugmentation_quasiIso {X : A} (I : InjectiveResolution X) :
    QuasiIso (resolutionAugmentation I).hom := by
  dsimp [resolutionAugmentation]
  have h := (quasiIso_extendMap_iff I.ι resolutionEmbedding).mpr (inferInstance : QuasiIso I.ι)
  infer_instance

/-- A lift of a coefficient map also lifts the map of bounded-below stalks. -/
def resolutionPlusMap {X Y : A} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    {a : X ⟶ Y} (f : InjectiveResolution.Hom I J a) : resolutionPlus I ⟶ resolutionPlus J :=
  (CochainComplex.plus A).homMk (extendMap f.hom resolutionEmbedding)

lemma resolutionAugmentation_natural {X Y : A} {I : InjectiveResolution X}
    {J : InjectiveResolution Y} {a : X ⟶ Y} (f : InjectiveResolution.Hom I J a) :
    resolutionAugmentation I ≫ resolutionPlusMap f =
      (CochainComplex.plus A).homMk ((CochainComplex.singleFunctor A 0).map a) ≫
        resolutionAugmentation J := by
  apply (CochainComplex.plus A).ι.map_injective
  change ((extendSingleIso resolutionEmbedding X 0 0 rfl).inv ≫
    extendMap I.ι resolutionEmbedding) ≫ extendMap f.hom resolutionEmbedding =
    (CochainComplex.singleFunctor A 0).map a ≫
    (extendSingleIso resolutionEmbedding Y 0 0 rfl).inv ≫ extendMap J.ι resolutionEmbedding
  have he :
      (extendSingleIso resolutionEmbedding X 0 0 rfl).inv ≫
        extendMap ((CochainComplex.single₀ A).map a) resolutionEmbedding =
      (CochainComplex.singleFunctor A 0).map a ≫
        (extendSingleIso resolutionEmbedding Y 0 0 rfl).inv := by
    apply hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [comp_f, extendSingleIso_inv_f, Category.assoc]
      have h0 : resolutionEmbedding.f (0 : ℕ) = (0 : ℤ) := rfl
      have hmap := extendMap_f ((CochainComplex.single₀ A).map a) resolutionEmbedding h0
      rw [hmap]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      change _ = ((single A (.up ℤ) 0).map a).f 0 ≫ _
      rw [single_map_f_self, single_map_f_self]
      simp
    · exact (isZero_single_obj_X (.up ℤ) 0 X n hn).eq_of_src _ _
  rw [Category.assoc, ← extendMap_comp, f.ι_comp_hom, extendMap_comp, ← Category.assoc, he]
  simp only [Category.assoc]

/-- The natural comparison with termwise application to an actual injective resolution. -/
def rightDerivedResolutionIso (F : A ⥤ B) [F.Additive] {X : A}
    (I : InjectiveResolution X) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (resolutionPlus I)) := by
  have hi : IsIso (DerivedCategory.Plus.Q.map (resolutionAugmentation I)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso A) _
      (resolutionAugmentation_quasiIso I)
  exact F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map (resolutionAugmentation I))) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I))).symm

@[reassoc]
lemma rightDerivedResolutionIso_unit (F : A ⥤ B) [F.Additive] {X : A}
    (I : InjectiveResolution X) :
    (rightDerivedResolutionIso F I).hom ≫ F.rightDerivedFunctorPlusUnit.app (resolutionPlus I) =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (resolutionAugmentation I)) := by
  simp [rightDerivedResolutionIso]

def rightValueResolutionIso (F : A ⥤ B) [F.Additive] (n : ℕ) {X : A}
    (I : InjectiveResolution X) :
    (rightValue F n).obj X ≅ ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).mapIso (rightDerivedResolutionIso F I) ≪≫
    (DerivedCategory.homologyFunctorFactors B (n : ℤ)).app _ ≪≫
    (homologyFunctor B (.up ℤ) (n : ℤ)).mapIso (mapExtendIso F resolutionEmbedding I.cocomplex) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso resolutionEmbedding rfl

@[reassoc]
lemma rightDerivedResolutionIso_natural (F : A ⥤ B) [F.Additive]
    {X Y : A} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    {a : X ⟶ Y} (f : InjectiveResolution.Hom I J a) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map a) ≫
      (rightDerivedResolutionIso F J).hom =
      (rightDerivedResolutionIso F I).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map (resolutionPlusMap f)) := by
  let T := F.rightDerivedFunctorPlus
  let Q := DerivedCategory.Plus.Q (C := A)
  let Q' := DerivedCategory.Plus.Q (C := B)
  let η := F.rightDerivedFunctorPlusUnit
  change T.map (Q.map ((CochainComplex.plus A).homMk ((CochainComplex.singleFunctor A 0).map a))) ≫
      T.map (Q.map (resolutionAugmentation J)) ≫ inv (η.app (resolutionPlus J)) =
      (T.map (Q.map (resolutionAugmentation I)) ≫ inv (η.app (resolutionPlus I))) ≫
        Q'.map (F.mapCochainComplexPlus.map (resolutionPlusMap f))
  rw [Category.assoc, ← cancel_mono (η.app (resolutionPlus J))]
  simp only [Category.assoc, IsIso.inv_hom_id, comp_id]
  have he := η.naturality (resolutionPlusMap f)
  change Q'.map (F.mapCochainComplexPlus.map (resolutionPlusMap f)) ≫ η.app (resolutionPlus J) =
    η.app (resolutionPlus I) ≫ T.map (Q.map (resolutionPlusMap f)) at he
  rw [he, IsIso.inv_hom_id_assoc, ← T.map_comp, ← T.map_comp,
    ← Q.map_comp, ← Q.map_comp, resolutionAugmentation_natural f]

@[reassoc]
lemma rightValueResolutionIso_natural (F : A ⥤ B) [F.Additive] (n : ℕ)
    {X Y : A} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    {a : X ⟶ Y} (f : InjectiveResolution.Hom I J a) :
    (rightValue F n).map a ≫ (rightValueResolutionIso F n J).hom =
      (rightValueResolutionIso F n I).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℕ)).map f.hom) n := by
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let H' := homologyFunctor B (.up ℤ) (n : ℤ)
  let e := resolutionEmbedding
  let Φ := (F.mapHomologicalComplex (.up ℕ)).map f.hom
  change H.map (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map a)) ≫ _ = _
  simp only [rightValueResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← H.map_comp_assoc, rightDerivedResolutionIso_natural F f, H.map_comp, Category.assoc]
  congr 1
  erw [(DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.naturality_assoc
    ((F.mapHomologicalComplex (.up ℤ)).map (extendMap f.hom e))]
  congr 1
  rw [← H'.map_comp_assoc, mapExtendIso_natural F e f.hom, H'.map_comp, Category.assoc]
  congr 1
  exact extendHomologyIso_hom_naturality Φ e rfl

@[reassoc]
lemma rightDerivedResolutionIso_natTrans {F G : A ⥤ B} [F.Additive] [G.Additive]
    (τ : F ⟶ G) {X : A} (I : InjectiveResolution X) :
    τ.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
      (rightDerivedResolutionIso G I).hom =
      (rightDerivedResolutionIso F I).hom ≫
        DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app (resolutionPlus I)) := by
  rw [← cancel_mono (G.rightDerivedFunctorPlusUnit.app (resolutionPlus I))]
  simp only [Category.assoc, rightDerivedResolutionIso_unit]
  rw [← NatTrans.rightDerivedFunctorPlus_fac_app τ (resolutionPlus I),
    rightDerivedResolutionIso_unit_assoc]
  exact (τ.rightDerivedFunctorPlus.naturality
    (DerivedCategory.Plus.Q.map (resolutionAugmentation I))).symm

end ResolutionValues

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Limits
open Shared.Lie

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) (M : ModuleCat.{max u v w} (U k g))

/-- An ambient invariant is a quotient invariant of the ideal invariants,
with the same evaluation at the unit. -/
def compositeInvariantsMap :
    ((idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h).obj M) ⟶
      (lieInvariants.{u,v,w} k g).obj M := by
  let F := idealInvariants.{u,v,w} h
  let G := quotientInvariants.{u,v,w} h
  let E := lieInvariants.{u,v,w} k g
  refine ModuleCat.ofHom (X := (F ⋙ G).obj M) (Y := E.obj M) ?_
  refine
    { toFun := fun z => (ModuleCat.CoextendScalars.equiv
        (Shared.Lie.augmentation k g).toRingHom M).symm
        { toFun := fun r => (show G.obj (F.obj M) from z) r (1 : U k (g ⧸ h))
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro s t
    let Z := ModuleCat.CoextendScalars.equiv
      (Shared.Lie.augmentation k (g ⧸ h)).toRingHom (F.obj M) z
    change Z (s + t) (1 : U k (g ⧸ h)) = _
    rw [_root_.map_add]
    rfl
  · intro a r
    let Z := ModuleCat.CoextendScalars.equiv
      (Shared.Lie.augmentation k (g ⧸ h)).toRingHom (F.obj M) z
    let r' : k := r
    change Z (Shared.Lie.augmentation k g a * r') (1 : U k (g ⧸ h)) =
      a • (Z r' (1 : U k (g ⧸ h)))
    rw [augmentation_quotient h]
    let r'' : (ModuleCat.restrictScalars (Shared.Lie.augmentation k (g ⧸ h)).toRingHom).obj
        (ModuleCat.of k k) := r'
    have he := Z.map_smul (envelopingQuotient h a) r''
    change Z (Shared.Lie.augmentation k (g ⧸ h) (envelopingQuotient h a) * r') =
      envelopingQuotient h a • Z r' at he
    erw [he]
    change Z r' (1 * envelopingQuotient h a) = _
    rw [one_mul, idealCoextend_apply]
  · intro z t
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro r
    rfl
  · intro s z
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro r
    rfl

@[simp]
lemma compositeInvariantsMap_apply
    (z : ((idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h).obj M)) (r : k) :
    compositeInvariantsMap h M z r =
      (show (quotientInvariants.{u,v,w} h).obj ((idealInvariants.{u,v,w} h).obj M) from z) r
        (1 : U k (g ⧸ h)) := rfl

lemma compositeInvariantsMap_injective : Function.Injective (compositeInvariantsMap h M) := by
  intro z t he
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro r
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := envelopingQuotient_surjective h a
  let z' : (quotientInvariants.{u,v,w} h).obj ((idealInvariants.{u,v,w} h).obj M) := z
  let t' : (quotientInvariants.{u,v,w} h).obj ((idealInvariants.{u,v,w} h).obj M) := t
  change z' r (envelopingQuotient h b) = t' r (envelopingQuotient h b)
  rw [idealCoextend_apply, idealCoextend_apply]
  exact congrArg (fun m : (lieInvariants.{u,v,w} k g).obj M => b • m r) he

lemma compositeInvariantsMap_surjective : Function.Surjective (compositeInvariantsMap h M) := by
  intro t
  let F := idealInvariants.{u,v,w} h
  let G := quotientInvariants.{u,v,w} h
  let V := lieInvariantInclusion.{u,v,w} k g
  have hV : ∀ y, coefficientRepresentation k g M y (t (1 : k)) = 0 :=
    (V.range M (t (1 : k))).mp ⟨t, rfl⟩
  let m : LieQuotientAction.invariants h (coefficientRepresentation k g M) :=
    ⟨t (1 : k), fun y => hV y⟩
  let z : (underlying k (g ⧸ h)).obj (F.obj M) := (idealInvariantEquiv h M).symm m
  have hz : ∀ y, coefficientRepresentation k (g ⧸ h) (F.obj M) y z = 0 := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ x =>
    apply (idealInvariantEquiv h M).injective
    apply Subtype.ext
    change (idealInvariantEquiv h M
      (inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h x) • z)).val = 0
    change (show F.obj M from z) (1 * inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h x)) = 0
    rw [one_mul, ← envelopingQuotient_inclusion, idealCoextend_apply]
    have hz' : (show F.obj M from z) (1 : U k (g ⧸ h)) = m.val :=
      congrArg Subtype.val ((idealInvariantEquiv h M).apply_symm_apply m)
    rw [hz']
    exact hV x
  let Vq := lieInvariantInclusion.{u,v,w} k (g ⧸ h)
  obtain ⟨s, hs⟩ := (Vq.range (F.obj M) z).mpr hz
  refine ⟨s, ?_⟩
  apply V.injective M
  change compositeInvariantsMap h M s (1 : k) = t (1 : k)
  have hsz : (show G.obj (F.obj M) from s) (1 : k) = z := hs
  rw [compositeInvariantsMap_apply, hsz]
  exact congrArg Subtype.val ((idealInvariantEquiv h M).apply_symm_apply m)

def compositeInvariantsEvaluationIso :
    idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h ≅ lieInvariants.{u,v,w} k g :=
  NatIso.ofComponents (fun M => (LinearEquiv.ofBijective (compositeInvariantsMap h M).hom
    ⟨compositeInvariantsMap_injective h M, compositeInvariantsMap_surjective h M⟩).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply ModuleCat.CoextendScalars.ext
      apply LinearMap.ext
      intro r
      rfl)

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe a b c

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type a} [Ring R] {ι : Type b} {s : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{c} R) s}

private theorem cycleBoundaries_eq_range
    (K : HomologicalComplex (ModuleCat.{c} R) s) (n : ι) :
    (K.sc n).moduleCatToCycles.range = cycleBoundaries K n := by
  ext z
  change (∃ x, _ = z) ↔ ∃ x, _ = z.val
  exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩,
    fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

/-- The categorical homology of a module complex is its actual cycle quotient. -/
def moduleQuotientHomologyIso (K : HomologicalComplex (ModuleCat.{c} R) s) (n : ι) :
    K.homology n ≅ (quotientHomology s n).obj K :=
  (K.sc n).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (cycleBoundaries_eq_range K n)).toModuleIso

@[reassoc]
theorem moduleQuotientHomologyIso_π
    (K : HomologicalComplex (ModuleCat.{c} R) s) (n : ι) :
    K.homologyπ n ≫ (moduleQuotientHomologyIso K n).hom =
      (K.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (homologyClass K n) := by
  simp only [moduleQuotientHomologyIso, Iso.trans_hom, ← Category.assoc]
  unfold HomologicalComplex.homologyπ
  rw [(K.sc n).π_moduleCatCyclesIso_hom]
  rw [Category.assoc]
  rfl

/-- This identification carries the categorical map to the map on cycle classes. -/
@[reassoc]
theorem moduleQuotientHomologyIso_natural (f : K ⟶ L) (n : ι) :
    HomologicalComplex.homologyMap f n ≫ (moduleQuotientHomologyIso L n).hom =
      (moduleQuotientHomologyIso K n).hom ≫ (quotientHomology s n).map f := by
  have h : HomologicalComplex.cyclesMap f n ≫ (L.sc n).moduleCatCyclesIso.hom =
      (K.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (cyclesMap f n) := by
    rw [← cancel_mono (L.sc n).moduleCatLeftHomologyData.i]
    simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i]
    change HomologicalComplex.cyclesMap f n ≫ L.iCycles n =
      (K.sc n).moduleCatCyclesIso.hom ≫ _ ≫ _
    rw [HomologicalComplex.cyclesMap_i]
    rw [show ModuleCat.ofHom (cyclesMap f n) ≫ (L.sc n).moduleCatLeftHomologyData.i =
        (K.sc n).moduleCatLeftHomologyData.i ≫ f.f n from rfl,
      ← Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i]
    rfl
  rw [← cancel_epi (K.homologyπ n)]
  calc
    _ = HomologicalComplex.cyclesMap f n ≫
          ((L.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (homologyClass L n)) := by
        rw [HomologicalComplex.homologyπ_naturality_assoc, moduleQuotientHomologyIso_π]
    _ = (K.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (homologyClass K n) ≫
          (quotientHomology s n).map f := by
        rw [← Category.assoc, h, Category.assoc]
        rfl
    _ = _ := by rw [moduleQuotientHomologyIso_π_assoc]

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Category
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre
section ClassicalIso
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- An isomorphism of additive functors induces the corresponding isomorphism
on every classical derived value, by functoriality of the canonical unit. -/
def rightValueNatIso (e : F ≅ G) (n : ℕ) : rightValue F n ≅ rightValue G n :=
  isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (isoWhiskerRight
      { hom := e.hom.rightDerivedFunctorPlus
        inv := e.inv.rightDerivedFunctorPlus
        hom_inv_id := by simp [← NatTrans.rightDerivedFunctorPlus_comp]
        inv_hom_id := by simp [← NatTrans.rightDerivedFunctorPlus_comp] }
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)))

end ClassicalIso
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Category
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedHomologicalAlgebra.LieHochschildSerre
section DerivedValueMap

open HomologicalComplex
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

@[reassoc]
lemma mapExtendIso_natTrans (τ : F ⟶ G) {ι ι' : Type*}
    {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (K : HomologicalComplex A c) :
    (τ.mapHomologicalComplex c').app (K.extend e) ≫ (mapExtendIso G e K).hom =
      (mapExtendIso F e K).hom ≫ extendMap ((τ.mapHomologicalComplex c).app K) e := by
  apply hom_ext
  intro i'
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    simp only [comp_f, mapExtendIso_hom_f _ e K hi, extendMap_f _ e hi, Category.assoc,
      NatTrans.mapHomologicalComplex_app_f, Iso.inv_hom_id_assoc]
    rw [← τ.naturality_assoc]
  · exact (F.map_isZero (K.isZero_extend_X e i' (fun i hi => h ⟨i,hi⟩))).eq_of_src _ _

variable [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

@[reassoc]
lemma rightValueResolutionIso_natIso (τ : F ≅ G) (n : ℕ)
    {X : A} (I : InjectiveResolution X) :
    (rightValueNatIso τ n).hom.app X ≫ (rightValueResolutionIso G n I).hom =
      (rightValueResolutionIso F n I).hom ≫
        homologyMap ((τ.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex) n := by
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let H' := homologyFunctor B (.up ℤ) (n : ℤ)
  let e := resolutionEmbedding
  let Φ := (τ.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex
  change H.map (τ.hom.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫ _ = _
  simp only [rightValueResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← H.map_comp_assoc, rightDerivedResolutionIso_natTrans τ.hom I, H.map_comp, Category.assoc]
  congr 1
  erw [(DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.naturality_assoc
    ((τ.hom.mapHomologicalComplex (.up ℤ)).app (I.cocomplex.extend e))]
  congr 1
  rw [← H'.map_comp_assoc, mapExtendIso_natTrans τ.hom e I.cocomplex, H'.map_comp, Category.assoc]
  congr 1
  exact extendHomologyIso_hom_naturality Φ e rfl

end DerivedValueMap
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Limits

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

section ResolutionLifts

open HomologicalComplex
variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- Chain maps into a K-injective complex realize all morphisms in the derived category. -/
theorem derivedMap_surjective_to_injective (L K : CochainComplex A ℤ) [K.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (L ⟶ K) → _) := by
  intro f
  let E := DerivedCategory.quotientCompQhIso A
  let T := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (T.obj L) K).surjective
    (E.hom.app L ≫ f ≫ E.inv.app K)
  obtain ⟨b, rfl⟩ := T.map_surjective g
  refine ⟨b, ?_⟩
  apply (cancel_epi (E.hom.app L)).mp
  apply (cancel_mono (E.inv.app K)).mp
  have hn := E.hom.naturality b
  simp only [Functor.comp_map] at hn
  rw [← hn, hg]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Equality in the derived category for maps into an injective model is homotopy. -/
def homotopy_of_derivedMap_eq_to_injective {L K : CochainComplex A ℤ} [K.IsKInjective]
    {f g : L ⟶ K} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Homotopy f g := by
  let E := DerivedCategory.quotientCompQhIso A
  let T := HomotopyCategory.quotient A (.up ℤ)
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective (T.obj L) K).injective
  have hf := E.hom.naturality f
  have hg := E.hom.naturality g
  simp only [Functor.comp_map] at hf hg
  rw [← cancel_mono (E.hom.app K), hf, hg, h]

/-- A map from the object into an injective complex extends to any
ordinary injective resolution of that object. -/
theorem liftFromInjectiveResolution {X : A} (J : InjectiveResolution X)
    (K : CochainComplex A ℕ) (a : (CochainComplex.single₀ A).obj X ⟶ K)
    (hK : ∀ n, Injective (K.X n)) :
    ∃ s : J.cocomplex ⟶ K, J.ι ≫ s = a := by
  letI := hK
  let e := resolutionEmbedding
  let E := e.extendFunctor A
  let i := E.map J.ι
  let a' := E.map a
  have hi : QuasiIso i := (quasiIso_extendMap_iff J.ι e).mpr inferInstance
  letI := hi
  haveI : CochainComplex.IsKInjective (E.obj K) := inferInstanceAs (CochainComplex.IsKInjective (K.extend ComplexShape.embeddingUpNat))
  let y : DerivedCategory.Q.obj (E.obj J.cocomplex) ⟶ DerivedCategory.Q.obj (E.obj K) :=
    inv (DerivedCategory.Q.map i) ≫ DerivedCategory.Q.map a'
  have hsurj := derivedMap_surjective_to_injective (E.obj J.cocomplex) (E.obj K)
  obtain ⟨s', hs'⟩ := hsurj y
  obtain ⟨s, hs⟩ := (E.map_surjective (X := J.cocomplex) (Y := K)) s'
  refine ⟨s, E.map_injective ?_⟩
  rw [E.map_comp, hs]
  have h : DerivedCategory.Q.map (i ≫ s') = DerivedCategory.Q.map a' := by
    rw [Functor.map_comp, hs']
    dsimp [y]
    exact IsIso.hom_inv_id_assoc _ _
  have H := homotopy_of_derivedMap_eq_to_injective h
  apply hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    have h0 := H.comm 0
    have hd : dNext 0 H.hom = 0 := by simp [dNext, E, e]
    have hd' : prevD 0 H.hom = 0 := by
      rw [prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)]
      have hz : IsZero ((K.extend e).X (-1)) :=
        K.isZero_extend_X e (-1) (fun n h => by change (n : ℤ) = -1 at h; omega)
      change H.hom 0 (-1) ≫ (K.extend e).d (-1) 0 = 0
      rw [hz.eq_of_src ((K.extend e).d (-1) 0) 0, comp_zero]
    simpa only [hd, hd', zero_add] using h0
  · have hz : IsZero ((E.obj ((CochainComplex.single₀ A).obj X)).X n) := by
      exact isZero_single_obj_X (.up ℤ) 0 X n hn |>.of_iso
        ((HomologicalComplex.eval A (.up ℤ) n).mapIso (extendSingleIso e X 0 0 rfl))
    exact hz.eq_of_src _ _

end ResolutionLifts

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

section RowModels

open GrothendieckEdges GrothendieckSpectralSequence
open HomologicalComplex

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

local notation "Q" => DerivedCategory.Plus.Q
local notation "Qh" => DerivedCategory.Plus.Qh

/-- The composition comparison commutes with the units on cochain models. -/
@[reassoc]
lemma composition_unit_on_complex (I : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app I ≫ (comparisonValue F G).app ((Q).obj I) =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj I) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app I) := by
  let I' := (HomotopyCategory.Plus.quotient A).obj I
  have h := congrArg (fun t => t.app I') (RightDerivedComposition.comparisonUniversal A B C F G).1
  simp only [inputComparisonValue, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id] at h
  have hm : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app I' =
      𝟙 _ := by
    apply (HomotopyCategory.Plus.ι C).map_injective
    change (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I.obj) = _
    change (HomotopyCategory.quotient C (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app I.obj) = _
    rw [(HomotopyCategory.Plus.ι C).map_id]
    erw [← (HomotopyCategory.quotient C (.up ℤ)).map_id]
    congr 1
  rw [hm, (Qh).map_id] at h
  erw [Category.id_comp] at h
  simp only [Functor.rightDerivedFunctorPlusUnit_app, Category.assoc]
  have hn := (comparisonValue F G).naturality
    ((DerivedCategory.Plus.quotientCompQhIso A).hom.app I)
  change (F ⋙ G).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso A).hom.app I) ≫
        (comparisonValue F G).app ((Q).obj I) =
    (comparisonValue F G).app ((Qh).obj I') ≫
      G.rightDerivedFunctorPlus.map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app I)) at hn
  rw [hn]
  have hh := congrArg (fun t =>
    (DerivedCategory.Plus.quotientCompQhIso C).inv.app ((F ⋙ G).mapCochainComplexPlus.obj I) ≫
      t ≫ G.rightDerivedFunctorPlus.map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app I))) h
  simp only [Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_obj] at *
  -- The two middle copies of the comparison between Qh and Q cancel.
  have qid_C (T : HomotopyCategory.Plus C) :
      (Qh).map (𝟙 T) = 𝟙 ((Qh).obj T) := CategoryTheory.Functor.map_id _ _
  have qid_B (T : HomotopyCategory.Plus B) :
      (Qh).map (𝟙 T) = 𝟙 ((Qh).obj T) := CategoryTheory.Functor.map_id _ _
  erw [qid_C, qid_B]
  let e := (DerivedCategory.Plus.quotientCompQhIso B).app (F.mapCochainComplexPlus.obj I)
  let b := F.rightDerivedFunctorPlusUnith.app I'
  let a := F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app I)
  let c := G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj I')
  have hG : G.rightDerivedFunctorPlus.map e.hom ≫
      G.rightDerivedFunctorPlus.map (e.inv ≫ 𝟙 _ ≫ b ≫ a) =
        G.rightDerivedFunctorPlus.map b ≫ G.rightDerivedFunctorPlus.map a := by
    rw [← G.rightDerivedFunctorPlus.map_comp, Iso.hom_inv_id_assoc, Category.id_comp,
      G.rightDerivedFunctorPlus.map_comp]
  erw [hG]
  have h₁ : 𝟙 _ ≫ (F ⋙ G).rightDerivedFunctorPlusUnith.app I' ≫
      (comparisonValue F G).app ((Qh).obj I') ≫ G.rightDerivedFunctorPlus.map a =
        (F ⋙ G).rightDerivedFunctorPlusUnith.app I' ≫
      (comparisonValue F G).app ((Qh).obj I') ≫ G.rightDerivedFunctorPlus.map a := Category.id_comp _
  have h₂ : 𝟙 _ ≫ c ≫ G.rightDerivedFunctorPlus.map b ≫ G.rightDerivedFunctorPlus.map a =
      c ≫ G.rightDerivedFunctorPlus.map b ≫ G.rightDerivedFunctorPlus.map a := Category.id_comp _
  erw [h₁, h₂]
  simp only [Category.assoc] at hh
  exact hh

/-- The map from the stalk of F(X) into termwise F of the chosen resolution. -/
def mappedResolutionAugmentation {X : A} (I : InjectiveResolution X) :
    (stalkComplex B).obj (F.obj X) ⟶ F.mapCochainComplexPlus.obj (resolutionPlus I) :=
  (CochainComplex.plus B).homMk
    (Y := F.mapCochainComplexPlus.obj ((stalkComplex A).obj X))
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X) ≫
    F.mapCochainComplexPlus.map (resolutionAugmentation I)

@[reassoc]
lemma stalkToDerived_on_resolution {X : A} (I : InjectiveResolution X) :
    (stalkToDerived F).app X ≫ (rightDerivedResolutionIso F I).hom =
      (Q).map (mappedResolutionAugmentation F I) := by
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I))]
  simp only [Category.assoc, rightDerivedResolutionIso_unit, stalkToDerived,
    NatTrans.comp_app, whiskerLeft_app]
  have h := (F.rightDerivedFunctorPlusUnit.naturality (resolutionAugmentation I)).symm
  change F.rightDerivedFunctorPlusUnit.app ((stalkComplex A).obj X) ≫
      F.rightDerivedFunctorPlus.map ((Q).map (resolutionAugmentation I)) =
    (Q).map (F.mapCochainComplexPlus.map (resolutionAugmentation I)) ≫
      F.rightDerivedFunctorPlusUnit.app (resolutionPlus I) at h
  rw [h]
  simp only [mappedResolutionAugmentation, Functor.map_comp, Category.assoc]
  congr 1
  apply (DerivedCategory.Plus.ι (C := B)).map_injective
  simp only [mappedStalkIso, FullyFaithful.preimageIso_hom, FullyFaithful.whiskeringRight_preimage_app,
    FullyFaithful.map_preimage, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, associator_inv_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.symm_hom, associator_hom_app, DerivedCategory.singleFunctorIsoCompQ_hom_app,
    Category.id_comp, Category.comp_id]
  change (𝟙 _ : _ ⟶ _) ≫ _ = _
  simp only [Category.id_comp, Iso.trans_hom, NatTrans.comp_app,
    associator_inv_app, isoWhiskerRight_hom, Iso.symm_hom, whiskerRight_app,
    associator_hom_app, Category.comp_id]
  rfl

@[reassoc]
lemma composition_on_resolution {X : A} (I : InjectiveResolution X) :
    (comparisonValue F G).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
      G.rightDerivedFunctorPlus.map (rightDerivedResolutionIso F I).hom =
    (rightDerivedResolutionIso (F ⋙ G) I).hom ≫
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj (resolutionPlus I)) := by
  rw [← cancel_mono (G.rightDerivedFunctorPlus.map
    (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I)))]
  simp only [Category.assoc, ← G.rightDerivedFunctorPlus.map_comp,
    rightDerivedResolutionIso_unit]
  rw [← composition_unit_on_complex F G (resolutionPlus I),
    rightDerivedResolutionIso_unit_assoc]
  exact ((comparisonValue F G).naturality ((Q).map (resolutionAugmentation I))).symm

/-- A chain lift of the augmentation computes the derived first edge. -/
lemma derivedFirstEdge_on_resolutions (P : Package F G) {X : A}
    (I : InjectiveResolution X) (J : InjectiveResolution (F.obj X))
    (s : resolutionPlus J ⟶ F.mapCochainComplexPlus.obj (resolutionPlus I))
    (hs : resolutionAugmentation J ≫ s = mappedResolutionAugmentation F I)
    (hI : ∀ n, Injective ((F.mapCochainComplexPlus.obj (resolutionPlus I)).obj.X n))
    (n : ℕ) :
    (derivedFirstEdge F G P n).app X ≫
        (DerivedCategory.Plus.homologyFunctor C (n : ℤ)).map
          (rightDerivedResolutionIso (F ⋙ G) I).hom =
      (DerivedCategory.Plus.homologyFunctor C (n : ℤ)).map
        ((rightDerivedResolutionIso G J).hom ≫ (Q).map (G.mapCochainComplexPlus.map s)) := by
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  letI := hI
  let E := F.mapCochainComplexPlus.obj (resolutionPlus I)
  haveI : IsIso (G.rightDerivedFunctorPlusUnit.app E) := by
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  letI := P.comparison_isIso
  haveI : IsIso (comparisonValue F G) := NatIso.isIso_of_isIso_app _
  have hc := composition_on_resolution F G I
  have hd := stalkToDerived_on_resolution F I
  change (H.map (G.rightDerivedFunctorPlus.map ((stalkToDerived F).app X)) ≫
    H.map ((asIso (comparisonValue F G)).inv.app ((DerivedCategory.Plus.singleFunctor A 0).obj X))) ≫
    H.map (rightDerivedResolutionIso (F ⋙ G) I).hom = _
  rw [Category.assoc]
  rw [← H.map_comp, ← H.map_comp]
  congr 1
  apply (cancel_mono (G.rightDerivedFunctorPlusUnit.app E)).mp
  simp only [Category.assoc]
  rw [← hc]
  have hcancel := (asIso (comparisonValue F G)).inv_hom_id_app_assoc
    ((DerivedCategory.Plus.singleFunctor A 0).obj X)
    (G.rightDerivedFunctorPlus.map (rightDerivedResolutionIso F I).hom)
  erw [hcancel]
  rw [← G.rightDerivedFunctorPlus.map_comp, hd]
  have h := G.rightDerivedFunctorPlusUnit.naturality s
  change (Q).map (G.mapCochainComplexPlus.map s) ≫ G.rightDerivedFunctorPlusUnit.app E =
    G.rightDerivedFunctorPlusUnit.app (resolutionPlus J) ≫ G.rightDerivedFunctorPlus.map ((Q).map s) at h
  rw [h, rightDerivedResolutionIso_unit_assoc, ← G.rightDerivedFunctorPlus.map_comp,
    ← (Q).map_comp, hs]


end RowModels

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance
open scoped ModuleCat.Algebra

universe u v w a b

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
attribute [local instance 100] LieRing.ofAssociativeRing

section IntegerCoordinates

/-- Use the same elements and additive maps in integer-linear coordinates. -/
def integerCoordinates (k : Type u) [Ring k] : ModuleCat.{w} k ⥤ ModuleCat.{w} ℤ where
  obj X := ModuleCat.of ℤ X
  map f := ModuleCat.ofHom f.hom.toAddMonoidHom.toIntLinearMap
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance (k : Type u) [Ring k] : (integerCoordinates.{u,w} k).Additive where
  map_add := by intros; ext; rfl

variable {k : Type u} [Ring k] {ι : Type a} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{w} k) c)

abbrev integerComplex :=
  ((integerCoordinates.{u,w} k).mapHomologicalComplex c).obj K

/-- The two scalar structures have the same cycle vectors. -/
def integerCyclesEquiv (n : ι) : cycles K n ≃ₗ[ℤ] cycles (integerComplex K) n where
  toFun := fun x => ⟨x.val, x.property⟩
  invFun := fun x => ⟨x.val, x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Scalar packaging preserves cycles and boundaries, and hence their quotient. -/
def integerHomologyEquiv (n : ι) : Homology K n ≃ₗ[ℤ] Homology (integerComplex K) n :=
  let e := integerCyclesEquiv K n
  (Submodule.Quotient.restrictScalarsEquiv ℤ (cycleBoundaries K n)).symm.trans
    (Submodule.Quotient.equiv _ _ e (by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hz
        exact ⟨e.symm z, hz, e.apply_symm_apply z⟩))

@[simp]
theorem integerHomologyEquiv_class (n : ι) (z : cycles K n) :
    integerHomologyEquiv K n (homologyClass K n z) =
      homologyClass (integerComplex K) n (integerCyclesEquiv K n z) := rfl

@[simp]
theorem integerHomologyEquiv_natural {L : HomologicalComplex (ModuleCat.{w} k) c}
    (f : K ⟶ L) (n : ι) (x : Homology K n) :
    integerHomologyEquiv L n (homologyMap f n x) =
      homologyMap (((integerCoordinates k).mapHomologicalComplex c).map f) n
        (integerHomologyEquiv K n x) := by
  induction x using Submodule.Quotient.induction_on with | _ z => rfl

end IntegerCoordinates

section LieResolutionComparison

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
attribute [local instance 2000] CE.Ext.trivialModule

/-- The augmented projective resolution given by the actual CE boundary. -/
abbrev lieProjectiveResolution : LeftResolution (U k g) k :=
  CE.Ext.resolution k g (CE.boundary k g) (CE.boundary_augmented k g) (CE.Ext.boundary_exact k g)

theorem lieProjectiveResolution_projective :
    (lieProjectiveResolution (k := k) (g := g)).IsProjective := by
  intro n
  change Module.Projective (U k g) (CE.V k g n)
  let := CE.term_free k g n
  exact Module.Projective.of_free

variable {M N : ModuleCat.{max u v w} (U k g)}

abbrev lieInvComplex (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) :=
  ((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).obj I.complex

/-- The trivial module is the restriction along the augmentation used for coextension. -/
def lieInjectiveHomIso (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) :
    injectiveHom k I.complex ≅ integerComplex (lieInvComplex.{u,v,w} I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (ModuleCat.CoextendScalars.equiv (Shared.Lie.augmentation k g).toRingHom
      (I.complex.X n)).symm.toAddEquiv.toIntLinearEquiv.toModuleIso)
    (by
      intro p q hpq
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      rfl)

def lieEvaluationIso (M : ModuleCat.{max u v w} (U k g)) :
    homComplex (lieProjectiveResolution (k := k) (g := g)).complex M ≅
      integerComplex ((chevalleyEilenberg.{u,v,w} k g).complex M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (CE.homEquiv k g ((underlying k g).obj M) n).toAddEquiv.toIntLinearEquiv.toModuleIso)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [CochainTheory.complex, CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d,
        ModuleCat.hom_comp, LinearMap.comp_apply]
      change CE.coboundary k g ((underlying k g).obj M) (CE.boundary k g) i
          (CE.homEquiv k g ((underlying k g).obj M) i f) =
        CE.homEquiv k g ((underlying k g).obj M) (i + 1)
          (((homComplex lieProjectiveResolution.complex M).d i (i + 1)).hom f)
      rw [P103.Ch11.ExtTorDefinitions.hom_differential]
      simpa only [lieProjectiveResolution, CE.Ext.resolution, CE.Ext.chain, ChainComplex.of_d,
        ModuleCat.hom_ofHom, CE.homCoboundary] using
        CE.coboundary_comparison k g ((underlying k g).obj M) (CE.boundary k g) i f)

def lieResolutionBalance (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) (n : ℕ) :
    Homology (injectiveHom k I.complex) n ≃ₗ[ℤ]
      ExtWith (lieProjectiveResolution (k := k) (g := g)) M n :=
  comparisonOfQuasiIsomorphisms lieProjectiveResolution I
    (projectiveAugmentation lieProjectiveResolution I)
    (injectiveAugmentation lieProjectiveResolution I)
    (projectiveAugmentation_quasiIso _ _ lieProjectiveResolution_projective)
    (injectiveAugmentation_quasiIso _ _) n

theorem lieResolutionBalance_formula
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) (n : ℕ) :
    (homologyMap (projectiveAugmentation lieProjectiveResolution I) n).comp
      (lieResolutionBalance I n).toLinearMap =
        homologyMap (injectiveAugmentation lieProjectiveResolution I) n :=
  comparisonOfQuasiIsomorphisms_formula _ _ _ _ _ _ n

theorem lieResolutionBalance_natural
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (J : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) N)
    (f : M ⟶ N) (m : I.complex ⟶ J.complex)
    (hm : CochainLift (ofInjective I) J f.hom m) (n : ℕ) :
    (lieResolutionBalance J n).toLinearMap.comp
        (homologyMap (injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) m) n) =
      (homologyMap (homPostMap (lieProjectiveResolution (k := k) (g := g)).complex f.hom) n).comp
        (lieResolutionBalance I n).toLinearMap := by
  let P := lieProjectiveResolution (k := k) (g := g)
  have hl : ChainLift P P LinearMap.id (𝟙 P.complex) := by
    apply LinearMap.ext
    intro x
    rfl
  have hh := balance_natural (U k g) k k M N P P I J
    lieProjectiveResolution_projective lieProjectiveResolution_projective
    LinearMap.id f.hom (𝟙 P.complex) m hl hm
    (projectiveAugmentation P I) (injectiveAugmentation P I)
    (projectiveAugmentation P J) (injectiveAugmentation P J)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (projectiveAugmentation_quasiIso _ _ lieProjectiveResolution_projective)
    (projectiveAugmentation_quasiIso _ _ lieProjectiveResolution_projective) n
    (lieResolutionBalance I n) (lieResolutionBalance J n)
    (lieResolutionBalance_formula I n) (lieResolutionBalance_formula J n)
  have hid : homPreMap (𝟙 P.complex) M ≫ homPostMap P.complex f.hom =
      homPostMap P.complex f.hom := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro F
    rfl
  rwa [hid] at hh



private theorem lieInjectiveHomIso_natural
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (J : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) N) (m : I.complex ⟶ J.complex) :
    injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) m ≫ (lieInjectiveHomIso J).hom =
      (lieInjectiveHomIso I).hom ≫
        (((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map
          (((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).map m)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rfl

private theorem lieEvaluationIso_natural (f : M ⟶ N) :
    homPostMap (lieProjectiveResolution (k := k) (g := g)).complex f.hom ≫
        (lieEvaluationIso N).hom =
      (lieEvaluationIso M).hom ≫
        (((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map
          ((chevalleyEilenberg.{u,v,w} k g).functor.map f)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro x
  let t' : CE.V k g n →ₗ[U k g] M := t
  change f (t' ((1 : U k g) ⊗ₜ[k] x)) =
    f (t' ((1 : U k g) ⊗ₜ[k] exteriorPower.map n (LinearMap.id (R := k)) x))
  rw [exteriorPower.map_id, LinearMap.id_apply]

private theorem homologyMap_comp_apply {R : Type a} [Ring R]
    {A B C : CochainComplex (ModuleCat.{b} R) ℕ}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) (x : Homology A n) :
    homologyMap (f ≫ g) n x = homologyMap g n (homologyMap f n x) :=
  congrArg (fun m => m.hom x) ((quotientHomology (.up ℕ) n).map_comp f g)

/-- Canonical comparison for an ordinary injective resolution, on additive quotients. -/
private def lieResolutionCohomologyAdd
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) (n : ℕ) :
    Homology (lieInvComplex I) n ≃ₗ[ℤ]
      Homology ((chevalleyEilenberg.{u,v,w} k g).complex M) n :=
  (integerHomologyEquiv (lieInvComplex I) n).trans
    ((LieQuotientAction.complexHomologyEquiv (lieInjectiveHomIso I).symm n).trans
      ((lieResolutionBalance I n).trans
        ((LieQuotientAction.complexHomologyEquiv (lieEvaluationIso M) n).trans
          (integerHomologyEquiv ((chevalleyEilenberg.{u,v,w} k g).complex M) n).symm)))

private theorem lieResolutionCohomologyAdd_natural
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (J : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) N)
    (f : M ⟶ N) (m : I.complex ⟶ J.complex) (hm : CochainLift (ofInjective I) J f.hom m)
    (n : ℕ) (z : Homology (lieInvComplex I) n) :
    lieResolutionCohomologyAdd J n
        (homologyMap (((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).map m) n z) =
      homologyMap ((chevalleyEilenberg.{u,v,w} k g).functor.map f) n
        (lieResolutionCohomologyAdd I n z) := by
  let F := (lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)
  let D := (chevalleyEilenberg.{u,v,w} k g).functor
  have hh := LinearMap.congr_fun (lieResolutionBalance_natural I J f m hm n)
  have hi := lieInjectiveHomIso_natural I J m
  have hi' : (((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map (F.map m)) ≫
        (lieInjectiveHomIso J).inv =
      (lieInjectiveHomIso I).inv ≫ injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) m := by
    apply (cancel_epi (lieInjectiveHomIso I).hom).mp
    rw [← Category.assoc, ← hi]
    simp
  apply (integerHomologyEquiv (D.obj N) n).injective
  rw [integerHomologyEquiv_natural]
  simp only [lieResolutionCohomologyAdd, LinearEquiv.trans_apply,
    LieQuotientAction.complexHomologyEquiv_apply, Iso.symm_hom]
  rw [integerHomologyEquiv_natural, ← homologyMap_comp_apply, hi', homologyMap_comp_apply]
  rw [show lieResolutionBalance J n
      (homologyMap (injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) m) n
        (homologyMap (lieInjectiveHomIso I).inv n (integerHomologyEquiv (lieInvComplex I) n z))) =
      homologyMap (homPostMap (lieProjectiveResolution (k := k) (g := g)).complex f.hom) n
        (lieResolutionBalance I n
          (homologyMap (lieInjectiveHomIso I).inv n (integerHomologyEquiv (lieInvComplex I) n z))) from hh _]
  rw [← homologyMap_comp_apply, lieEvaluationIso_natural, homologyMap_comp_apply]
  simp only [D, CochainTheory.functor, LinearEquiv.apply_symm_apply]

private theorem homologyMap_smul_id (K : CochainComplex (ModuleCat.{w} k) ℕ)
    (r : k) (n : ℕ) (z : Homology K n) :
    homologyMap (r • 𝟙 K) n z = r • z := by
  induction z using Submodule.Quotient.induction_on with | _ z => rfl

private theorem lieInvariants_map_smul_id (X : ModuleCat.{max u v w} (U k g)) (r : k) :
    (lieInvariants.{u,v,w} k g).map (r • 𝟙 X) = r • 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro x
  let x' : k := x
  change algebraMap k (U k g) r • t x' = t (x' * r)
  have hs := (ModuleCat.CoextendScalars.equiv (Shared.Lie.augmentation k g).toRingHom X t).map_smul
    (algebraMap k (U k g) r) x
  change t (Shared.Lie.augmentation k g (algebraMap k (U k g) r) * x') = _ at hs
  rw [(Shared.Lie.augmentation k g).commutes, mul_comm] at hs
  exact hs.symm

private theorem lieInvComplex_smul_id
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) (r : k) :
    ((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).map (r • 𝟙 I.complex) =
      r • 𝟙 (lieInvComplex I) := by
  ext n : 1
  exact lieInvariants_map_smul_id (I.complex.X n) r

private theorem ceCochain_map_smul_id (X : ModuleCat.{max u v w} (U k g)) (r : k) :
    (chevalleyEilenberg.{u,v,w} k g).functor.map (r • 𝟙 X) =
      r • 𝟙 ((chevalleyEilenberg.{u,v,w} k g).functor.obj X) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro x
  let t' : CE.W k g n →ₗ[k] (underlying k g).obj X := t
  change r • t' (exteriorPower.map n (LinearMap.id (R := k)) x) = r • t' x
  rw [exteriorPower.map_id, LinearMap.id_apply]

/-- The comparison is linear over the base field by naturality for scalar multiplication. -/
def lieResolutionCohomologyEquiv
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) (n : ℕ) :
    Homology (lieInvComplex I) n ≃ₗ[k]
      Homology ((chevalleyEilenberg.{u,v,w} k g).complex M) n :=
  { (lieResolutionCohomologyAdd I n).toAddEquiv with
    map_smul' := fun r z => by
      have hm : CochainLift (ofInjective I) I (r • 𝟙 M : M ⟶ M).hom (r • 𝟙 I.complex) := by
        apply LinearMap.ext
        intro x
        change r • I.η x = I.η (r • x)
        exact ((I.η.restrictScalars k).map_smul r x).symm
      have hh := lieResolutionCohomologyAdd_natural I I (r • 𝟙 M) (r • 𝟙 I.complex) hm n z
      rw [lieInvComplex_smul_id, ceCochain_map_smul_id, homologyMap_smul_id,
        homologyMap_smul_id] at hh
      exact hh }

theorem lieResolutionCohomologyEquiv_integer
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (n : ℕ) (z : Homology (lieInvComplex I) n) :
    integerHomologyEquiv ((chevalleyEilenberg.{u,v,w} k g).complex M) n
      (lieResolutionCohomologyEquiv I n z) =
      homologyMap (lieEvaluationIso M).hom n
        (lieResolutionBalance I n (homologyMap (lieInjectiveHomIso I).inv n
          (integerHomologyEquiv (lieInvComplex I) n z))) := by
  change integerHomologyEquiv _ n (lieResolutionCohomologyAdd I n z) = _
  simp only [lieResolutionCohomologyAdd, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LieQuotientAction.complexHomologyEquiv_apply, Iso.symm_hom]

theorem lieResolutionCohomologyEquiv_natural
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (J : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) N)
    (f : M ⟶ N) (m : I.complex ⟶ J.complex) (hm : CochainLift (ofInjective I) J f.hom m)
    (n : ℕ) (z : Homology (lieInvComplex I) n) :
    lieResolutionCohomologyEquiv J n
        (homologyMap (((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).map m) n z) =
      homologyMap ((chevalleyEilenberg.{u,v,w} k g).functor.map f) n
        (lieResolutionCohomologyEquiv I n z) :=
  lieResolutionCohomologyAdd_natural I J f m hm n z


end LieResolutionComparison

section LieDerivedCohomology

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

theorem moduleInjectiveResolution_lift {R : Type a} [Ring R]
    {X Y : ModuleCat.{max a b} R}
    {I : CategoryTheory.InjectiveResolution X} {J : CategoryTheory.InjectiveResolution Y}
    {f : X ⟶ Y} (m : CategoryTheory.InjectiveResolution.Hom I J f) :
    CochainLift (ofInjective (moduleInjectiveResolution I)) (moduleInjectiveResolution J) f.hom
      m.hom := by
  apply LinearMap.ext
  intro x
  change (m.hom.f 0).hom ((I.ι.f 0).hom x) = (J.ι.f 0).hom (f.hom x)
  have hh := congrArg (fun φ => φ.hom x) m.ι_f_zero_comp_hom_f_zero
  simp only [CochainComplex.single₀_map_f_zero, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
  exact hh

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

/-- Derived invariants compared with the actual CE cohomology through an ordinary resolution. -/
def lieCohomologyIsoAt {M : ModuleCat.{max u v w} (U k g)}
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    (rightValue (lieInvariants.{u,v,w} k g) n).obj M ≅
      ((chevalleyEilenberg.{u,v,w} k g).cohomology n).obj M :=
  rightValueResolutionIso (lieInvariants k g) n I ≪≫
    moduleQuotientHomologyIso (((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) n ≪≫
    (lieResolutionCohomologyEquiv (moduleInjectiveResolution I) n).toModuleIso

@[reassoc]
theorem lieCohomologyIsoAt_natural
    {M N : ModuleCat.{max u v w} (U k g)} {f : M ⟶ N}
    {I : CategoryTheory.InjectiveResolution M} {J : CategoryTheory.InjectiveResolution N}
    (m : CategoryTheory.InjectiveResolution.Hom I J f) (n : ℕ) :
    (rightValue (lieInvariants.{u,v,w} k g) n).map f ≫ (lieCohomologyIsoAt J n).hom =
      (lieCohomologyIsoAt I n).hom ≫ ((chevalleyEilenberg.{u,v,w} k g).cohomology n).map f := by
  simp only [lieCohomologyIsoAt, Iso.trans_hom, Category.assoc]
  rw [rightValueResolutionIso_natural_assoc (lieInvariants k g) n m,
    moduleQuotientHomologyIso_natural_assoc]
  congr 1
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact lieResolutionCohomologyEquiv_natural (moduleInjectiveResolution I)
    (moduleInjectiveResolution J) f m.hom (moduleInjectiveResolution_lift m) n x

/-- The cohomology comparison is natural in all Lie-module coefficient maps. -/
def lieCohomologyIso (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
    [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)] (n : ℕ) :
    rightValue (lieInvariants.{u,v,w} k g) n ≅ (chevalleyEilenberg.{u,v,w} k g).cohomology n :=
  NatIso.ofComponents (fun M => lieCohomologyIsoAt (CategoryTheory.injectiveResolution M) n)
    (by
      intro M N f
      let m : CategoryTheory.InjectiveResolution.Hom (CategoryTheory.injectiveResolution M)
          (CategoryTheory.injectiveResolution N) f :=
        ⟨CategoryTheory.InjectiveResolution.desc f _ _, by simp⟩
      exact lieCohomologyIsoAt_natural m n)

theorem lieCohomologyIso_hom_app {M : ModuleCat.{max u v w} (U k g)}
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    (lieCohomologyIso.{u,v,w} k g n).hom.app M = (lieCohomologyIsoAt I n).hom := by
  let m : CategoryTheory.InjectiveResolution.Hom (CategoryTheory.injectiveResolution M) I (𝟙 M) :=
    ⟨CategoryTheory.InjectiveResolution.desc (𝟙 M) _ _, by simp⟩
  change (lieCohomologyIsoAt (CategoryTheory.injectiveResolution M) n).hom = _
  calc
    _ = _ ≫ ((chevalleyEilenberg.{u,v,w} k g).cohomology n).map (𝟙 M) := by simp
    _ = (rightValue (lieInvariants.{u,v,w} k g) n).map (𝟙 M) ≫ (lieCohomologyIsoAt I n).hom :=
      (lieCohomologyIsoAt_natural m n).symm
    _ = _ := by simp

end LieDerivedCohomology
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Comparison
open scoped TensorProduct

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g L : Type v} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing L] [LieAlgebra k L]

/-- The enveloping algebra map extending a Lie homomorphism. -/
def envelopingMap (f : L →ₗ⁅k⁆ g) : U k L →ₐ[k] U k g :=
  UniversalEnvelopingAlgebra.lift k ((inclusion k g).comp f)

@[simp]
theorem envelopingMap_inclusion (f : L →ₗ⁅k⁆ g) (x : L) :
    envelopingMap f (inclusion k L x) = inclusion k g (f x) :=
  UniversalEnvelopingAlgebra.lift_ι_apply _ _ x

theorem envelopingMap_augmentation (f : L →ₗ⁅k⁆ g) :
    (Shared.Lie.augmentation k g).comp (envelopingMap f) = Shared.Lie.augmentation k L := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change Shared.Lie.augmentation k g (envelopingMap f (inclusion k L x)) =
    Shared.Lie.augmentation k L (inclusion k L x)
  rw [envelopingMap_inclusion, (augmentation_properties k g).1, (augmentation_properties k L).1]

variable (f : L →ₗ⁅k⁆ g)

/-- Apply the enveloping map and exterior-power map to the two tensor factors. -/
def ceTensorMap (n : ℕ) : CE.V k L n →ₗ[k] CE.V k g n :=
  TensorProduct.map (envelopingMap f).toLinearMap (exteriorPower.map n f.toLinearMap)

@[simp]
theorem ceTensorMap_tmul (n : ℕ) (a : U k L) (z : CE.W k L n) :
    ceTensorMap f n (a ⊗ₜ[k] z) =
      envelopingMap f a ⊗ₜ[k] exteriorPower.map n f.toLinearMap z :=
  TensorProduct.map_tmul _ _ _ _

@[simp]
theorem ceTensorMap_wedge (n : ℕ) (a : U k L) (x : Fin n → L) :
    ceTensorMap f n (a ⊗ₜ[k] CE.wedge k L n x) =
      envelopingMap f a ⊗ₜ[k] CE.wedge k g n (f ∘ x) := by
  rw [ceTensorMap_tmul, exteriorPower.map_apply_ιMulti]
  rfl

private theorem ceTensorMap_bracketSum (n : ℕ) (a : U k L) (x : Fin (n + 1) → L) :
    ceTensorMap f n (CE.bracketSum k L n a x) =
      CE.bracketSum k g n (envelopingMap f a) (f ∘ x) := by
  cases n with
  | zero => simp [CE.bracketSum]
  | succ n =>
    simp only [CE.bracketSum, map_sum, map_zsmul, ceTensorMap_wedge]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 3
    funext b
    refine Fin.cases ?_ (fun _ => ?_) b
    · simpa only [Function.comp_apply, Fin.cons_zero] using f.map_lie (x i.castSucc) (x j.succ)
    · rfl

private theorem ceTensorMap_boundary_linear (n : ℕ) :
    (ceTensorMap f n).comp ((CE.boundary k L n).restrictScalars k) =
      ((CE.boundary k g n).restrictScalars k).comp (ceTensorMap f (n + 1)) := by
  apply TensorProduct.ext'
  intro a z
  have h : TensorProduct.curry ((ceTensorMap f n).comp ((CE.boundary k L n).restrictScalars k)) a =
      TensorProduct.curry (((CE.boundary k g n).restrictScalars k).comp (ceTensorMap f (n + 1))) a := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change ceTensorMap f n (CE.boundary k L n (a ⊗ₜ[k] CE.wedge k L (n + 1) x)) =
      CE.boundary k g n (ceTensorMap f (n + 1) (a ⊗ₜ[k] CE.wedge k L (n + 1) x))
    rw [ceTensorMap_wedge, CE.boundary_formula, CE.boundary_formula, map_add, ceTensorMap_bracketSum]
    congr 1
    simp only [CE.actionSum, map_sum, map_zsmul, ceTensorMap_wedge, map_mul,
      envelopingMap_inclusion, Function.comp_apply]
    rfl
  exact LinearMap.congr_fun h z

variable (k L g) in
abbrev ceChain :=
  CE.Ext.chain k g (CE.boundary k g) (CE.boundary_augmented k g)

/-- On actual CE chains, a Lie map induces a semilinear chain map. -/
def ceChainMap : ceChain k L ⟶
    ((ModuleCat.restrictScalars (envelopingMap f).toRingHom).mapHomologicalComplex (.down ℕ)).obj
      (ceChain k g) :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (X := ModuleCat.of (U k L) (CE.V k L n))
      (Y := (ModuleCat.restrictScalars (envelopingMap f).toRingHom).obj
        (ModuleCat.of (U k g) (CE.V k g n)))
      { toFun := ceTensorMap f n
        map_add' := map_add _
        map_smul' := by
          intro a z
          change ceTensorMap f n (a • z) = envelopingMap f a • ceTensorMap f n z
          induction z using TensorProduct.inductionOn with
          | tmul b z =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, ceTensorMap_tmul, map_mul]
          | add z z' hz hz' => simp only [smul_add, map_add, hz, hz'] })
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simp only [Functor.mapHomologicalComplex_obj_d, ceChain, CE.Ext.chain, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      change CE.boundary k g n (ceTensorMap f (n + 1) z) =
        ceTensorMap f n (CE.boundary k L n z)
      exact (LinearMap.congr_fun (ceTensorMap_boundary_linear f n) z).symm)

/-- The semilinear map commutes with the original CE augmentations. -/
theorem ceChainMap_augmentation (z : CE.V k L 0) :
    CE.augmentation k g (ceTensorMap f 0 z) = CE.augmentation k L z := by
  have h : (CE.augmentation k g).comp (ceTensorMap f 0) = CE.augmentation k L := by
    apply TensorProduct.ext'
    intro a z
    have hh : TensorProduct.curry ((CE.augmentation k g).comp (ceTensorMap f 0)) a =
        TensorProduct.curry (CE.augmentation k L) a := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro x
      change CE.augmentation k g (ceTensorMap f 0 (a ⊗ₜ[k] CE.wedge k L 0 x)) =
        CE.augmentation k L (a ⊗ₜ[k] CE.wedge k L 0 x)
      rw [ceTensorMap_wedge, CE.augmentation_tmul, CE.augmentation_tmul]
      simp only [exteriorPower.zeroEquiv_ιMulti, mul_one]
      exact DFunLike.congr_fun (envelopingMap_augmentation f) a
    exact LinearMap.congr_fun hh z
  exact LinearMap.congr_fun h z

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance

universe a b c

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section ChangeOfRings

variable {R S : Type a} [Ring R] [Ring S] (φ : R →+* S)

private def restrictLinearMap
    {X : ModuleCat.{b} S} {Y : ModuleCat.{c} S} (z : X →ₗ[S] Y) :
    (ModuleCat.restrictScalars φ).obj X →ₗ[R] (ModuleCat.restrictScalars φ).obj Y where
  toFun := z
  map_add' := z.map_add
  map_smul' r t := z.map_smul (φ r) t

/-- Restrict the scalar structure on a linear map, then compose at both ends. -/
def homScalarChange
    {X : ModuleCat.{b} S} {Y : ModuleCat.{c} S}
    {X' : ModuleCat.{b} R} {Y' : ModuleCat.{c} R}
    (l : X' ⟶ (ModuleCat.restrictScalars φ).obj X)
    (m : (ModuleCat.restrictScalars φ).obj Y ⟶ Y') :
    (X →ₗ[S] Y) →ₗ[ℤ] (X' →ₗ[R] Y') :=
  ({ toFun := fun z => m.hom.comp ((restrictLinearMap φ z).comp l.hom)
     map_zero' := by
       apply LinearMap.ext
       intro x
       change m.hom ((0 : X →ₗ[S] Y) (l.hom x)) = 0
       simp
     map_add' := fun z w => by
       apply LinearMap.ext
       intro x
       change m.hom ((z + w) (l.hom x)) = m.hom (z (l.hom x)) + m.hom (w (l.hom x))
       simp } :
      (X →ₗ[S] Y) →+ (X' →ₗ[R] Y')).toIntLinearMap

variable {C : ChainComplex (ModuleCat.{b} S) ℕ} {C' : ChainComplex (ModuleCat.{b} R) ℕ}
  {D : CochainComplex (ModuleCat.{c} S) ℕ} {D' : CochainComplex (ModuleCat.{c} R) ℕ}

abbrev cochainRestrict (D : CochainComplex (ModuleCat.{c} S) ℕ) :=
  ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D

abbrev chainRestrict (C : ChainComplex (ModuleCat.{b} S) ℕ) :=
  ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj C

/-- Scalar change and a lift between the covariant complexes of the Hom computation. -/
def injectiveHomScalarChange
    {A : ModuleCat.{b} S} {A' : ModuleCat.{b} R}
    (l : A' ⟶ (ModuleCat.restrictScalars φ).obj A)
    (m : cochainRestrict φ D ⟶ D') : injectiveHom A D ⟶ injectiveHom A' D' where
  f q := ModuleCat.ofHom (homScalarChange φ l (m.f q))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change A →ₗ[S] D.X i at h
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (m.comm i j)) (h (l.hom x))

/-- Scalar change and a lift between the contravariant complexes of the Hom computation. -/
def projectiveHomScalarChange
    {B : ModuleCat.{c} S} {B' : ModuleCat.{c} R}
    (l : C' ⟶ chainRestrict φ C)
    (m : (ModuleCat.restrictScalars φ).obj B ⟶ B') : homComplex C B ⟶ homComplex C' B' where
  f q := ModuleCat.ofHom (homScalarChange φ (l.f q) m)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change C.X i →ₗ[S] B at h
    apply LinearMap.ext
    intro x
    exact congrArg (fun y : C.X i => m.hom (h y))
      (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (l.comm j i).symm) x)

/-- Simultaneous naturality of the Hom bicomplex across a change of rings. -/
def homBicomplexScalarChange
    (l : C' ⟶ chainRestrict φ C)
    (m : cochainRestrict φ D ⟶ D') : homBicomplex C D ⟶ homBicomplex C' D' where
  f p := injectiveHomScalarChange φ (l.f p) m
  comm' p p' _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change C.X p →ₗ[S] D.X q at h
    apply LinearMap.ext
    intro x
    exact congrArg (fun y : C.X p => (m.f q).hom (h y))
      (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (l.comm p' p).symm) x)

abbrev homTotalScalarChange (l : C' ⟶ chainRestrict φ C)
    (m : cochainRestrict φ D ⟶ D') : homTotal C D ⟶ homTotal C' D' :=
  HomologicalComplex₂.total.map (homBicomplexScalarChange φ l m) (.up ℕ)

end ChangeOfRings

section AugmentationChangeOfRings

variable {R S : Type a} [Ring R] [Ring S] (φ : R →+* S)
  {A : Type b} [AddCommGroup A] [Module S A] {A' : Type b} [AddCommGroup A'] [Module R A']
  {B : Type c} [AddCommGroup B] [Module S B] {B' : Type c} [AddCommGroup B'] [Module R B']
  (P : LeftResolution S A) (Q : LeftResolution R A')
  (I : InjectiveResolution S B) (J : InjectiveResolution R B')
  (l : Q.complex ⟶ chainRestrict φ P.complex) (m : cochainRestrict φ I.complex ⟶ J.complex)
  (f : ModuleCat.of R A' ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of S A))
  (g : (ModuleCat.restrictScalars φ).obj (ModuleCat.of S B) ⟶ ModuleCat.of R B')

theorem projectiveAugmentation_scalarChange
    (hm : ∀ t : B, (m.f 0).hom (I.η t) = J.η (g.hom t)) :
    projectiveAugmentation P I ≫ homTotalScalarChange φ l m =
      projectiveHomScalarChange φ l g ≫ projectiveAugmentation Q J := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    projectiveAugmentation_formula P I n, projectiveAugmentation_formula Q J n]
  dsimp only [homTotalScalarChange]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change P.complex.X n →ₗ[S] B at t
  apply LinearMap.ext
  intro z
  exact hm (t ((l.f n).hom z))

theorem injectiveAugmentation_scalarChange
    (hl : ∀ z : Q.complex.X 0, P.ε ((l.f 0).hom z) = f.hom (Q.ε z)) :
    injectiveAugmentation P I ≫ homTotalScalarChange φ l m =
      injectiveHomScalarChange φ f m ≫ injectiveAugmentation Q J := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    injectiveAugmentation_formula P I n, injectiveAugmentation_formula Q J n]
  dsimp only [homTotalScalarChange]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change A →ₗ[S] I.complex.X n at t
  apply LinearMap.ext
  intro z
  exact congrArg (fun y : A => (m.f n).hom (t y)) (hl z)

/-- The canonical balanced comparison respects change of rings with both
augmented chain maps. This applies even when restriction of the projective
resolution need not remain projective. -/
theorem balance_scalarChange_natural
    (hl : ∀ z : Q.complex.X 0, P.ε ((l.f 0).hom z) = f.hom (Q.ε z))
    (hm : ∀ t : B, (m.f 0).hom (I.η t) = J.η (g.hom t))
    (hQ : Q.IsProjective) (n : ℕ)
    (e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n)
    (e' : Homology (injectiveHom A' J.complex) n ≃ₗ[ℤ] ExtWith Q B' n)
    (he : (homologyMap (projectiveAugmentation P I) n).comp e.toLinearMap =
      homologyMap (injectiveAugmentation P I) n)
    (he' : (homologyMap (projectiveAugmentation Q J) n).comp e'.toLinearMap =
      homologyMap (injectiveAugmentation Q J) n)
    (x : Homology (injectiveHom A I.complex) n) :
    e' (homologyMap (injectiveHomScalarChange φ f m) n x) =
      homologyMap (projectiveHomScalarChange φ l g) n (e x) := by
  have ha := projectiveAugmentation_scalarChange φ P Q I J l m g hm
  have hb := injectiveAugmentation_scalarChange φ P Q I J l m f hl
  have haH := congrArg (fun t => homologyMap t n) ha
  have hbH := congrArg (fun t => homologyMap t n) hb
  rw [quotient_homology_comp, quotient_homology_comp] at haH hbH
  apply (projectiveAugmentation_quasiIso Q J hQ n).1
  calc
    homologyMap (projectiveAugmentation Q J) n (e' (homologyMap (injectiveHomScalarChange φ f m) n x)) =
        homologyMap (injectiveAugmentation Q J) n (homologyMap (injectiveHomScalarChange φ f m) n x) :=
      DFunLike.congr_fun he' _
    _ = homologyMap (homTotalScalarChange φ l m) n (homologyMap (injectiveAugmentation P I) n x) :=
      (DFunLike.congr_fun hbH x).symm
    _ = homologyMap (homTotalScalarChange φ l m) n (homologyMap (projectiveAugmentation P I) n (e x)) :=
      congrArg (homologyMap (homTotalScalarChange φ l m) n) (DFunLike.congr_fun he x).symm
    _ = _ := DFunLike.congr_fun haH (e x)

end AugmentationChangeOfRings
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

section RestrictionQuotients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes

universe u v w t

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable {ι : Type t} {c : ComplexShape ι}

def restrictQuotientHomology (f : R →+* S) (C : HomologicalComplex (ModuleCat.{w} S) c) (n : ι) :
    (ModuleCat.restrictScalars f).obj ((quotientHomology c n).obj C) ≅
      (quotientHomology c n).obj (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj C) :=
  (show (ModuleCat.restrictScalars f).obj ((quotientHomology c n).obj C) ≃ₗ[R]
      (quotientHomology c n).obj (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj C) from
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := by
        intro r x
        induction x using Submodule.Quotient.induction_on with | _ x =>
        rfl }).toModuleIso

theorem restrictQuotientHomology_natural (f : R →+* S)
    {C D : HomologicalComplex (ModuleCat.{w} S) c} (a : C ⟶ D) (n : ι) :
    (ModuleCat.restrictScalars f).map ((quotientHomology c n).map a) ≫
        (restrictQuotientHomology f D n).hom =
      (restrictQuotientHomology f C n).hom ≫
        (quotientHomology c n).map (((ModuleCat.restrictScalars f).mapHomologicalComplex c).map a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with | _ x =>
  rfl

/-- Multiplication on quotient cohomology is induced by multiplication on cycles. -/
theorem restrictQuotientHomology_action (f : R →+* S)
    (C : HomologicalComplex (ModuleCat.{w} S) c) (n : ι) (s : S)
    (a : ((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj C ⟶
      ((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj C)
    (ha : ∀ (x : C.X n), (a.f n).hom x = s • x)
    (x : Homology C n) :
    (restrictQuotientHomology f C n).hom (s • x) =
      ((quotientHomology c n).map a).hom ((restrictQuotientHomology f C n).hom x) := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  let D := ((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj C
  change homologyClass D n ⟨s • x.val, _⟩ =
    homologyClass D n (cyclesMap a n ⟨x.val, x.property⟩)
  exact congrArg (homologyClass D n) (Subtype.ext (ha x.val).symm)

end RestrictionQuotients

section IdealCoextension

open CategoryTheory Shared.Lie LieQuotientAction
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
variable {M N : ModuleCat.{max u v w} (U k g)}

/-- Evaluation at one has the same coordinate on coextension from
the quotient and on invariants after restriction to the ideal. -/
def idealToLieInvariants (M : ModuleCat.{max u v w} (U k g)) :
    (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M) ≅
      (lieInvariants.{u,v,w} k h).obj ((restrictIdeal.{u,v,w} h).obj M) := by
  let T := (restrictIdeal.{u,v,w} h).obj M
  let L := lieInvariantInclusion.{u,v,w} k h
  let e := (restrictionCoefficient.{u,v,w} h M).hom
  let f := LinearEquiv.ofInjective (L.evaluation.app T).hom (L.injective T)
  let b : invariants h (coefficientRepresentation k g M) →ₗ[k]
      LinearMap.range (L.evaluation.app T).hom :=
    (e.comp (invariants h (coefficientRepresentation k g M)).subtype).codRestrict _ (by
      intro x
      apply (L.range T (e x.val)).mpr
      intro y
      rw [← restrictionCoefficient_intertwines h M y x.val]
      change e (coefficientRepresentation k g M y x.val) = 0
      rw [x.property, map_zero])
  let j := LinearEquiv.ofBijective b ⟨by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.range (L.evaluation.app T).hom => z.val) he, by
    intro x
    have H := (L.range T x.val).mp x.property
    refine ⟨⟨x.val, ?_⟩, Subtype.ext rfl⟩
    intro y
    have he := restrictionCoefficient_intertwines h M y (show (underlying k g).obj M from x.val)
    change coefficientRepresentation k g M y x.val = _ at he
    exact he.trans (H y)⟩
  exact ((idealInvariantEquiv.{u,v,w} h M).trans (j.trans f.symm)).toModuleIso

theorem idealToLieInvariants_eval (M : ModuleCat.{max u v w} (U k g))
    (x : (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M)) :
    ((idealToLieInvariants.{u,v,w} h M).hom x) (1 : k) =
      (show (idealInvariants.{u,v,w} h).obj M from x) (1 : U k (g ⧸ h)) := by
  change (lieInvariantInclusion.{u,v,w} k h).evaluation.app _ ((idealToLieInvariants h M).hom x) = _
  dsimp only [idealToLieInvariants, LinearEquiv.toModuleIso, LinearEquiv.trans_apply]
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ ((lieInvariantInclusion.{u,v,w} k h).injective _)).apply_symm_apply _)

theorem idealToLieInvariants_natural (a : M ⟶ N) :
    ((idealInvariants.{u,v,w} h ⋙ underlying k (g ⧸ h)).map a) ≫
        (idealToLieInvariants.{u,v,w} h N).hom =
      (idealToLieInvariants.{u,v,w} h M).hom ≫
        (restrictIdeal.{u,v,w} h ⋙ lieInvariants.{u,v,w} k h).map a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (lieInvariantInclusion.{u,v,w} k h).injective ((restrictIdeal.{u,v,w} h).obj N)
  change ((idealToLieInvariants h N).hom
    ((idealInvariants.{u,v,w} h ⋙ underlying k (g ⧸ h)).map a x)) (1 : k) =
      (show (lieInvariants.{u,v,w} k h).obj ((restrictIdeal.{u,v,w} h).obj N) from
        (restrictIdeal.{u,v,w} h ⋙ lieInvariants.{u,v,w} k h).map a
          ((idealToLieInvariants h M).hom x)) (1 : k)
  rw [idealToLieInvariants_eval]
  change a.hom ((show (idealInvariants.{u,v,w} h).obj M from x) (1 : U k (g ⧸ h))) =
    a.hom (((idealToLieInvariants h M).hom x) (1 : k))
  rw [idealToLieInvariants_eval]

/-- The same coextension comparison on every term of a cochain complex. -/
def idealToLieInvariantsComplex (C : CochainComplex (ModuleCat.{max u v w} (U k g)) ℕ) :
    ((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).obj
        (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj C) ≅
      ((lieInvariants.{u,v,w} k h).mapHomologicalComplex (.up ℕ)).obj
        (((restrictIdeal.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj C) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => idealToLieInvariants h (C.X n))
    (fun p q _ => (idealToLieInvariants_natural h (C.d p q)).symm)

theorem idealToLieInvariantsComplex_natural
    {C D : CochainComplex (ModuleCat.{max u v w} (U k g)) ℕ} (a : C ⟶ D) :
    ((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).map
        (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map a) ≫
          (idealToLieInvariantsComplex h D).hom =
      (idealToLieInvariantsComplex h C).hom ≫
        ((lieInvariants.{u,v,w} k h).mapHomologicalComplex (.up ℕ)).map
          (((restrictIdeal.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map a) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact idealToLieInvariants_natural h (a.f n)

/-- Scalar restriction carries the ambient injective model to an injective
model over the ideal enveloping algebra. -/
def restrictIdealResolution (I : CategoryTheory.InjectiveResolution M) :
    CategoryTheory.InjectiveResolution ((restrictIdeal.{u,v,w} h).obj M) := by
  let F := restrictIdeal.{u,v,w} h
  let e := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).app M
  exact
    { cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      injective := fun n => restrictIdeal_injective h (I.cocomplex.X n) (I.injective n)
      ι := e.inv ≫ (F.mapHomologicalComplex (.up ℕ)).map I.ι }

def restrictIdealResolutionHom {I : CategoryTheory.InjectiveResolution M}
    {J : CategoryTheory.InjectiveResolution N} {a : M ⟶ N}
    (f : CategoryTheory.InjectiveResolution.Hom I J a) :
    CategoryTheory.InjectiveResolution.Hom (restrictIdealResolution h I)
      (restrictIdealResolution h J) ((restrictIdeal.{u,v,w} h).map a) where
  hom := ((restrictIdeal.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map f.hom
  ι_f_zero_comp_hom_f_zero := by
    let F := restrictIdeal.{u,v,w} h
    let H := F.mapHomologicalComplex (.up ℕ)
    let e := HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0
    have hs := e.inv.naturality a
    change (F ⋙ HomologicalComplex.single _ (.up ℕ) 0).map a ≫ e.inv.app N =
      e.inv.app M ≫ H.map ((HomologicalComplex.single _ (.up ℕ) 0).map a) at hs
    have he : (restrictIdealResolution h I).ι ≫ H.map f.hom =
        (HomologicalComplex.single _ (.up ℕ) 0).map (F.map a) ≫
          (restrictIdealResolution h J).ι := by
      change (e.inv.app M ≫ H.map I.ι) ≫ H.map f.hom =
        (F ⋙ HomologicalComplex.single _ (.up ℕ) 0).map a ≫ (e.inv.app N ≫ H.map J.ι)
      rw [Category.assoc, ← Functor.map_comp, f.ι_comp_hom, Functor.map_comp,
        ← Category.assoc, ← hs, Category.assoc]
    exact congrArg (fun k => k.f 0) he

section QuotientOperators

local notation "Q" => U k (g ⧸ h)

/-- Left multiplication by a quotient enveloping element is a k-linear
operator after restricting scalars. -/
def quotientScalarOperator (A : ModuleCat.{max u v w} Q) (a : Q) :
    ((underlying k (g ⧸ h)).obj A) ⟶ ((underlying k (g ⧸ h)).obj A) :=
  ModuleCat.ofHom (X := (underlying k (g ⧸ h)).obj A)
    (Y := (underlying k (g ⧸ h)).obj A)
    { toFun := fun z => a • (z : A)
      map_add' := smul_add a
      map_smul' := fun r z => by
        change a • ((algebraMap k Q) r • (z : A)) =
          (algebraMap k Q) r • (a • (z : A))
        rw [← mul_smul, ← mul_smul, Algebra.commutes] }

/-- The termwise quotient action also acts on the underlying resolution. -/
def underlyingQuotientOperator
    (C : CochainComplex (ModuleCat.{max u v w} Q) ℕ) (a : Q) :
    ((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).obj C ⟶
      ((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).obj C where
  f n := quotientScalarOperator h (C.X n) a
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : C.X p := x
    change (C.d p q).hom (a • x') = a • (C.d p q).hom x'
    exact (C.d p q).hom.map_smul a x'

theorem underlyingQuotientOperator_homology (C : CochainComplex (ModuleCat.{max u v w} Q) ℕ)
    (n : ℕ) (a : Q) (x : Homology C n) :
    (restrictQuotientHomology (algebraMap k Q) C n).hom (a • x) =
      homologyMap (underlyingQuotientOperator h C a) n
        ((restrictQuotientHomology (algebraMap k Q) C n).hom x) :=
  restrictQuotientHomology_action (algebraMap k Q) C n a
    (underlyingQuotientOperator h C a) (fun _ => rfl) x

end QuotientOperators

end IdealCoextension

section DerivedIdealValues

open CategoryTheory Shared.Lie LieQuotientAction
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
variable {M N : ModuleCat.{max u v w} (U k g)}

variable [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]

/-- The comparison for the ideal functor uses its genuine quotient module
resolution, then forgets to the underlying vector space. -/
def idealResolutionValueIso (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    (underlying k (g ⧸ h)).obj ((rightValue (idealInvariants.{u,v,w} h) n).obj M) ≅
      (quotientHomology (.up ℕ) n).obj
        (((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).obj
          (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)) := by
  let C := ((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  exact (underlying k (g ⧸ h)).mapIso
    (rightValueResolutionIso (idealInvariants.{u,v,w} h) n I ≪≫ moduleQuotientHomologyIso C n) ≪≫
    restrictQuotientHomology (algebraMap k (U k (g ⧸ h))) C n

@[reassoc]
theorem idealResolutionValueIso_natural
    {I : CategoryTheory.InjectiveResolution M} {J : CategoryTheory.InjectiveResolution N}
    {a : M ⟶ N} (f : CategoryTheory.InjectiveResolution.Hom I J a) (n : ℕ) :
    (underlying k (g ⧸ h)).map ((rightValue (idealInvariants.{u,v,w} h) n).map a) ≫ (idealResolutionValueIso h J n).hom =
      (idealResolutionValueIso h I n).hom ≫ (quotientHomology (.up ℕ) n).map
        (((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).map
          (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map f.hom)) := by
  let m := ((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map f.hom
  have hs :=
    rightValueResolutionIso_natural_assoc (idealInvariants.{u,v,w} h) n f (moduleQuotientHomologyIso
      (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex) n).hom
  simp only [idealResolutionValueIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hs, moduleQuotientHomologyIso_natural m n,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    restrictQuotientHomology_natural]
  simp only [Functor.map_comp, Category.assoc, m]

end DerivedIdealValues

section IdealOperators

open CategoryTheory Shared.Lie LieQuotientAction
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
attribute [local instance] LieQuotientAction.restrictedModule resolutionTermModule

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
variable {M : ModuleCat.{max u v w} (U k g)}

section ResolutionAction

variable (I : CategoryTheory.InjectiveResolution M) (y : g)

/-- In coextended trivial-module coordinates the same quotient operator
is obtained by transporting the scalar operator along evaluation. -/
def idealLieResolutionOperator :
    lieInvComplex (moduleInjectiveResolution (restrictIdealResolution h I)) ⟶
      lieInvComplex (moduleInjectiveResolution (restrictIdealResolution h I)) :=
  let e := idealToLieInvariantsComplex h I.cocomplex
  e.inv ≫ underlyingQuotientOperator h
    (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (inclusion k (g ⧸ h) (quotientMap k g h y)) ≫ e.hom

theorem idealLieResolutionOperator_eval (n : ℕ)
    (x : (lieInvariants.{u,v,w} k h).obj ((restrictIdeal.{u,v,w} h).obj (I.cocomplex.X n))) :
    (show (lieInvariants.{u,v,w} k h).obj ((restrictIdeal.{u,v,w} h).obj (I.cocomplex.X n)) from
      ((idealLieResolutionOperator h I y).f n).hom x) (1 : k) =
        inclusion k g y • (show I.cocomplex.X n from x (1 : k)) := by
  let e := idealToLieInvariants h (I.cocomplex.X n)
  let t : (idealInvariants.{u,v,w} h).obj (I.cocomplex.X n) := e.inv.hom x
  change (e.hom (inclusion k (g ⧸ h) (quotientMap k g h y) • t)) (1 : k) =
    inclusion k g y • (show I.cocomplex.X n from x (1 : k))
  rw [idealToLieInvariants_eval]
  change t (1 * inclusion k (g ⧸ h) (quotientMap k g h y)) =
    inclusion k g y • (show I.cocomplex.X n from x (1 : k))
  erw [one_mul, ← envelopingQuotient_inclusion, idealCoextend_apply]
  have hx : e.hom (e.inv x) = x := by
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) x
  rw [← hx, idealToLieInvariants_eval]

theorem idealLieResolutionOperator_comm :
    (idealToLieInvariantsComplex h I.cocomplex).hom ≫ idealLieResolutionOperator h I y =
      underlyingQuotientOperator h
        (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
        (inclusion k (g ⧸ h) (quotientMap k g h y)) ≫
      (idealToLieInvariantsComplex h I.cocomplex).hom := by
  simp only [idealLieResolutionOperator, Iso.hom_inv_id_assoc]

/-- The two coordinates of the operator on the invariant resolution agree
on the value at one of every trivial-module map. -/
theorem idealInjectiveHomAction :
    injectiveHomEndomorphism h (moduleInjectiveResolution I) y ≫
      (lieInjectiveHomIso (moduleInjectiveResolution (restrictIdealResolution h I))).hom =
    (lieInjectiveHomIso (moduleInjectiveResolution (restrictIdealResolution h I))).hom ≫
      ((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map (idealLieResolutionOperator h I y) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let T := (restrictIdeal.{u,v,w} h).obj (I.cocomplex.X n)
  let e := ModuleCat.CoextendScalars.equiv (augmentation k h).toRingHom T
  let J := moduleInjectiveResolution I
  change k →ₗ[U k h] I.cocomplex.X n at f
  apply (lieInvariantInclusion.{u,v,w} k h).injective T
  change (e.symm (trivialHomAction h (resolutionTermRepresentation J n)
      (resolutionTerm_restriction h J n) y f)) (1 : k) =
    (show (lieInvariants.{u,v,w} k h).obj T from
      ((idealLieResolutionOperator h I y).f n).hom (e.symm f)) (1 : k)
  rw [idealLieResolutionOperator_eval]
  change trivialHomAction h (resolutionTermRepresentation J n)
    (resolutionTerm_restriction h J n) y f 1 = inclusion k g y • f 1
  rw [trivialHomAction_evaluate]
  rfl

end ResolutionAction

section CochainOperators

local instance idealCoefficientTower (M : ModuleCat.{max u v w} (U k g)) :
    IsScalarTower k (U k g) ((underlying k g).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The actual Lie operator on the ideal cochains in integer coordinates,
obtained from the free-resolution Hom model by the same evaluation used
in the balance comparison. -/
def idealCochainIntegerOperator (y : g) :
    integerComplex ((chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)) ⟶
      integerComplex ((chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)) :=
  let e := lieEvaluationIso.{u,v,w} ((restrictIdeal.{u,v,w} h).obj M)
  e.inv ≫ resolutionCochainAction h (M := (underlying k g).obj M) (coefficientRepresentation k g M)
    (restrictedModule_inclusion h) y ≫ e.hom

theorem idealCochainIntegerOperator_eval (n : ℕ) (y : g)
    (t : CE.W k h n →ₗ[k] (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M))
    (x : Fin n → h) :
    (show CE.W k h n →ₗ[k] (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) from
      ((idealCochainIntegerOperator h (M := M) y).f n).hom t) (CE.wedge k h n x) =
      (show (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) from
        coefficientRepresentation k g M y (t (CE.wedge k h n x))) -
        ∑ i : Fin n, t (CE.wedge k h n (Function.update x i ⁅y, x i⁆)) := by
  let T := (restrictIdeal.{u,v,w} h).obj M
  let e := lieEvaluationIso.{u,v,w} T
  let f : CE.V k h n →ₗ[U k h] T := (e.inv.f n).hom t
  have hf (w : CE.W k h n) : CE.homEquiv k h ((underlying k g).obj M) n f w = t w := by
    have he : e.inv.f n ≫ e.hom.f n = 𝟙 _ :=
      congrArg (fun a => a.f n) e.inv_hom_id
    have hh := congrArg
      (fun a => (show CE.W k h n →ₗ[k] (underlying k h).obj T from a.hom t) w) he
    exact hh
  change CE.homEquiv k h ((underlying k g).obj M) n
    (resolutionHomAction h (coefficientRepresentation k g M) n y f) (CE.wedge k h n x) = _
  rw [resolutionHomAction_evaluate, derivative_formula]
  simp only [hf]

theorem idealCochainIntegerOperator_comm (y : g) :
    (lieEvaluationIso.{u,v,w} ((restrictIdeal.{u,v,w} h).obj M)).hom ≫ idealCochainIntegerOperator h y =
      resolutionCochainAction h (M := (underlying k g).obj M) (coefficientRepresentation k g M) (restrictedModule_inclusion h) y ≫
        (lieEvaluationIso.{u,v,w} ((restrictIdeal.{u,v,w} h).obj M)).hom := by
  simp only [idealCochainIntegerOperator, Iso.hom_inv_id_assoc]

end CochainOperators

end IdealOperators

section IdealCohomology

open CategoryTheory Shared.Lie LieQuotientAction
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
set_option maxRecDepth 3072
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
attribute [local instance] LieQuotientAction.restrictedModule

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
variable {M : ModuleCat.{max u v w} (U k g)}

local instance idealActionTower (M : ModuleCat.{max u v w} (U k g)) :
    IsScalarTower k (U k g) ((underlying k g).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private theorem idealHomologyMap_comp_apply {R : Type*} [Ring R]
    {A B C : CochainComplex (ModuleCat.{w} R) ℕ}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) (x : Homology A n) :
    homologyMap (f ≫ g) n x = homologyMap g n (homologyMap f n x) :=
  congrArg (fun m => m.hom x) ((quotientHomology (.up ℕ) n).map_comp f g)

/-- The balance comparison transports the quotient action to the ideal
Lie cochain operator in every degree. -/
theorem idealResolutionCohomologyAction
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) (y : g)
    (z : Homology (lieInvComplex (moduleInjectiveResolution (restrictIdealResolution h I))) n) :
    let D := (chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)
    let J := moduleInjectiveResolution (restrictIdealResolution h I)
    integerHomologyEquiv D n
        (lieResolutionCohomologyEquiv J n (homologyMap (idealLieResolutionOperator h I y) n z)) =
      homologyMap (idealCochainIntegerOperator h (M := M) y) n
        (integerHomologyEquiv D n (lieResolutionCohomologyEquiv J n z)) := by
  dsimp only
  rw [lieResolutionCohomologyEquiv_integer, lieResolutionCohomologyEquiv_integer,
    integerHomologyEquiv_natural]
  let J := moduleInjectiveResolution (restrictIdealResolution h I)
  let e := lieInjectiveHomIso J
  have hs :
      ((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map
        (idealLieResolutionOperator h I y) ≫ e.inv =
        e.inv ≫ injectiveHomEndomorphism h (moduleInjectiveResolution I) y := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← idealInjectiveHomAction,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← idealHomologyMap_comp_apply, hs, idealHomologyMap_comp_apply]
  let E := lieEvaluationIso.{u,v,w} ((restrictIdeal.{u,v,w} h).obj M)
  let v := homologyMap e.inv n (integerHomologyEquiv (lieInvComplex J) n z)
  let A := homComplex (lieProjectiveResolution (k := k) (g := h)).complex ((restrictIdeal.{u,v,w} h).obj M)
  let a : A ⟶ A := resolutionCochainAction h (M := (underlying k g).obj M)
    (coefficientRepresentation k g M) (restrictedModule_inclusion h) y
  have hbal : lieResolutionBalance J n
      (homologyMap (injectiveHomEndomorphism h (moduleInjectiveResolution I) y) n v) =
      homologyMap a n (lieResolutionBalance J n v) :=
    resolutionBalance_action h (M := (underlying k g).obj M) (moduleInjectiveResolution I) y n v
  calc
    _ = homologyMap E.hom n (homologyMap a n (lieResolutionBalance J n v)) :=
      congrArg (homologyMap E.hom n) hbal
    _ = homologyMap (a ≫ E.hom) n (lieResolutionBalance J n v) :=
      (idealHomologyMap_comp_apply a E.hom n _).symm
    _ = homologyMap (E.hom ≫ idealCochainIntegerOperator h (M := M) y) n
        (lieResolutionBalance J n v) :=
      congrArg (fun f => homologyMap f n (lieResolutionBalance J n v))
        (idealCochainIntegerOperator_comm h (M := M) y).symm
    _ = _ := idealHomologyMap_comp_apply E.hom (idealCochainIntegerOperator h (M := M) y) n _

variable [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]

/-- The actual quotient derived value, computed through the chosen ambient
injective resolution, compared with the exterior-power cohomology. -/
def idealCohomologyIsoAt (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    (underlying k (g ⧸ h)).obj ((rightValue (idealInvariants.{u,v,w} h) n).obj M) ≅
      ((chevalleyEilenberg.{u,v,w} k h).cohomology n).obj ((restrictIdeal.{u,v,w} h).obj M) :=
  idealResolutionValueIso h I n ≪≫
    (quotientHomology (.up ℕ) n).mapIso (idealToLieInvariantsComplex h I.cocomplex) ≪≫
    (lieResolutionCohomologyEquiv (moduleInjectiveResolution (restrictIdealResolution h I)) n).toModuleIso

theorem idealCohomologyIsoAt_action
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) (y : g)
    (x : (rightValue (idealInvariants.{u,v,w} h) n).obj M) :
    let D := (chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)
    integerHomologyEquiv D n ((idealCohomologyIsoAt h I n).hom
      (inclusion k (g ⧸ h) (quotientMap k g h y) • x)) =
      homologyMap (idealCochainIntegerOperator h (M := M) y) n
        (integerHomologyEquiv D n ((idealCohomologyIsoAt h I n).hom x)) := by
  let F := idealInvariants.{u,v,w} h
  let C := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e := rightValueResolutionIso F n I ≪≫ moduleQuotientHomologyIso C n
  let z := e.hom x
  let r := restrictQuotientHomology (algebraMap k (U k (g ⧸ h))) C n
  let m := (idealToLieInvariantsComplex h I.cocomplex).hom
  let a := inclusion k (g ⧸ h) (quotientMap k g h y)
  let J := moduleInjectiveResolution (restrictIdealResolution h I)
  change integerHomologyEquiv _ n
      (lieResolutionCohomologyEquiv J n (homologyMap m n (r.hom (e.hom (a • x))))) =
    homologyMap (idealCochainIntegerOperator h (M := M) y) n
      (integerHomologyEquiv _ n (lieResolutionCohomologyEquiv J n (homologyMap m n (r.hom z))))
  have hs : e.hom (a • x) = a • z := e.hom.hom.map_smul a x
  rw [hs]
  have hr := underlyingQuotientOperator_homology h C n a z
  change r.hom (a • z) = _ at hr
  rw [hr, ← idealHomologyMap_comp_apply, ← idealLieResolutionOperator_comm,
    idealHomologyMap_comp_apply]
  exact idealResolutionCohomologyAction h I n y _

/-- Entrywise form of the cochain action required by the CE comparison. -/
theorem idealCohomologyIsoAt_action_class
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) (y : g)
    (z : cycles ((chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)) n) :
    let D := (chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)
    ∃ z' : cycles D n,
      (∀ x : Fin n → h,
        z'.val (CE.wedge k h n x) =
          (show (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) from
            coefficientRepresentation k g M y (z.val (CE.wedge k h n x))) -
          ∑ i : Fin n, z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
      (idealCohomologyIsoAt h I n).inv (homologyClass D n z') =
        inclusion k (g ⧸ h) (quotientMap k g h y) •
          (show (rightValue (idealInvariants.{u,v,w} h) n).obj M from
            (idealCohomologyIsoAt h I n).inv (homologyClass D n z)) := by
  dsimp only
  let D := (chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)
  let a := idealCochainIntegerOperator h (M := M) y
  let z' : cycles D n :=
    (integerCyclesEquiv D n).symm (cyclesMap a n (integerCyclesEquiv D n z))
  refine ⟨z', idealCochainIntegerOperator_eval h n y z.val, ?_⟩
  let e := idealCohomologyIsoAt h I n
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  apply (integerHomologyEquiv D n).injective
  let x : (rightValue (idealInvariants.{u,v,w} h) n).obj M := e.inv (homologyClass D n z)
  have hx : e.hom x = homologyClass D n z :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) _
  have hz' : e.hom (e.inv (homologyClass D n z')) = homologyClass D n z' :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) _
  change integerHomologyEquiv D n (e.hom (e.inv (homologyClass D n z'))) =
    integerHomologyEquiv D n (e.hom (inclusion k (g ⧸ h) (quotientMap k g h y) • x))
  rw [hz', idealCohomologyIsoAt_action h I n y x, hx]
  rfl

@[reassoc]
theorem idealCohomologyIsoAt_natural
    {N : ModuleCat.{max u v w} (U k g)} {I : CategoryTheory.InjectiveResolution M}
    {J : CategoryTheory.InjectiveResolution N} {a : M ⟶ N}
    (f : CategoryTheory.InjectiveResolution.Hom I J a) (n : ℕ) :
    (underlying k (g ⧸ h)).map ((rightValue (idealInvariants.{u,v,w} h) n).map a) ≫
        (idealCohomologyIsoAt h J n).hom =
      (idealCohomologyIsoAt h I n).hom ≫
        ((chevalleyEilenberg.{u,v,w} k h).cohomology n).map ((restrictIdeal.{u,v,w} h).map a) := by
  let H : CochainComplex (ModuleCat.{max u v w} k) ℕ ⥤ ModuleCat.{max u v w} k :=
    quotientHomology (ComplexShape.up ℕ) n
  let A := idealToLieInvariantsComplex h I.cocomplex
  let B := idealToLieInvariantsComplex h J.cocomplex
  let T := ((underlying k (g ⧸ h)).mapHomologicalComplex (.up ℕ)).map
    (((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map f.hom)
  let C := ((lieInvariants.{u,v,w} k h).mapHomologicalComplex (.up ℕ)).map
    (((restrictIdeal.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map f.hom)
  let e := (lieResolutionCohomologyEquiv (moduleInjectiveResolution (restrictIdealResolution h I)) n).toModuleIso
  let b := (lieResolutionCohomologyEquiv (moduleInjectiveResolution (restrictIdealResolution h J)) n).toModuleIso
  let U := (restrictIdeal.{u,v,w} h).map a
  let D := (chevalleyEilenberg.{u,v,w} k h).cohomology n
  change _ ≫ ((idealResolutionValueIso h J n).hom ≫ H.map B.hom ≫ b.hom) =
    (_ ≫ H.map A.hom ≫ e.hom) ≫ D.map U
  rw [idealResolutionValueIso_natural_assoc]
  change (idealResolutionValueIso h I n).hom ≫ H.map T ≫ H.map B.hom ≫ b.hom = _
  have hs : T ≫ B.hom = A.hom ≫ C := idealToLieInvariantsComplex_natural h f.hom
  rw [← H.map_comp_assoc, hs, H.map_comp]
  simp only [Category.assoc]
  congr 1
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact lieResolutionCohomologyEquiv_natural
    (moduleInjectiveResolution (restrictIdealResolution h I))
    (moduleInjectiveResolution (restrictIdealResolution h J)) U
    (restrictIdealResolutionHom h f).hom
    (moduleInjectiveResolution_lift (restrictIdealResolutionHom h f)) n z

/-- The quotient-aware ideal cohomology comparison is natural in the
ambient coefficient module. -/
def idealCohomologyIso (n : ℕ) :
    rightValue (idealInvariants.{u,v,w} h) n ⋙ underlying k (g ⧸ h) ≅
      restrictIdeal.{u,v,w} h ⋙ (chevalleyEilenberg.{u,v,w} k h).cohomology n :=
  NatIso.ofComponents (fun M => idealCohomologyIsoAt h (CategoryTheory.injectiveResolution M) n)
    (by
      intro M N a
      let f : CategoryTheory.InjectiveResolution.Hom (CategoryTheory.injectiveResolution M)
          (CategoryTheory.injectiveResolution N) a :=
        ⟨CategoryTheory.InjectiveResolution.desc a _ _, by simp⟩
      exact idealCohomologyIsoAt_natural h f n)

theorem idealCohomologyIso_app (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    (idealCohomologyIso h n).app M = idealCohomologyIsoAt h I n := by
  apply Iso.ext
  let f : CategoryTheory.InjectiveResolution.Hom (CategoryTheory.injectiveResolution M) I (𝟙 M) :=
    ⟨CategoryTheory.InjectiveResolution.desc (𝟙 M) _ _, by simp⟩
  have hs := idealCohomologyIsoAt_natural h f n
  change (idealCohomologyIsoAt h (CategoryTheory.injectiveResolution M) n).hom = _
  calc
    _ = _ ≫ ((chevalleyEilenberg.{u,v,w} k h).cohomology n).map
          ((restrictIdeal.{u,v,w} h).map (𝟙 M)) := by simp
    _ = (underlying k (g ⧸ h)).map ((rightValue (idealInvariants.{u,v,w} h) n).map (𝟙 M)) ≫
          (idealCohomologyIsoAt h I n).hom := hs.symm
    _ = _ := by simp

theorem idealCohomologyIso_action (n : ℕ) (y : g)
    (z : cycles ((chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)) n) :
    let D := (chevalleyEilenberg.{u,v,w} k h).complex ((restrictIdeal.{u,v,w} h).obj M)
    ∃ z' : cycles D n,
      (∀ x : Fin n → h,
        z'.val (CE.wedge k h n x) =
          (show (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) from
            coefficientRepresentation k g M y (z.val (CE.wedge k h n x))) -
          ∑ i : Fin n, z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
      (idealCohomologyIso h n).inv.app M (homologyClass D n z') =
        inclusion k (g ⧸ h) (quotientMap k g h y) •
          (show (rightValue (idealInvariants.{u,v,w} h) n).obj M from
            (idealCohomologyIso h n).inv.app M (homologyClass D n z)) :=
  idealCohomologyIsoAt_action_class h (CategoryTheory.injectiveResolution M) n y z

end IdealCohomology

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance

open scoped TensorProduct

universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 650000
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule

section LieChangeOfRings

variable {k : Type u} {g L : Type v} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing L] [LieAlgebra k L]
  (f : L →ₗ⁅k⁆ g)

/-- The trivial source and target modules use the same scalar coefficients. -/
def ceTrivialChange : ModuleCat.of (U k L) k ⟶
    (ModuleCat.restrictScalars (envelopingMap f).toRingHom).obj (ModuleCat.of (U k g) k) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (U k L) k)
    (Y := (ModuleCat.restrictScalars (envelopingMap f).toRingHom).obj (ModuleCat.of (U k g) k))
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change Shared.Lie.augmentation k L a * x =
          Shared.Lie.augmentation k g (envelopingMap f a) * x
        exact congrArg (· * x) (DFunLike.congr_fun (envelopingMap_augmentation f) a).symm }

variable {M : ModuleCat.{max u v w} (U k g)} {N : ModuleCat.{max u v w} (U k L)}

/-- The map of contravariant Hom complexes is the original exterior pullback
with the specified coefficient map. -/
theorem lieEvaluationIso_scalarChange
    (a : (ModuleCat.restrictScalars (envelopingMap f).toRingHom).obj M ⟶ N)
    (b : (underlying k g).obj M ⟶ (underlying k L).obj N)
    (hb : ∀ t : M, b.hom t = a.hom t)
    (comm : ∀ n t, (chevalleyEilenberg.{u,v,w} k L).d N n (pullback f b.hom n t) =
      pullback f b.hom (n + 1) ((chevalleyEilenberg.{u,v,w} k g).d M n t)) :
    projectiveHomScalarChange (envelopingMap f).toRingHom (ceChainMap f) a ≫ (lieEvaluationIso N).hom =
      (lieEvaluationIso M).hom ≫
        ((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map
          ((chevalleyEilenberg.{u,v,w} k g).map (chevalleyEilenberg.{u,v,w} k L) f b comm) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro x
  let t' : CE.V k g n →ₗ[U k g] M := t
  change a.hom (t' (ceTensorMap f n ((1 : U k L) ⊗ₜ[k] x))) =
    b.hom (t' ((1 : U k g) ⊗ₜ[k] exteriorPower.map n f.toLinearMap x))
  rw [ceTensorMap_tmul, map_one, hb]

variable
  (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
  (J : P103.Specs.Ch10.Comparison.InjectiveResolution (U k L) N)
  (m : cochainRestrict (envelopingMap f).toRingHom I.complex ⟶ J.complex)
  (vmap : lieInvComplex I ⟶ lieInvComplex J)

/-- Degreewise compatibility identifies the changed Hom complex with the map
on the actual coextended invariant vectors. -/
theorem lieInjectiveHomIso_scalarChange
    (hv : ∀ n (t : (lieInvariants.{u,v,w} k g).obj (I.complex.X n)) (s : k),
       (show (lieInvariants.{u,v,w} k L).obj (J.complex.X n) from (vmap.f n).hom t) s =
        (m.f n).hom (t s)) :
    injectiveHomScalarChange (envelopingMap f).toRingHom (ceTrivialChange f) m ≫ (lieInjectiveHomIso J).hom =
      (lieInjectiveHomIso I).hom ≫
        ((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map vmap := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  let t' : k →ₗ[U k g] (I.complex.X n) := t
  change (show (lieInvariants.{u,v,w} k L).obj (J.complex.X n) from _) =
    (vmap.f n).hom (show (lieInvariants.{u,v,w} k g).obj (I.complex.X n) from t')
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro s
  exact (hv n t' s).symm

/-- Because all invariant maps are linear, evaluation at one determines the
comparison on every scalar. -/
theorem lieInvariantMapEvaluation
    (hv : ∀ n (t : (lieInvariants.{u,v,w} k g).obj (I.complex.X n)),
      (show (lieInvariants.{u,v,w} k L).obj (J.complex.X n) from (vmap.f n).hom t) (1 : k) =
        (m.f n).hom (t (1 : k))) :
    ∀ n (t : (lieInvariants.{u,v,w} k g).obj (I.complex.X n)) (s : k),
      (show (lieInvariants.{u,v,w} k L).obj (J.complex.X n) from (vmap.f n).hom t) s =
        (m.f n).hom (t s) := by
  intro n t s
  let t' : (lieInvariants.{u,v,w} k L).obj (J.complex.X n) := (vmap.f n).hom t
  have hs := lieCoextend_apply (I.complex.X n) t (algebraMap k (U k g) s)
  have hs' := lieCoextend_apply (J.complex.X n) t' (algebraMap k (U k L) s)
  rw [(Shared.Lie.augmentation k g).commutes] at hs
  rw [(Shared.Lie.augmentation k L).commutes] at hs'
  have hm := (m.f n).hom.map_smul (algebraMap k (U k L) s) (t (1 : k))
  change (m.f n).hom (envelopingMap f (algebraMap k (U k L) s) • t (1 : k)) =
    algebraMap k (U k L) s • (m.f n).hom (t (1 : k)) at hm
  rw [(envelopingMap f).commutes] at hm
  change t' s = (m.f n).hom (t s)
  calc
    t' s = algebraMap k (U k L) s • t' (1 : k) := hs'
    _ = algebraMap k (U k L) s • (m.f n).hom (t (1 : k)) :=
      congrArg ((algebraMap k (U k L) s) • ·) (hv n t)
    _ = (m.f n).hom (algebraMap k (U k g) s • t (1 : k)) := hm.symm
    _ = _ := congrArg (m.f n).hom hs.symm

private theorem scalarChange_homologyMap_comp {R : Type*} [Ring R]
    {A B C : CochainComplex (ModuleCat R) ℕ} (l : A ⟶ B) (m : B ⟶ C)
    (n : ℕ) (z : Homology A n) :
    homologyMap (l ≫ m) n z = homologyMap m n (homologyMap l n z) :=
  congrArg (fun t => t.hom z) ((quotientHomology (.up ℕ) n).map_comp l m)

theorem lieResolutionCohomologyEquiv_scalarChange
    (a : (ModuleCat.restrictScalars (envelopingMap f).toRingHom).obj M ⟶ N)
    (hm : ∀ t : M, (m.f 0).hom (I.η t) = J.η (a.hom t))
    (b : (underlying k g).obj M ⟶ (underlying k L).obj N)
    (hb : ∀ t : M, b.hom t = a.hom t)
    (comm : ∀ n t, (chevalleyEilenberg.{u,v,w} k L).d N n (pullback f b.hom n t) =
      pullback f b.hom (n + 1) ((chevalleyEilenberg.{u,v,w} k g).d M n t))
    (hv : ∀ n (t : (lieInvariants.{u,v,w} k g).obj (I.complex.X n)) (s : k),
      (show (lieInvariants.{u,v,w} k L).obj (J.complex.X n) from (vmap.f n).hom t) s =
        (m.f n).hom (t s))
    (n : ℕ) (z : Homology (lieInvComplex I) n) :
    lieResolutionCohomologyEquiv J n (homologyMap vmap n z) =
      homologyMap ((chevalleyEilenberg.{u,v,w} k g).map
        (chevalleyEilenberg.{u,v,w} k L) f b comm) n (lieResolutionCohomologyEquiv I n z) := by
  let P := lieProjectiveResolution (k := k) (g := g)
  let Q := lieProjectiveResolution (k := k) (g := L)
  let E := (chevalleyEilenberg.{u,v,w} k g).map (chevalleyEilenberg.{u,v,w} k L) f b comm
  have hl : ∀ t : Q.complex.X 0, P.ε ((ceChainMap f).f 0 |>.hom t) =
      (ceTrivialChange f).hom (Q.ε t) := ceChainMap_augmentation f
  have hbalance := balance_scalarChange_natural (envelopingMap f).toRingHom P Q I J (ceChainMap f) m
    (ceTrivialChange f) a hl hm lieProjectiveResolution_projective n
    (lieResolutionBalance I n) (lieResolutionBalance J n)
    (lieResolutionBalance_formula I n) (lieResolutionBalance_formula J n)
  have hi := lieInjectiveHomIso_scalarChange f I J m vmap hv
  have hi' : ((integerCoordinates k).mapHomologicalComplex (.up ℕ)).map vmap ≫
        (lieInjectiveHomIso J).inv =
      (lieInjectiveHomIso I).inv ≫ injectiveHomScalarChange (envelopingMap f).toRingHom (ceTrivialChange f) m := by
    apply (cancel_epi (lieInjectiveHomIso I).hom).mp
    rw [← Category.assoc, ← hi]
    simp
  apply (integerHomologyEquiv _ n).injective
  rw [integerHomologyEquiv_natural _ E, lieResolutionCohomologyEquiv_integer,
    lieResolutionCohomologyEquiv_integer, integerHomologyEquiv_natural _ vmap]
  rw [← scalarChange_homologyMap_comp, hi', scalarChange_homologyMap_comp,
    hbalance, ← scalarChange_homologyMap_comp,
    lieEvaluationIso_scalarChange f a b hb comm, scalarChange_homologyMap_comp]

end LieChangeOfRings
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes

universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 650000
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) {M : ModuleCat.{max u v w} (U k g)}
  (I : CategoryTheory.InjectiveResolution M)

/-- The inclusion between the two actual invariant-resolution complexes
under the ambient and ideal evaluations. -/
def restrictionInvariantComplexMap :
    lieInvComplex (moduleInjectiveResolution I) ⟶
      lieInvComplex (moduleInjectiveResolution (restrictIdealResolution h I)) :=
  (NatTrans.mapHomologicalComplex (compositeInvariantsEvaluationIso.{u,v,w} h).inv (.up ℕ)).app
      I.cocomplex ≫
    (NatTrans.mapHomologicalComplex (Functor.whiskerLeft (idealInvariants.{u,v,w} h)
      (lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation) (.up ℕ)).app I.cocomplex ≫
    (idealToLieInvariantsComplex.{u,v,w} h I.cocomplex).hom

theorem restrictionInvariantComplexMap_eval
    (n : ℕ) (t : (lieInvariants.{u,v,w} k g).obj (I.cocomplex.X n)) :
    (show (lieInvariants.{u,v,w} k h).obj ((restrictIdeal.{u,v,w} h).obj (I.cocomplex.X n))
        from ((restrictionInvariantComplexMap h I).f n).hom t) (1 : k) =
      t (1 : k) := by
  let X := I.cocomplex.X n
  let e := (compositeInvariantsEvaluationIso.{u,v,w} h).app X
  let s := e.inv t
  change ((idealToLieInvariants.{u,v,w} h X).hom
    ((lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation.app
      ((idealInvariants.{u,v,w} h).obj X) s)) (1 : k) = t (1 : k)
  rw [idealToLieInvariants_eval]
  change (show (quotientInvariants.{u,v,w} h).obj ((idealInvariants.{u,v,w} h).obj X) from s)
      (1 : k) (1 : U k (g ⧸ h)) = t (1 : k)
  rw [← compositeInvariantsMap_apply]
  change (e.hom (e.inv t)) (1 : k) = t (1 : k)
  exact congrArg (fun z : (lieInvariants.{u,v,w} k g).obj X => z (1 : k))
    (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) t)

open LieQuotientAction

/-- Under the canonical balanced comparisons, the invariant-resolution map
is induced by restriction of actual Chevalley–Eilenberg cochains. -/
theorem restrictionInvariantComplexMap_cohomology (n : ℕ)
    (z : Homology (lieInvComplex (moduleInjectiveResolution I)) n) :
    lieResolutionCohomologyEquiv (moduleInjectiveResolution (restrictIdealResolution h I)) n
        (homologyMap (restrictionInvariantComplexMap h I) n z) =
      homologyMap (restrictionCochain.{u,v,w} h M) n
        (lieResolutionCohomologyEquiv (moduleInjectiveResolution I) n z) := by
  let P := moduleInjectiveResolution I
  let Q := moduleInjectiveResolution (restrictIdealResolution h I)
  let m : cochainRestrict (envelopingMap h.incl).toRingHom P.complex ⟶ Q.complex := 𝟙 Q.complex
  let a : (ModuleCat.restrictScalars (envelopingMap h.incl).toRingHom).obj M ⟶
      (restrictIdeal.{u,v,w} h).obj M := 𝟙 _
  let b := restrictionCoefficient.{u,v,w} h M
  let E := (chevalleyEilenberg.{u,v,w} k g).map
    (chevalleyEilenberg.{u,v,w} k h) h.incl b
    (pullback_commutes k g h _ _ _ _ _ _ (restrictionCoefficient_intertwines.{u,v,w} h M)
      _ _ ((chevalleyEilenberg.{u,v,w} k g).formula _)
      ((chevalleyEilenberg.{u,v,w} k h).formula _))
  change lieResolutionCohomologyEquiv Q n
      (homologyMap (restrictionInvariantComplexMap h I) n z) =
    homologyMap E n (lieResolutionCohomologyEquiv P n z)
  have hm : ∀ t : M, (m.f 0).hom (P.η t) = Q.η (a.hom t) := fun _ => rfl
  have hb : ∀ t : M, b.hom t = a.hom t := fun _ => rfl
  have hv := lieInvariantMapEvaluation h.incl P Q m (restrictionInvariantComplexMap h I)
    (restrictionInvariantComplexMap_eval h I)
  exact lieResolutionCohomologyEquiv_scalarChange h.incl P Q m (restrictionInvariantComplexMap h I)
    a hm b hb _ hv n z

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory CategoryTheory.Functor Shared.Lie
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

/-- The ambient comparison uses the same invariant vectors as the two
successive coextensions. -/
def ambientCohomologyIso (n : ℕ) :
    rightValue (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h) n ≅
      (chevalleyEilenberg.{u,v,w} k g).cohomology n :=
  rightValueNatIso (compositeInvariantsEvaluationIso h) n ≪≫ lieCohomologyIso k g n

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.GrothendieckEdges
open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

section RowNat

open HomologicalComplex
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The unit augmentation in the ordinary cochain degrees. -/
def mappedResolutionAugmentationNat {X : A} (I : InjectiveResolution X) :
    (CochainComplex.single₀ B).obj (F.obj X) ⟶
      (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  (singleMapHomologicalComplex F (.up ℕ) 0).inv.app X ≫
    (F.mapHomologicalComplex (.up ℕ)).map I.ι

private lemma extend_map_stalk {X : A} :
    (extendSingleIso resolutionEmbedding (F.obj X) 0 0 rfl).inv ≫
      extendMap ((singleMapHomologicalComplex F (.up ℕ) 0).inv.app X) resolutionEmbedding =
    (singleMapHomologicalComplex F (.up ℤ) 0).inv.app X ≫
      (F.mapHomologicalComplex (.up ℤ)).map (extendSingleIso resolutionEmbedding X 0 0 rfl).inv ≫
          (mapExtendIso F resolutionEmbedding ((CochainComplex.single₀ A).obj X)).hom := by
  apply HomologicalComplex.hom_ext
  intro p
  by_cases hp : p = 0
  · subst p
    have h0 : resolutionEmbedding.f (0 : ℕ) = (0 : ℤ) := rfl
    simp only [HomologicalComplex.comp_f, mapExtendIso_hom_f _ _ _ h0,
      extendSingleIso_inv_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
    erw [extendMap_f _ _ h0]
    simp only [singleMapHomologicalComplex_inv_app_self, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← F.map_comp_assoc (singleObjXSelf (.up ℤ) 0 X).inv
        (singleObjXSelf (.up ℤ) 0 X).hom, Iso.inv_hom_id, F.map_id, Category.id_comp]
    rw [← F.map_comp_assoc (((CochainComplex.single₀ A).obj X).extendXIso resolutionEmbedding h0).inv
        (((CochainComplex.single₀ A).obj X).extendXIso resolutionEmbedding h0).hom,
      Iso.inv_hom_id, F.map_id, Category.id_comp]
    let h := (((single B (.up ℕ) 0).obj (F.obj X)).extendXIso resolutionEmbedding h0)
    erw [h.inv_hom_id_assoc, (singleObjXSelf (.up ℕ) 0 (F.obj X)).inv_hom_id_assoc]
    rfl
  · exact (isZero_single_obj_X (.up ℤ) 0 (F.obj X) p hp).eq_of_src _ _

/-- Extend an ordinary lift along the ℕ-indexed augmentation to the integer model. -/
def extendResolutionLift {X : A} (I : InjectiveResolution X)
    (J : InjectiveResolution (F.obj X))
    (s : J.cocomplex ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :
    resolutionPlus J ⟶ F.mapCochainComplexPlus.obj (resolutionPlus I) :=
  (CochainComplex.plus B).homMk (extendMap s resolutionEmbedding ≫
    (mapExtendIso F resolutionEmbedding I.cocomplex).inv)

lemma extendResolutionLift_augmentation {X : A} (I : InjectiveResolution X)
    (J : InjectiveResolution (F.obj X))
    (s : J.cocomplex ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hs : J.ι ≫ s = mappedResolutionAugmentationNat F I) :
    resolutionAugmentation J ≫ extendResolutionLift F I J s = mappedResolutionAugmentation F I := by
  apply (CochainComplex.plus B).ι.map_injective
  let e := resolutionEmbedding
  let c := (mapExtendIso F e I.cocomplex)
  let Fi := F.mapHomologicalComplex (.up ℤ)
  apply (cancel_mono c.hom).mp
  simp only [CategoryTheory.Functor.map_comp]
  change (((extendSingleIso e (F.obj X) 0 0 rfl).inv ≫ extendMap J.ι e) ≫
      (extendMap s e ≫ c.inv)) ≫ c.hom =
    ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app X ≫
      Fi.map ((extendSingleIso e X 0 0 rfl).inv ≫ extendMap I.ι e)) ≫ c.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Fi.map_comp]
  rw [← extendMap_comp, hs]
  simp only [mappedResolutionAugmentationNat, extendMap_comp, Category.assoc]
  rw [mapExtendIso_natural, ← Category.assoc, ← Category.assoc, extend_map_stalk F]
  simp only [Category.assoc]
  rfl

private lemma mapExtendIso_composite (K : CochainComplex A ℕ) :
    (mapExtendIso (F ⋙ G) resolutionEmbedding K).hom =
      (G.mapHomologicalComplex (.up ℤ)).map (mapExtendIso F resolutionEmbedding K).hom ≫
      (mapExtendIso G resolutionEmbedding ((F.mapHomologicalComplex (.up ℕ)).obj K)).hom := by
  apply hom_ext
  intro i
  by_cases hi : ∃ p, resolutionEmbedding.f p = i
  · obtain ⟨p, hp⟩ := hi
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, mapExtendIso_hom_f _ _ _ hp,
      CategoryTheory.Functor.comp_map, Functor.map_comp, Category.assoc]
    let t := (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso resolutionEmbedding hp)
    rw [← G.map_comp_assoc t.inv t.hom, Iso.inv_hom_id, G.map_id, Category.id_comp]
    rfl
  · exact ((F ⋙ G).map_isZero (K.isZero_extend_X resolutionEmbedding i
      (fun p h => hi ⟨p,h⟩))).eq_of_src _ _

private lemma mapExtend_lift_comm {X : A} (I : InjectiveResolution X)
    (J : InjectiveResolution (F.obj X))
    (s : J.cocomplex ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :
    (G.mapHomologicalComplex (.up ℤ)).map (extendResolutionLift F I J s).hom ≫
      (mapExtendIso (F ⋙ G) resolutionEmbedding I.cocomplex).hom =
    (mapExtendIso G resolutionEmbedding J.cocomplex).hom ≫
      extendMap ((G.mapHomologicalComplex (.up ℕ)).map s) resolutionEmbedding := by
  change (G.mapHomologicalComplex (.up ℤ)).map
      (extendMap s resolutionEmbedding ≫ (mapExtendIso F resolutionEmbedding I.cocomplex).inv) ≫ _ = _
  let p := mapExtendIso F resolutionEmbedding I.cocomplex
  let Gi := G.mapHomologicalComplex (.up ℤ)
  rw [mapExtendIso_composite F G]
  rw [Gi.map_comp, Category.assoc, ← Gi.map_comp_assoc p.inv p.hom,
    Iso.inv_hom_id, Gi.map_id, Category.id_comp, mapExtendIso_natural]

/-- In ordinary cochain degrees the first edge is the chain lift of the
augmentation, with quotient invariants applied in each degree. -/
theorem derivedFirstEdge_on_resolution_homology (P : Package F G) {X : A}
    (I : InjectiveResolution X) (J : InjectiveResolution (F.obj X))
    (s : J.cocomplex ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hs : J.ι ≫ s = mappedResolutionAugmentationNat F I)
    (hF : ∀ X, Injective X → Injective (F.obj X)) (n : ℕ) :
    (derivedFirstEdge F G P n).app X ≫ (rightValueResolutionIso (F ⋙ G) n I).hom =
      (rightValueResolutionIso G n J).hom ≫
        homologyMap ((G.mapHomologicalComplex (.up ℕ)).map s) n := by
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let H' := homologyFunctor C (.up ℤ) (n : ℤ)
  let e := resolutionEmbedding
  let b := extendResolutionLift F I J s
  have hI p : Injective ((F.mapCochainComplexPlus.obj (resolutionPlus I)).obj.X p) :=
    hF _ (resolutionPlus_injective I p)
  have he := derivedFirstEdge_on_resolutions F G P I J b
    (extendResolutionLift_augmentation F I J s hs) hI n
  simp only [rightValueResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, he, H.map_comp, Category.assoc]
  congr 1
  erw [(DerivedCategory.homologyFunctorFactors C (n : ℤ)).hom.naturality_assoc
    ((G.mapHomologicalComplex (.up ℤ)).map b.hom)]
  congr 1
  rw [← H'.map_comp_assoc, mapExtend_lift_comm F G I J s, H'.map_comp, Category.assoc]
  congr 1
  exact extendHomologyIso_hom_naturality ((G.mapHomologicalComplex (.up ℕ)).map s) e rfl


end RowNat

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open LieQuotientAction

universe u v w

set_option maxHeartbeats 700000

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) {M : ModuleCat.{max u v w} (U k g)}
  (I : CategoryTheory.InjectiveResolution M)
  (J : CategoryTheory.InjectiveResolution ((idealInvariants.{u,v,w} h).obj M))


variable (s : J.cocomplex ⟶ ((idealInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)


/-- Under the actual augmentation evaluations, the lift compares the
two invariant complexes. -/
def inflationInvariantComplexMap :
    lieInvComplex (moduleInjectiveResolution J) ⟶ lieInvComplex (moduleInjectiveResolution I) :=
  ((quotientInvariants.{u,v,w} h).mapHomologicalComplex (.up ℕ)).map s ≫
    ((compositeInvariantsEvaluationIso.{u,v,w} h).hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex

/-- The same resolution map over U(g) is obtained by evaluating at one. -/
def inflationResolutionMap :
    cochainRestrict (envelopingQuotient h).toRingHom J.cocomplex ⟶ I.cocomplex :=
  ((ModuleCat.restrictScalars (envelopingQuotient h).toRingHom).mapHomologicalComplex (.up ℕ)).map s ≫
    ((ModuleCat.restrictCoextendScalarsAdj.{w,max u v,max u v}
      (envelopingQuotient h).toRingHom).counit.mapHomologicalComplex (.up ℕ)).app I.cocomplex

private abbrev inflationModuleMap :
    (ModuleCat.restrictScalars (envelopingQuotient h).toRingHom).obj ((idealInvariants.{u,v,w} h).obj M) ⟶ M :=
  (ModuleCat.restrictCoextendScalarsAdj.{w,max u v,max u v}
    (envelopingQuotient h).toRingHom).counit.app M

/-- The lifted inflation has the stated augmentation. -/
theorem inflationResolutionMap_augmentation
    (hs : J.ι ≫ s = mappedResolutionAugmentationNat (idealInvariants.{u,v,w} h) I)
    (t : (idealInvariants.{u,v,w} h).obj M) :
    ((inflationResolutionMap h I J s).f 0).hom ((moduleInjectiveResolution J).η t) = (moduleInjectiveResolution I).η ((inflationModuleMap h (M := M)).hom t) := by
  let fx : (idealInvariants.{u,v,w} h).obj M ⟶ (idealInvariants.{u,v,w} h).obj (I.cocomplex.X 0) :=
    (idealInvariants.{u,v,w} h).map ((HomologicalComplex.singleObjXSelf (.up ℕ) 0 M).inv ≫ I.ι.f 0)
  have hf : ((HomologicalComplex.singleObjXSelf (.up ℕ) 0 ((idealInvariants.{u,v,w} h).obj M)).inv ≫ J.ι.f 0) ≫ s.f 0 =
      fx := by
    have hh := congrArg (fun b => b.f 0) hs
    simp only [mappedResolutionAugmentationNat, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      CategoryTheory.Functor.mapHomologicalComplex_map_f] at hh
    rw [Category.assoc, hh]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, fx, CategoryTheory.Functor.map_comp]
  let z : (idealInvariants.{u,v,w} h).obj (I.cocomplex.X 0) := (s.f 0).hom ((moduleInjectiveResolution J).η t)
  have hz : z = fx.hom t := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hf) t
  change z (1 : U k (g ⧸ h)) = _
  rw [hz]
  rfl

/-- On ordinary cohomology of injective resolutions, the map is inflation
by the quotient Lie map and the inclusion of invariant vectors. -/
theorem inflationInvariantComplexMap_cohomology
    (hs : J.ι ≫ s = mappedResolutionAugmentationNat (idealInvariants.{u,v,w} h) I)
    (n : ℕ) (z : Homology (lieInvComplex (moduleInjectiveResolution J)) n) :
    lieResolutionCohomologyEquiv (moduleInjectiveResolution I) n
        (homologyMap (inflationInvariantComplexMap h I J s) n z) =
      homologyMap (inflationCochain.{u,v,w} h M) n
        (lieResolutionCohomologyEquiv (moduleInjectiveResolution J) n z) := by
  let f := quotientMap k g h
  let m := inflationResolutionMap h I J s
  let a := inflationModuleMap h (M := M)
  let b := inflationCoefficient.{u,v,w} h M
  let vmap := inflationInvariantComplexMap h I J s
  let E := (chevalleyEilenberg.{u,v,w} k (g ⧸ h)).map
    (chevalleyEilenberg.{u,v,w} k g) f b
    (pullback_commutes k (g ⧸ h) g _ _ _ _ _ _ (inflationCoefficient_intertwines.{u,v,w} h M)
      _ _ ((chevalleyEilenberg.{u,v,w} k (g ⧸ h)).formula _)
      ((chevalleyEilenberg.{u,v,w} k g).formula _))
  change lieResolutionCohomologyEquiv (moduleInjectiveResolution I) n (homologyMap vmap n z) =
    homologyMap E n (lieResolutionCohomologyEquiv (moduleInjectiveResolution J) n z)
  refine lieResolutionCohomologyEquiv_scalarChange f (moduleInjectiveResolution J) (moduleInjectiveResolution I) m vmap a
    (inflationResolutionMap_augmentation h I J s hs) b (fun _ => rfl) _ ?_ n z
  intro j t r
  rfl

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category Shared.Lie
open P103.Specs.Ch10.Comparison
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.GrothendieckEdges AdvancedHomologicalAlgebra.GrothendieckSpectralSequence

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

/-- The row edge is induced by actual exterior pullback along the Lie
quotient, with the ideal invariant coefficient inclusion. -/
theorem inflation_edge_comparison
    (P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h))
    (M : ModuleCat.{max u v w} (U k g)) (n : ℕ) :
    (lieCohomologyIso.{u,v,w} k (g ⧸ h) n).hom.app ((idealInvariants.{u,v,w} h).obj M) ≫
      (quotientHomology (.up ℕ) n).map (inflationCochain.{u,v,w} h M) =
      (derivedFirstEdge (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P n).app M ≫
        (ambientCohomologyIso.{u,v,w} h n).hom.app M := by
  let F := idealInvariants.{u,v,w} h
  let G := quotientInvariants.{u,v,w} h
  let T := compositeInvariantsEvaluationIso.{u,v,w} h
  let I := CategoryTheory.injectiveResolution M
  let J := CategoryTheory.injectiveResolution (F.obj M)
  have hF (X : ModuleCat.{max u v w} (U k g)) (hX : Injective X) : Injective (F.obj X) :=
    coextend_injective.{max u v,w} _ X hX
  obtain ⟨s, hs⟩ := liftFromInjectiveResolution J ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (mappedResolutionAugmentationNat F I) (fun i => hF _ (I.injective i))
  let K := ((lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := (G.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let p := (lieResolutionCohomologyEquiv (moduleInjectiveResolution I) n).toModuleIso
  let q := (lieResolutionCohomologyEquiv (moduleInjectiveResolution J) n).toModuleIso
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n
  let C := quotientHomology (S := k) (.up ℕ) n
  let E := inflationCochain.{u,v,w} h M
  let edge := (derivedFirstEdge F G P n).app M
  have hq : (lieCohomologyIso.{u,v,w} k (g ⧸ h) n).hom.app (F.obj M) =
      (lieCohomologyIsoAt J n).hom := lieCohomologyIso_hom_app J n
  have hp : (lieCohomologyIso.{u,v,w} k g n).hom.app M = (lieCohomologyIsoAt I n).hom :=
    lieCohomologyIso_hom_app I n
  change _ ≫ C.map E = edge ≫ ((rightValueNatIso T n).hom.app M ≫
    (lieCohomologyIso.{u,v,w} k g n).hom.app M)
  rw [hq, hp]
  simp only [lieCohomologyIsoAt, Iso.trans_hom, Category.assoc]
  erw [rightValueResolutionIso_natIso_assoc T n I]
  have he := derivedFirstEdge_on_resolution_homology F G P I J s hs hF n
  erw [reassoc_of% he]
  change (rightValueResolutionIso G n J).hom ≫
      (moduleQuotientHomologyIso L n).hom ≫ q.hom ≫ C.map E =
    (rightValueResolutionIso G n J).hom ≫ H.map ((G.mapHomologicalComplex (.up ℕ)).map s) ≫
      H.map ((T.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex) ≫
      (moduleQuotientHomologyIso K n).hom ≫ p.hom
  rw [← H.map_comp_assoc]
  change _ = (rightValueResolutionIso G n J).hom ≫
    HomologicalComplex.homologyMap (inflationInvariantComplexMap h I J s) n ≫
      (moduleQuotientHomologyIso K n).hom ≫ p.hom
  erw [moduleQuotientHomologyIso_natural_assoc (inflationInvariantComplexMap h I J s) n]
  congr 1
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (inflationInvariantComplexMap_cohomology h I J s hs n z).symm

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AdvancedHomologicalAlgebra.GrothendieckEdges

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u₁ v₁ u₂ v₂ w₁ w₂

variable {B : Type u₁} {C : Type u₂}
  [Category.{v₁} B] [Abelian B] [Category.{v₂} C] [Abelian C]
  [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive] (U : B ⥤ C)

-- Naturality of a comparison to an exact functor identifies the normalized
-- truncation edge once its value on each stalk is known.
theorem ColumnTruncation.edge_comp_of_stalk {n : ℤ} (T : ColumnTruncation G n)
    (e₀ : rightValue G 0 ≅ G) (τ : G ⟶ U)
    (κ : G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ⟶
      DerivedCategory.Plus.homologyFunctor B n ⋙ U)
    (hκ : ∀ X : B, κ.app ((DerivedCategory.Plus.singleFunctor B n).obj X) =
      (shiftedStalkValueIso G n ≪≫ e₀).hom.app X ≫ τ.app X ≫
        U.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B n).inv.app X)) :
    T.edge G e₀ ≫ whiskerLeft (DerivedCategory.Plus.homologyFunctor B n) τ = κ := by
  ext Y
  let i : (DerivedCategory.Plus.TStructure.t.truncLE n).obj Y ⟶ Y :=
    (DerivedCategory.Plus.TStructure.t.truncLEι n).app Y
  let p : (DerivedCategory.Plus.TStructure.t.truncLE n).obj Y ⟶
      (DerivedCategory.Plus.singleFunctor B n).obj ((DerivedCategory.Plus.homologyFunctor B n).obj Y) :=
    (DerivedCategory.Plus.TStructure.t.truncGEπ n).app
      ((DerivedCategory.Plus.TStructure.t.truncLE n).obj Y) ≫ T.point.hom.app Y
  have hnorm :
      (DerivedCategory.Plus.homologyFunctor B n).map p ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj Y) =
      (DerivedCategory.Plus.homologyFunctor B n).map i := T.point_normalization Y
  have hnatp := κ.naturality p
  have hnati := κ.naturality i
  simp only [Functor.comp_map] at hnatp hnati
  have hlo : T.lower.hom.app Y =
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n).map i := by
    rw [T.lower_hom]
    rfl
  apply (cancel_epi (T.lower.hom.app Y)).mp
  change T.lower.hom.app Y ≫
    ((T.edge G e₀).app Y ≫ τ.app ((DerivedCategory.Plus.homologyFunctor B n).obj Y)) = _
  simp only [ColumnTruncation.edge, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, isoWhiskerLeft_hom, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hlo]
  change (DerivedCategory.Plus.homologyFunctor C n).map
      (G.rightDerivedFunctorPlus.map p) ≫
    ((shiftedStalkValueIso G n ≪≫ e₀).hom.app ((DerivedCategory.Plus.homologyFunctor B n).obj Y) ≫
      τ.app ((DerivedCategory.Plus.homologyFunctor B n).obj Y)) = _
  let f : (DerivedCategory.Plus.homologyFunctor B n).obj
      ((DerivedCategory.Plus.singleFunctor B n).obj ((DerivedCategory.Plus.homologyFunctor B n).obj Y)) ⟶
      (DerivedCategory.Plus.homologyFunctor B n).obj Y :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app
      ((DerivedCategory.Plus.homologyFunctor B n).obj Y)
  have hf : (DerivedCategory.Plus.homologyFunctor B n).map p ≫ f =
      (DerivedCategory.Plus.homologyFunctor B n).map i := hnorm
  change _ = (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map i) ≫ κ.app Y
  rw [hnati]
  have hnatp_assoc := congrArg (fun t => t ≫ U.map f) hnatp
  simp only [Category.assoc] at hnatp_assoc
  rw [← hf, U.map_comp, ← hnatp_assoc, hκ]
  simp only [Category.assoc, ← Functor.map_comp, f, Iso.inv_hom_id_app]
  erw [U.map_id]
  simp only [Category.comp_id]

section ExactComparison

variable [U.Additive] [U.PreservesHomology]

open HomologicalComplex

/-- Exact additive functors commute with cohomology of the ordinary complexes. -/
def exactComplexHomologyIso (n : ℤ) :
    U.mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor C (.up ℤ) n ≅
      homologyFunctor B (.up ℤ) n ⋙ U :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso U) (by
    intro K L f
    exact ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor B (.up ℤ) n).map f) U)

/-- Cohomology on the bounded-below derived category, before localization. -/
def plusHomologyFactors (D : Type*) [Category* D] [Abelian D] [HasDerivedCategory D] (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor D n ≅
      CochainComplex.Plus.ι D ⋙ homologyFunctor D (.up ℤ) n :=
  NatIso.ofComponents (fun K => (DerivedCategory.homologyFunctorFactors D n).app K.obj) (by
    intro K L f
    exact (DerivedCategory.homologyFunctorFactors D n).hom.naturality f.hom)

/-- The ordinary comparison on a cochain complex, seen after localization. -/
def exactComplexHomologyFactors (n : ℤ) :
    U.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      DerivedCategory.Plus.Q ⋙ (DerivedCategory.Plus.homologyFunctor B n ⋙ U) :=
  isoWhiskerLeft U.mapCochainComplexPlus (plusHomologyFactors C n) ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight U.mapCochainComplexPlusCompι _ ≪≫
    CategoryTheory.Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (CochainComplex.Plus.ι B) (exactComplexHomologyIso U n) ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (plusHomologyFactors B n).symm _ ≪≫
    CategoryTheory.Functor.associator _ _ _

local notation "η" => G.rightDerivedFunctorPlusUnit

/-- The derived unit followed by cohomology, with the associator included. -/
def derivedHomologyUnit (n : ℤ) :
    (G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.homologyFunctor C n ⟶
      DerivedCategory.Plus.Q ⋙ (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n) :=
  whiskerRight (η) _ ≫ (CategoryTheory.Functor.associator _ _ _).hom

theorem derivedHomologyUnit_isRightDerived (n : ℤ) :
    (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n).IsRightDerivedFunctor
      (derivedHomologyUnit G n) (CochainComplex.Plus.quasiIso B) := by
  have hG := CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus G
  have h' : (CochainComplex.Plus.localizerMorphism B).Derives
      ((G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.homologyFunctor C n) := by
    intro K L f hf
    have h := hG f hf
    change IsIso ((DerivedCategory.Plus.homologyFunctor C n).map
      (((CochainComplex.Plus.localizerMorphism B).functor ⋙
        G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map f))
    infer_instance
  apply h'.isRightDerivedFunctor_of_isIso
  intro K
  dsimp [derivedHomologyUnit]
  infer_instance

/-- Derived cohomology of G maps naturally to U of cohomology. -/
def derivedToExactHomology (τ : G ⟶ U) (n : ℤ) :
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ⟶
      DerivedCategory.Plus.homologyFunctor B n ⋙ U := by
  letI := derivedHomologyUnit_isRightDerived G n
  exact (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n).rightDerivedDesc
    (derivedHomologyUnit G n) (CochainComplex.Plus.quasiIso B)
    (DerivedCategory.Plus.homologyFunctor B n ⋙ U)
    ((CategoryTheory.Functor.associator _ _ _).hom ≫ whiskerRight τ.mapCochainComplexPlus
      (DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n) ≫
      (exactComplexHomologyFactors U n).hom)

@[reassoc]
theorem derivedToExactHomology_fac (τ : G ⟶ U) (n : ℤ) (K : CochainComplex.Plus B) :
    (DerivedCategory.Plus.homologyFunctor C n).map ((η).app K) ≫
      (derivedToExactHomology G U τ n).app (DerivedCategory.Plus.Q.obj K) =
    (DerivedCategory.Plus.homologyFunctor C n).map
      (DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K)) ≫
        (exactComplexHomologyFactors U n).hom.app K := by
  letI := derivedHomologyUnit_isRightDerived G n
  have h := (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n).rightDerived_fac
    (derivedHomologyUnit G n) (CochainComplex.Plus.quasiIso B)
    (DerivedCategory.Plus.homologyFunctor B n ⋙ U)
    ((CategoryTheory.Functor.associator _ _ _).hom ≫ whiskerRight τ.mapCochainComplexPlus
      (DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n) ≫
      (exactComplexHomologyFactors U n).hom)
  simpa only [derivedToExactHomology, derivedHomologyUnit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Category.id_comp, Category.comp_id, Functor.comp_map] using
      congrArg (fun t => t.app K) h


/-- In a complex with vanishing adjacent differentials, homology is
canonically the term itself. -/
def homologyTermIso {D : Type*} [Category* D] [Abelian D]
    (K : CochainComplex D ℤ) (n : ℤ)
    (hf : K.d ((ComplexShape.up ℤ).prev n) n = 0)
    (hg : K.d n ((ComplexShape.up ℤ).next n) = 0) : K.homology n ≅ K.X n :=
  (ShortComplex.HomologyData.ofZeros (S := K.sc n) hf hg).left.homologyIso

@[reassoc]
theorem homologyπ_homologyTermIso_hom {D : Type*} [Category* D] [Abelian D]
    (K : CochainComplex D ℤ) (n : ℤ)
    (hf : K.d ((ComplexShape.up ℤ).prev n) n = 0)
    (hg : K.d n ((ComplexShape.up ℤ).next n) = 0) :
    K.homologyπ n ≫ (homologyTermIso K n hf hg).hom = K.iCycles n := by
  let h := ShortComplex.HomologyData.ofZeros (S := K.sc n) hf hg
  change (K.sc n).homologyπ ≫ h.left.homologyIso.hom = (K.sc n).iCycles
  rw [h.left.homologyπ_comp_homologyIso_hom, ← h.left.cyclesIso_hom_comp_i]
  rfl

@[reassoc]
theorem homologyTermIso_naturality {D : Type*} [Category* D] [Abelian D]
    {K L : CochainComplex D ℤ} (f : K ⟶ L) (n : ℤ)
    (hfK : K.d ((ComplexShape.up ℤ).prev n) n = 0)
    (hgK : K.d n ((ComplexShape.up ℤ).next n) = 0)
    (hfL : L.d ((ComplexShape.up ℤ).prev n) n = 0)
    (hgL : L.d n ((ComplexShape.up ℤ).next n) = 0) :
    homologyMap f n ≫ (homologyTermIso L n hfL hgL).hom =
      (homologyTermIso K n hfK hgK).hom ≫ f.f n := by
  rw [← cancel_epi (K.homologyπ n)]
  simp only [homologyπ_naturality_assoc, homologyπ_homologyTermIso_hom, 
    homologyπ_homologyTermIso_hom_assoc, cyclesMap_i]

@[reassoc]
theorem exactComplexHomologyIso_comp_term (n : ℤ) (K : CochainComplex B ℤ)
    (hf : K.d ((ComplexShape.up ℤ).prev n) n = 0)
    (hg : K.d n ((ComplexShape.up ℤ).next n) = 0) :
    (exactComplexHomologyIso U n).hom.app K ≫ U.map (homologyTermIso K n hf hg).hom =
      (homologyTermIso ((U.mapHomologicalComplex (.up ℤ)).obj K) n
        (by simp [hf]) (by simp [hg])).hom := by
  let h := (ShortComplex.HomologyData.ofZeros (S := K.sc n) hf hg).left
  change ((K.sc n).mapHomologyIso U).hom ≫ U.map h.homologyIso.hom = _
  rw [h.mapHomologyIso_eq U]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← U.map_comp, Iso.inv_hom_id]
  erw [U.map_id]
  erw [Category.comp_id]
  apply (cancel_epi (((U.mapHomologicalComplex (.up ℤ)).obj K).homologyπ n)).mp
  rw [homologyπ_homologyTermIso_hom]
  change ((K.sc n).map U).homologyπ ≫ (h.map U).homologyIso.hom = ((K.sc n).map U).iCycles
  rw [(h.map U).homologyπ_comp_homologyIso_hom, ← (h.map U).cyclesIso_hom_comp_i]
  rfl


@[reassoc]
theorem singleObjHomologySelfIso_eq_term {D : Type*} [Category* D] [Abelian D]
    (n : ℤ) (X : D) :
    (singleObjHomologySelfIso (.up ℤ) n X).hom =
      (homologyTermIso ((CochainComplex.singleFunctor D n).obj X) n rfl rfl).hom ≫
        (singleObjXSelf (.up ℤ) n X).hom := by
  rw [← cancel_epi (((CochainComplex.singleFunctor D n).obj X).homologyπ n)]
  rw [homologyπ_homologyTermIso_hom_assoc]
  exact (homologyπ_singleObjHomologySelfIso_hom (.up ℤ) n X).trans
    (singleObjCyclesSelfIso_hom (.up ℤ) n X)

@[reassoc]
theorem exactComplexHomologyIso_comp_stalk (τ : G ⟶ U) (n : ℤ) (X : B) :
    homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app
      ((CochainComplex.singleFunctor B n).obj X)) n ≫
      (exactComplexHomologyIso U n).hom.app ((CochainComplex.singleFunctor B n).obj X) ≫
      U.map (singleObjHomologySelfIso (.up ℤ) n X).hom =
    homologyMap ((singleMapHomologicalComplex G (.up ℤ) n).hom.app X) n ≫
      (singleObjHomologySelfIso (.up ℤ) n (G.obj X)).hom ≫ τ.app X := by
  let K := (CochainComplex.singleFunctor B n).obj X
  let tf := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K
  let gf : (G.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (CochainComplex.singleFunctor C n).obj (G.obj X) :=
    (singleMapHomologicalComplex G (.up ℤ) n).hom.app X
  rw [singleObjHomologySelfIso_eq_term n X, U.map_comp]
  change homologyMap tf n ≫ (exactComplexHomologyIso U n).hom.app K ≫
      U.map (homologyTermIso K n rfl rfl).hom ≫ U.map (singleObjXSelf (.up ℤ) n X).hom = _
  rw [exactComplexHomologyIso_comp_term_assoc U n K rfl rfl]
  rw [singleObjHomologySelfIso_eq_term n (G.obj X), Category.assoc]
  erw [homologyTermIso_naturality_assoc gf n (by simp [K]) (by simp [K]) rfl rfl,
    homologyTermIso_naturality_assoc tf n (by simp [K]) (by simp [K])
    (by simp [K]) (by simp [K])]
  have hgf : gf.f n ≫ (singleObjXSelf (.up ℤ) n (G.obj X)).hom ≫ τ.app X =
      G.map (singleObjXSelf (.up ℤ) n X).hom ≫ τ.app X := by
    change ((singleMapHomologicalComplex G (.up ℤ) n).hom.app X).f n ≫ _ = _
    rw [singleMapHomologicalComplex_hom_app_self, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun t => (homologyTermIso ((G.mapHomologicalComplex (.up ℤ)).obj K) n
    (by simp [K]) (by simp [K])).hom ≫ t)
    ((τ.naturality (singleObjXSelf (.up ℤ) n X).hom).symm.trans hgf.symm)


/-- A stalk in a specified degree, viewed as a bounded-below complex. -/
def plusStalkObj (D : Type*) [Category* D] [Abelian D] (n : ℤ) (X : D) :
    CochainComplex.Plus D :=
  ⟨(CochainComplex.singleFunctor D n).obj X, n, inferInstance⟩

/-- Mapping a termwise stalk agrees with the stalk of the mapped object. -/
def mapPlusStalkIso (n : ℤ) (X : B) :
    (G.mapCochainComplexPlus).obj (plusStalkObj B n X) ≅
      plusStalkObj C n (G.obj X) :=
  (CochainComplex.plus C).isoMk ((singleMapHomologicalComplex G (.up ℤ) n).app X)

/-- The map from the stalk of the value to the derived value of the stalk. -/
def stalkDerivedApp (n : ℤ) (X : B) :
    (DerivedCategory.Plus.singleFunctor C n).obj (G.obj X) ⟶
      G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B n).obj X) :=
  DerivedCategory.Plus.Q.map (mapPlusStalkIso G n X).inv ≫
    G.rightDerivedFunctorPlusUnit.app (plusStalkObj B n X)

@[reassoc]
theorem exactComplexHomologyFactors_comp_stalk (τ : G ⟶ U) (n : ℤ) (X : B) :
    (DerivedCategory.Plus.homologyFunctor C n).map
      (DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app (plusStalkObj B n X))) ≫
      (exactComplexHomologyFactors U n).hom.app (plusStalkObj B n X) ≫
      U.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app X) =
    (DerivedCategory.Plus.homologyFunctor C n).map
      (DerivedCategory.Plus.Q.map (mapPlusStalkIso G n X).hom) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (G.obj X) ≫ τ.app X := by
  let K := plusStalkObj B n X
  let f := τ.mapCochainComplexPlus.app K
  let g := (mapPlusStalkIso G n X).hom
  change (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫ _ =
    (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map g) ≫ _
  have hB : (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app X =
      (plusHomologyFactors B n).hom.app K ≫ (singleObjHomologySelfIso (.up ℤ) n X).hom := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso, plusHomologyFactors,
      DerivedCategory.singleFunctorsPostcompQIso]
    rfl
  have hC : (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (G.obj X) =
      (plusHomologyFactors C n).hom.app (plusStalkObj C n (G.obj X)) ≫
        (singleObjHomologySelfIso (.up ℤ) n (G.obj X)).hom := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso, plusHomologyFactors,
      DerivedCategory.singleFunctorsPostcompQIso]
    rfl
  rw [hB, hC, U.map_comp]
  simp only [exactComplexHomologyFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.assoc]
  simp only [Functor.mapCochainComplexPlusCompι_hom_app]
  erw [(homologyFunctor C (.up ℤ) n).map_id, Category.id_comp]
  change (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫
      (plusHomologyFactors C n).hom.app (U.mapCochainComplexPlus.obj K) ≫
      (exactComplexHomologyIso U n).hom.app K.obj ≫
      U.map ((plusHomologyFactors B n).inv.app K) ≫ U.map ((plusHomologyFactors B n).hom.app K) ≫
      U.map (singleObjHomologySelfIso (.up ℤ) n X).hom = _
  erw [← U.map_comp_assoc, Iso.inv_hom_id_app, U.map_id, Category.id_comp]
  have hf : (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫
      (plusHomologyFactors C n).hom.app (U.mapCochainComplexPlus.obj K) =
    (plusHomologyFactors C n).hom.app (G.mapCochainComplexPlus.obj K) ≫ homologyMap f.hom n :=
      (plusHomologyFactors C n).hom.naturality f
  have hg : (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map g) ≫
      (plusHomologyFactors C n).hom.app (plusStalkObj C n (G.obj X)) =
    (plusHomologyFactors C n).hom.app (G.mapCochainComplexPlus.obj K) ≫ homologyMap g.hom n :=
      (plusHomologyFactors C n).hom.naturality g
  rw [reassoc_of% hf, reassoc_of% hg]
  congr 1
  exact exactComplexHomologyIso_comp_stalk G U τ n X

@[reassoc]
theorem derivedToExactHomology_stalk_comp (τ : G ⟶ U) (n : ℤ) (X : B) :
    (DerivedCategory.Plus.homologyFunctor C n).map (stalkDerivedApp G n X) ≫
      (derivedToExactHomology G U τ n).app ((DerivedCategory.Plus.singleFunctor B n).obj X) ≫
      U.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app X) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app (G.obj X) ≫ τ.app X := by
  let H := DerivedCategory.Plus.homologyFunctor C n
  change H.map (DerivedCategory.Plus.Q.map (mapPlusStalkIso G n X).inv ≫
      G.rightDerivedFunctorPlusUnit.app (plusStalkObj B n X)) ≫ _ = _
  rw [H.map_comp, Category.assoc]
  erw [derivedToExactHomology_fac_assoc G U τ n (plusStalkObj B n X),
    exactComplexHomologyFactors_comp_stalk G U τ n X]
  erw [← H.map_comp_assoc, ← DerivedCategory.Plus.Q.map_comp, Iso.inv_hom_id,
    DerivedCategory.Plus.Q.map_id, H.map_id, Category.id_comp]


theorem stalkDerivedApp_zero (X : B) :
    stalkDerivedApp G 0 X = (stalkToDerived G).app X := by
  simp only [stalkDerivedApp, stalkToDerived, NatTrans.comp_app, whiskerLeft_app]
  congr 1
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  simp only [mappedStalkIso, mapPlusStalkIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app, Functor.FullyFaithful.map_preimage]
  simp [DerivedCategory.singleFunctorIsoCompQ]
  erw [Category.id_comp]
  rfl

open CochainComplex in
theorem ordinary_stalk_shift_homology {D : Type*} [Category* D] [Abelian D]
    (n : ℤ) (X : D) :
    let _K := (CochainComplex.singleFunctor D n).obj X
    let f := ((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X
    (homologyFunctor D (.up ℤ) 0).shiftMap f 0 n (add_zero n) ≫
      (singleObjHomologySelfIso (.up ℤ) n X).hom =
    (singleObjHomologySelfIso (.up ℤ) 0 X).hom := by
  intro K f
  let K₀ := (CochainComplex.singleFunctor D 0).obj X
  let K' : CochainComplex D ℤ := K⟦n⟧
  let σ := (CochainComplex.shiftShortComplexFunctorIso D n 0 n (add_zero n)).hom.app K
  have hf : K'.d ((ComplexShape.up ℤ).prev 0) 0 = 0 := by
    simp [K', K, CochainComplex.shiftFunctor_obj_d']
  have hg : K'.d 0 ((ComplexShape.up ℤ).next 0) = 0 := by
    simp [K', K, CochainComplex.shiftFunctor_obj_d']
  have hσ :
      ShortComplex.homologyMap σ ≫ (homologyTermIso K n rfl rfl).hom =
        (homologyTermIso K' 0 hf hg).hom ≫ σ.τ₂ := by
    let h := ShortComplex.HomologyMapData.ofZeros σ
      (show (K'.sc 0).f = 0 from hf) (show (K'.sc 0).g = 0 from hg)
      (show (K.sc n).f = 0 from rfl) (show (K.sc n).g = 0 from rfl)
    exact h.left.homologyMap_comm
  rw [Functor.shiftMap, Category.assoc]
  change homologyMap f 0 ≫ (CochainComplex.ShiftSequence.shiftIso D n 0 n
    (add_zero n)).hom.app K ≫ (singleObjHomologySelfIso (.up ℤ) n X).hom = _
  erw [CochainComplex.ShiftSequence.shiftIso_hom_app, singleObjHomologySelfIso_eq_term,
    reassoc_of% hσ, homologyTermIso_naturality_assoc f 0 rfl rfl hf hg]
  rw [singleObjHomologySelfIso_eq_term]
  congr 1
  change f.f 0 ≫ σ.τ₂ ≫ (singleObjXSelf (.up ℤ) n X).hom =
    (singleObjXSelf (.up ℤ) 0 X).hom
  simp [f, σ, CochainComplex.singleFunctors, singleObjXSelf, singleObjXIsoOfEq,
    HomologicalComplex.XIsoOfEq]


theorem homotopy_homology_isoShiftZero {D : Type*} [Category* D] [Abelian D] :
    ((HomotopyCategory.homologyFunctor D (.up ℤ) 0).isoShiftZero ℤ).hom = 𝟙 _ := by
  let L := HomotopyCategory.quotient D (.up ℤ)
  apply ((whiskeringLeft _ _ _).obj L).map_injective
  ext K
  change ((HomotopyCategory.homologyFunctor D (.up ℤ) 0).isoShiftZero ℤ).hom.app (L.obj K) = 𝟙 _
  erw [Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj]
  change (HomotopyCategory.homologyFunctorFactors D (.up ℤ) 0).hom.app K ≫
    𝟙 _ ≫ (HomotopyCategory.homologyFunctorFactors D (.up ℤ) 0).inv.app K = _
  simp
  rfl

theorem derived_homology_isoShiftZero {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D] :
    ((DerivedCategory.homologyFunctor D 0).isoShiftZero ℤ).hom = 𝟙 _ := by
  let L := DerivedCategory.Qh (C := D)
  apply ((whiskeringLeft _ _ _).obj L).map_injective
  ext K
  change ((DerivedCategory.homologyFunctor D 0).isoShiftZero ℤ).hom.app (L.obj K) = 𝟙 _
  erw [Functor.ShiftSequence.induced_isoShiftZero_hom_app_obj]
  rw [homotopy_homology_isoShiftZero]
  simp
  rfl

theorem derived_stalk_shift_homology {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (n : ℤ) (X : D) :
    let K := (DerivedCategory.singleFunctor D n).obj X
    let f := ((DerivedCategory.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X
    (DerivedCategory.homologyFunctor D 0).map f ≫
      ((DerivedCategory.homologyFunctor D 0).isoShift n).hom.app K ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D n).hom.app X =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app X := by
  intro K f
  let H := DerivedCategory.homologyFunctor D 0
  have h₀ : (H.isoShiftZero ℤ).inv = 𝟙 _ := by
    have h₀' : (H.isoShiftZero ℤ).hom = 𝟙 _ := derived_homology_isoShiftZero
    apply (cancel_mono (H.isoShiftZero ℤ).hom).mp
    rw [Iso.inv_hom_id, h₀', Category.id_comp]
    rfl
  have hf : f = ShiftedHom.map
      (((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X)
        (DerivedCategory.Q (C := D)) := by
    change (((CochainComplex.singleFunctors D).postcomp DerivedCategory.Q).shiftIso
      n 0 n (add_zero n)).inv.app X = _
    rw [SingleFunctors.postcomp_shiftIso_inv_app]
    rfl
  change H.map f ≫ (H.isoShift n).hom.app K ≫ _ = _
  have hmap : H.map f ≫ (H.isoShift n).hom.app K = H.shiftMap f 0 n (add_zero n) := by
    unfold Functor.isoShift Functor.shiftMap
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, Iso.symm_hom,
      whiskerLeft_app, h₀, NatTrans.id_app]
    erw [Category.id_comp]
    rfl
  rw [← Category.assoc, hmap, hf, DerivedCategory.shiftMap_homologyFunctor_map_Q
    _ 0 n (add_zero n)]
  have h (j : ℤ) : (DerivedCategory.singleFunctorCompHomologyFunctorIso D j).hom.app X =
      (DerivedCategory.homologyFunctorFactors D j).hom.app
        ((CochainComplex.singleFunctor D j).obj X) ≫
        (singleObjHomologySelfIso (.up ℤ) j X).hom := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorsPostcompQIso]
  rw [h n, h 0]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun t => (DerivedCategory.homologyFunctorFactors D 0).hom.app
    ((CochainComplex.singleFunctor D 0).obj X) ≫ t) (ordinary_stalk_shift_homology n X)


/-- Homology of a stalk is normalized compatibly with moving the stalk to degree zero. -/
theorem plus_stalk_shift_homology {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (n : ℤ) (X : D) :
    let K := (DerivedCategory.Plus.singleFunctor D n).obj X
    let f := ((DerivedCategory.Plus.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X
    (DerivedCategory.Plus.homologyFunctor D 0).map f ≫
      ((DerivedCategory.Plus.homologyFunctor D 0).isoShift n).hom.app K ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D n).hom.app X =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app X := by
  intro K f
  let ι := DerivedCategory.Plus.ι (C := D)
  let HD := DerivedCategory.homologyFunctor D 0
  let HP := DerivedCategory.Plus.homologyFunctor D 0
  let e := (DerivedCategory.Plus.singleFunctors D).shiftIso n 0 n (add_zero n)
  let e' := (DerivedCategory.singleFunctors D).shiftIso n 0 n (add_zero n)
  have he :
      ι.map (e.hom.app X) = (ι.commShiftIso n).hom.app K ≫ e'.hom.app X := by
    unfold e DerivedCategory.Plus.singleFunctors
    rw [SingleFunctors.map_lift_shiftIso_hom_app]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [(shiftFunctor (DerivedCategory D) n).map_id, Category.id_comp, Category.comp_id]
    rfl
  have hf : ι.map f ≫ (ι.commShiftIso n).hom.app K = e'.inv.app X := by
    apply (cancel_mono (e'.hom.app X)).mp
    rw [Category.assoc, ← he, ← ι.map_comp, Iso.inv_hom_id_app, ι.map_id, Iso.inv_hom_id_app]
    rfl
  have hshift :
      (HP.isoShift n).hom.app K =
        HD.map ((ι.commShiftIso n).hom.app K) ≫ (HD.isoShift n).hom.app (ι.obj K) := by
    have h0 : (HD.isoShiftZero ℤ).inv = 𝟙 _ := by
      apply (cancel_mono (HD.isoShiftZero ℤ).hom).mp
      rw [Iso.inv_hom_id, derived_homology_isoShiftZero, Category.id_comp]
      rfl
    have h₀c : ((ι ⋙ HD).isoShiftZero ℤ).inv = 𝟙 _ := by
      change ((isoWhiskerLeft ι (HD.isoShiftZero ℤ)) ≪≫ Iso.refl _).inv = 𝟙 _
      simp [h0]
    have hₛ : (((ι ⋙ HD).shiftIso n 0 n (add_zero n))).hom.app K =
        HD.map ((ι.commShiftIso n).hom.app K) ≫
          ((HD.shiftIso n 0 n (add_zero n))).hom.app (ι.obj K) := by
      change (((shiftFunctor _ n).associator ι (HD.shift 0)).symm ≪≫
        isoWhiskerRight (ι.commShiftIso n) (HD.shift 0) ≪≫
        (ι.associator _ _) ≪≫ isoWhiskerLeft ι (HD.shiftIso n 0 n (add_zero n))).hom.app K = _
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, associator_inv_app,
        associator_hom_app, Category.id_comp]
      rfl
    change ((ι ⋙ HD).isoShift n).hom.app K = _
    simp only [Functor.isoShift, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      Iso.symm_hom, whiskerLeft_app, h₀c, h0, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, hₛ]
  change HD.map (ι.map f) ≫ (HP.isoShift n).hom.app K ≫ _ = _
  erw [hshift, Category.assoc, ← HD.map_comp_assoc, hf]
  exact derived_stalk_shift_homology n X


open CochainComplex in
theorem ordinaryStalkShiftMap (n : ℤ) (X : B) :
    let σB := ((singleFunctors B).shiftIso n 0 n (add_zero n)).inv.app X
    let σC : ShiftedHom ((CochainComplex.singleFunctor C 0).obj (G.obj X))
        ((CochainComplex.singleFunctor C n).obj (G.obj X)) n :=
      ((singleFunctors C).shiftIso n 0 n (add_zero n)).inv.app (G.obj X)
    let μ₀ := (singleMapHomologicalComplex G (.up ℤ) 0).hom.app X
    let μₙ := (singleMapHomologicalComplex G (.up ℤ) n).hom.app X
    (ShiftedHom.map σB (G.mapHomologicalComplex (.up ℤ))).comp
      (ShiftedHom.mk₀ 0 rfl μₙ) (zero_add n) =
    (ShiftedHom.mk₀ 0 rfl μ₀).comp σC (add_zero n) := by
  intro σB σC μ₀ μₙ
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [ShiftedHom.map, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    simp [σB, σC, μ₀, μₙ, CochainComplex.singleFunctors, singleMapHomologicalComplex,
      eqToHom_map, eqToHom_trans]
  · exact (isZero_single_obj_X (.up ℤ) 0 X i hi |> G.map_isZero).eq_of_src _ _


/-- The shifted degree-zero stalk map in bounded-below ordinary complexes. -/
def plusOrdinaryStalkShift (D : Type*) [Category* D] [Abelian D] (n : ℤ) (X : D) :
    ShiftedHom (plusStalkObj D 0 X) (plusStalkObj D n X) n :=
  (CochainComplex.Plus.fullyFaithfulι D).preimage
    (((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X ≫
      ((CochainComplex.Plus.ι D).commShiftIso n).inv.app (plusStalkObj D n X))

@[reassoc]
theorem plusOrdinaryStalkShift_map (D : Type*) [Category* D] [Abelian D] (n : ℤ) (X : D) :
    (plusOrdinaryStalkShift D n X).map (CochainComplex.Plus.ι D) =
      ((CochainComplex.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X := by
  unfold ShiftedHom.map plusOrdinaryStalkShift
  erw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

theorem shiftedMap_injective {D E : Type*} [Category* D] [Category* E]
    [HasShift D ℤ] [HasShift E ℤ] (F : D ⥤ E) [F.CommShift ℤ] [F.Faithful]
    {X Y : D} {n : ℤ} {f g : ShiftedHom X Y n} (h : f.map F = g.map F) : f = g := by
  exact F.map_injective ((cancel_mono ((F.commShiftIso n).hom.app Y)).mp h)

@[reassoc]
theorem plusOrdinaryStalkShift_Q (D : Type*) [Category* D] [Abelian D] [HasDerivedCategory D]
    (n : ℤ) (X : D) :
    (plusOrdinaryStalkShift D n X).map (DerivedCategory.Plus.Q (C := D)) =
      ((DerivedCategory.Plus.singleFunctors D).shiftIso n 0 n (add_zero n)).inv.app X := by
  let ι := DerivedCategory.Plus.ι (C := D)
  let Q := DerivedCategory.Plus.Q (C := D)
  let q := DerivedCategory.Q (C := D)
  let c := CochainComplex.Plus.ι D
  let K := plusStalkObj D n X
  let f := plusOrdinaryStalkShift D n X
  let e := (DerivedCategory.Plus.singleFunctors D).shiftIso n 0 n (add_zero n)
  let e' := (DerivedCategory.singleFunctors D).shiftIso n 0 n (add_zero n)
  have he :
      ι.map (e.hom.app X) = (ι.commShiftIso n).hom.app (Q.obj K) ≫ e'.hom.app X := by
    unfold e DerivedCategory.Plus.singleFunctors
    rw [SingleFunctors.map_lift_shiftIso_hom_app]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [(shiftFunctor (DerivedCategory D) n).map_id, Category.id_comp, Category.comp_id]
    rfl
  have he' : ShiftedHom.map (a := n) (X := Q.obj (plusStalkObj D 0 X)) (Y := Q.obj K) (e.inv.app X) ι =
      e'.inv.app X := by
    apply (cancel_mono (e'.hom.app X)).mp
    change (ι.map (e.inv.app X) ≫ (ι.commShiftIso n).hom.app (Q.obj K)) ≫ _ = _
    rw [Category.assoc, ← he, ← ι.map_comp, Iso.inv_hom_id_app, ι.map_id, Iso.inv_hom_id_app]
    rfl
  change f.map Q = e.inv.app X
  apply shiftedMap_injective ι
  rw [he', ← ShiftedHom.comp_map]
  have h := ShiftedHom.map_naturality_1 f (DerivedCategory.Plus.QCompιIso D)
  have hh : f.map (Q ⋙ ι) = f.map (c ⋙ q) := by
    simp only [DerivedCategory.Plus.QCompιIso_hom_app, DerivedCategory.Plus.QCompιIso_inv_app,
      ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
    erw [Category.id_comp, (shiftFunctor (DerivedCategory D) n).map_id, Category.comp_id] at h
    exact h
  rw [hh, ShiftedHom.comp_map, plusOrdinaryStalkShift_map]
  change _ = (((CochainComplex.singleFunctors D).postcomp DerivedCategory.Q).shiftIso
    n 0 n (add_zero n)).inv.app X
  rw [SingleFunctors.postcomp_shiftIso_inv_app]
  rfl


theorem plusOrdinaryStalkShift_map_stalk (n : ℤ) (X : B) :
    ((plusOrdinaryStalkShift B n X).map G.mapCochainComplexPlus).comp
      (ShiftedHom.mk₀ 0 rfl (mapPlusStalkIso G n X).hom) (zero_add n) =
    (ShiftedHom.mk₀ 0 rfl (mapPlusStalkIso G 0 X).hom).comp
      (plusOrdinaryStalkShift C n (G.obj X)) (add_zero n) := by
  let i := CochainComplex.Plus.ι C
  let j := CochainComplex.Plus.ι B
  let f := plusOrdinaryStalkShift B n X
  let g := plusOrdinaryStalkShift C n (G.obj X)
  let F := G.mapCochainComplexPlus
  let F' := G.mapHomologicalComplex (.up ℤ)
  let μ₀ := (mapPlusStalkIso G 0 X).hom
  let μₙ := (mapPlusStalkIso G n X).hom
  change (f.map F).comp (ShiftedHom.mk₀ 0 rfl μₙ) (zero_add n) =
    (ShiftedHom.mk₀ 0 rfl μ₀).comp g (add_zero n)
  apply shiftedMap_injective i
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, ← ShiftedHom.comp_map, show g.map i = _ from
      plusOrdinaryStalkShift_map C n (G.obj X)]
  have ht := ShiftedHom.map_naturality_1 f G.mapCochainComplexPlusCompι
  have hf : f.map (F ⋙ i) = f.map (j ⋙ F') := by
    simp only [Functor.mapCochainComplexPlusCompι_hom_app,
      Functor.mapCochainComplexPlusCompι_inv_app, ShiftedHom.comp_mk₀,
      ShiftedHom.mk₀_comp] at ht
    erw [Category.id_comp, (shiftFunctor (CochainComplex C ℤ) n).map_id, Category.comp_id] at ht
    exact ht
  rw [hf, ShiftedHom.comp_map, show f.map j = _ from plusOrdinaryStalkShift_map B n X]
  exact ordinaryStalkShiftMap G n X

theorem stalkDerivedApp_comm_shift (n : ℤ) (X : B) :
    let σB : ShiftedHom ((DerivedCategory.Plus.singleFunctor B 0).obj X)
        ((DerivedCategory.Plus.singleFunctor B n).obj X) n :=
      ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (add_zero n)).inv.app X
    let σC : ShiftedHom ((DerivedCategory.Plus.singleFunctor C 0).obj (G.obj X))
        ((DerivedCategory.Plus.singleFunctor C n).obj (G.obj X)) n :=
      ((DerivedCategory.Plus.singleFunctors C).shiftIso n 0 n (add_zero n)).inv.app (G.obj X)
    (ShiftedHom.mk₀ 0 rfl (stalkDerivedApp G 0 X)).comp
        (σB.map G.rightDerivedFunctorPlus) (add_zero n) =
      σC.comp (ShiftedHom.mk₀ 0 rfl (stalkDerivedApp G n X)) (zero_add n) := by
  intro σB σC
  let Q := DerivedCategory.Plus.Q (C := B)
  let Q' := DerivedCategory.Plus.Q (C := C)
  let F := G.mapCochainComplexPlus
  let R := G.rightDerivedFunctorPlus
  let f := plusOrdinaryStalkShift B n X
  let g := plusOrdinaryStalkShift C n (G.obj X)
  let μ₀ := (mapPlusStalkIso G 0 X)
  let μₙ := (mapPlusStalkIso G n X)
  let α := G.rightDerivedFunctorPlusUnit
  have hf : f.map Q = σB := plusOrdinaryStalkShift_Q B n X
  have hg : g.map Q' = σC := plusOrdinaryStalkShift_Q C n (G.obj X)
  have ht := ShiftedHom.map_naturality f α
  change (((f.map (F ⋙ Q')).comp (ShiftedHom.mk₀ 0 rfl (α.app (plusStalkObj B n X)))
      (zero_add n))) = _ at ht
  rw [ShiftedHom.comp_map, ShiftedHom.comp_map, hf] at ht
  have hμ := congrArg (fun x => ShiftedHom.map x Q') (plusOrdinaryStalkShift_map_stalk G n X)
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, hg] at hμ
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at ht hμ ⊢
  change (Q'.map μ₀.inv ≫ α.app (plusStalkObj B 0 X)) ≫ σB.map R =
    σC ≫ (shiftFunctor (DerivedCategory.Plus C) n).map
      (Q'.map μₙ.inv ≫ α.app (plusStalkObj B n X))
  let S := shiftFunctor (DerivedCategory.Plus C) n
  have hμ' : Q'.map μ₀.inv ≫ (f.map F).map Q' = σC ≫ S.map (Q'.map μₙ.inv) := by
    apply (cancel_epi (Q'.map μ₀.hom)).mp
    change (f.map F).map Q' ≫ S.map (Q'.map μₙ.hom) = Q'.map μ₀.hom ≫ σC at hμ
    simp only [← reassoc_of% hμ, ← Functor.map_comp_assoc, Iso.hom_inv_id]
    erw [← S.map_comp, ← Q'.map_comp, Iso.hom_inv_id, Q'.map_id, Q'.map_id, S.map_id,
      Category.id_comp, Category.comp_id]
  erw [Category.assoc, ← ht, ← Category.assoc (Q'.map μ₀.inv), hμ',
    Category.assoc, ← S.map_comp]


theorem shiftedStalkValueIso_inv_eq (n : ℤ) (hn : n ≠ 0) (X : B) :
    let R := G.rightDerivedFunctorPlus
    let H := DerivedCategory.Plus.homologyFunctor C 0
    let σ : ShiftedHom ((DerivedCategory.Plus.singleFunctor B 0).obj X)
        ((DerivedCategory.Plus.singleFunctor B n).obj X) n :=
      ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (add_zero n)).inv.app X
    (shiftedStalkValueIso G n).inv.app X =
      H.map (σ.map R) ≫ (H.isoShift n).hom.app (R.obj ((DerivedCategory.Plus.singleFunctor B n).obj X)) := by
  intro R H σ
  simp only [shiftedStalkValueIso, dite_eq_right hn, id_eq, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app,
    whiskerRight_app, ShiftedHom.map, Functor.map_comp, Category.assoc]
  rfl

theorem stalkDerivedApp_homology_normalization (n : ℤ) (X : B) :
    (degreeZeroUnit G).app X ≫ (shiftedStalkValueIso G n).inv.app X =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app (G.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map (stalkDerivedApp G n X) := by
  by_cases hn : n = 0
  · subst n
    simp [shiftedStalkValueIso, degreeZeroUnit, stalkDerivedApp_zero]
    erw [Category.comp_id]
  let R := G.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let Hn := DerivedCategory.Plus.homologyFunctor C n
  let SB := DerivedCategory.Plus.singleFunctor B n
  let SC := DerivedCategory.Plus.singleFunctor C n
  let S₀ := DerivedCategory.Plus.singleFunctor C 0
  let S := shiftFunctor (DerivedCategory.Plus C) n
  let c₀ : H.obj (S₀.obj (G.obj X)) ≅ G.obj X :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (G.obj X)
  let cₙ : Hn.obj (SC.obj (G.obj X)) ≅ G.obj X :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app (G.obj X)
  let σB : ShiftedHom ((DerivedCategory.Plus.singleFunctor B 0).obj X) (SB.obj X) n :=
    ((DerivedCategory.Plus.singleFunctors B).shiftIso n 0 n (add_zero n)).inv.app X
  let σC : ShiftedHom (S₀.obj (G.obj X)) (SC.obj (G.obj X)) n :=
    ((DerivedCategory.Plus.singleFunctors C).shiftIso n 0 n (add_zero n)).inv.app (G.obj X)
  let a := stalkDerivedApp G n X
  have hs := stalkDerivedApp_comm_shift G n X
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hs
  change (stalkDerivedApp G 0 X) ≫ σB.map R = σC ≫ S.map a at hs
  have hh := plus_stalk_shift_homology n (G.obj X)
  change H.map σC ≫ (H.isoShift n).hom.app (SC.obj (G.obj X)) ≫ cₙ.hom = c₀.hom at hh
  have hh' : c₀.inv ≫ H.map σC ≫ (H.isoShift n).hom.app (SC.obj (G.obj X)) = cₙ.inv := by
    apply (cancel_mono cₙ.hom).mp
    calc
      (c₀.inv ≫ H.map σC ≫ (H.isoShift n).hom.app (SC.obj (G.obj X))) ≫ cₙ.hom =
          c₀.inv ≫ (H.map σC ≫ (H.isoShift n).hom.app (SC.obj (G.obj X)) ≫ cₙ.hom) := by
        simp only [Category.assoc]
      _ = cₙ.inv ≫ cₙ.hom := by rw [hh, c₀.inv_hom_id, cₙ.inv_hom_id]
  have hzero : (degreeZeroUnit G).app X = c₀.inv ≫ H.map (stalkDerivedApp G 0 X) := by
    rw [stalkDerivedApp_zero]
    rfl
  rw [shiftedStalkValueIso_inv_eq G n hn X, hzero]
  change (c₀.inv ≫ H.map (stalkDerivedApp G 0 X)) ≫ H.map (σB.map R) ≫
      (H.isoShift n).hom.app (R.obj (SB.obj X)) = cₙ.inv ≫ Hn.map a
  rw [Category.assoc, ← H.map_comp_assoc, hs, H.map_comp, Category.assoc]
  erw [H.isoShift_hom_naturality n a]
  change c₀.inv ≫ H.map σC ≫ (H.isoShift n).hom.app (SC.obj (G.obj X)) ≫ Hn.map a = _
  rw [← Category.assoc (H.map σC), ← Category.assoc c₀.inv, hh']


theorem derivedToExactHomology_stalk (τ : G ⟶ U) (e₀ : rightValue G 0 ≅ G)
    (he₀ : e₀.inv = degreeZeroUnit G) (n : ℤ) (X : B) :
    (derivedToExactHomology G U τ n).app ((DerivedCategory.Plus.singleFunctor B n).obj X) =
      (shiftedStalkValueIso G n ≪≫ e₀).hom.app X ≫ τ.app X ≫
      U.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B n).inv.app X) := by
  let SB := DerivedCategory.Plus.singleFunctor B n
  let SC := DerivedCategory.Plus.singleFunctor C n
  let HB := DerivedCategory.Plus.homologyFunctor B n
  let HC := DerivedCategory.Plus.homologyFunctor C n
  let R := G.rightDerivedFunctorPlus
  let e : HC.obj (R.obj (SB.obj X)) ≅ G.obj X := (shiftedStalkValueIso G n ≪≫ e₀).app X
  let b : HB.obj (SB.obj X) ≅ X := (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).app X
  let c : HC.obj (SC.obj (G.obj X)) ≅ G.obj X :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app (G.obj X)
  let κ : HC.obj (R.obj (SB.obj X)) ⟶ U.obj (HB.obj (SB.obj X)) :=
    (derivedToExactHomology G U τ n).app (SB.obj X)
  let a : SC.obj (G.obj X) ⟶ R.obj (SB.obj X) := stalkDerivedApp G n X
  have he : e.inv = c.inv ≫ HC.map a := by
    change e₀.inv.app X ≫ (shiftedStalkValueIso G n).inv.app X = _
    rw [he₀, stalkDerivedApp_homology_normalization]
    rfl
  have hκ : HC.map a ≫ κ ≫ U.map b.hom = c.hom ≫ τ.app X :=
    derivedToExactHomology_stalk_comp G U τ n X
  change κ = e.hom ≫ τ.app X ≫ U.map b.inv
  apply (cancel_epi e.inv).mp
  apply (cancel_mono (U.map b.hom)).mp
  trans τ.app X
  · rw [Category.assoc, he, Category.assoc, hκ, Iso.inv_hom_id_assoc]
  symm
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← U.map_comp, Iso.inv_hom_id,
    U.map_id, Category.comp_id]

/-- The classical truncation edge followed by evaluation is the canonical
derived map to cohomology after an exact functor. -/
theorem columnEdge_comp_exact {n : ℤ} (T : ColumnTruncation G n)
    (e₀ : rightValue G 0 ≅ G) (he₀ : e₀.inv = degreeZeroUnit G) (τ : G ⟶ U) :
    T.edge G e₀ ≫ whiskerLeft (DerivedCategory.Plus.homologyFunctor B n) τ =
      derivedToExactHomology G U τ n :=
  ColumnTruncation.edge_comp_of_stalk G U T e₀ τ _ (derivedToExactHomology_stalk G U τ e₀ he₀ n)

end ExactComparison
end AdvancedHomologicalAlgebra.GrothendieckEdges

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition

universe u₀ v₀ w₀

section ColumnModels

variable {A : Type u₀} {B : Type u₁} {C : Type u₂}
  [Category.{v₀} A] [Abelian A] [Category.{v₁} B] [Abelian B]
  [Category.{v₂} C] [Abelian C] [HasDerivedCategory.{w₀} A]
  [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) (U : B ⥤ C)
  [F.Additive] [G.Additive] [U.Additive] [U.PreservesHomology]

theorem classicalColumn_on_derivedResolution {X : A} (I : InjectiveResolution X)
    (n : ℕ) (T : ColumnTruncation G (n : ℤ)) (e₀ : rightValue G 0 ≅ G)
    (he₀ : e₀.inv = degreeZeroUnit G) (τ : G ⟶ U) :
    let K := F.mapCochainComplexPlus.obj (resolutionPlus I)
    let HC := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
    let HB := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
    (classicalColumn F G T e₀).app X ≫ τ.app ((rightValue F n).obj X) ≫
      U.map (HB.map (rightDerivedResolutionIso F I).hom) =
    HC.map (rightDerivedResolutionIso (F ⋙ G) I).hom ≫
      HC.map (DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K)) ≫
        (exactComplexHomologyFactors U (n : ℤ)).hom.app K := by
  intro K HC HB
  let Y := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let γ := (comparisonValue F G).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let ι := (rightDerivedResolutionIso F I).hom
  let κ := derivedToExactHomology G U τ (n : ℤ)
  have hab := congrArg (fun t => t.app Y) (columnEdge_comp_exact G U T e₀ he₀ τ)
  have hn := κ.naturality ι
  change HC.map (G.rightDerivedFunctorPlus.map ι) ≫ κ.app (DerivedCategory.Plus.Q.obj K) =
    κ.app Y ≫ U.map (HB.map ι) at hn
  change (HC.map γ ≫ (T.edge G e₀).app Y) ≫ τ.app (HB.obj Y) ≫ U.map (HB.map ι) = _
  rw [Category.assoc, ← Category.assoc ((T.edge G e₀).app Y)]
  change HC.map γ ≫ ((T.edge G e₀ ≫ whiskerLeft HB τ).app Y) ≫ U.map (HB.map ι) = _
  rw [hab]
  change HC.map γ ≫ κ.app Y ≫ U.map (HB.map ι) = _
  rw [← hn, ← HC.map_comp_assoc, composition_on_resolution F G I,
    HC.map_comp, Category.assoc]
  erw [derivedToExactHomology_fac G U τ (n : ℤ) K]


open HomologicalComplex

/-- The cohomology comparison for an exact functor commutes with the
quotient map from cycles. -/
@[reassoc]
theorem mapHomologyIso_homologyπ (S : ShortComplex B) :
    (S.map U).homologyπ ≫ (S.mapHomologyIso U).hom =
      (S.mapCyclesIso U).hom ≫ U.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq U, h.mapCyclesIso_eq U]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    (h.map U).homologyπ_comp_homologyIso_hom_assoc]
  have he : (h.map U).π = U.map h.π := rfl
  rw [he, ← U.map_comp, ← U.map_comp, h.π_comp_homologyIso_inv]

set_option maxHeartbeats 1000000 in
/-- Evaluation after exact coefficients commutes with the extension-by-zero
comparison on homology. -/
@[reassoc]
theorem exactHomologyIso_extend
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (K : HomologicalComplex B c) {i : ι} {i' : ι'} (hi : e.f i = i') :
    (((K.extend e).sc i').mapHomologyIso U).hom ≫ U.map (K.extendHomologyIso e hi).hom =
      homologyMap (mapExtendIso U e K).hom i' ≫
        (((U.mapHomologicalComplex c).obj K).extendHomologyIso e hi).hom ≫
        ((K.sc i).mapHomologyIso U).hom := by
  let L := (U.mapHomologicalComplex c).obj K
  let M := (U.mapHomologicalComplex c').obj (K.extend e)
  let f := (mapExtendIso U e K).hom
  let a := ((K.extend e).sc i').mapCyclesIso U
  let b := (K.sc i).mapCyclesIso U
  have hc :
      a.hom ≫ U.map (K.extendCyclesIso e hi).hom =
        cyclesMap f i' ≫ (L.extendCyclesIso e hi).hom ≫ b.hom := by
    apply (cancel_mono (U.map (K.iCycles i))).mp
    change (a.hom ≫ U.map (K.extendCyclesIso e hi).hom) ≫ U.map (K.iCycles i) =
      (cyclesMap f i' ≫ (L.extendCyclesIso e hi).hom ≫ b.hom) ≫ U.map (K.iCycles i)
    simp only [Category.assoc, ← U.map_comp, extendCyclesIso_hom_iCycles]
    change a.hom ≫ U.map ((K.extend e).iCycles i' ≫ (K.extendXIso e hi).hom) = _
    rw [U.map_comp, ← Category.assoc a.hom]
    have ha : a.hom ≫ U.map ((K.extend e).iCycles i') = M.iCycles i' :=
      ShortComplex.mapCyclesIso_hom_iCycles _ U
    have hb : b.hom ≫ U.map (K.iCycles i) = L.iCycles i :=
      ShortComplex.mapCyclesIso_hom_iCycles _ U
    rw [ha, hb, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc]
    rw [mapExtendIso_hom_f U e K hi, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (M.homologyπ i')).mp
  change M.homologyπ i' ≫ (((K.extend e).sc i').mapHomologyIso U).hom ≫
      U.map (K.extendHomologyIso e hi).hom =
    M.homologyπ i' ≫ homologyMap f i' ≫ (L.extendHomologyIso e hi).hom ≫
      ((K.sc i).mapHomologyIso U).hom
  have hπ₁ : M.homologyπ i' ≫ (((K.extend e).sc i').mapHomologyIso U).hom =
      a.hom ≫ U.map ((K.extend e).homologyπ i') :=
    mapHomologyIso_homologyπ U ((K.extend e).sc i')
  have hπ₂ : L.homologyπ i ≫ ((K.sc i).mapHomologyIso U).hom =
      b.hom ≫ U.map (K.homologyπ i) :=
    mapHomologyIso_homologyπ U (K.sc i)
  rw [reassoc_of% hπ₁, ← U.map_comp, homologyπ_extendHomologyIso_hom,
    U.map_comp, homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom_assoc,
    hπ₂, ← reassoc_of% hc]



set_option maxHeartbeats 1000000 in
/-- The column edge, followed by evaluation, is the map on cohomology of
ordinary injective resolutions induced by the termwise evaluation. -/
theorem classicalColumn_on_resolutions {X : A} (I : InjectiveResolution X)
    (n : ℕ) (T : ColumnTruncation G (n : ℤ)) (e₀ : rightValue G 0 ≅ G)
    (he₀ : e₀.inv = degreeZeroUnit G) (τ : G ⟶ U) :
    let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    (classicalColumn F G T e₀).app X ≫ τ.app ((rightValue F n).obj X) ≫
      U.map (rightValueResolutionIso F n I).hom =
    (rightValueResolutionIso (F ⋙ G) n I).hom ≫
      homologyMap ((τ.mapHomologicalComplex (.up ℕ)).app K) n ≫
        ((K.sc n).mapHomologyIso U).hom := by
  intro K
  let e := resolutionEmbedding
  let K' := F.mapCochainComplexPlus.obj (resolutionPlus I)
  let HC := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let HB := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let Hc := HomologicalComplex.homologyFunctor C (.up ℤ) (n : ℤ)
  let Hb := HomologicalComplex.homologyFunctor B (.up ℤ) (n : ℤ)
  let f := τ.mapCochainComplexPlus.app K'
  let a := (mapExtendIso F e I.cocomplex).hom
  let a₀ := (mapExtendIso (F ⋙ G) e I.cocomplex).hom
  let a₁ := (mapExtendIso (F ⋙ U) e I.cocomplex).hom
  let g := ((τ.mapHomologicalComplex (.up ℕ)).app K)
  let ℓ := (rightDerivedResolutionIso F I).hom
  let r := (rightDerivedResolutionIso (F ⋙ G) I).hom
  let iC := DerivedCategory.homologyFunctorFactors C (n : ℤ)
  let iB := DerivedCategory.homologyFunctorFactors B (n : ℤ)
  let pB := K.extendHomologyIso e (show e.f n = (n : ℤ) from rfl)
  let pC := ((G.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso e
    (show e.f n = (n : ℤ) from rfl)
  let pU := ((U.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso e
    (show e.f n = (n : ℤ) from rfl)
  let c := exactComplexHomologyIso U (n : ℤ)
  let d := (K.sc n).mapHomologyIso U
  let Q := DerivedCategory.Plus.Q (C := C)
  have hcol := classicalColumn_on_derivedResolution F G U I n T e₀ he₀ τ
  change (classicalColumn F G T e₀).app X ≫ τ.app ((rightValue F n).obj X) ≫ U.map (HB.map ℓ) =
      HC.map r ≫ HC.map (Q.map f) ≫ (exactComplexHomologyFactors U (n : ℤ)).hom.app K' at hcol
  have hfac : (exactComplexHomologyFactors U (n : ℤ)).hom.app K' =
      iC.hom.app (U.mapCochainComplexPlus.obj K').obj ≫
        c.hom.app K'.obj ≫ U.map (iB.inv.app K'.obj) := by
    simp only [exactComplexHomologyFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      associator_hom_app, associator_inv_app, Category.id_comp,
      Functor.mapCochainComplexPlusCompι_hom_app]
    erw [Hc.map_id, Category.id_comp, Category.comp_id]
    rfl
  have hf : HC.map (Q.map f) ≫ iC.hom.app (U.mapCochainComplexPlus.obj K').obj =
      iC.hom.app (G.mapCochainComplexPlus.obj K').obj ≫ Hc.map f.hom :=
    iC.hom.naturality f.hom
  have ha : (U.mapHomologicalComplex (.up ℤ)).map a ≫ (mapExtendIso U e K).hom = a₁ :=
    (mapExtendIso_composite F U I.cocomplex).symm
  have ht : f.hom ≫ a₁ = a₀ ≫ extendMap g e :=
    mapExtendIso_natTrans (whiskerLeft F τ) e I.cocomplex
  have hc : Hc.map ((U.mapHomologicalComplex (.up ℤ)).map a) ≫ c.hom.app (K.extend e) =
      c.hom.app K'.obj ≫ U.map (Hb.map a) :=
    c.hom.naturality a
  have hp : c.hom.app (K.extend e) ≫ U.map pB.hom =
      Hc.map (mapExtendIso U e K).hom ≫ pU.hom ≫ d.hom :=
    exactHomologyIso_extend U e K (show e.f n = (n : ℤ) from rfl)
  have hg : Hc.map (extendMap g e) ≫ pU.hom = pC.hom ≫ homologyMap g n :=
    extendHomologyIso_hom_naturality g e (show e.f n = (n : ℤ) from rfl)
  change (classicalColumn F G T e₀).app X ≫ τ.app ((rightValue F n).obj X) ≫
      U.map (HB.map ℓ ≫ iB.hom.app K'.obj ≫ Hb.map a ≫ pB.hom) =
      (HC.map r ≫ iC.hom.app (G.mapCochainComplexPlus.obj K').obj ≫ Hc.map a₀ ≫ pC.hom) ≫
        homologyMap g n ≫ d.hom
  rw [U.map_comp, U.map_comp, U.map_comp, reassoc_of% hcol, hfac]
  simp only [Category.assoc]
  erw [← U.map_comp_assoc, Iso.inv_hom_id_app, U.map_id, Category.id_comp,
    reassoc_of% hf, ← reassoc_of% hc, hp]
  rw [← Hc.map_comp_assoc ((U.mapHomologicalComplex (.up ℤ)).map a) (mapExtendIso U e K).hom,
    ha, ← Hc.map_comp_assoc, ht, Hc.map_comp, Category.assoc]
  rw [reassoc_of% hg]

end ColumnModels
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes

universe u v w t
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
  {ι : Type t} {c : ComplexShape ι}

/-- The categorical homology comparison along restriction of scalars agrees
with the identification of the two concrete cycle quotients. -/
@[reassoc]
theorem restrictMapHomologyIso_compare
    (f : R →+* S) (C : HomologicalComplex (ModuleCat.{w} S) c) (n : ι) :
    let F := ModuleCat.restrictScalars f
    let D := (F.mapHomologicalComplex c).obj C
    ((C.sc n).mapHomologyIso F).hom ≫
      F.map (moduleQuotientHomologyIso C n).hom ≫ (restrictQuotientHomology f C n).hom =
        (moduleQuotientHomologyIso D n).hom := by
  dsimp only
  let F := ModuleCat.restrictScalars f
  let D := (F.mapHomologicalComplex c).obj C
  let H := (C.sc n).moduleCatLeftHomologyData
  let J := H.map F
  let K := (D.sc n).moduleCatLeftHomologyData
  have hh : H.π ≫ H.homologyIso.inv ≫ (moduleQuotientHomologyIso C n).hom =
      ModuleCat.ofHom (homologyClass C n) := by
    rw [H.π_comp_homologyIso_inv_assoc, show (C.sc n).homologyπ ≫
      (moduleQuotientHomologyIso C n).hom = H.cyclesIso.hom ≫
        ModuleCat.ofHom (homologyClass C n) from moduleQuotientHomologyIso_π C n,
      Iso.inv_hom_id_assoc]
  change ((C.sc n).mapHomologyIso F).hom ≫ F.map (moduleQuotientHomologyIso C n).hom ≫
    (restrictQuotientHomology f C n).hom = (moduleQuotientHomologyIso D n).hom
  rw [H.mapHomologyIso_eq F, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← F.map_comp_assoc]
  rw [← cancel_epi (D.homologyπ n), ← Category.assoc, moduleQuotientHomologyIso_π]
  change ((C.sc n).map F).homologyπ ≫ J.homologyIso.hom ≫
      F.map (H.homologyIso.inv ≫ (moduleQuotientHomologyIso C n).hom) ≫
      (restrictQuotientHomology f C n).hom =
    K.cyclesIso.hom ≫ ModuleCat.ofHom (homologyClass D n)
  rw [J.homologyπ_comp_homologyIso_hom_assoc]
  have hπ : J.π = F.map H.π := rfl
  rw [hπ, ← F.map_comp_assoc, hh]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hJ : J.cyclesIso.hom ≫ J.i = (D.sc n).iCycles :=
    J.cyclesIso_hom_comp_i
  have hK : K.cyclesIso.hom ≫ K.i = (D.sc n).iCycles :=
    K.cyclesIso_hom_comp_i
  have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hJ.trans hK.symm)) x
  change ((J.cyclesIso.hom).hom x).val = ((K.cyclesIso.hom).hom x).val at hx
  exact congrArg (homologyClass D n) (Subtype.ext hx)

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory Shared.Lie
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Comparison

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 750000
set_option hygiene false
set_option quotPrecheck false
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g) {M : ModuleCat.{max u v w} (U k g)}
  (I : CategoryTheory.InjectiveResolution M)

local notation "F" => idealInvariants.{u,v,w} h
local notation "G" => quotientInvariants.{u,v,w} h
local notation "W" => underlying k (g ⧸ h)
local notation "c" => ComplexShape.up ℕ

private theorem restrictionInvariantModelFactorization :
    (((compositeInvariantsEvaluationIso.{u,v,w} h).hom.mapHomologicalComplex c).app I.cocomplex) ≫
      restrictionInvariantComplexMap h I =
    ((lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation.mapHomologicalComplex c).app
      (((F).mapHomologicalComplex c).obj I.cocomplex) ≫
      (idealToLieInvariantsComplex h I.cocomplex).hom := by
  let e := compositeInvariantsEvaluationIso.{u,v,w} h
  have he : (e.hom.mapHomologicalComplex c).app I.cocomplex ≫
      (e.inv.mapHomologicalComplex c).app I.cocomplex = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro n
    exact e.hom_inv_id_app (I.cocomplex.X n)
  change (e.hom.mapHomologicalComplex c).app I.cocomplex ≫
      (e.inv.mapHomologicalComplex c).app I.cocomplex ≫ _ = _
  rw [← Category.assoc, he, Category.id_comp]
  rfl

private theorem restrictionInvariantCohomologyFactorization (n : ℕ) :
    (lieResolutionCohomologyEquiv (moduleInjectiveResolution I) n).toModuleIso.hom ≫
      (quotientHomology c n).map (restrictionCochain.{u,v,w} h M) =
    (quotientHomology c n).map (restrictionInvariantComplexMap h I) ≫
      (lieResolutionCohomologyEquiv (moduleInjectiveResolution (restrictIdealResolution h I)) n).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (restrictionInvariantComplexMap_cohomology h I n z).symm

variable [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

/-- The CE restriction square on the categorical injective model of the
derived invariant functors, with the actual quotient evaluation. -/
theorem restrictionCE_on_models (n : ℕ) :
    (rightValueNatIso (compositeInvariantsEvaluationIso.{u,v,w} h) n ≪≫
      lieCohomologyIso.{u,v,w} k g n).hom.app M ≫
        (quotientHomology c n).map (restrictionCochain.{u,v,w} h M) =
    (rightValueResolutionIso (F ⋙ G) n I).hom ≫
      HomologicalComplex.homologyMap
        (((lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation.mapHomologicalComplex c).app
          (((F).mapHomologicalComplex c).obj I.cocomplex)) n ≫
      (((((F).mapHomologicalComplex c).obj I.cocomplex).sc n).mapHomologyIso W).hom ≫
      (W).map (rightValueResolutionIso F n I).inv ≫ (idealCohomologyIso h n).hom.app M := by
  let e := compositeInvariantsEvaluationIso.{u,v,w} h
  let C := ((F).mapHomologicalComplex c).obj I.cocomplex
  let t := ((lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation.mapHomologicalComplex c).app C
  let u₂ := (idealToLieInvariantsComplex h I.cocomplex).hom
  let v₂ := restrictionInvariantComplexMap h I
  let ι₂ := (lieResolutionCohomologyEquiv
    (moduleInjectiveResolution (restrictIdealResolution h I)) n).toModuleIso.hom
  let eHC := (e.hom.mapHomologicalComplex c).app I.cocomplex
  let H := (quotientHomology c n :
    CochainComplex (ModuleCat.{max u v w} k) ℕ ⥤ ModuleCat.{max u v w} k)
  have h₁ := lieCohomologyIso_hom_app I n
  have h₂ : (idealCohomologyIso h n).hom.app M = (idealCohomologyIsoAt h I n).hom :=
    congrArg Iso.hom (idealCohomologyIso_app h I n)
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, h₂]
  simp only [lieCohomologyIsoAt, Iso.trans_hom, Category.assoc]
  rw [rightValueResolutionIso_natIso_assoc e n I]
  have ht : (W).map (rightValueResolutionIso F n I).inv ≫ (idealCohomologyIsoAt h I n).hom =
      (W).map (moduleQuotientHomologyIso C n).hom ≫
        (restrictQuotientHomology (algebraMap k (U k (g ⧸ h))) C n).hom ≫ H.map u₂ ≫ ι₂ := by
    simp only [idealCohomologyIsoAt, idealResolutionValueIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
    rfl
  rw [ht, restrictMapHomologyIso_compare_assoc]
  rw [moduleQuotientHomologyIso_natural_assoc eHC n, moduleQuotientHomologyIso_natural_assoc t n]
  erw [restrictionInvariantCohomologyFactorization h I n]
  change _ ≫ _ ≫ H.map eHC ≫ H.map v₂ ≫ ι₂ = _ ≫ _ ≫ H.map t ≫ H.map u₂ ≫ ι₂
  rw [← H.map_comp_assoc, ← H.map_comp_assoc, restrictionInvariantModelFactorization h I]
  rfl


/-- The Grothendieck column edge is restriction of CE classes, followed
through the original inclusion of quotient invariants. -/
theorem restriction_edge_comparison
    (P : GrothendieckSpectralSequence.Package F G)
    (O : GrothendieckEdges.ObjectEdges F G P)
    (M : ModuleCat.{max u v w} (U k g)) (n : ℕ) :
    (rightValueNatIso (compositeInvariantsEvaluationIso.{u,v,w} h) n ≪≫
      lieCohomologyIso.{u,v,w} k g n).hom.app M ≫
        (quotientHomology c n).map (restrictionCochain.{u,v,w} h M) =
    (GrothendieckEdges.classicalColumn F G (O.truncation n) O.degreeZero).app M ≫
      (lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation.app ((rightValue F n).obj M) ≫
        (idealCohomologyIso h n).hom.app M := by
  let I := CategoryTheory.injectiveResolution M
  let τ := (lieInvariantInclusion.{u,v,w} k (g ⧸ h)).evaluation
  have hf := restrictionCE_on_models h I n
  have hc := classicalColumn_on_resolutions F G W I n (O.truncation n)
    O.degreeZero O.degreeZero_hom τ
  rw [hf, ← reassoc_of% hc]
  simp only [← (W).map_comp_assoc, Iso.hom_inv_id, (W).map_id, Category.id_comp]
  rfl

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
open HomologicalComplex
open P103.Specs.Ch10.Horseshoe

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe r w

variable {R : Type r} [Ring R]

def categoricalInjectiveResolution {X : ModuleCat.{max r w} R}
    (I : P103.Specs.Ch10.InjectiveResolutions.Resolution R X) :
    CategoryTheory.InjectiveResolution X where
  cocomplex := I.complex
  injective n := (Module.injective_iff_injective_object R (I.complex.X n)).mp
    (I.injectiveTerm n)
  ι := (CochainComplex.fromSingle₀Equiv I.complex X).symm
    ⟨ModuleCat.ofHom I.η, by
      apply ModuleCat.hom_ext
      ext x
      exact I.exact_zero.apply_apply_eq_zero x⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · exact ⟨ModuleCat.shortComplex_exact _ I.exact_zero,
          (ModuleCat.mono_iff_injective _).mpr I.injective_η⟩
      · rfl
      · rfl
      · exact I.complex.shape _ _ (by decide)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      exact ModuleCat.shortComplex_exact _ (I.exact_succ n)⟩

@[simp] theorem categoricalInjectiveResolution_cocomplex {X : ModuleCat.{max r w} R}
    (I : P103.Specs.Ch10.InjectiveResolutions.Resolution R X) :
    (categoricalInjectiveResolution I).cocomplex = I.complex := rfl

@[simp] theorem categoricalInjectiveResolution_ι_f_zero {X : ModuleCat.{max r w} R}
    (I : P103.Specs.Ch10.InjectiveResolutions.Resolution R X) :
    (categoricalInjectiveResolution I).ι.f 0 = ModuleCat.ofHom I.η :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

structure InjectiveHorseshoe (S : ShortComplex (ModuleCat.{max r w} R)) where
  left : CategoryTheory.InjectiveResolution S.X₁
  middle : CategoryTheory.InjectiveResolution S.X₂
  right : CategoryTheory.InjectiveResolution S.X₃
  inclusion : CategoryTheory.InjectiveResolution.Hom left middle S.f
  projection : CategoryTheory.InjectiveResolution.Hom middle right S.g
  zero : inclusion.hom ≫ projection.hom = 0
  splitting (n : ℕ) :
    (ShortComplex.mk (inclusion.hom.f n) (projection.hom.f n)
      (by simpa using congrArg (fun f => f.f n) zero)).Splitting

namespace InjectiveHorseshoe

variable {S : ShortComplex (ModuleCat.{max r w} R)} (H : InjectiveHorseshoe S)

abbrev shortComplex : ShortComplex (CochainComplex (ModuleCat.{max r w} R) ℕ) :=
  ShortComplex.mk H.inclusion.hom H.projection.hom H.zero

theorem shortExact : H.shortComplex.ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact H.shortComplex).mpr
    fun n => (H.splitting n).shortExact

theorem map_shortExact {D : Type*} [Category D] [Abelian D]
    (F : ModuleCat.{max r w} R ⥤ D) [F.Additive] :
    (H.shortComplex.map (F.mapHomologicalComplex (.up ℕ))).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
    fun n => ((H.splitting n).map F).shortExact

private def termEquiv (n : ℕ) :
    H.middle.cocomplex.X n ≃ₗ[R] (H.left.cocomplex.X n × H.right.cocomplex.X n) :=
  let s := H.splitting n
  { (s.r.hom.prod (H.projection.hom.f n).hom) with
    invFun := (H.inclusion.hom.f n).hom.coprod s.s.hom
    left_inv := fun x => DFunLike.congr_fun (congrArg ModuleCat.Hom.hom s.id) x
    right_inv := fun y => by
      have hi := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom s.f_r) y.1
      have hp := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom s.s_g) y.2
      have hsr := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom s.s_r) y.2
      have hz := congrArg (fun f : H.left.cocomplex ⟶ H.right.cocomplex => (f.f n).hom y.1) H.zero
      apply Prod.ext
      · change s.r.hom ((H.inclusion.hom.f n).hom y.1 + s.s.hom y.2) = y.1
        rw [_root_.map_add, show s.r.hom ((H.inclusion.hom.f n).hom y.1) = y.1 from hi,
          show s.r.hom (s.s.hom y.2) = 0 from hsr, add_zero]
      · change (H.projection.hom.f n).hom ((H.inclusion.hom.f n).hom y.1 + s.s.hom y.2) = y.2
        rw [_root_.map_add,
          show (H.projection.hom.f n).hom ((H.inclusion.hom.f n).hom y.1) = 0 from hz,
          show (H.projection.hom.f n).hom (s.s.hom y.2) = y.2 from hp, zero_add] }

def moduleData : InjectiveData S.f.hom S.g.hom
    (moduleInjectiveResolution H.left) (moduleInjectiveResolution H.right) where
  middle := moduleInjectiveResolution H.middle
  term := H.termEquiv
  inclusion := H.inclusion.hom
  projection := H.projection.hom
  inclusion_apply n x := Prod.ext
    (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (H.splitting n).f_r) x)
    (congrArg (fun f : H.left.cocomplex ⟶ H.right.cocomplex => (f.f n).hom x) H.zero)
  projection_apply _ _ := rfl
  augmentation_inclusion := by
    change (H.inclusion.hom.f 0).hom.comp (H.left.ι.f 0).hom =
      (H.middle.ι.f 0).hom.comp S.f.hom
    simpa only [CochainComplex.single₀_map_f_zero, ModuleCat.hom_comp] using
      congrArg ModuleCat.Hom.hom H.inclusion.ι_f_zero_comp_hom_f_zero
  augmentation_projection := by
    change (H.projection.hom.f 0).hom.comp (H.middle.ι.f 0).hom =
      (H.right.ι.f 0).hom.comp S.g.hom
    simpa only [CochainComplex.single₀_map_f_zero, ModuleCat.hom_comp] using
      congrArg ModuleCat.Hom.hom H.projection.ι_f_zero_comp_hom_f_zero

end InjectiveHorseshoe

def injectiveHorseshoe {S : ShortComplex (ModuleCat.{max r w} R)} (hS : S.ShortExact) :
    InjectiveHorseshoe S := by
  let L : CategoryTheory.InjectiveResolution S.X₁ := CategoryTheory.injectiveResolution _
  let N : CategoryTheory.InjectiveResolution S.X₃ := CategoryTheory.injectiveResolution _
  let H := (P103.Ch10.Horseshoe.injective_horseshoe R S.X₁ S.X₂ S.X₃ S.f.hom S.g.hom
    hS.moduleCat_injective_f ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_surjective_g (moduleInjectiveResolution L) (moduleInjectiveResolution N)).some
  let M := categoricalInjectiveResolution H.middle
  refine
    { left := L
      middle := M
      right := N
      inclusion := ⟨H.inclusion, ?_⟩
      projection := ⟨H.projection, ?_⟩
      zero := ?_
      splitting := ?_ }
  · rw [CochainComplex.single₀_map_f_zero, categoricalInjectiveResolution_ι_f_zero]
    exact ModuleCat.hom_ext H.augmentation_inclusion
  · rw [CochainComplex.single₀_map_f_zero, categoricalInjectiveResolution_ι_f_zero]
    exact ModuleCat.hom_ext H.augmentation_projection
  · apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext x
    exact (H.projection_apply n _).trans (congrArg Prod.snd (H.inclusion_apply n x))
  · intro n
    let e := H.term n
    let r := ModuleCat.ofHom ((LinearMap.fst R _ _).comp e.toLinearMap)
    let s := ModuleCat.ofHom (e.symm.toLinearMap.comp (LinearMap.inr R _ _))
    refine ⟨r, s, ?_, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      ext x
      exact congrArg Prod.fst (H.inclusion_apply n x)
    · apply ModuleCat.hom_ext
      ext x
      change (H.projection.f n).hom (e.symm (0, x)) = x
      rw [H.projection_apply, e.apply_symm_apply]
    · apply ModuleCat.hom_ext
      ext x
      apply e.injective
      change e ((H.inclusion.f n).hom (e x).1 + e.symm (0, (H.projection.f n).hom x)) = e x
      rw [_root_.map_add, H.inclusion_apply, e.apply_symm_apply, H.projection_apply]
      exact Prod.ext (add_zero _) (zero_add _)

end AdvancedHomologicalAlgebra.LieHochschildSerre

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Shared.Lie
open P103.Specs.Ch10.HomologySequence

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

private theorem CochainTheory.map_apply (D : CochainTheory.{u,v,w} k g)
    {M N : ModuleCat.{max u v w} (U k g)} (a : M ⟶ N) (n : ℕ)
    (t : CE.W k g n →ₗ[k] (underlying k g).obj M) :
    ((D.functor.map a).f n).hom t = ((underlying k g).map a).hom.comp t := by
  change (show CE.W k g n →ₗ[k] (underlying k g).obj N from ((D.functor.map a).f n).hom t) =
    ((underlying k g).map a).hom.comp t
  apply LinearMap.ext
  intro x
  change ((underlying k g).map a).hom
    (t (exteriorPower.map n (LinearMap.id (R := k)) x)) =
    ((underlying k g).map a).hom (t x)
  rw [exteriorPower.map_id, LinearMap.id_apply]

private theorem CochainTheory.degreewiseExact (D : CochainTheory.{u,v,w} k g)
    {S : ShortComplex (ModuleCat.{max u v w} (U k g))} (hS : S.ShortExact) :
    DegreewiseExact (D.functor.map S.f) (D.functor.map S.g) := by
  intro n
  let T := S.map (underlying k g)
  have hT : T.ShortExact := hS.map_of_exact (underlying k g)
  have hinj : Function.Injective T.f.hom := hT.moduleCat_injective_f
  have he : Function.Exact T.f.hom T.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact
  have hsurj : Function.Surjective T.g.hom := hT.moduleCat_surjective_g
  obtain ⟨hinj', he'⟩ := P103.HomTensorExactness.homCovariant k T.X₁ T.X₂ T.X₃
    (CE.W k g n) T.f.hom T.g.hom hinj he
  refine ⟨?_, ?_, ?_⟩
  · intro f f' eq
    apply hinj'
    exact (D.map_apply S.f n f).symm.trans (eq.trans (D.map_apply S.f n f'))
  · intro f
    change CE.W k g n →ₗ[k] T.X₂ at f
    constructor
    · intro hf
      have hf' : P103.HomTensorExactness.post T.g.hom f = 0 :=
        (D.map_apply S.g n f).symm.trans hf
      obtain ⟨a, ha⟩ := (he' f).mp hf'
      exact ⟨a, (D.map_apply S.f n a).trans ha⟩
    · rintro ⟨a, ha⟩
      have hf' : P103.HomTensorExactness.post T.g.hom f = 0 :=
        (he' f).mpr ⟨a, (D.map_apply S.f n a).symm.trans ha⟩
      exact (D.map_apply S.g n f).trans hf' 
  · intro f
    obtain ⟨a, ha⟩ := Module.projective_lifting_property T.g.hom f hsurj
    exact ⟨a, (D.map_apply S.g n a).trans ha⟩

private theorem CochainTheory.restrict_degreewiseExact (h : LieIdeal k g)
    (D : CochainTheory.{u,v,w} k h)
    {S : ShortComplex (ModuleCat.{max u v w} (U k g))} (hS : S.ShortExact) :
    DegreewiseExact ((restrictIdeal.{u,v,w} h ⋙ D.functor).map S.f)
      ((restrictIdeal.{u,v,w} h ⋙ D.functor).map S.g) :=
  D.degreewiseExact (hS.map_of_exact (restrictIdeal.{u,v,w} h))

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre
local notation "stalk" => GrothendieckEdges.stalkComplex


local instance (C : Type*) [Category* C] [Abelian C] : (stalk C).PreservesZeroMorphisms where
  map_zero X Y := (CochainComplex.plus C).ι.map_injective
    ((CochainComplex.singleFunctor C 0).map_zero X Y)

local instance {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] : F.mapCochainComplexPlus.PreservesZeroMorphisms where
  map_zero K L := (CochainComplex.plus B).ι.map_injective
    ((F.mapHomologicalComplex (.up ℤ)).map_zero K.obj L.obj)

section ResolutionBoundary

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

private abbrev underlyingRow {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex (CochainComplex.Plus C)) :=
  S.map (CochainComplex.Plus.ι C)

/-- The ordinary short exact sequence boundary, considered in the bounded-below category. -/
private def plusSESδ (S : ShortComplex (CochainComplex.Plus A))
    (hS : (underlyingRow S).ShortExact) :
    ShiftedHom (DerivedCategory.Plus.Q.obj S.X₃) (DerivedCategory.Plus.Q.obj S.X₁) (1 : ℤ) :=
  DerivedCategory.TStructure.t.plus.homMk
    (triangleOfSESδ hS ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Plus.Q.obj S.X₁))

@[simp]
private lemma plusSESδ_map_ι (S : ShortComplex (CochainComplex.Plus A))
    (hS : (underlyingRow S).ShortExact) :
    (plusSESδ S hS).map DerivedCategory.Plus.ι = triangleOfSESδ hS := by
  change (triangleOfSESδ hS ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Plus.Q.obj S.X₁)) ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app _ = _
  erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

@[reassoc]
private lemma plusSESδ_natural {S T : ShortComplex (CochainComplex.Plus A)}
    (hS : (underlyingRow S).ShortExact) (hT : (underlyingRow T).ShortExact)
    (f : S ⟶ T) :
    plusSESδ S hS ≫ (DerivedCategory.Plus.Q.map f.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.Q.map f.τ₃ ≫ plusSESδ T hT := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [← cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
    (DerivedCategory.Plus.Q.obj T.X₁))]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]
  rw [← Category.assoc]
  change (plusSESδ S hS).map DerivedCategory.Plus.ι ≫ _ =
    _ ≫ (plusSESδ T hT).map DerivedCategory.Plus.ι
  simp only [plusSESδ_map_ι]
  exact triangleOfSESδ_naturality hS hT
    ((CochainComplex.Plus.ι A).mapShortComplex.map f)

private def plusCone {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    CochainComplex.Plus A := by
  refine ⟨CochainComplex.mappingCone f.hom, ?_⟩
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  exact ⟨min (a - 1) b,
    CochainComplex.isStrictlyGE_mappingCone f.hom a b _
      (lt_of_le_of_lt (min_le_left _ _) (by omega)) (min_le_right _ _)⟩

private def plusConeDesc (S : ShortComplex (CochainComplex.Plus A)) :
    plusCone S.f ⟶ S.X₃ :=
  (CochainComplex.plus A).homMk (CochainComplex.mappingCone.descShortComplex (underlyingRow S))

private def plusConeδ {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    ShiftedHom (plusCone f) K (1 : ℤ) :=
  (CochainComplex.plus A).homMk
    ((CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
      ((CochainComplex.Plus.ι A).commShiftIso (1 : ℤ)).inv.app K)

@[simp]
private lemma plusConeδ_map_ι {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (plusConeδ f).map (CochainComplex.Plus.ι A) =
      (CochainComplex.mappingCone.triangle f.hom).mor₃ := by
  simp [plusConeδ, ShiftedHom.map, Category.comp_id]

@[reassoc]
private lemma plusConeDesc_δ (S : ShortComplex (CochainComplex.Plus A))
    (hS : (underlyingRow S).ShortExact) :
    DerivedCategory.Plus.Q.map (plusConeDesc S) ≫ plusSESδ S hS =
      (plusConeδ S.f).map DerivedCategory.Plus.Q := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [← cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
    (DerivedCategory.Plus.Q.obj S.X₁))]
  simp only [Functor.map_comp, Category.assoc]
  change _ ≫ (plusSESδ S hS).map DerivedCategory.Plus.ι =
    ((plusConeδ S.f).map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι
  rw [plusSESδ_map_ι, ← ShiftedHom.comp_map]
  change DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex (underlyingRow S)) ≫
      triangleOfSESδ hS = _
  rw [DerivedCategory.descShortComplex_triangleOfSESδ]
  have h := ShiftedHom.map_naturality (plusConeδ S.f)
    (DerivedCategory.Plus.QCompιIso A).hom
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  simp only [DerivedCategory.Plus.QCompιIso_hom_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  calc
    _ = ((plusConeδ S.f).map (CochainComplex.Plus.ι A)).map DerivedCategory.Q := by
      rw [plusConeδ_map_ι]
      rfl
    _ = _ := (ShiftedHom.comp_map ..).symm.trans h.symm

private def mapPlusConeIso (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    F.mapCochainComplexPlus.obj (plusCone f) ≅ plusCone (F.mapCochainComplexPlus.map f) :=
  (CochainComplex.plus B).fullyFaithfulι.preimageIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f.hom F)



@[reassoc]
private lemma mapPlusConeIso_desc (F : A ⥤ B) [F.Additive]
    (S : ShortComplex (CochainComplex.Plus A)) :
    (mapPlusConeIso F S.f).hom ≫ plusConeDesc (S.map F.mapCochainComplexPlus) =
      F.mapCochainComplexPlus.map (plusConeDesc S) := by
  apply (CochainComplex.plus B).ι.map_injective
  exact CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex
    F (underlyingRow S)

@[reassoc]
private lemma mapPlusConeδ (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (plusConeδ f).map F.mapCochainComplexPlus =
      (mapPlusConeIso F f).hom ≫ plusConeδ (F.mapCochainComplexPlus.map f) := by
  apply (CochainComplex.plus B).ι.map_injective
  rw [← cancel_mono (((CochainComplex.Plus.ι B).commShiftIso (1 : ℤ)).hom.app
    (F.mapCochainComplexPlus.obj K))]
  simp only [Functor.map_comp, Category.assoc]
  change ((plusConeδ f).map F.mapCochainComplexPlus).map (CochainComplex.Plus.ι B) =
    _ ≫ (plusConeδ (F.mapCochainComplexPlus.map f)).map (CochainComplex.Plus.ι B)
  rw [← ShiftedHom.comp_map, plusConeδ_map_ι]
  have h := ShiftedHom.map_naturality (plusConeδ f) F.mapCochainComplexPlusCompι.hom
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  simp only [Functor.mapCochainComplexPlusCompι_hom_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  calc
    _ = ((plusConeδ f).map (CochainComplex.Plus.ι A)).map
        (F.mapHomologicalComplex (.up ℤ)) :=
      h.trans (ShiftedHom.comp_map ..)
    _ = _ := by
      rw [plusConeδ_map_ι]
      exact CochainComplex.mappingCone.map_δ f.hom F

private lemma mapPlusSESδ (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
    (S : ShortComplex (CochainComplex.Plus A))
    (hS : (underlyingRow S).ShortExact)
    (hFS : (underlyingRow (S.map F.mapCochainComplexPlus)).ShortExact)
    :
    F.rightDerivedFunctorPlusUnit.app S.X₃ ≫
      (plusSESδ S hS).map F.rightDerivedFunctorPlus =
    plusSESδ (S.map F.mapCochainComplexPlus) hFS ≫
      (F.rightDerivedFunctorPlusUnit.app S.X₁)⟦(1 : ℤ)⟧' := by
  let Q₁ := DerivedCategory.Plus.Q (C := A)
  let Q₂ := DerivedCategory.Plus.Q (C := B)
  let M := F.mapCochainComplexPlus
  let D := F.rightDerivedFunctorPlus
  let η := F.rightDerivedFunctorPlusUnit
  have hIsoImage : IsIso (Q₂.map (plusConeDesc (S.map M))) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso B) _
      (CochainComplex.mappingCone.quasiIso_descShortComplex hFS)
  have hIsoComp : IsIso (Q₂.map (M.map (plusConeDesc S))) := by
    rw [← mapPlusConeIso_desc F S, Q₂.map_comp]
    infer_instance
  have hpre {X Y Z : DerivedCategory.Plus A} (f : X ⟶ Y)
      (d : ShiftedHom Y Z (1 : ℤ)) :
      (show ShiftedHom X Z (1 : ℤ) from f ≫ d).map D = D.map f ≫ d.map D := by
    simp [ShiftedHom.map, Functor.map_comp]
  have hpre₂ {X Y Z : CochainComplex.Plus B} (f : X ⟶ Y)
      (d : ShiftedHom Y Z (1 : ℤ)) :
      (show ShiftedHom X Z (1 : ℤ) from f ≫ d).map Q₂ = Q₂.map f ≫ d.map Q₂ := by
    simp [ShiftedHom.map, Functor.map_comp]
  rw [← cancel_epi (Q₂.map (M.map (plusConeDesc S)))]
  change (M ⋙ Q₂).map (plusConeDesc S) ≫ η.app S.X₃ ≫ _ = _
  rw [η.naturality_assoc]
  change η.app (plusCone S.f) ≫ (D.map (Q₁.map (plusConeDesc S)) ≫ _) =
    Q₂.map (M.map (plusConeDesc S)) ≫ (_ ≫ _)
  rw [← hpre, plusConeDesc_δ, ← ShiftedHom.comp_map]
  have hη := ShiftedHom.map_naturality (plusConeδ S.f) η
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map,
    mapPlusConeδ, hpre₂] at hη
  rw [← hη]
  have hc := plusConeDesc_δ (S.map M) hFS
  change Q₂.map (plusConeDesc (S.map M)) ≫ plusSESδ (S.map M) hFS =
    (plusConeδ (M.map S.f)).map Q₂ at hc
  rw [← hc]
  simp only [Category.assoc, ← Q₂.map_comp_assoc]
  erw [mapPlusConeIso_desc F S]


variable [EnoughInjectives A]





private def plusStalkBoundary {S : ShortComplex A} (hS : S.ShortExact) :
    ShiftedHom (DerivedCategory.Plus.singleFunctor A 0 |>.obj S.X₃)
      (DerivedCategory.Plus.singleFunctor A 0 |>.obj S.X₁) (1 : ℤ) :=
  (plusTriangle A hS).mor₃

private theorem plusStalkBoundary_natural {S : ShortComplex A} (hS : S.ShortExact)
    {T : ShortComplex (CochainComplex.Plus A)} (hT : (underlyingRow T).ShortExact)
    (f : S.map (stalk A) ⟶ T) :
    plusStalkBoundary hS ≫ (DerivedCategory.Plus.Q.map f.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.Q.map f.τ₃ ≫ plusSESδ T hT := by
  have hS' : (underlyingRow (S.map (stalk A))).ShortExact :=
    hS.map_of_exact (CochainComplex.singleFunctor A 0)
  exact plusSESδ_natural hS' hT f

private theorem rightDerivedBoundaryOnRow (F : A ⥤ B) [F.Additive]
    {S : ShortComplex A} (hS : S.ShortExact)
    {T : ShortComplex (CochainComplex.Plus A)} (hT : (underlyingRow T).ShortExact)
    (hFT : (underlyingRow (T.map F.mapCochainComplexPlus)).ShortExact)
    (f : S.map (stalk A) ⟶ T)
    [IsIso (F.rightDerivedFunctorPlusUnit.app T.X₁)]
    [IsIso (F.rightDerivedFunctorPlusUnit.app T.X₃)] :
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f.τ₃) ≫
        inv (F.rightDerivedFunctorPlusUnit.app T.X₃)) ≫ plusSESδ _ hFT =
      (plusStalkBoundary hS).map F.rightDerivedFunctorPlus ≫
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f.τ₁) ≫
          inv (F.rightDerivedFunctorPlusUnit.app T.X₁))⟦(1 : ℤ)⟧' := by
  let Q := DerivedCategory.Plus.Q (C := A)
  let F' := F.rightDerivedFunctorPlus
  let η := F.rightDerivedFunctorPlusUnit
  have h := congrArg (fun d : ShiftedHom _ _ (1 : ℤ) => d.map F')
    (plusStalkBoundary_natural hS hT f)
  have hmap : (plusStalkBoundary hS).map F' ≫ (F'.map (Q.map f.τ₁))⟦(1 : ℤ)⟧' =
      F'.map (Q.map f.τ₃) ≫ (plusSESδ T hT).map F' := by
    simpa only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc,
      Functor.commShiftIso_hom_naturality] using h
  have hmodel := mapPlusSESδ F T hT hFT
  change η.app T.X₃ ≫ (plusSESδ T hT).map F' =
    plusSESδ _ hFT ≫ (η.app T.X₁)⟦(1 : ℤ)⟧' at hmodel
  rw [← cancel_mono ((η.app T.X₁)⟦(1 : ℤ)⟧')]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    ]
  rw [← hmodel, IsIso.inv_hom_id_assoc]
  have hc : F'.map (Q.map f.τ₁) ≫ inv (η.app T.X₁) ≫ η.app T.X₁ =
      F'.map (Q.map f.τ₁) := by simp
  erw [hc]
  exact hmap.symm

private theorem plusSESδ_homology {T : ShortComplex (CochainComplex.Plus B)}
    (hT : (underlyingRow T).ShortExact) (n m : ℤ) (hn : n + 1 = m) :
    (DerivedCategory.Plus.homologyFunctor B 0).shiftMap (plusSESδ T hT) n m (by omega) ≫
        (DerivedCategory.homologyFunctorFactors B m).hom.app T.X₁.obj =
      (DerivedCategory.homologyFunctorFactors B n).hom.app T.X₃.obj ≫ hT.δ n m hn := by
  change (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor B 0).shiftMap _ _ _ _ ≫ _ = _
  have h (d : ShiftedHom (DerivedCategory.Plus.Q.obj T.X₃)
        (DerivedCategory.Plus.Q.obj T.X₁) (1 : ℤ)) :
      (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor B 0).shiftMap
          d n m (by omega) =
        (DerivedCategory.homologyFunctor B 0).shiftMap
          (d.map DerivedCategory.Plus.ι) n m (by omega) := by
    dsimp [Functor.shiftMap, Functor.shiftIso, Functor.shift, Functor.ShiftSequence.leftComp,
      ShiftedHom.map]
    erw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Category.id_comp]
  rw [h, plusSESδ_map_ι]
  exact AdvancedHomologicalAlgebra.ShortExactDerivedTriangle.cohomology_boundary
    B (underlyingRow T) hT n m hn

private theorem rightValueBoundaryOnRow (F : A ⥤ B) [F.Additive]
    {S : ShortComplex A} (hS : S.ShortExact)
    {T : ShortComplex (CochainComplex.Plus A)} (hT : (underlyingRow T).ShortExact)
    (hFT : (underlyingRow (T.map F.mapCochainComplexPlus)).ShortExact)
    (f : S.map (stalk A) ⟶ T)
    [IsIso (F.rightDerivedFunctorPlusUnit.app T.X₁)]
    [IsIso (F.rightDerivedFunctorPlusUnit.app T.X₃)] (n : ℕ) :
    rightBoundary F hS n ≫
        (DerivedCategory.Plus.homologyFunctor B (((n + 1 : ℕ) : ℤ))).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f.τ₁) ≫
            inv (F.rightDerivedFunctorPlusUnit.app T.X₁)) ≫
        (DerivedCategory.homologyFunctorFactors B (((n + 1 : ℕ) : ℤ))).hom.app
          (F.mapCochainComplexPlus.obj T.X₁).obj =
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f.τ₃) ≫
            inv (F.rightDerivedFunctorPlusUnit.app T.X₃)) ≫
        (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
          (F.mapCochainComplexPlus.obj T.X₃).obj ≫
        hFT.δ (n : ℤ) (((n + 1 : ℕ) : ℤ)) (by simp) := by
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let F' := F.rightDerivedFunctorPlus
  have h := congrArg (fun d : ShiftedHom _ _ (1 : ℤ) =>
      H.shiftMap d (n : ℤ) (((n + 1 : ℕ) : ℤ)) (by omega))
    (rightDerivedBoundaryOnRow F hS hT hFT f)
  rw [Functor.shiftMap_comp', Functor.shiftMap_comp] at h
  change _ ≫ _ ≫ _ = _
  have hd : rightBoundary F hS n =
      H.shiftMap ((plusStalkBoundary hS).map F') (n : ℤ) (((n + 1 : ℕ) : ℤ)) (by omega) := rfl
  erw [hd, ← Category.assoc, ← h, Category.assoc]
  erw [plusSESδ_homology hFT (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega)]
  rfl

end ResolutionBoundary

section ExtendedResolutionBoundary

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

private def extendToPlus (C : Type*) [Category* C] [Abelian C] :
    CochainComplex C ℕ ⥤ CochainComplex.Plus C :=
  (CochainComplex.plus C).lift (resolutionEmbedding.extendFunctor C)
    (fun K => ⟨0, by
      change CochainComplex.IsStrictlyGE (K.extend resolutionEmbedding) 0
      infer_instance⟩)

local instance (C : Type*) [Category* C] [Abelian C] :
    (extendToPlus C).PreservesZeroMorphisms where
  map_zero K L := (CochainComplex.plus C).ι.map_injective
    ((resolutionEmbedding.extendFunctor C).map_zero K L)

private theorem extendShortExact {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℕ)} (hS : S.ShortExact) :
    (S.map (resolutionEmbedding.extendFunctor C)).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro j
  by_cases hj : ∃ n : ℕ, resolutionEmbedding.f n = j
  · obtain ⟨n, hn⟩ := hj
    let e := resolutionEmbedding.extendFunctorCompEvalIso C hn
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e).symm
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n)
  · let U := (S.map (resolutionEmbedding.extendFunctor C)).map
      (HomologicalComplex.eval C (.up ℤ) j)
    have h₁ : IsZero U.X₁ := S.X₁.isZero_extend_X resolutionEmbedding j
      (fun n hn => hj ⟨n, hn⟩)
    have h₂ : IsZero U.X₂ := S.X₂.isZero_extend_X resolutionEmbedding j
      (fun n hn => hj ⟨n, hn⟩)
    have h₃ : IsZero U.X₃ := S.X₃.isZero_extend_X resolutionEmbedding j
      (fun n hn => hj ⟨n, hn⟩)
    exact { exact := ShortComplex.exact_of_isZero_X₂ U h₂
            mono_f := h₁.mono _
            epi_g := h₃.epi _ }

private def extendStalkIso (C : Type*) [Category* C] [Abelian C] :
    stalk C ≅ CochainComplex.single₀ C ⋙ extendToPlus C :=
  NatIso.ofComponents (fun X => (CochainComplex.plus C).fullyFaithfulι.preimageIso
    (HomologicalComplex.extendSingleIso resolutionEmbedding X 0 0 rfl).symm) (by
      intro X Y f
      apply (CochainComplex.plus C).ι.map_injective
      change ((CochainComplex.singleFunctor C 0).map f ≫
            (HomologicalComplex.extendSingleIso resolutionEmbedding Y 0 0 rfl).inv) =
        ((HomologicalComplex.extendSingleIso resolutionEmbedding X 0 0 rfl).inv ≫
          HomologicalComplex.extendMap ((CochainComplex.single₀ C).map f) resolutionEmbedding)
      apply HomologicalComplex.hom_ext
      intro i
      by_cases hi : i = 0
      · subst i
        simp only [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
          Category.assoc]
        have h0 : resolutionEmbedding.f (0 : ℕ) = (0 : ℤ) := rfl
        have hmap := HomologicalComplex.extendMap_f ((CochainComplex.single₀ C).map f)
          resolutionEmbedding h0
        rw [hmap]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        have hℤ := HomologicalComplex.single_map_f_self (c := ComplexShape.up ℤ) 0 f
        have hℕ := HomologicalComplex.single_map_f_self (c := ComplexShape.up ℕ) 0 f
        conv_lhs => erw [hℤ]
        conv_rhs => erw [hℕ]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi).eq_of_src _ _)

private def mapExtendNatIso (F : A ⥤ B) [F.Additive] :
    (resolutionEmbedding.extendFunctor A ⋙ F.mapHomologicalComplex (.up ℤ)) ≅
      (F.mapHomologicalComplex (.up ℕ) ⋙ resolutionEmbedding.extendFunctor B) :=
  NatIso.ofComponents (mapExtendIso F resolutionEmbedding)
    (fun f => mapExtendIso_natural F resolutionEmbedding f)

/-- The stalk-triangle boundary computed on a degreewise split row of injective
resolutions, in the same coordinates as `rightValueResolutionIso`. -/
private theorem rightValueResolutionBoundary (F : A ⥤ B) [F.Additive]
    {S : ShortComplex A} (hS : S.ShortExact)
    {I₁ : CategoryTheory.InjectiveResolution S.X₁}
    {I₂ : CategoryTheory.InjectiveResolution S.X₂}
    {I₃ : CategoryTheory.InjectiveResolution S.X₃}
    (i : CategoryTheory.InjectiveResolution.Hom I₁ I₂ S.f)
    (p : CategoryTheory.InjectiveResolution.Hom I₂ I₃ S.g)
    (hz : i.hom ≫ p.hom = 0)
    (hI : (ShortComplex.mk i.hom p.hom hz).ShortExact)
    (hFI : ((ShortComplex.mk i.hom p.hom hz).map
      (F.mapHomologicalComplex (.up ℕ))).ShortExact)
    (n : ℕ) :
    rightBoundary F hS n ≫ (rightValueResolutionIso F (n+1) I₁).hom =
      (rightValueResolutionIso F n I₃).hom ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I₃.cocomplex).extendHomologyIso
          resolutionEmbedding (rfl : resolutionEmbedding.f n = (n : ℤ))).inv ≫
        (extendShortExact hFI).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex).extendHomologyIso
          resolutionEmbedding (rfl : resolutionEmbedding.f (n+1) = ((n+1 : ℕ) : ℤ))).hom := by
  let R := ShortComplex.mk i.hom p.hom hz
  let T := R.map (extendToPlus A)
  let Φ : S.map (CochainComplex.single₀ A) ⟶ R := ShortComplex.homMk I₁.ι I₂.ι I₃.ι
    i.ι_comp_hom p.ι_comp_hom
  let f : S.map (stalk A) ⟶ T :=
    S.mapNatTrans (extendStalkIso A).hom ≫ (extendToPlus A).mapShortComplex.map Φ
  have hT : (underlyingRow T).ShortExact := extendShortExact hI
  let e : underlyingRow (T.map F.mapCochainComplexPlus) ≅
      (R.map (F.mapHomologicalComplex (.up ℕ))).map (resolutionEmbedding.extendFunctor B) :=
    R.mapNatIso (mapExtendNatIso F)
  have hFT : (underlyingRow (T.map F.mapCochainComplexPlus)).ShortExact :=
    ShortComplex.shortExact_of_iso e.symm (extendShortExact hFI)
  letI : IsIso (F.rightDerivedFunctorPlusUnit.app T.X₁) :=
    resolutionPlus_unit_isIso F I₁
  letI : IsIso (F.rightDerivedFunctorPlusUnit.app T.X₃) :=
    resolutionPlus_unit_isIso F I₃
  have h := rightValueBoundaryOnRow F hS hT hFT f n
  have he := HomologicalComplex.HomologySequence.δ_naturality e.hom hFT (extendShortExact hFI)
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)
  let E₁ := (((F.mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex).extendHomologyIso
    resolutionEmbedding (rfl : resolutionEmbedding.f (n+1) = ((n+1 : ℕ) : ℤ)))
  let E₃ := (((F.mapHomologicalComplex (.up ℕ)).obj I₃.cocomplex).extendHomologyIso
    resolutionEmbedding (rfl : resolutionEmbedding.f n = (n : ℤ)))
  simp only [rightValueResolutionIso, rightDerivedResolutionIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  change rightBoundary F hS n ≫ _ ≫ _ ≫
      HomologicalComplex.homologyMap e.hom.τ₁ (((n+1 : ℕ) : ℤ)) ≫ E₁.hom =
    _ ≫ _ ≫ HomologicalComplex.homologyMap e.hom.τ₃ (n : ℤ) ≫ E₃.hom ≫ E₃.inv ≫
      (extendShortExact hFI).δ _ _ _ ≫ E₁.hom
  simp only [Iso.hom_inv_id_assoc]
  erw [← reassoc_of% he]
  exact (reassoc_of% h) _

end ExtendedResolutionBoundary

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P103.Ch10.HomologySequence
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence

universe a b

variable {R : Type a} [Ring R]

private def elementHom {M : ModuleCat.{max a b} R} (m : M) :
    ModuleCat.of R (ULift.{b} R) ⟶ M :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton R M m).comp ULift.moduleEquiv.toLinearMap)

@[reassoc]
private theorem elementHom_comp {M N : ModuleCat.{max a b} R} (m : M) (f : M ⟶ N) :
    elementHom m ≫ f = elementHom (f.hom m) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact f.hom.map_smul r.down m

private theorem elementHom_zero {M : ModuleCat.{max a b} R} :
    elementHom (0 : M) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact smul_zero r.down

private abbrev extendNatCochain :
    CochainComplex (ModuleCat.{max a b} R) ℕ ⥤ CochainComplex (ModuleCat.{max a b} R) ℤ :=
  ComplexShape.embeddingUpNat.extendFunctor _

private def extendQuotientHomologyIso (K : CochainComplex (ModuleCat.{max a b} R) ℕ)
    (n : ℕ) : ((extendNatCochain (R := R)).obj K).homology (n : ℤ) ≅
      (quotientHomology (.up ℕ) n).obj K :=
  K.extendHomologyIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl) ≪≫
    moduleQuotientHomologyIso K n

/-- A concrete cycle sent into the extended complex projects to the same quotient class. -/
private theorem extendQuotientHomologyIso_liftCycles
    (K : CochainComplex (ModuleCat.{max a b} R) ℕ) (n : ℕ)
    (z : P103.Specs.Ch10.Complexes.cycles K n) (j : ℤ)
    (hj : (ComplexShape.up ℤ).next (n : ℤ) = j)
    (h : (elementHom z.val ≫
        (K.extendXIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).inv) ≫
          (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) j = 0) :
    (K.extend ComplexShape.embeddingUpNat).liftCycles
      (elementHom z.val ≫ (K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).inv) j hj h ≫
      (K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ) ≫
      (extendQuotientHomologyIso K n).hom =
      elementHom (homologyClass K n z) := by
  let e := ComplexShape.embeddingUpNat
  let K' := K.extend e
  have hn : e.f n = (n : ℤ) := rfl
  let s := (K.sc n).moduleCatCyclesIso
  let c := K'.liftCycles (elementHom z.val ≫ (K.extendXIso e hn).inv) j hj h
  have hc : c ≫ (K.extendCyclesIso e hn).hom = (elementHom z ≫ s.inv) := by
    rw [← cancel_mono (K.iCycles n), Category.assoc, K.extendCyclesIso_hom_iCycles,
      liftCycles_i_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.assoc]
    change _ = elementHom z ≫ s.inv ≫ (K.sc n).iCycles
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles, elementHom_comp]
    rfl
  change c ≫ K'.homologyπ (n : ℤ) ≫
      ((K.extendHomologyIso e hn).hom ≫ (moduleQuotientHomologyIso K n).hom) = _
  rw [← Category.assoc (K'.homologyπ (n : ℤ)), K.homologyπ_extendHomologyIso_hom,
    Category.assoc, moduleQuotientHomologyIso_π, ← Category.assoc c, hc,
    Category.assoc, Iso.inv_hom_id_assoc, elementHom_comp]
  rfl

/-- The categorical connecting map has the positive lift-and-differentiate formula
on the original exterior cocycle quotients after extending cochain indices to integers. -/
private theorem extendBoundary_connecting
    {S : ShortComplex (CochainComplex (ModuleCat.{max a b} R) ℕ)}
    (hT : (S.map (extendNatCochain (R := R))).ShortExact) (n : ℕ) :
    Connecting S.f S.g n (n+1)
      (((extendQuotientHomologyIso S.X₃ n).inv ≫
        hT.δ (n : ℤ) ((n+1 : ℕ) : ℤ) (by simp) ≫
        (extendQuotientHomologyIso S.X₁ (n+1)).hom).hom) := by
  intro z b a hb ha
  let e := ComplexShape.embeddingUpNat
  let T := S.map (extendNatCochain (R := R))
  let m := n+1
  have hn : e.f n = (n : ℤ) := rfl
  have hm : e.f m = (m : ℤ) := rfl
  have hrel : (ComplexShape.up ℤ).Rel (n : ℤ) (m : ℤ) := by simp [m]
  let x₃ := elementHom z.val ≫ (S.X₃.extendXIso e hn).inv
  let x₂ := elementHom b ≫ (S.X₂.extendXIso e hn).inv
  let x₁ := elementHom a.val ≫ (S.X₁.extendXIso e hm).inv
  have hx₃ : x₃ ≫ T.X₃.d (n : ℤ) (m : ℤ) = 0 := by
    change x₃ ≫ (S.X₃.extend e).d (n : ℤ) (m : ℤ) = 0
    rw [S.X₃.extend_d_eq e hn hm]
    simp only [x₃, Category.assoc, Iso.inv_hom_id_assoc, elementHom_comp_assoc]
    have hz : (S.X₃.d n m).hom z.val = 0 :=
      (cycle_iff S.X₃ (show (ComplexShape.up ℕ).Rel n m from rfl) z.val).mp z.property
    rw [hz, elementHom_zero, zero_comp]
  have hx₂ : x₂ ≫ T.g.f (n : ℤ) = x₃ := by
    change x₂ ≫ (extendMap S.g e).f (n : ℤ) = x₃
    rw [extendMap_f _ e hn]
    simp only [x₂, x₃, Category.assoc, Iso.inv_hom_id_assoc, elementHom_comp_assoc, hb]
  have hx₁ : x₁ ≫ T.f.f (m : ℤ) = x₂ ≫ T.X₂.d (n : ℤ) (m : ℤ) := by
    change x₁ ≫ (extendMap S.f e).f (m : ℤ) = x₂ ≫ (S.X₂.extend e).d (n : ℤ) (m : ℤ)
    rw [extendMap_f _ e hm, S.X₂.extend_d_eq e hn hm]
    simp only [x₁, x₂, Category.assoc, Iso.inv_hom_id_assoc, elementHom_comp_assoc]
    exact congrArg (fun t => elementHom t ≫ (S.X₂.extendXIso e hm).inv) ha
  have hnext : (ComplexShape.up ℤ).next (m : ℤ) = (m : ℤ) + 1 :=
    (ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (m : ℤ) ((m : ℤ) + 1) from rfl)
  have hδ := hT.δ_eq (n : ℤ) (m : ℤ) hrel x₃ hx₃ x₂ hx₂ x₁ hx₁ ((m : ℤ) + 1) hnext
  let c₃ := T.X₃.liftCycles x₃ (m : ℤ) ((ComplexShape.up ℤ).next_eq' hrel) hx₃
  let e₃ := extendQuotientHomologyIso S.X₃ n
  let e₁ := extendQuotientHomologyIso S.X₁ m
  have p₃ : c₃ ≫ T.X₃.homologyπ (n : ℤ) ≫ e₃.hom =
      elementHom (homologyClass S.X₃ n z) :=
    extendQuotientHomologyIso_liftCycles S.X₃ n z (m : ℤ)
      ((ComplexShape.up ℤ).next_eq' hrel) hx₃
  have hz₁ : x₁ ≫ (S.X₁.extend e).d (m : ℤ) ((m : ℤ) + 1) = 0 := by
    have hnext' : e.f (m+1) = (m : ℤ) + 1 := by simp [e]
    rw [S.X₁.extend_d_eq e hm hnext']
    simp only [x₁, Category.assoc, Iso.inv_hom_id_assoc, elementHom_comp_assoc]
    have hz : (S.X₁.d m (m+1)).hom a.val = 0 :=
      (cycle_iff S.X₁ (show (ComplexShape.up ℕ).Rel m (m+1) from rfl) a.val).mp a.property
    rw [hz, elementHom_zero, zero_comp]
  let c₁ := T.X₁.liftCycles x₁ ((m : ℤ) + 1) hnext hz₁
  let π₃ := T.X₃.homologyπ (n : ℤ)
  let π₁ := T.X₁.homologyπ (m : ℤ)
  let δ := hT.δ (n : ℤ) (m : ℤ) hrel
  have p₁ : c₁ ≫ π₁ ≫ e₁.hom = elementHom (homologyClass S.X₁ m a) :=
    extendQuotientHomologyIso_liftCycles S.X₁ m a ((m : ℤ) + 1) hnext hz₁
  have h₃ : c₃ ≫ π₃ =
        elementHom (homologyClass S.X₃ n z) ≫ e₃.inv := by
    rw [← cancel_mono e₃.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact p₃
  change c₃ ≫ π₃ ≫ δ = c₁ ≫ π₁ at hδ
  let z' : (quotientHomology (.up ℕ) n).obj S.X₃ := homologyClass S.X₃ n z
  let mδ := e₃.inv ≫ δ ≫ e₁.hom
  have ht : elementHom z' ≫ mδ = elementHom (homologyClass S.X₁ m a) := by
    change elementHom z' ≫ e₃.inv ≫ δ ≫ e₁.hom = _
    calc
      _ = (elementHom z' ≫ e₃.inv) ≫ δ ≫ e₁.hom := (Category.assoc _ _ _).symm
      _ = (c₃ ≫ π₃) ≫ δ ≫ e₁.hom := congrArg (fun f => f ≫ δ ≫ e₁.hom) h₃.symm
      _ = (c₃ ≫ π₃ ≫ δ) ≫ e₁.hom := by simp only [Category.assoc]
      _ = c₁ ≫ π₁ ≫ e₁.hom := by rw [hδ, Category.assoc]
      _ = _ := p₁
  have ht' := congrArg (fun f => f.hom (ULift.up (1 : R))) ((elementHom_comp z' mδ).symm.trans ht)
  change (1 : R) • mδ.hom z' = (1 : R) • (homologyClass S.X₁ m a) at ht'
  change mδ.hom z' = (homologyClass S.X₁ m) a
  simpa only [one_smul] using ht'

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open CategoryTheory
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence

universe a b c d

section ShortComplexIso

variable {R : Type a} [Ring R] {ι : Type b} {s : ComplexShape ι}
  {S T : ShortComplex (HomologicalComplex (ModuleCat.{c} R) s)}

/-- The positive lift formula is invariant under isomorphism of coefficient rows. -/
private theorem connecting_of_shortComplexIso (e : S ≅ T) (n m : ι)
    (δ : (quotientHomology s n).obj S.X₃ ⟶ (quotientHomology s m).obj S.X₁)
    (hδ : Connecting S.f S.g n m δ.hom) :
    Connecting T.f T.g n m
      (((quotientHomology s n).map e.inv.τ₃ ≫ δ ≫ (quotientHomology s m).map e.hom.τ₁).hom) := by
  intro z b a hb ha
  let z' := cyclesMap e.inv.τ₃ n z
  let a' := cyclesMap e.inv.τ₁ m a
  let b' := (e.inv.τ₂.f n).hom b
  have hb' : (S.g.f n).hom b' = z'.val := by
    have h := congrArg (fun f => (f.f n).hom b) e.inv.comm₂₃
    change (S.g.f n).hom b' = (e.inv.τ₃.f n).hom ((T.g.f n).hom b) at h
    exact h.trans (congrArg (e.inv.τ₃.f n).hom hb)
  have ha' : (S.f.f m).hom a'.val = (S.X₂.d n m).hom b' := by
    have h := congrArg (fun f => (f.f m).hom a.val) e.inv.comm₁₂
    have he := congrArg (fun f => f.hom b) (e.inv.τ₂.comm n m)
    change (S.f.f m).hom a'.val = (e.inv.τ₂.f m).hom ((T.f.f m).hom a.val) at h
    change (S.X₂.d n m).hom b' = (e.inv.τ₂.f m).hom ((T.X₂.d n m).hom b) at he
    exact h.trans ((congrArg (e.inv.τ₂.f m).hom ha).trans he.symm)
  change homologyMap e.hom.τ₁ m (δ.hom (homologyClass S.X₃ n z')) =
    homologyClass T.X₁ m a
  refine (congrArg (P103.Specs.Ch10.Complexes.homologyMap e.hom.τ₁ m) (hδ z' b' a' hb' ha')).trans ?_
  change homologyClass T.X₁ m (cyclesMap e.hom.τ₁ m a') = homologyClass T.X₁ m a
  apply congrArg (homologyClass T.X₁ m)
  apply Subtype.ext
  have h := congrArg (fun f : T ⟶ T => (f.τ₁.f m).hom a.val) e.inv_hom_id
  exact h

end ShortComplexIso

section ScalarRestriction

variable {R : Type a} {A : Type d} [Ring R] [Ring A]
  {ι : Type b} {s : ComplexShape ι}

/-- Restricting scalars does not change cycle representatives or either lift
in the positive boundary formula. -/
private theorem restrictQuotientBoundary_connecting (f : R →+* A)
    (S : ShortComplex (HomologicalComplex (ModuleCat.{c} A) s)) (n m : ι)
    (δ : (quotientHomology s n).obj S.X₃ ⟶ (quotientHomology s m).obj S.X₁)
    (hδ : Connecting S.f S.g n m δ.hom) :
    let F := ModuleCat.restrictScalars f
    let T := S.map (F.mapHomologicalComplex s)
    Connecting T.f T.g n m
      (((restrictQuotientHomology f S.X₃ n).inv ≫ F.map δ ≫
        (restrictQuotientHomology f S.X₁ m).hom).hom) := by
  dsimp only
  intro z b a hb ha
  let z' : cycles S.X₃ n := ⟨z.val, z.property⟩
  let a' : cycles S.X₁ m := ⟨a.val, a.property⟩
  let q₁ := (restrictQuotientHomology f S.X₁ m).hom
  change q₁.hom (δ.hom (homologyClass S.X₃ n z')) =
    q₁.hom (homologyClass S.X₁ m a')
  exact congrArg q₁.hom (hδ z' b a' hb ha)

end ScalarRestriction

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

open LieQuotientAction

universe a b u v w

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule

private theorem degreewiseExact_of_shortExact {R : Type a} [Ring R]
    {S : ShortComplex (CochainComplex (ModuleCat.{b} R) ℕ)} (hS : S.ShortExact) :
    DegreewiseExact S.f S.g := by
  intro n
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  exact ⟨hs.moduleCat_injective_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs.exact,
    hs.moduleCat_surjective_g⟩

section IntegerConnectors

variable {k : Type a} [Ring k] {A B C : CochainComplex (ModuleCat.{b} k) ℕ}
  (i : A ⟶ B) (p : B ⟶ C)

private abbrev mapIntegers (k : Type a) [Ring k] :=
  (integerCoordinates.{a,b} k).mapHomologicalComplex (.up ℕ)

private theorem integer_degreewiseExact_iff :
    DegreewiseExact ((mapIntegers k).map i) ((mapIntegers k).map p) ↔ DegreewiseExact i p :=
  Iff.rfl

private def integerConnector (n m : ℕ) (δ : Homology C n →ₗ[k] Homology A m) :
    Homology (integerComplex C) n →ₗ[ℤ] Homology (integerComplex A) m :=
  (integerHomologyEquiv A m).toLinearMap.comp
    (δ.toAddMonoidHom.toIntLinearMap.comp (integerHomologyEquiv C n).symm.toLinearMap)

private theorem integerConnector_apply (n m : ℕ)
    (δ : Homology C n →ₗ[k] Homology A m) (x : Homology C n) :
    integerConnector n m δ (integerHomologyEquiv C n x) =
      integerHomologyEquiv A m (δ x) := by
  simp only [integerConnector, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe]

private theorem integerConnector_is_connecting (n m : ℕ)
    (δ : Homology C n →ₗ[k] Homology A m) (hδ : Connecting i p n m δ) :
    Connecting ((mapIntegers k).map i) ((mapIntegers k).map p) n m (integerConnector n m δ) := by
  intro z b c hb hc
  let z' := (integerCyclesEquiv C n).symm z
  let c' := (integerCyclesEquiv A m).symm c
  change integerConnector n m δ ((integerHomologyEquiv C n) (homologyClass C n z')) =
    (integerHomologyEquiv A m) (homologyClass A m c')
  rw [integerConnector_apply]
  exact congrArg (integerHomologyEquiv A m) (hδ z' b c' hb hc)

end IntegerConnectors

section LieConnectors

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

private abbrev lieInvFunctor :=
  (lieInvariants.{u,v,w} k g).mapHomologicalComplex (.up ℕ)

private abbrev ceFunctor := (chevalleyEilenberg.{u,v,w} k g).functor

private theorem lieInjectiveHomNaturalInv
    {M N : ModuleCat.{max u v w} (U k g)}
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (J : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) N)
    (m : I.complex ⟶ J.complex) :
    (mapIntegers k).map ((lieInvFunctor (k := k) (g := g)).map m) ≫
      (lieInjectiveHomIso J).inv =
      (lieInjectiveHomIso I).inv ≫ injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) m := by
  apply (cancel_epi (lieInjectiveHomIso I).hom).mp
  rw [← Category.assoc, ← lieInjectiveHomIso_natural I J m]
  simp

private theorem lieBalancedComparison
    {M : ModuleCat.{max u v w} (U k g)}
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M) (n : ℕ) :
    P103.Specs.Ch11.ExtExactSequences.BalancedComparison
      (A := ModuleCat.of (U k g) k) (lieProjectiveResolution (k := k) (g := g)) I n
      (lieResolutionBalance I n) := by
  let P := lieProjectiveResolution (k := k) (g := g)
  exact ⟨P103.Ch11.ExtBalance.projectiveAugmentation P I,
    P103.Ch11.ExtBalance.injectiveAugmentation P I,
    P103.Ch11.ExtBalance.projectiveAugmentation_formula P I,
    P103.Ch11.ExtBalance.injectiveAugmentation_formula P I,
    P103.Ch11.ExtBalance.projectiveAugmentation_quasiIso P I
      (lieProjectiveResolution_projective (k := k) (g := g)),
    P103.Ch11.ExtBalance.injectiveAugmentation_quasiIso P I, lieResolutionBalance_formula I n⟩

/-- The two actual coefficient boundaries agree under the normalized balance
comparison level for a degreewise split sequence of injective resolutions. -/
theorem lieResolutionCohomology_connecting
    {S : ShortComplex (ModuleCat.{max u v w} (U k g))} (hS : S.ShortExact)
    (H : InjectiveHorseshoe S) (n : ℕ)
    (δ : Homology ((lieInvFunctor (k := k) (g := g)).obj H.right.cocomplex) n →ₗ[k]
      Homology ((lieInvFunctor (k := k) (g := g)).obj H.left.cocomplex) (n+1))
    (hδ : Connecting ((lieInvFunctor (k := k) (g := g)).map H.inclusion.hom)
      ((lieInvFunctor (k := k) (g := g)).map H.projection.hom) n (n+1) δ) :
    Connecting ((ceFunctor (k := k) (g := g)).map S.f)
      ((ceFunctor (k := k) (g := g)).map S.g) n (n+1)
      ((lieResolutionCohomologyEquiv (moduleInjectiveResolution H.left) (n+1)).toLinearMap.comp
        (δ.comp (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.right) n).symm.toLinearMap)) := by
  let P := lieProjectiveResolution (k := k) (g := g)
  let IQ := lieInvFunctor (k := k) (g := g)
  let CE := ceFunctor (k := k) (g := g)
  let L := moduleInjectiveResolution H.left
  let M := moduleInjectiveResolution H.middle
  let N := moduleInjectiveResolution H.right
  let B := H.moduleData
  let eL := lieInjectiveHomIso L
  let eM := lieInjectiveHomIso M
  let eN := lieInjectiveHomIso N
  have hrel : (ComplexShape.up ℕ).Rel n (n+1) := rfl
  have hI := degreewiseExact_of_shortExact (H.map_shortExact (lieInvariants.{u,v,w} k g))
  have hI' := (integer_degreewiseExact_iff (IQ.map H.inclusion.hom) (IQ.map H.projection.hom)).mpr hI
  have hInj := P103.Ch10.HorseshoeNaturality.split_exact _ _
    (P103.Ch10.HorseshoeNaturality.split_map
      (P103.Specs.Ch11.ExtBalance.covariantHom (ModuleCat.of (U k g) k))
      B.inclusion B.projection
      (P103.Ch10.HorseshoeNaturality.injective_split _ _ _ _ _ _ _ _ B))
  obtain ⟨ε, hε⟩ := P103.Ch10.HomologySequence.exists_connecting _ _ hInj hrel
  have hIδ : (P103.Specs.Ch10.Complexes.homologyMap eL.inv (n+1)).comp (integerConnector n (n+1) δ) =
      ε.comp (P103.Specs.Ch10.Complexes.homologyMap eN.inv n) := by
    exact (P103.Ch10.HomologySequence.naturality _ _ _ _
      eL.inv eM.inv eN.inv
      (lieInjectiveHomNaturalInv L M H.inclusion.hom)
      (lieInjectiveHomNaturalInv M N H.projection.hom)
      hI' hInj n (n+1) hrel _ ε
      (integerConnector_is_connecting _ _ n (n+1) δ hδ) hε).2.2.1
  have hF := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact
  have hExt := P103.Ch11.ExtExactSequences.second_degreewise_exact.{max u v,u,max u v w}
    (A := ModuleCat.of (U k g) k) P
    (lieProjectiveResolution_projective (k := k) (g := g)) S.f S.g hS.moduleCat_injective_f hF hS.moduleCat_surjective_g
  obtain ⟨τ, hτ⟩ := P103.Ch10.HomologySequence.exists_connecting _ _ hExt hrel
  have hBal := P103.Ch11.ExtExactSequences.balance_connecting.{max u v,u,max u v w} (U k g) (ModuleCat.of (U k g) k) P
    (lieProjectiveResolution_projective (k := k) (g := g)) S.X₁ S.X₂ S.X₃ S.f S.g hS.moduleCat_injective_f hF
    hS.moduleCat_surjective_g L N B n τ ε hτ hε (lieResolutionBalance N n)
    (lieResolutionBalance L (n+1)) (lieBalancedComparison N n) (lieBalancedComparison L (n+1))
  have hCE : DegreewiseExact (CE.map S.f) (CE.map S.g) := (chevalleyEilenberg.{u,v,w} k g).degreewiseExact hS
  obtain ⟨δ', hδ'⟩ := P103.Ch10.HomologySequence.exists_connecting _ _ hCE hrel
  have hEval : (P103.Specs.Ch10.Complexes.homologyMap (lieEvaluationIso S.X₁).hom (n+1)).comp τ =
      (integerConnector n (n+1) δ').comp (P103.Specs.Ch10.Complexes.homologyMap (lieEvaluationIso S.X₃).hom n) :=
    (P103.Ch10.HomologySequence.naturality _ _ _ _
      (lieEvaluationIso S.X₁).hom (lieEvaluationIso S.X₂).hom (lieEvaluationIso S.X₃).hom
      (lieEvaluationIso_natural S.f) (lieEvaluationIso_natural S.g) hExt
      ((integer_degreewiseExact_iff _ _).mpr hCE) n (n+1) hrel _ _ hτ
      (integerConnector_is_connecting _ _ n (n+1) δ' hδ')).2.2.1
  rw [← show δ' =
      (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.left) (n+1)).toLinearMap.comp
        (δ.comp (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.right) n).symm.toLinearMap)
      from ?_]
  · exact hδ'
  apply LinearMap.ext
  intro x
  let e := lieResolutionCohomologyEquiv N n
  let z : Homology (IQ.obj H.right.cocomplex) n := e.symm x
  have hx : e z = x := e.apply_symm_apply x
  change δ' x = lieResolutionCohomologyEquiv L (n+1) (δ z)
  apply (integerHomologyEquiv (CE.obj S.X₁) (n+1)).injective
  let ιL := integerHomologyEquiv (IQ.obj H.left.cocomplex) (n+1)
  let ιN := integerHomologyEquiv (IQ.obj H.right.cocomplex) n
  let κL := integerHomologyEquiv (CE.obj S.X₁) (n+1)
  let κN := integerHomologyEquiv (CE.obj S.X₃) n
  let aL := P103.Specs.Ch10.Complexes.homologyMap (lieEvaluationIso S.X₁).hom (n+1)
  let aN := P103.Specs.Ch10.Complexes.homologyMap (lieEvaluationIso S.X₃).hom n
  let qL := P103.Specs.Ch10.Complexes.homologyMap eL.inv (n+1)
  let qN := P103.Specs.Ch10.Complexes.homologyMap eN.inv n
  let b := qN (ιN z)
  have hZ : qL (ιL (δ z)) = ε b :=
    (congrArg qL (integerConnector_apply n (n+1) δ z)).symm.trans
      (LinearMap.congr_fun hIδ (ιN z))
  have hB : lieResolutionBalance L (n+1) (ε b) =
      τ (lieResolutionBalance N n b) := LinearMap.congr_fun hBal b
  have hE : aL (τ (lieResolutionBalance N n b)) =
      integerConnector n (n+1) δ' (aN (lieResolutionBalance N n b)) :=
    LinearMap.congr_fun hEval (lieResolutionBalance N n b)
  have hN : aN (lieResolutionBalance N n b) = κN x :=
    (lieResolutionCohomologyEquiv_integer N n z).symm.trans (congrArg κN hx)
  calc
    κL (δ' x) = integerConnector n (n+1) δ' (κN x) := (integerConnector_apply _ _ δ' x).symm
    _ = integerConnector n (n+1) δ' (aN (lieResolutionBalance N n b)) := congrArg _ hN.symm
    _ = aL (τ (lieResolutionBalance N n b)) := hE.symm
    _ = aL (lieResolutionBalance L (n+1) (ε b)) := congrArg aL hB.symm
    _ = aL (lieResolutionBalance L (n+1) (qL (ιL (δ z)))) :=
      congrArg (fun y => aL (lieResolutionBalance L (n+1) y)) hZ.symm
    _ = κL (lieResolutionCohomologyEquiv L (n+1) (δ z)) :=
      (lieResolutionCohomologyEquiv_integer L (n+1) (δ z)).symm

end LieConnectors
end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
open Shared.Lie P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

section BoundaryNaturality

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

private theorem rightValueNatIso_boundary (e : F ≅ G)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    rightBoundary F hS n ≫ (rightValueNatIso e (n+1)).hom.app S.X₁ =
      (rightValueNatIso e n).hom.app S.X₃ ≫ rightBoundary G hS n := by
  let τ := e.hom.rightDerivedFunctorPlus
  let T := plusTriangle A hS
  let H := DerivedCategory.Plus.homologyFunctor B 0
  have hs := ShiftedHom.map_naturality
    (show ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) from T.mor₃) τ
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hs
  have hs' := congrArg
    (fun d : ShiftedHom _ _ (1 : ℤ) => H.shiftMap d (n : ℤ) ((n+1 : ℕ) : ℤ) (by omega)) hs
  rw [Functor.shiftMap_comp, Functor.shiftMap_comp'] at hs'
  exact hs'

end BoundaryNaturality

section ExteriorConnectors

universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

private theorem lieCohomologyIso_connectors :
    PreservesCEConnectors (chevalleyEilenberg.{u,v,w} k g).functor
      (rightValue (lieInvariants.{u,v,w} k g))
      (rightBoundary (lieInvariants.{u,v,w} k g))
      (lieCohomologyIso.{u,v,w} k g) := by
  intro S hS
  refine ⟨(chevalleyEilenberg.{u,v,w} k g).degreewiseExact hS, ?_⟩
  intro n
  let F := lieInvariants.{u,v,w} k g
  let K := F.mapHomologicalComplex (.up ℕ)
  let H := injectiveHorseshoe hS
  let hK := H.map_shortExact F
  let hE := extendShortExact hK
  let J₃ := moduleQuotientHomologyIso (K.obj H.right.cocomplex) n
  let J₁ := moduleQuotientHomologyIso (K.obj H.left.cocomplex) (n+1)
  let E₃ := extendQuotientHomologyIso.{u,max v w} (K.obj H.right.cocomplex) n
  let E₁ := extendQuotientHomologyIso.{u,max v w} (K.obj H.left.cocomplex) (n+1)
  let L₃ := rightValueResolutionIso F n H.right ≪≫ J₃
  let L₁ := rightValueResolutionIso F (n+1) H.left ≪≫ J₁
  let δ := E₃.inv ≫ hE.δ (n : ℤ) ((n+1 : ℕ) : ℤ) (by simp) ≫ E₁.hom
  have hδ := extendBoundary_connecting.{u,max v w} hE n
  have hR := rightValueResolutionBoundary F hS H.inclusion H.projection H.zero
    H.shortExact hK n
  have hR' : rightBoundary F hS n ≫ L₁.hom = L₃.hom ≫ δ := by
    simp only [L₁, L₃, J₁, J₃, K, E₁, E₃, δ, extendQuotientHomologyIso, Iso.trans_hom, Iso.trans_inv,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact (reassoc_of% hR) _
  have he : (lieCohomologyIso.{u,v,w} k g n).hom.app S.X₃ =
      L₃.hom ≫ (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.right) n).toModuleIso.hom := by
    rw [lieCohomologyIso_hom_app H.right]
    rfl
  have he' : (lieCohomologyIso.{u,v,w} k g (n+1)).hom.app S.X₁ =
      L₁.hom ≫ (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.left) (n+1)).toModuleIso.hom := by
    rw [lieCohomologyIso_hom_app H.left]
    rfl
  let B₃ := (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.right) n).toModuleIso
  let B₁ := (lieResolutionCohomologyEquiv (moduleInjectiveResolution H.left) (n+1)).toModuleIso
  have he'' : (lieCohomologyIso.{u,v,w} k g n).inv.app S.X₃ ≫ L₃.hom = B₃.inv := by
    rw [← cancel_mono B₃.hom, Category.assoc, ← he, Iso.inv_hom_id_app, Iso.inv_hom_id]
  rw [he', reassoc_of% hR', reassoc_of% he'']
  exact lieResolutionCohomology_connecting hS H n δ.hom hδ

variable (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]

private theorem ambientCohomologyIso_connectors :
    PreservesCEConnectors (chevalleyEilenberg.{u,v,w} k g).functor
      (rightValue (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h))
      (rightBoundary (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h))
      (ambientCohomologyIso h) := by
  intro S hS
  obtain ⟨hE, hδ⟩ := lieCohomologyIso_connectors (k := k) (g := g) hS
  refine ⟨hE, fun n => ?_⟩
  have h := rightValueNatIso_boundary (compositeInvariantsEvaluationIso h) hS n
  simpa only [ambientCohomologyIso, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, reassoc_of% h, Iso.inv_hom_id_app_assoc] using hδ n

end ExteriorConnectors

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Shared.Lie
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)

/-- Restriction carries a horseshoe to its degreewise split horseshoe
of injective resolutions for the ideal algebra. -/
private def restrictIdealHorseshoe
    {S : ShortComplex (ModuleCat.{max u v w} (U k g))}
    (H : InjectiveHorseshoe S) :
    InjectiveHorseshoe (S.map (restrictIdeal.{u,v,w} h)) where
  left := restrictIdealResolution h H.left
  middle := restrictIdealResolution h H.middle
  right := restrictIdealResolution h H.right
  inclusion := restrictIdealResolutionHom h H.inclusion
  projection := restrictIdealResolutionHom h H.projection
  zero := by
    let R := (restrictIdeal.{u,v,w} h).mapHomologicalComplex (.up ℕ)
    change R.map H.inclusion.hom ≫ R.map H.projection.hom = 0
    rw [← R.map_comp, H.zero, R.map_zero]
  splitting n := (H.splitting n).map (restrictIdeal.{u,v,w} h)

variable [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
private theorem idealCohomologyIso_connectors :
    PreservesCEConnectors (restrictIdeal.{u,v,w} h ⋙ (chevalleyEilenberg.{u,v,w} k h).functor)
      (fun n => rightValue (idealInvariants.{u,v,w} h) n ⋙ underlying k (g ⧸ h))
      (fun hS n => (underlying k (g ⧸ h)).map (rightBoundary (idealInvariants.{u,v,w} h) hS n))
      (idealCohomologyIso h) := by
  intro S hS
  refine ⟨(chevalleyEilenberg.{u,v,w} k h).restrict_degreewiseExact h hS, ?_⟩
  intro n
  let F := idealInvariants.{u,v,w} h
  let W := underlying k (g ⧸ h)
  let R := restrictIdeal.{u,v,w} h
  let K := F.mapHomologicalComplex (.up ℕ)
  let V := W.mapHomologicalComplex (.up ℕ)
  let I := (lieInvariants.{u,v,w} k h).mapHomologicalComplex (.up ℕ)
  let Q (t : ℕ) : CochainComplex (ModuleCat.{max u v w} k) ℕ ⥤ ModuleCat.{max u v w} k :=
    quotientHomology (.up ℕ) t
  let H := injectiveHorseshoe hS
  let Hr := restrictIdealHorseshoe h H
  have hSr : (S.map R).ShortExact := hS.map_of_exact R
  let T := H.shortComplex.map K
  let T' := T.map V
  let B := Hr.shortComplex.map I
  let hT := H.map_shortExact F
  let hE := extendShortExact hT
  let J₃ := moduleQuotientHomologyIso T.X₃ n
  let J₁ := moduleQuotientHomologyIso T.X₁ (n+1)
  let E₃ := extendQuotientHomologyIso T.X₃ n
  let E₁ := extendQuotientHomologyIso T.X₁ (n+1)
  let δ : (quotientHomology (.up ℕ) n).obj T.X₃ ⟶
      (quotientHomology (.up ℕ) (n+1)).obj T.X₁ :=
    E₃.inv ≫ hE.δ (n : ℤ) ((n+1 : ℕ) : ℤ) (by simp) ≫ E₁.hom
  have hδ : Connecting T.f T.g n (n+1) δ.hom := extendBoundary_connecting hE n
  let L₃ := rightValueResolutionIso F n H.right ≪≫ J₃
  let L₁ := rightValueResolutionIso F (n+1) H.left ≪≫ J₁
  have hR := rightValueResolutionBoundary F hS H.inclusion H.projection H.zero
    H.shortExact hT n
  have hR' : rightBoundary F hS n ≫ L₁.hom = L₃.hom ≫ δ := by
    simp only [L₁, L₃, J₁, J₃, E₁, E₃, δ, T, K, extendQuotientHomologyIso,
      Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]
    exact (reassoc_of% hR) _
  let W₃ := restrictQuotientHomology (algebraMap k (U k (g ⧸ h))) T.X₃ n
  let W₁ := restrictQuotientHomology (algebraMap k (U k (g ⧸ h))) T.X₁ (n+1)
  let δW := W₃.inv ≫ W.map δ ≫ W₁.hom
  have hδW : Connecting T'.f T'.g n (n+1) δW.hom :=
    restrictQuotientBoundary_connecting (algebraMap k (U k (g ⧸ h))) T n (n+1) δ hδ
  let P₃ := idealResolutionValueIso h H.right n
  let P₁ := idealResolutionValueIso h H.left (n+1)
  have hRW : W.map (rightBoundary F hS n) ≫ P₁.hom = P₃.hom ≫ δW := by
    change W.map (rightBoundary F hS n) ≫ W.map L₁.hom ≫ W₁.hom =
      (W.map L₃.hom ≫ W₃.hom) ≫ W₃.inv ≫ W.map δ ≫ W₁.hom
    rw [← W.map_comp_assoc, hR', W.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let e₁ := idealToLieInvariantsComplex h H.left.cocomplex
  let e₂ := idealToLieInvariantsComplex h H.middle.cocomplex
  let e₃ := idealToLieInvariantsComplex h H.right.cocomplex
  let e : T' ≅ B := ShortComplex.isoMk e₁ e₂ e₃
    (idealToLieInvariantsComplex_natural h H.inclusion.hom).symm
    (idealToLieInvariantsComplex_natural h H.projection.hom).symm
  let U₃ := (Q n).mapIso e₃
  let U₁ := (Q (n+1)).mapIso e₁
  let δr := U₃.inv ≫ δW ≫ U₁.hom
  have hδr : Connecting B.f B.g n (n+1) δr.hom :=
    connecting_of_shortComplexIso e n (n+1) δW hδW
  let C₃ := (lieResolutionCohomologyEquiv
      (moduleInjectiveResolution (restrictIdealResolution h H.right)) n).toModuleIso
  let C₁ := (lieResolutionCohomologyEquiv
      (moduleInjectiveResolution (restrictIdealResolution h H.left)) (n+1)).toModuleIso
  have hCE := lieResolutionCohomology_connecting hSr Hr n δr.hom hδr
  have h₃ : (idealCohomologyIso h n).inv.app S.X₃ = C₃.inv ≫ U₃.inv ≫ P₃.inv := by
    change ((idealCohomologyIso h n).app S.X₃).inv = _
    rw [idealCohomologyIso_app h H.right n]
    rfl
  have h₁ : (idealCohomologyIso h (n+1)).hom.app S.X₁ = P₁.hom ≫ U₁.hom ≫ C₁.hom := by
    change ((idealCohomologyIso h (n+1)).app S.X₁).hom = _
    rw [idealCohomologyIso_app h H.left (n+1)]
    rfl
  have hc :
      (idealCohomologyIso h n).inv.app S.X₃ ≫ W.map (rightBoundary F hS n) ≫
          (idealCohomologyIso h (n+1)).hom.app S.X₁ =
        C₃.inv ≫ δr ≫ C₁.hom := by
    simp only [h₃, h₁, Category.assoc, reassoc_of% hRW,
      Iso.inv_hom_id_assoc, δr]
  change Connecting _ _ n (n+1)
    (((idealCohomologyIso h n).inv.app S.X₃ ≫ W.map (rightBoundary F hS n) ≫
      (idealCohomologyIso h (n+1)).hom.app S.X₁).hom)
  rw [hc]
  exact hCE

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Category HomologicalComplex
open Shared.Lie
open AdvancedHomologicalAlgebra.GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
namespace AdvancedHomologicalAlgebra.LieHochschildSerre
section OrdinaryAugmentation
universe u v
variable {B : Type u} [Category.{v} B] [Abelian B]

theorem extendSingleHomology (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))
    (h : e.f (0 : ℕ) = (0 : ℤ)) (Y : B) :
    (singleObjHomologySelfIso (.up ℤ) 0 Y).inv ≫
      homologyMap (extendSingleIso e Y 0 0 h).inv 0 ≫
      (((CochainComplex.single₀ B).obj Y).extendHomologyIso e h).hom =
      (singleObjHomologySelfIso (.up ℕ) 0 Y).inv := by
  let C := (CochainComplex.single₀ B).obj Y
  let D := (CochainComplex.singleFunctor B 0).obj Y
  let s := (extendSingleIso e Y 0 0 h).inv
  rw [← singleObjCyclesSelfIso_inv_homologyπ (.up ℤ) 0 Y,
    ← singleObjCyclesSelfIso_inv_homologyπ (.up ℕ) 0 Y]
  simp only [Category.assoc, homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom]
  have hs : (singleObjCyclesSelfIso (.up ℤ) 0 Y).inv ≫ cyclesMap s 0 ≫
        (C.extendCyclesIso e h).hom = (singleObjCyclesSelfIso (.up ℕ) 0 Y).inv := by
    rw [← cancel_mono (C.iCycles 0)]
    rw [Category.assoc, Category.assoc, extendCyclesIso_hom_iCycles,
      cyclesMap_i_assoc]
    change (singleObjCyclesSelfIso (.up ℤ) 0 Y).inv ≫ D.iCycles 0 ≫
        s.f 0 ≫ (C.extendXIso e h).hom =
      (singleObjCyclesSelfIso (.up ℕ) 0 Y).inv ≫ C.iCycles 0
    rw [singleObjCyclesSelfIso_inv_iCycles_assoc, singleObjCyclesSelfIso_inv_iCycles]
    dsimp only [s]
    erw [extendSingleIso_inv_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [(C.extendXIso e h).inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ C.homologyπ 0) hs

section ZeroStalkClasses
variable {R : Type*} [Ring R]
  {C : CochainComplex (ModuleCat.{v} R) ℕ} {Y : ModuleCat.{v} R}

def augmentationCycle (f : (CochainComplex.single₀ (ModuleCat.{v} R)).obj Y ⟶ C) (y : Y) :
    P103.Specs.Ch10.Complexes.cycles C 0 :=
  P103.Specs.Ch10.Complexes.cyclesMap f 0
    ⟨(singleObjXSelf (.up ℕ) 0 Y).inv y, by rfl⟩

theorem augmentationCycle_val (f : (CochainComplex.single₀ (ModuleCat.{v} R)).obj Y ⟶ C) (y : Y) :
    (augmentationCycle f y).val = f.f 0 ((singleObjXSelf (.up ℕ) 0 Y).inv y) := rfl

theorem ordinaryAugmentation_homologyClass
    (f : (CochainComplex.single₀ (ModuleCat.{v} R)).obj Y ⟶ C)
    (j : C.homology 0 ⟶ (quotientHomology (.up ℕ) 0).obj C)
    (hj : C.homologyπ 0 ≫ j = (C.sc 0).moduleCatCyclesIso.hom ≫
        ModuleCat.ofHom (homologyClass C 0)) (y : Y) :
    ((singleObjHomologySelfIso (.up ℕ) 0 Y).inv ≫
      HomologicalComplex.homologyMap f 0 ≫ j) y = homologyClass C 0 (augmentationCycle f y) := by
  let K := (CochainComplex.single₀ (ModuleCat.{v} R)).obj Y
  rw [← singleObjCyclesSelfIso_inv_homologyπ (.up ℕ) 0 Y,
    Category.assoc, homologyπ_naturality_assoc, hj]
  change (homologyClass C 0) ((C.sc 0).moduleCatCyclesIso.hom
    (HomologicalComplex.cyclesMap f 0 ((singleObjCyclesSelfIso (.up ℕ) 0 Y).inv y))) = _
  congr 1
  apply Subtype.ext
  change ((C.sc 0).moduleCatLeftHomologyData.i.hom
    ((C.sc 0).moduleCatCyclesIso.hom
      (HomologicalComplex.cyclesMap f 0 ((singleObjCyclesSelfIso (.up ℕ) 0 Y).inv y)))) = _
  have h := (C.sc 0).moduleCatCyclesIso_hom_i
  have h' := congrArg (fun g => g (HomologicalComplex.cyclesMap f 0
    ((singleObjCyclesSelfIso (.up ℕ) 0 Y).inv y))) h
  change _ = (C.iCycles 0) (HomologicalComplex.cyclesMap f 0
    ((singleObjCyclesSelfIso (.up ℕ) 0 Y).inv y)) at h'
  erw [h', augmentationCycle_val]
  have hh : (singleObjCyclesSelfIso (.up ℕ) 0 Y).inv ≫
      HomologicalComplex.cyclesMap f 0 ≫ C.iCycles 0 =
      (singleObjXSelf (.up ℕ) 0 Y).inv ≫ f.f 0 := by
    rw [cyclesMap_i, singleObjCyclesSelfIso_inv_iCycles_assoc]
  exact congrArg (fun g : Y ⟶ C.X 0 => g y) hh
end ZeroStalkClasses

section ExtAugmentation
open P103.Specs.Ch11.ExtBalance P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.ExtExactSequences P103.Ch11.ExtBalance

universe s a b
variable {S : Type s} [Ring S] {X : Type a} {V : Type b}
  [AddCommGroup X] [Module S X] [AddCommGroup V] [Module S V]
variable (P : LeftResolution S X) (I : P103.Specs.Ch10.Comparison.InjectiveResolution S V)

def injectiveAugmentationCycle (f : X →ₗ[S] V) :
    P103.Specs.Ch10.Complexes.cycles (injectiveHom X I.complex) 0 :=
  ⟨I.η.comp f, by
    change ((injectiveHom X I.complex).d 0 ((ComplexShape.up ℕ).next 0)).hom (I.η.comp f) = 0
    rw [CochainComplex.next]
    change ((I.complex.d 0 1).hom.comp (I.η.comp f)) = 0
    ext x
    exact (I.exact_zero _).2 ⟨f x, rfl⟩⟩

theorem balance_zero_apply [Small.{b} S] (hP : P.IsProjective) (f : X →ₗ[S] V)
    (e : Homology (injectiveHom X I.complex) 0 ≃ₗ[ℤ] ExtWith P V 0)
    (he : (P103.Specs.Ch10.Complexes.homologyMap (projectiveAugmentation P I) 0).comp
      e.toLinearMap = P103.Specs.Ch10.Complexes.homologyMap (injectiveAugmentation P I) 0) :
    e (homologyClass _ 0 (injectiveAugmentationCycle I f)) = homClass P V f := by
  apply (projectiveAugmentation_quasiIso P I hP 0).injective
  have h := DFunLike.congr_fun he (homologyClass _ 0 (injectiveAugmentationCycle I f))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [h]
  change homologyClass _ 0 (P103.Specs.Ch10.Complexes.cyclesMap
      (injectiveAugmentation P I) 0 (injectiveAugmentationCycle I f)) =
    homologyClass _ 0 (P103.Specs.Ch10.Complexes.cyclesMap
      (projectiveAugmentation P I) 0
        ((P103.HomTensorExactness.pre P.ε).toIntLinearMap.codRestrict _ _ f))
  apply congrArg (homologyClass _ 0)
  apply Subtype.ext
  change (injectiveAugmentation P I).f 0 (I.η.comp f) =
    (projectiveAugmentation P I).f 0 (f.comp P.ε)
  rw [injectiveAugmentation_formula P I 0, projectiveAugmentation_formula P I 0]
  rfl

end ExtAugmentation

end OrdinaryAugmentation
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex
open GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtBalance P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.ExtExactSequences P103.Ch11.ExtBalance

section ResolutionAugmentationAtZero
variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) [F.Additive]

@[reassoc]
theorem rightValueResolutionIso_degreeZeroUnit {X : A} (I : CategoryTheory.InjectiveResolution X) :
    (degreeZeroUnit F).app X ≫ (rightValueResolutionIso F 0 I).hom =
      (singleObjHomologySelfIso (.up ℕ) 0 (F.obj X)).inv ≫
        HomologicalComplex.homologyMap (mappedResolutionAugmentationNat F I) 0 := by
  let E := resolutionEmbedding
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let C := (stalkComplex B).obj (F.obj X)
  let m := mappedResolutionAugmentation F I
  let b := mapExtendIso F E I.cocomplex
  let d := K.extendHomologyIso E (show E.f (0 : ℕ) = (0 : ℤ) from rfl)
  let z := (extendSingleIso E (F.obj X) 0 0 rfl).inv
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let H' := HomologicalComplex.homologyFunctor B (.up ℤ) 0
  let u := (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).app (F.obj X)
  let s := singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)
  let i := (plusHomologyFactors B 0).app C
  have hu : u.hom = i.hom ≫ s.hom := by
    simp [u, i, s, DerivedCategory.singleFunctorCompHomologyFunctorIso, plusHomologyFactors,
      DerivedCategory.singleFunctorsPostcompQIso]
    rfl
  have hu' : u.inv ≫ i.hom = s.inv := by
    apply (cancel_mono s.hom).mp
    rw [Category.assoc, ← hu, Iso.inv_hom_id, Iso.inv_hom_id]
  have hq : H.map ((DerivedCategory.Plus.Q (C := B)).map m) ≫
      (plusHomologyFactors B 0).hom.app (F.mapCochainComplexPlus.obj (resolutionPlus I)) =
      i.hom ≫ H'.map m.hom :=
    (plusHomologyFactors B 0).hom.naturality m
  have hm : m.hom ≫ b.hom = z ≫ extendMap (mappedResolutionAugmentationNat F I) E := by
    change ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app X ≫
      (F.mapHomologicalComplex (.up ℤ)).map ((extendSingleIso E X 0 0 rfl).inv ≫
        extendMap I.ι E)) ≫ b.hom = _
    simp only [Functor.map_comp, Category.assoc, mappedResolutionAugmentationNat, extendMap_comp]
    rw [mapExtendIso_natural, ← Category.assoc, ← Category.assoc]
    dsimp only [z, E]
    rw [← Category.assoc (extendSingleIso resolutionEmbedding (F.obj X) 0 0 rfl).inv,
      extend_map_stalk F]
    simp only [Category.assoc]
  change (u.inv ≫ H.map ((stalkToDerived F).app X)) ≫ _ = _
  simp only [rightValueResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change u.inv ≫ H.map ((stalkToDerived F).app X) ≫
    H.map (rightDerivedResolutionIso F I).hom ≫
      (plusHomologyFactors B 0).hom.app (F.mapCochainComplexPlus.obj (resolutionPlus I)) ≫
        H'.map b.hom ≫ d.hom = _
  rw [← H.map_comp_assoc, stalkToDerived_on_resolution F I]
  rw [reassoc_of% hq, reassoc_of% hu', ← H'.map_comp_assoc, hm, H'.map_comp]
  have hn := extendHomologyIso_hom_naturality (mappedResolutionAugmentationNat F I) E
    (show E.f (0 : ℕ) = (0 : ℤ) from rfl)
  change s.inv ≫ (H'.map z ≫ H'.map (extendMap (mappedResolutionAugmentationNat F I) E)) ≫ d.hom = _
  simp only [Category.assoc]
  erw [hn]
  change (singleObjHomologySelfIso (.up ℤ) 0 (F.obj X)).inv ≫
    HomologicalComplex.homologyMap (extendSingleIso E (F.obj X) 0 0 rfl).inv 0 ≫
      (((CochainComplex.single₀ B).obj (F.obj X)).extendHomologyIso E rfl).hom ≫
        HomologicalComplex.homologyMap (mappedResolutionAugmentationNat F I) 0 = _
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ HomologicalComplex.homologyMap (mappedResolutionAugmentationNat F I) 0)
    (extendSingleHomology E rfl (F.obj X))

end ResolutionAugmentationAtZero

section ModuleResolutionAugmentation
universe b a c
variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
  {R : Type b} [Ring R] [HasDerivedCategory.{a} (ModuleCat.{c} R)]
  [EnoughInjectives (ModuleCat.{c} R)]
  (F : A ⥤ ModuleCat.{c} R) [F.Additive]

theorem rightValueResolutionIso_class {X : A} (I : CategoryTheory.InjectiveResolution X)
    (y : F.obj X) :
    let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    ((degreeZeroUnit F).app X ≫ (rightValueResolutionIso F 0 I).hom ≫
      (moduleQuotientHomologyIso K 0).hom) y =
      homologyClass K 0 (augmentationCycle (mappedResolutionAugmentationNat F I) y) := by
  dsimp only
  rw [← Category.assoc, rightValueResolutionIso_degreeZeroUnit F I, Category.assoc]
  exact ordinaryAugmentation_homologyClass _ _ (moduleQuotientHomologyIso_π _ _) y

omit [HasDerivedCategory A] [EnoughInjectives A]
  [HasDerivedCategory.{a} (ModuleCat.{c} R)] [EnoughInjectives (ModuleCat.{c} R)] in
theorem mappedResolutionAugmentationCycle_val {X : A} (I : CategoryTheory.InjectiveResolution X)
    (y : F.obj X) :
    (augmentationCycle (mappedResolutionAugmentationNat F I) y).val =
      F.map ((singleObjXSelf (.up ℕ) 0 X).inv ≫ I.ι.f 0) y := by
  rw [augmentationCycle_val]
  have h : (singleObjXSelf (.up ℕ) 0 (F.obj X)).inv ≫ (mappedResolutionAugmentationNat F I).f 0 =
      F.map ((singleObjXSelf (.up ℕ) 0 X).inv ≫ I.ι.f 0) := by
    simp only [mappedResolutionAugmentationNat, HomologicalComplex.comp_f,
      singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f,
      Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  exact congrArg (fun f => f y) h
end ModuleResolutionAugmentation

section LieAugmentationAtZero
universe u v w
attribute [local instance 2000] CE.Ext.trivialModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  {M : ModuleCat.{max u v w} (U k g)}

theorem lieResolutionCohomologyEquiv_augmented
    (I : P103.Specs.Ch10.Comparison.InjectiveResolution (U k g) M)
    (t : (lieInvariants.{u,v,w} k g).obj M) (x : P103.Specs.Ch10.Complexes.cycles (lieInvComplex I) 0)
    (hx : ∀ a : k, (show (lieInvariants.{u,v,w} k g).obj (I.complex.X 0) from x.val) a =
      I.η (t a)) :
    ∃ z : P103.Specs.Ch10.Complexes.cycles ((chevalleyEilenberg.{u,v,w} k g).complex M) 0,
      z.val (CE.wedge k g 0 Fin.elim0) = t (1 : k) ∧
      lieResolutionCohomologyEquiv I 0 (homologyClass _ 0 x) = homologyClass _ 0 z := by
  let D := (chevalleyEilenberg.{u,v,w} k g).complex M
  let P := lieProjectiveResolution (k := k) (g := g)
  let a := ModuleCat.CoextendScalars.equiv (Shared.Lie.augmentation k g).toRingHom M t
  let y : P103.Specs.Ch10.Complexes.cycles (homComplex P.complex M) 0 :=
    (P103.HomTensorExactness.pre P.ε).toIntLinearMap.codRestrict _ (by
      intro f
      change ((homComplex P.complex M).d 0 ((ComplexShape.up ℕ).next 0)).hom _ = 0
      rw [CochainComplex.next]
      change (f.comp P.ε).comp (P.complex.d 1 0).hom = 0
      ext b
      have h : (P.complex.d 1 0).hom b ∈ LinearMap.ker P.ε := by
        rw [← P.exact_zero]
        exact ⟨b, rfl⟩
      change f (P.ε ((P.complex.d 1 0).hom b)) = 0
      rw [h, map_zero]) a
  let z := (integerCyclesEquiv D 0).symm
    (P103.Specs.Ch10.Complexes.cyclesMap (lieEvaluationIso M).hom 0 y)
  refine ⟨z, ?_, ?_⟩
  · change a (CE.augmentation k g ((1 : U k g) ⊗ₜ[k] CE.wedge k g 0 Fin.elim0)) = t (1 : k)
    simp only [CE.augmentation_tmul, CE.wedge, exteriorPower.zeroEquiv_ιMulti, map_one, mul_one] <;> rfl
  · apply (integerHomologyEquiv D 0).injective
    rw [lieResolutionCohomologyEquiv_integer I]
    rw [integerHomologyEquiv_class, integerHomologyEquiv_class]
    have hcycle : P103.Specs.Ch10.Complexes.cyclesMap (lieInjectiveHomIso I).inv 0
        (integerCyclesEquiv (lieInvComplex I) 0 x) = injectiveAugmentationCycle I a := by
      apply Subtype.ext
      apply LinearMap.ext
      exact hx
    change P103.Specs.Ch10.Complexes.homologyMap (lieEvaluationIso M).hom 0
      (lieResolutionBalance I 0 (homologyClass _ 0
        (P103.Specs.Ch10.Complexes.cyclesMap (lieInjectiveHomIso I).inv 0
          (integerCyclesEquiv (lieInvComplex I) 0 x)))) = _
    rw [hcycle, balance_zero_apply P I lieProjectiveResolution_projective a
      (lieResolutionBalance I 0) (lieResolutionBalance_formula I 0)] <;> rfl

variable [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

theorem lieCohomologyIso_augmentation :
    PreservesCEAugmentation.{u,v,w} (𝟭 _) (chevalleyEilenberg.{u,v,w} k g)
      (degreeZeroUnit (lieInvariants.{u,v,w} k g))
      (fun M m => (show (lieInvariants.{u,v,w} k g).obj M from m) (1 : k))
      (lieCohomologyIso k g 0) := by
  intro M t
  let F := lieInvariants.{u,v,w} k g
  let I := CategoryTheory.injectiveResolution M
  let x := augmentationCycle (mappedResolutionAugmentationNat F I) t
  have hx := mappedResolutionAugmentationCycle_val F I t
  obtain ⟨z, hz, he⟩ := lieResolutionCohomologyEquiv_augmented (moduleInjectiveResolution I) t x (by
    intro a
    change (show F.obj (I.cocomplex.X 0) from x.val) a = _
    rw [hx] <;> rfl)
  refine ⟨z, hz, ?_⟩
  change (((degreeZeroUnit F).app M ≫ (lieCohomologyIso k g 0).hom.app M) t) =
    homologyClass _ 0 z
  rw [lieCohomologyIso_hom_app I 0]
  change (lieResolutionCohomologyEquiv (moduleInjectiveResolution I) 0
    (((degreeZeroUnit F).app M ≫ (rightValueResolutionIso F 0 I).hom ≫
      (moduleQuotientHomologyIso _ 0).hom) t)) = _
  rw [rightValueResolutionIso_class F I t]
  exact he

end LieAugmentationAtZero

section DerivedAugmentationNaturality
variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

theorem mappedResolutionAugmentationNat_natural (τ : F ⟶ G) {X : A}
    (I : CategoryTheory.InjectiveResolution X) :
    mappedResolutionAugmentationNat F I ≫
        (τ.mapHomologicalComplex (.up ℕ)).app I.cocomplex =
      (CochainComplex.single₀ B).map (τ.app X) ≫ mappedResolutionAugmentationNat G I := by
  apply HomologicalComplex.from_single_hom_ext
  change ((mappedResolutionAugmentationNat F I).f 0 ≫ τ.app (I.cocomplex.X 0)) =
    ((CochainComplex.single₀ B).map (τ.app X)).f 0 ≫ (mappedResolutionAugmentationNat G I).f 0
  rw [← cancel_epi (singleObjXSelf (.up ℕ) 0 (F.obj X)).inv]
  simp only [mappedResolutionAugmentationNat, HomologicalComplex.comp_f, single_map_f_self,
    singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp_assoc, ← G.map_comp]
  exact τ.naturality _

theorem rightValueNatIso_degreeZeroUnit (τ : F ≅ G) (X : A) :
    (degreeZeroUnit F).app X ≫ (rightValueNatIso τ 0).hom.app X =
      τ.hom.app X ≫ (degreeZeroUnit G).app X := by
  let I := CategoryTheory.injectiveResolution X
  let K := HomologicalComplex.homologyFunctor B (.up ℕ) 0
  apply (cancel_mono (rightValueResolutionIso G 0 I).hom).mp
  rw [Category.assoc, rightValueResolutionIso_natIso τ 0 I,
    rightValueResolutionIso_degreeZeroUnit_assoc F I, Category.assoc,
    rightValueResolutionIso_degreeZeroUnit G I]
  change (singleObjHomologySelfIso (.up ℕ) 0 (F.obj X)).inv ≫
    K.map (mappedResolutionAugmentationNat F I) ≫
      K.map ((τ.hom.mapHomologicalComplex (.up ℕ)).app I.cocomplex) =
    τ.hom.app X ≫ (singleObjHomologySelfIso (.up ℕ) 0 (G.obj X)).inv ≫
      K.map (mappedResolutionAugmentationNat G I)
  rw [← K.map_comp, mappedResolutionAugmentationNat_natural τ.hom I,
    K.map_comp, ← Category.assoc]
  erw [singleObjHomologySelfIso_inv_naturality (.up ℕ) 0 (τ.hom.app X)]
  exact Category.assoc _ _ _

end DerivedAugmentationNaturality

section CompositeAndIdealAugmentation
universe u v w
attribute [local instance 2000] CE.Ext.trivialModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

theorem ambientCohomologyIso_augmentation :
    PreservesCEAugmentation.{u,v,w} (𝟭 _) (chevalleyEilenberg.{u,v,w} k g)
      (degreeZeroUnit (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h))
      (fun M m =>
        (show (idealInvariants.{u,v,w} h).obj M from
          (show (quotientInvariants.{u,v,w} h).obj ((idealInvariants.{u,v,w} h).obj M) from m) (1 : k))
            (1 : U k (g ⧸ h)))
      (ambientCohomologyIso h 0) := by
  intro M m
  let T := compositeInvariantsEvaluationIso.{u,v,w} h
  let t := T.hom.app M m
  obtain ⟨z, hz, he⟩ := lieCohomologyIso_augmentation (k := k) (g := g) M t
  refine ⟨z, ?_, ?_⟩
  · change z.val (CE.wedge k g 0 Fin.elim0) = compositeInvariantsMap h M m (1 : k)
    exact hz
  · change (((degreeZeroUnit _).app M ≫ (rightValueNatIso T 0).hom.app M ≫
      (lieCohomologyIso.{u,v,w} k g 0).hom.app M) m) = _
    rw [← Category.assoc, rightValueNatIso_degreeZeroUnit T M]
    exact he

theorem restrictIdealResolution_augmentation_apply {M : ModuleCat.{max u v w} (U k g)}
    (I : CategoryTheory.InjectiveResolution M) (x : M) :
    (moduleInjectiveResolution (restrictIdealResolution h I)).η x =
      (moduleInjectiveResolution I).η x := by
  let W := restrictIdeal.{u,v,w} h
  have he := mappedResolutionAugmentationCycle_val W I x
  rw [augmentationCycle_val] at he
  exact he

theorem idealCohomologyIso_augmentation :
    PreservesCEAugmentation.{u,v,w} (restrictIdeal.{u,v,w} h) (chevalleyEilenberg.{u,v,w} k h)
      (whiskerRight (degreeZeroUnit (idealInvariants.{u,v,w} h)) (underlying k (g ⧸ h)))
      (fun M m => (show (idealInvariants.{u,v,w} h).obj M from m) (1 : U k (g ⧸ h)))
      (idealCohomologyIso h 0) := by
  intro M m
  let I := CategoryTheory.injectiveResolution M
  let F := idealInvariants.{u,v,w} h
  let Uq := underlying.{u,v,max u v w} k (g ⧸ h)
  let C := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let K := (Uq.mapHomologicalComplex (.up ℕ)).obj C
  let x := augmentationCycle (mappedResolutionAugmentationNat F I) m
  let x' : P103.Specs.Ch10.Complexes.cycles K 0 := ⟨x.val, x.property⟩
  let f := (idealToLieInvariantsComplex h I.cocomplex).hom
  let y := P103.Specs.Ch10.Complexes.cyclesMap f 0 x'
  let t := (idealToLieInvariants h M).hom m
  let L := moduleInjectiveResolution (restrictIdealResolution h I)
  have hx := mappedResolutionAugmentationCycle_val F I m
  have hy : ∀ a : k, (show (lieInvariants.{u,v,w} k h).obj (L.complex.X 0) from y.val) a =
      L.η (t a) := by
    intro a
    change ((idealToLieInvariants h (I.cocomplex.X 0)).hom x.val) a =
      (moduleInjectiveResolution (restrictIdealResolution h I)).η (t a)
    rw [hx, restrictIdealResolution_augmentation_apply]
    let η := (singleObjXSelf (.up ℕ) 0 M).inv ≫ I.ι.f 0
    have hn := congrArg (fun f => f m) (idealToLieInvariants_natural h η)
    change ((idealToLieInvariants h (I.cocomplex.X 0)).hom (F.map η m)) =
      (lieInvariants.{u,v,w} k h).map ((restrictIdeal.{u,v,w} h).map η) t at hn
    rw [hn] <;> rfl
  obtain ⟨z, hz, he⟩ := lieResolutionCohomologyEquiv_augmented L t y hy
  refine ⟨z, hz.trans (idealToLieInvariants_eval h M m), ?_⟩
  change (idealCohomologyIsoAt h I 0).hom ((degreeZeroUnit F).app M m) =
    homologyClass _ 0 z
  change lieResolutionCohomologyEquiv L 0
    (P103.Specs.Ch10.Complexes.homologyMap f 0
      ((restrictQuotientHomology (algebraMap k (U k (g ⧸ h))) C 0).hom
        (((degreeZeroUnit F).app M ≫ (rightValueResolutionIso F 0 I).hom ≫
          (moduleQuotientHomologyIso C 0).hom) m))) = _
  rw [rightValueResolutionIso_class F I m]
  exact he

end CompositeAndIdealAugmentation

end AdvancedHomologicalAlgebra.LieHochschildSerre
end

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Shared.Lie
open AdvancedHomologicalAlgebra.GrothendieckEdges AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem firstQuadrant_all_pages {C : Type*} [Category* C] [Abelian C]
    (X : RowDiagram C) (base : G05FilteredEdges.FirstQuadrant X) :
    ∀ (r : ℕ) (p n : ℤ), p < 0 ∨ n < p → IsZero (X.page r p n) := by
  intro r
  induction r with
  | zero => exact base
  | succ r ih =>
    intro p n hp
    let p' : ℤ := p - ((r : ℤ) + 2)
    let n' : ℤ := n - 1
    have ep : p' + ((r : ℤ) + 2) = p := sub_add_cancel _ _
    have en : n' + 1 = n := sub_add_cancel _ _
    have hm : IsZero (X.page r (p' + ((r : ℤ) + 2)) (n' + 1)) := by
      rw [ep, en]
      exact ih p n hp
    have hz := (X.pageComplex r p' n').isZero_homology_of_isZero_X₂ hm
    have hs := IsZero.of_iso hz (X.nextIso r p' n')
    rwa [ep, en] at hs

/-- Exactness is preserved by replacing the terms by isomorphic coordinates. -/
private theorem conjugateClassicalFiveTerms {C : Type*} [Category* C] [Abelian C]
    {X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ Y₃ Y₄ Y₅ : C}
    {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃} {d : Y₃ ⟶ Y₄} {h : Y₄ ⟶ Y₅}
    (H : ClassicalFiveTerms f g d h)
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄) (e₅ : X₅ ≅ Y₅) :
    ClassicalFiveTerms
      (e₁.hom ≫ f ≫ e₂.inv) (e₂.hom ≫ g ≫ e₃.inv)
      (e₃.hom ≫ d ≫ e₄.inv) (e₄.hom ≫ h ≫ e₅.inv) := by
  let := H.mono
  have hfg : (e₁.hom ≫ f ≫ e₂.inv) ≫ (e₂.hom ≫ g ≫ e₃.inv) = 0 := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% H.fg, zero_comp, comp_zero]
  have hgd : (e₂.hom ≫ g ≫ e₃.inv) ≫ (e₃.hom ≫ d ≫ e₄.inv) = 0 := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% H.gd, zero_comp, comp_zero]
  have hdh : (e₃.hom ≫ d ≫ e₄.inv) ≫ (e₄.hom ≫ h ≫ e₅.inv) = 0 := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% H.dh, zero_comp, comp_zero]
  exact {
    mono := inferInstance
    fg := hfg
    gd := hgd
    dh := hdh
    exact_f_g := G05FilteredEdges.exact_conjugate e₁ e₂ e₃ _ _ _ H.exact_f_g hfg
    exact_g_d := G05FilteredEdges.exact_conjugate e₂ e₃ e₄ _ _ _ H.exact_g_d hgd
    exact_d_h := G05FilteredEdges.exact_conjugate e₃ e₄ e₅ _ _ _ H.exact_d_h hdh }

open CategoryTheory.Functor
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence

private theorem CEComparison.fiveTerms
    {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g)
    [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
    [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
    [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]
    {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
    {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
    {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
    {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
    (J : CEComparison h Dg Dh Dq E P O) (M : ModuleCat.{max u v w} (U k g)) :
    ClassicalFiveTerms
      ((quotientHomology (.up ℕ) 1).map (E.inflation.app M))
      ((J.restrictToInvariants h 1).app M) (J.transgression h M)
      ((quotientHomology (.up ℕ) 2).map (E.inflation.app M)) := by
  let eRow (n : ℕ) := ((J.quotient n).app ((idealInvariants.{u,v,w} h).obj M)).symm
  let eTarget (n : ℕ) := ((J.ambient n).app M).symm
  have hInflation (n : ℕ) :
      (eRow n).hom ≫ (derivedFirstEdge _ _ P n).app M ≫ (eTarget n).inv =
        (quotientHomology (.up ℕ) n).map (E.inflation.app M) := by
    dsimp only [eRow, eTarget, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv]
    rw [← J.inflation_edge M n]
    exact ((J.quotient n).app ((idealInvariants.{u,v,w} h).obj M)).inv_hom_id_assoc _
  have HH := conjugateClassicalFiveTerms (O.fiveTerms M) (eRow 1) (eTarget 1)
    (Iso.refl _) (eRow 2) (eTarget 2)
  rw [hInflation, hInflation] at HH
  simpa only [eTarget, eRow, CEComparison.restrictToInvariants, CEComparison.transgression,
    CEComparison.rowIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.symm_inv,
    Iso.app_inv, Iso.app_hom, Iso.refl_inv, Iso.refl_hom, isoWhiskerLeft_hom, whiskerLeft_app,
    Category.comp_id, Category.id_comp, Category.assoc] using HH

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Shared.Lie

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
  (h : LieIdeal k g)
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

def cohomologyComparison :
    CohomologyComparison h (chevalleyEilenberg.{u,v,w} k g)
      (chevalleyEilenberg.{u,v,w} k h) (chevalleyEilenberg.{u,v,w} k (g ⧸ h)) where
  ambient := ambientCohomologyIso h
  ideal := idealCohomologyIso h
  quotient := lieCohomologyIso k (g ⧸ h)
  quotientInclusion := lieInvariantInclusion k (g ⧸ h)
  ambient_augmentation := ambientCohomologyIso_augmentation h
  ambient_connectors := ambientCohomologyIso_connectors h
  ideal_augmentation := idealCohomologyIso_augmentation h
  ideal_connectors := idealCohomologyIso_connectors h
  quotient_augmentation := lieCohomologyIso_augmentation
  quotient_connectors := lieCohomologyIso_connectors
  ideal_action M n y z := idealCohomologyIso_action h n y z

end AdvancedHomologicalAlgebra.LieHochschildSerre

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Shared.Lie

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing

theorem ce_cohomology_comparison : CohomologyComparisonStatement.{u,v,w} := by
  intro k g _ _ _ h
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k g))
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k (g ⧸ h)))
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
  exact ⟨chevalleyEilenberg k g, chevalleyEilenberg k h, chevalleyEilenberg k (g ⧸ h),
    ⟨cohomologyComparison h⟩⟩

/-- The Hochschild–Serre spectral sequence for every ideal of a Lie
algebra over a field, with its cochain edges and the induced five terms. -/
theorem hochschild_serre : FullStatement.{u,v,w} := by
  intro k g _ _ _ h
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k g))
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k (g ⧸ h)))
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
  obtain ⟨P, ⟨O⟩⟩ := derived_spectral_sequence.{u,v,w} k g h
  let J : CEComparison h (chevalleyEilenberg.{u,v,w} k g)
      (chevalleyEilenberg.{u,v,w} k h) (chevalleyEilenberg.{u,v,w} k (g ⧸ h))
      (edgeCochains.{u,v,w} h) P O :=
    { toCohomologyComparison := cohomologyComparison h
      inflation_edge := inflation_edge_comparison h P
      restriction_edge := restriction_edge_comparison h P O }
  refine ⟨_, _, _, _, P, O, J, ?_, CEComparison.fiveTerms h J⟩
  intro M
  exact firstQuadrant_all_pages _ (O.objectCase.quadrant M)

end AdvancedHomologicalAlgebra.LieHochschildSerre

end
