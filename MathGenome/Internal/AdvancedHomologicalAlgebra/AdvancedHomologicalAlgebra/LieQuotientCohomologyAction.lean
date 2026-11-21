import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieQuotientCohomologyAction
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import Mathlib.LinearAlgebra.Basis.VectorSpace
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.IdealEnvelopingFreeness
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtBalance

set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] AdvancedHomologicalAlgebra.LieQuotientAction.resolutionTermModule
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w w'
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]

/-- Stability of ideal invariants under the ambient Lie algebra. -/
theorem invariant_stable (ρ : Representation k g M) (y : g) (m : invariants h ρ) :
    ρ y (m : M) ∈ invariants h ρ := by
  intro a
  have hc := congrArg (fun T : Module.End k M => T (m : M)) (ρ.map_lie a y)
  have ha := m.property a
  have hb := m.property ⟨⁅(a : g), y⁆, lie_mem_left k g h _ _ a.property⟩
  change ρ (a : g) (ρ y (m : M)) = 0
  change ρ ⁅(a : g), y⁆ (m : M) =
    ρ (a : g) (ρ y (m : M)) - ρ y (ρ (a : g) (m : M)) at hc
  rw [ha, map_zero, sub_zero, hb] at hc
  exact hc.symm

/-- The ambient representation on the invariant subspace. -/
def invariantAmbient (ρ : Representation k g M) :
    Representation k g (invariants h ρ) where
  toFun y :=
    { toFun m := ⟨ρ y m, invariant_stable h ρ y m⟩
      map_add' _ _ := by ext; exact map_add (ρ y) _ _
      map_smul' _ _ := by ext; exact map_smul (ρ y) _ _ }
  map_add' y z := by ext m; exact LinearMap.congr_fun (ρ.map_add y z) m
  map_smul' r y := by ext m; exact LinearMap.congr_fun (ρ.map_smul r y) m
  map_lie' {y z} := by ext m; exact LinearMap.congr_fun (ρ.map_lie y z) m

/-- Factoring the ambient representation through the ideal quotient. -/
def invariantQuotient (ρ : Representation k g M) :
    Representation k (g ⧸ h) (invariants h ρ) :=
  { h.toSubmodule.liftQ (invariantAmbient h ρ).toLinearMap (by
      intro a ha
      apply LinearMap.ext
      intro m
      apply Subtype.ext
      exact m.property ⟨a, ha⟩) with
    map_lie' := by
      intro y z
      induction y using Submodule.Quotient.induction_on with | _ y =>
      induction z using Submodule.Quotient.induction_on with | _ z =>
      exact (invariantAmbient h ρ).map_lie y z }

theorem invariantQuotient_formula (ρ : Representation k g M) :
    IsInvariantAction h ρ (invariantQuotient h ρ) := by
  intro y m
  rfl

theorem invariantAction_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.invariantActionExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ
  exact ⟨invariantQuotient h ρ, invariantQuotient_formula h ρ⟩

variable (ρ : Representation k g M)
  (σ : Representation k (g ⧸ h) (invariants h ρ)) (hσ : IsInvariantAction h ρ σ)
  {N : Type w'} [AddCommGroup N] [Module k N]
  (τ : Representation k (g ⧸ h) N)

/-- A map from an inflated module lands in the invariant subspace. -/
def adjunctionForward (f : Morphism (inflation h τ) ρ) : Morphism τ σ := by
  refine ⟨{ toFun := fun n => ⟨f.val n, ?_⟩
            map_add' := fun x y => Subtype.ext (f.val.map_add x y)
            map_smul' := fun r n => Subtype.ext (f.val.map_smul r n) }, ?_⟩
  · intro a
    have hf := f.property (a : g) n
    have hz : quotientMap k g h (a : g) = 0 :=
      (Submodule.Quotient.mk_eq_zero h.toSubmodule).mpr a.property
    change f.val (τ (quotientMap k g h (a : g)) n) = ρ a (f.val n) at hf
    rw [hz, map_zero, LinearMap.zero_apply, map_zero] at hf
    exact hf.symm
  · intro z n
    induction z using Submodule.Quotient.induction_on with | _ y =>
    apply Subtype.ext
    change f.val (τ (quotientMap k g h y) n) =
      (σ (quotientMap k g h y) _ : M)
    rw [hσ]
    exact f.property y n

/-- Forgetting the invariant-subspace codomain gives the inverse map. -/
def adjunctionBackward (f : Morphism τ σ) : Morphism (inflation h τ) ρ :=
  ⟨(invariants h ρ).subtype.comp f.val, by
    intro y n
    change (f.val (τ (quotientMap k g h y) n) : M) = ρ y (f.val n : M)
    rw [f.property, hσ]⟩

/-- The invariant functor is right adjoint to inflation: the Hom bijection
and its inverse preserve every value on the underlying modules. -/
def adjunctionEquiv : Morphism (inflation h τ) ρ ≃ Morphism τ σ where
  toFun := adjunctionForward h ρ σ hσ τ
  invFun := adjunctionBackward h ρ σ hσ τ
  left_inv f := by apply Subtype.ext; apply LinearMap.ext; intro n; rfl
  right_inv f := by apply Subtype.ext; apply LinearMap.ext; intro n; rfl

theorem adjunction_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.adjunctionExpected.{u,v,w,w'} := by
  intro k g _ _ _ h M _ _ ρ σ hσ N _ _ τ
  exact ⟨adjunctionEquiv h ρ σ hσ τ, (fun _ _ => rfl), (fun _ _ => rfl)⟩

theorem composite_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.compositeExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ σ hσ m
  constructor
  · intro hm y
    rw [← hσ y m, hm, Submodule.coe_zero]
  · intro hm z
    induction z using Submodule.Quotient.induction_on with | _ y =>
    apply Subtype.ext
    exact (hσ y m).trans (hm y)

/-- Interpret a Lie intertwiner as a linear map for the genuine enveloping
algebra actions, using the shared universal-property theorem. -/
def morphismLinear {L : Type*} [LieRing L] [LieAlgebra k L]
    {P : Type*} {Q : Type*} [AddCommGroup P] [Module k P]
    [AddCommGroup Q] [Module k Q]
    (α : Representation k L P) (β : Representation k L Q) (f : Morphism α β) :
    letI := actionModule k L P (representationEquiv k L P α)
    letI := actionModule k L Q (representationEquiv k L Q β)
    P →ₗ[U k L] Q := by
  letI := actionModule k L P (representationEquiv k L P α)
  letI := actionModule k L Q (representationEquiv k L Q β)
  exact
    { toFun := f.val
      map_add' := f.val.map_add
      map_smul' := (morphism_correspondence k L P Q α β f.val).mpr f.property }

/-- The adjunction preserves Baer's extension property on the original carrier,
even when the enveloping ring is in a larger universe. -/
theorem invariantsBaer (hσ : IsInvariantAction h ρ σ) :
    letI := actionModule k g M (representationEquiv k g M ρ)
    Module.Baer (U k g) M →
    letI := actionModule k (g ⧸ h) (invariants h ρ)
      (representationEquiv k (g ⧸ h) (invariants h ρ) σ)
    Module.Baer (U k (g ⧸ h)) (invariants h ρ) := by
  letI := actionModule k g M (representationEquiv k g M ρ)
  intro hBaer
  letI := actionModule k (g ⧸ h) (invariants h ρ)
    (representationEquiv k (g ⧸ h) (invariants h ρ) σ)
  letI : IsScalarTower k (U k (g ⧸ h)) (invariants h ρ) := action_tower k (g ⧸ h) (invariants h ρ)
    (representationEquiv k (g ⧸ h) (invariants h ρ) σ)
  intro J t
  let X := ↥J
  let Y := U k (g ⧸ h)
  let f : X →ₗ[Y] Y := J.subtype
  have hf : Function.Injective f := Subtype.val_injective
  letI := underlyingModule k (g ⧸ h) X
  letI := underlyingModule k (g ⧸ h) Y
  letI : IsScalarTower k (U k (g ⧸ h)) X := underlying_tower k (g ⧸ h) X
  letI : IsScalarTower k (U k (g ⧸ h)) Y := underlying_tower k (g ⧸ h) Y
  let τX := moduleRepresentation (k := k) (g ⧸ h) X
  let τY := moduleRepresentation (k := k) (g ⧸ h) Y
  let fm : Morphism τX τY := ⟨f.restrictScalars k, by
    intro z x
    exact f.map_smul (inclusion k (g ⧸ h) z) x⟩
  let tm : Morphism τX σ := ⟨t.restrictScalars k, by
    intro z x
    have ht := t.map_smul (inclusion k (g ⧸ h) z) x
    change t (τX z x) =
      representationEquiv k (g ⧸ h) (invariants h ρ) σ (inclusion k (g ⧸ h) z) (t x) at ht
    rw [(representation_properties k (g ⧸ h) (invariants h ρ)).1] at ht
    exact ht⟩
  let fg : Morphism (inflation h τX) (inflation h τY) :=
    ⟨fm.val, fun y x => fm.property (quotientMap k g h y) x⟩
  let tg := adjunctionBackward h ρ σ hσ τX tm
  letI := actionModule k g X (representationEquiv k g X (inflation h τX))
  letI := actionModule k g Y (representationEquiv k g Y (inflation h τY))
  obtain ⟨b, hb⟩ := hBaer.extension_property (morphismLinear _ _ fg) hf
    (morphismLinear _ _ tg)
  letI : IsScalarTower k (U k g) X := action_tower k g X (representationEquiv k g X (inflation h τX))
  letI : IsScalarTower k (U k g) Y := action_tower k g Y (representationEquiv k g Y (inflation h τY))
  letI : IsScalarTower k (U k g) M := action_tower k g M (representationEquiv k g M ρ)
  let bm : Morphism (inflation h τY) ρ := ⟨b.restrictScalars k, by
    apply (morphism_correspondence k g Y M (inflation h τY) ρ _).mp
    exact b.map_smul⟩
  let v := adjunctionForward h ρ σ hσ τY bm
  refine ⟨?_, ?_⟩
  · exact
      { toFun := v.val
        map_add' := v.val.map_add
        map_smul' := by
          intro a y
          have hv := (morphism_correspondence k (g ⧸ h) Y (invariants h ρ)
            τY σ v.val).mpr v.property a y
          have hY : representationEquiv k (g ⧸ h) Y τY = Algebra.lsmul k k Y :=
            (representationEquiv k (g ⧸ h) Y).apply_symm_apply _
          rw [hY] at hv
          exact hv }
  · intro x hx
    apply Subtype.ext
    exact LinearMap.congr_fun hb ⟨x, hx⟩

/-- The invariant functor sends injective g-modules to injective q-modules. -/
theorem injective_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.injectiveExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ σ hσ
  letI := actionModule k g M (representationEquiv k g M ρ)
  intro hinj
  letI := actionModule k (g ⧸ h) (invariants h ρ)
    (representationEquiv k (g ⧸ h) (invariants h ρ) σ)
  exact (invariantsBaer h ρ σ hσ (Module.Baer.of_injective hinj)).injective

theorem inflationExact_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.inflationExactExpected.{u,v,w} := by
  intro k g _ _ _ h X Y Z _ _ _ _ _ _ α β γ f t hf hex ht
  exact ⟨hf, hex, ht⟩

/-- Precomposition naturality of the adjunction, with all actions explicit. -/
theorem adjunction_precompose
    {P : Type*} [AddCommGroup P] [Module k P]
    (υ : Representation k (g ⧸ h) P) (a : Morphism υ τ)
    (f : Morphism (inflation h τ) ρ) (p : P) :
    ((adjunctionEquiv h ρ σ hσ υ)
      ⟨f.val.comp a.val, fun y p => by
        change f.val (a.val (υ (quotientMap k g h y) p)) = _
        rw [a.property]
        exact f.property y (a.val p)⟩).val p =
      ((adjunctionEquiv h ρ σ hσ τ) f).val (a.val p) := rfl

/-- The invariant map on a coefficient intertwiner. -/
def invariantsMap {P : Type*} [AddCommGroup P] [Module k P]
    (ρ' : Representation k g P) (a : Morphism ρ ρ') :
    invariants h ρ →ₗ[k] invariants h ρ' where
  toFun m := ⟨a.val m, fun x => by
    rw [← a.property, m.property x, map_zero]⟩
  map_add' x y := Subtype.ext (a.val.map_add x y)
  map_smul' r x := Subtype.ext (a.val.map_smul r x)

include hσ in
/-- The invariant map respects any quotient actions with the stated formula. -/
theorem invariantsMap_intertwines {P : Type*} [AddCommGroup P] [Module k P]
    (ρ' : Representation k g P)
    (σ' : Representation k (g ⧸ h) (invariants h ρ'))
    (hσ' : IsInvariantAction h ρ' σ') (a : Morphism ρ ρ') :
    LieIntertwines σ σ' (invariantsMap h ρ ρ' a) := by
  intro z m
  induction z using Submodule.Quotient.induction_on with | _ y =>
  apply Subtype.ext
  change a.val (σ (quotientMap k g h y) m : M) =
    (σ' (quotientMap k g h y) _ : P)
  rw [hσ, hσ']
  exact a.property y m

/-- Postcomposition naturality of the adjunction. -/
theorem adjunction_postcompose {P : Type*} [AddCommGroup P] [Module k P]
    (ρ' : Representation k g P)
    (σ' : Representation k (g ⧸ h) (invariants h ρ'))
    (hσ' : IsInvariantAction h ρ' σ') (a : Morphism ρ ρ')
    (f : Morphism (inflation h τ) ρ) (n : N) :
    ((adjunctionEquiv h ρ' σ' hσ' τ)
      ⟨a.val.comp f.val, fun y n => by
        change a.val (f.val (_)) = _
        rw [f.property]
        exact a.property y (f.val n)⟩).val n =
      invariantsMap h ρ ρ' a (((adjunctionEquiv h ρ σ hσ τ) f).val n) := rfl

/-- The printed operation is well-defined on exterior-power cochains. -/
def derivative (ρ : Representation k g M) (n : ℕ) (y : g) :
    Module.End k (Cochains h (M := M) n) where
  toFun f := (ρ y).comp f - f.comp (CE.wedgeDeriv n (LieModule.toEnd k g h y))
  map_add' f t := by
    apply LinearMap.ext
    intro z
    change ρ y (f z + t z) - (f _ + t _) = (ρ y (f z) - f _) + (ρ y (t z) - t _)
    rw [map_add]
    abel
  map_smul' r f := by
    apply LinearMap.ext
    intro z
    change ρ y (r • f z) - r • f _ = r • (ρ y (f z) - f _)
    rw [map_smul, smul_sub]

/-- Insertion on the actual exterior cochains. -/
def insertion (n : ℕ) (a : h) :
    Cochains h (M := M) (n+1) →ₗ[k] Cochains h (M := M) n where
  toFun f := f.comp (CE.wedgeInsert k h n a)
  map_add' f t := by ext z; rfl
  map_smul' r f := by ext z; rfl

theorem derivative_formula (ρ : Representation k g M) :
    HasDerivativeFormula h ρ (derivative h ρ) := by
  intro n y f x
  simp only [derivative, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    LinearMap.comp_apply, CE.wedgeDeriv_wedge, map_sum]
  rfl

theorem insertion_formula : HasInsertionFormula h (insertion h (M := M)) := by
  intro n a f x
  change f (CE.wedgeInsert k h n a (CE.wedge k h n x)) = _
  rw [CE.wedgeInsert_wedge]

/-- Exterior derivation is linear in its generating endomorphism. -/
theorem wedgeDeriv_add (n : ℕ) (D E : Module.End k h) :
    CE.wedgeDeriv n (D + E) = CE.wedgeDeriv n D + CE.wedgeDeriv n E := by
  classical
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
    CE.wedgeDeriv_wedge, AlternatingMap.map_update_add, Finset.sum_add_distrib]

theorem wedgeDeriv_smul (n : ℕ) (r : k) (D : Module.End k h) :
    CE.wedgeDeriv n (r • D) = r • CE.wedgeDeriv n D := by
  classical
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
    CE.wedgeDeriv_wedge, AlternatingMap.map_update_smul, Finset.smul_sum]

theorem wedgeInsert_sub (n : ℕ) (a b : h) :
    CE.wedgeInsert k h n (a-b) = CE.wedgeInsert k h n a - CE.wedgeInsert k h n b := by
  simp only [CE.wedgeInsert, map_sub]

/-- The commutator of exterior derivations is the exterior derivation of
 the commutator, in every exterior degree. -/
theorem wedgeDeriv_commutator (n : ℕ) (D E : Module.End k h) :
    (CE.wedgeDeriv n D).comp (CE.wedgeDeriv n E) -
      (CE.wedgeDeriv n E).comp (CE.wedgeDeriv n D) =
        CE.wedgeDeriv n (D.comp E - E.comp D) := by
  induction n with
  | zero =>
    apply LinearMap.ext
    intro x
    simp only [CE.wedgeDeriv_zero, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.zero_apply, sub_self]
  | succ n ih =>
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    have hx : CE.wedge k h (n+1) x =
        CE.wedgeInsert k h n (x 0) (CE.wedge k h n (fun i => x i.succ)) := by
      rw [CE.wedgeInsert_wedge]
      congr 1
      exact (Fin.cons_self_tail x).symm
    change CE.wedgeDeriv (n+1) D (CE.wedgeDeriv (n+1) E (CE.wedge k h (n+1) x)) -
      CE.wedgeDeriv (n+1) E (CE.wedgeDeriv (n+1) D (CE.wedge k h (n+1) x)) =
        CE.wedgeDeriv (n+1) (D.comp E - E.comp D) (CE.wedge k h (n+1) x)
    rw [hx]
    simp only [CE.wedgeDeriv_insert, map_add, wedgeInsert_sub,
      LinearMap.sub_apply, LinearMap.comp_apply]
    have hi := LinearMap.congr_fun ih (CE.wedge k h n (fun i => x i.succ))
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hi
    rw [← hi, map_sub]
    abel

/-- The printed infinitesimal action is a representation. -/
def cochainRepresentation (ρ : Representation k g M) (n : ℕ) :
    Representation k g (Cochains h (M := M) n) where
  toFun := derivative h ρ n
  map_add' y z := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    simp only [derivative, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.comp_apply, map_add, LieModule.toEnd, wedgeDeriv_add,
      LinearMap.add_apply]
    abel
  map_smul' r y := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    simp only [derivative, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.comp_apply, map_smul, LieModule.toEnd, wedgeDeriv_smul,
      LinearMap.smul_apply, smul_sub, RingHom.id_apply]
  map_lie' {y z} := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    have hr := LinearMap.congr_fun (ρ.map_lie y z) (f x)
    have he : CE.wedgeDeriv n (LieModule.toEnd k g h ⁅y,z⁆) =
        (CE.wedgeDeriv n (LieModule.toEnd k g h y)).comp
          (CE.wedgeDeriv n (LieModule.toEnd k g h z)) -
        (CE.wedgeDeriv n (LieModule.toEnd k g h z)).comp
          (CE.wedgeDeriv n (LieModule.toEnd k g h y)) := by
      rw [wedgeDeriv_commutator]
      congr 1
      exact (LieModule.toEnd k g h).map_lie y z
    change ρ ⁅y,z⁆ (f x) - f (CE.wedgeDeriv n (LieModule.toEnd k g h ⁅y,z⁆) x) =
      derivative h ρ n y (derivative h ρ n z f) x -
        derivative h ρ n z (derivative h ρ n y f) x
    rw [he]
    change ρ ⁅y,z⁆ (f x) = ρ y (ρ z (f x)) - ρ z (ρ y (f x)) at hr
    simp only [derivative, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.comp_apply, map_sub] at *
    rw [hr]
    abel

/-- Inserting every possible first argument detects a positive-degree cochain. -/
theorem insertion_ext {n : ℕ} {f t : Cochains h (M := M) (n+1)}
    (ht : ∀ a, insertion h n a f = insertion h n a t) : f = t := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  have he := LinearMap.congr_fun (ht (x 0)) (CE.wedge k h n (fun i => x i.succ))
  change f (CE.wedgeInsert k h n (x 0) _) = t (CE.wedgeInsert k h n (x 0) _) at he
  have hx : Fin.cons (x 0) (fun i => x i.succ) = x := Fin.cons_self_tail x
  rw [CE.wedgeInsert_wedge, hx] at he
  exact he

/-- The mixed Cartan commutator with an ambient element. -/
theorem derivative_insertion (ρ : Representation k g M) (n : ℕ) (y : g) (a : h)
    (f : Cochains h (M := M) (n+1)) :
    insertion h n a (derivative h ρ (n+1) y f) =
      derivative h ρ n y (insertion h n a f) - insertion h n ⁅y,a⁆ f := by
  apply LinearMap.ext
  intro x
  change ρ y (f (CE.wedgeInsert k h n a x)) -
    f (CE.wedgeDeriv (n+1) (LieModule.toEnd k g h y) (CE.wedgeInsert k h n a x)) =
    (ρ y (f (CE.wedgeInsert k h n a x)) -
      f (CE.wedgeInsert k h n a (CE.wedgeDeriv n (LieModule.toEnd k g h y) x))) -
        f (CE.wedgeInsert k h n ⁅y,a⁆ x)
  rw [CE.wedgeDeriv_insert, map_add]
  change ρ y (f (CE.wedgeInsert k h n a x)) -
    (f (CE.wedgeInsert k h n ⁅y,a⁆ x) +
      f (CE.wedgeInsert k h n a (CE.wedgeDeriv n (LieModule.toEnd k g h y) x))) = _
  abel

section Cartan
open scoped TensorProduct
variable [Module.Free k h]
variable [Module (CE.U k h) M] [IsScalarTower k (CE.U k h) M]
variable (ρ : Representation k g M)
variable (hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m)

/-- Restriction to h uses the same given coefficient representation. -/
abbrev differential (n : ℕ) : Cochains h (M := M) n →ₗ[k] Cochains h (M := M) (n+1) :=
  CE.coboundary k h M (CE.boundary k h) n

include hρ in
theorem differential_formula : HasDifferentialFormula h ρ (differential h (M := M)) := by
  intro n f x
  rw [differential, CE.coboundary_formula k h M _ (CE.boundary_formula k h)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact hρ (x i) _

theorem differential_squared (n : ℕ) :
    (differential h (M := M) (n+1)).comp (differential h (M := M) n) = 0 :=
  CE.coboundary_squared k h M _ (CE.boundary_squared k h) n

theorem insertion_comparison (n : ℕ) (a : h) (F : CE.V k h (n+1) →ₗ[CE.U k h] M) :
    insertion h n a (CE.homEquiv k h M (n+1) F) =
      CE.homEquiv k h M n (F.comp (CE.insert k h n a)) := by
  apply LinearMap.ext
  intro z
  simp only [insertion, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    CE.homEquiv_apply, CE.insert_tmul]

include hρ in
theorem derivative_comparison (n : ℕ) (a : h) (F : CE.V k h n →ₗ[CE.U k h] M) :
    derivative h ρ n a (CE.homEquiv k h M n F) =
      CE.homEquiv k h M n (F.comp (CE.lieAction k h n a)) := by
  apply LinearMap.ext
  intro z
  simp only [derivative, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    LinearMap.comp_apply, CE.homEquiv_apply, CE.lieAction, CE.rightAction_tmul,
    CE.exteriorAction_tmul, one_mul, map_sub]
  congr 1
  · have hs := F.map_smul (inclusion k h a) ((1 : CE.U k h) ⊗ₜ[k] z)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hs
    rw [hs]
    exact (hρ a _).symm

include hρ in
theorem cartan_zero (a : h) (f : Cochains h (M := M) 0) :
    insertion h 0 a (differential h (M := M) 0 f) = derivative h ρ 0 a f := by
  obtain ⟨F, rfl⟩ := (CE.homEquiv k h M 0).surjective f
  rw [differential, CE.coboundary_comparison, insertion_comparison,
    derivative_comparison h ρ hρ]
  apply LinearMap.ext
  intro z
  simp only [CE.homEquiv_apply, LinearMap.comp_apply, CE.homCoboundary]
  rw [CE.boundary_insert_zero, CE.lieAction_zero]

include hρ in
theorem cartan_succ (n : ℕ) (a : h) (f : Cochains h (M := M) (n+1)) :
    differential h (M := M) n (insertion h n a f) +
      insertion h (n+1) a (differential h (M := M) (n+1) f) = derivative h ρ (n+1) a f := by
  obtain ⟨F, rfl⟩ := (CE.homEquiv k h M (n+1)).surjective f
  rw [insertion_comparison, differential, differential,
    CE.coboundary_comparison, CE.coboundary_comparison, insertion_comparison,
    derivative_comparison h ρ hρ]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.add_apply, CE.homEquiv_apply, LinearMap.comp_apply,
    CE.homCoboundary]
  rw [CE.boundary_insert, map_sub]
  abel

private theorem cartan_commute_algebra {A : Type*} [AddCommGroup A]
    (a b c d e : A) (h : c+e=b-a) : a-(d-c)=b-d-e := by
  calc
    _ = a + (c+e) - d - e := by abel
    _ = _ := by rw [h]; abel

include hρ in
/-- Equivariance of the CE differential follows from the two Cartan
commutators, with a separate degree-zero start. -/
theorem differential_derivative (n : ℕ) (y : g) (f : Cochains h (M := M) n) :
    differential h (M := M) n (derivative h ρ n y f) =
      derivative h ρ (n+1) y (differential h (M := M) n f) := by
  induction n with
  | zero =>
    apply insertion_ext h
    intro a
    rw [cartan_zero h ρ hρ, derivative_insertion, cartan_zero h ρ hρ,
      cartan_zero h ρ hρ]
    have hr := LinearMap.congr_fun ((cochainRepresentation h ρ 0).map_lie y (a : g)) f
    change derivative h ρ 0 ⁅y,(a : g)⁆ f =
      derivative h ρ 0 y (derivative h ρ 0 a f) -
        derivative h ρ 0 a (derivative h ρ 0 y f) at hr
    change derivative h ρ 0 a (derivative h ρ 0 y f) =
      derivative h ρ 0 y (derivative h ρ 0 a f) - derivative h ρ 0 ⁅y,(a : g)⁆ f
    rw [hr]
    abel
  | succ n ih =>
    apply insertion_ext h
    intro a
    have hc (b : h) (t : Cochains h (M := M) (n+1)) :
        insertion h (n+1) b (differential h (M := M) (n+1) t) =
          derivative h ρ (n+1) b t - differential h (M := M) n (insertion h n b t) := by
      have ht := cartan_succ h ρ hρ n b t
      rw [← ht]
      abel
    rw [hc a _, derivative_insertion h ρ (n+1) y a, hc a _,
      derivative_insertion h ρ n y a, map_sub, map_sub, ih]
    have hr := LinearMap.congr_fun ((cochainRepresentation h ρ (n+1)).map_lie y (a : g)) f
    change derivative h ρ (n+1) ⁅y,(a : g)⁆ f =
      derivative h ρ (n+1) y (derivative h ρ (n+1) a f) -
        derivative h ρ (n+1) a (derivative h ρ (n+1) y f) at hr
    have ht := cartan_succ h ρ hρ n ⁅y,a⁆ f
    change differential h (M := M) n (insertion h n ⁅y,a⁆ f) +
      insertion h (n+1) ⁅y,a⁆ (differential h (M := M) (n+1) f) =
        derivative h ρ (n+1) ⁅y,(a : g)⁆ f at ht
    rw [hr] at ht
    exact cartan_commute_algebra _ _ _ _ _ ht

end Cartan

theorem cartan_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.cartanExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ
  letI := actionModule k h M (representationEquiv k h M (ρ.comp h.incl))
  letI : IsScalarTower k (CE.U k h) M :=
    action_tower k h M (representationEquiv k h M (ρ.comp h.incl))
  have hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m :=
    fun a m => (representation_properties k h M).1 (ρ.comp h.incl) a m
  exact ⟨differential h (M := M), derivative h ρ, insertion h,
    differential_formula h ρ hρ, differential_squared h, derivative_formula h ρ,
    insertion_formula h, cartan_zero h ρ hρ, cartan_succ h ρ hρ⟩

/-- Restriction of a representation to a stable linear subspace. -/
def subspaceRepresentation (α : Representation k g M) (S : Submodule k M)
    (hS : ∀ y m, m ∈ S → α y m ∈ S) : Representation k g S where
  toFun y :=
    { toFun m := ⟨α y m, hS y m m.property⟩
      map_add' _ _ := by ext; exact map_add (α y) _ _
      map_smul' _ _ := by ext; exact map_smul (α y) _ _ }
  map_add' y z := by ext m; exact LinearMap.congr_fun (α.map_add y z) m
  map_smul' r y := by ext m; exact LinearMap.congr_fun (α.map_smul r y) m
  map_lie' {y z} := by ext m; exact LinearMap.congr_fun (α.map_lie y z) m

/-- The action on a quotient by a stable subspace. -/
def quotientRepresentation (α : Representation k g M) (S : Submodule k M)
    (hS : ∀ y m, m ∈ S → α y m ∈ S) : Representation k g (M ⧸ S) where
  toFun y := S.mapQ S (α y) (hS y)
  map_add' y z := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change S.mkQ (α (y+z) x) = S.mkQ (α y x) + S.mkQ (α z x)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' r y := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change S.mkQ (α (r • y) x) = r • S.mkQ (α y x)
    rw [map_smul, LinearMap.smul_apply, map_smul]
  map_lie' {y z} := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change S.mkQ (α ⁅y,z⁆ x) = S.mkQ (α y (α z x)) - S.mkQ (α z (α y x))
    have he := LinearMap.congr_fun (α.map_lie y z) x
    change α ⁅y,z⁆ x = α y (α z x) - α z (α y x) at he
    rw [he, map_sub]

/-- Factoring an action that annihilates the ideal through the actual quotient. -/
def factorRepresentation (α : Representation k g M) (hα : ∀ a : h, α a = 0) :
    Representation k (g ⧸ h) M :=
  { h.toSubmodule.liftQ α.toLinearMap (by
      intro a ha
      exact hα ⟨a, ha⟩) with
    map_lie' := by
      intro y z
      induction y using Submodule.Quotient.induction_on with | _ y =>
      induction z using Submodule.Quotient.induction_on with | _ z =>
      exact α.map_lie y z }

section Cohomology
variable (ρ : Representation k g M) (c : CochainCalculus h ρ)

/-- Cycles are stable under the displayed action. -/
def cycleRepresentation (n : ℕ) : Representation k g (LinearMap.ker (c.d n)) :=
  subspaceRepresentation (c.L n) (LinearMap.ker (c.d n)) (by
    intro y f hf
    change c.d n (c.L n y f) = 0
    rw [c.commute, hf, map_zero])

theorem boundaries_stable (n : ℕ) (y : g) (f : LinearMap.ker (c.d n))
    (hf : f ∈ cocycleBoundaries h c.d n) :
    cycleRepresentation h ρ c n y f ∈ cocycleBoundaries h c.d n := by
  cases n with
  | zero =>
    change f = 0 at hf
    rw [hf, map_zero]
    exact Submodule.zero_mem _
  | succ n =>
    change (f : Cochains h (n+1)) ∈ LinearMap.range (c.d n) at hf
    obtain ⟨t, ht⟩ := hf
    change c.L (n+1) y f ∈ LinearMap.range (c.d n)
    exact ⟨c.L n y t, by rw [c.commute, ht]⟩

/-- Ambient action on the ordinary cycle/boundary quotient. -/
def cohomologyAmbient (n : ℕ) : Representation k g (Cohomology h c.d n) :=
  quotientRepresentation (cycleRepresentation h ρ c n) (cocycleBoundaries h c.d n)
    (boundaries_stable h ρ c n)

/-- Cartan homotopy kills the ideal on cohomology, including in degree zero. -/
theorem cohomology_ideal_zero (n : ℕ) (a : h) :
    cohomologyAmbient h ρ c n a = 0 := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with | _ f =>
  change cohomologyClass h c.d n (CochainCalculus.cycleAction h c n a f) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  cases n with
  | zero =>
    change CochainCalculus.cycleAction h c 0 a f = 0
    apply Subtype.ext
    change c.L 0 a f = 0
    rw [← c.cartan_zero, f.property, map_zero]
  | succ n =>
    change c.L (n+1) a f ∈ LinearMap.range (c.d n)
    refine ⟨c.i n a f, ?_⟩
    have ht := c.cartan_succ n a f
    rw [f.property, map_zero, add_zero] at ht
    exact ht

/-- The quotient Lie action on the actual CE cohomology quotient. -/
def cohomologyQuotient (n : ℕ) : Representation k (g ⧸ h) (Cohomology h c.d n) :=
  factorRepresentation h (cohomologyAmbient h ρ c n) (cohomology_ideal_zero h ρ c n)

theorem cohomologyQuotient_formula (n : ℕ) (y : g) (f : LinearMap.ker (c.d n)) :
    cohomologyQuotient h ρ c n (quotientMap k g h y) (cohomologyClass h c.d n f) =
      cohomologyClass h c.d n (CochainCalculus.cycleAction h c n y f) := rfl

/-- A vector is a degree-zero cochain via the canonical Λ⁰h = k map. -/
def zeroCochain : M →ₗ[k] Cochains h (M := M) 0 where
  toFun m := (LinearMap.toSpanSingleton k M m).comp (exteriorPower.zeroEquiv k h).toLinearMap
  map_add' _ _ := by
    apply LinearMap.ext
    intro z
    exact smul_add _ _ _
  map_smul' r m := by
    apply LinearMap.ext
    intro z
    exact smul_comm _ _ _

@[simp] theorem zeroCochain_wedge (m : M) (x : Fin 0 → h) :
    zeroCochain h m (CE.wedge k h 0 x) = m := by
  change (exteriorPower.zeroEquiv k h (exteriorPower.ιMulti k 0 x)) • m = m
  rw [exteriorPower.zeroEquiv_ιMulti, one_smul]

/-- The degree-zero cochain/vector identification uses evaluation on the
empty wedge and is valid for modules of every rank. -/
def zeroCochainEquiv : M ≃ₗ[k] Cochains h (M := M) 0 where
  toLinearMap := zeroCochain h
  invFun f := f (CE.wedge k h 0 Fin.elim0)
  left_inv m := zeroCochain_wedge h m _
  right_inv f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change zeroCochain h (f (CE.wedge k h 0 Fin.elim0)) (CE.wedge k h 0 x) = _
    rw [zeroCochain_wedge]
    congr 1

theorem differential_zero_formula (f : Cochains h (M := M) 0) (x : Fin 1 → h) :
    c.d 0 f (CE.wedge k h 1 x) = ρ (x 0) (f (CE.wedge k h 0 Fin.elim0)) := by
  rw [c.d_formula]
  have he : (0 : Fin 1).removeNth x = Fin.elim0 := Subsingleton.elim _ _
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    zero_add, add_zero, Fin.val_zero, pow_zero, one_zsmul, CE.cochainBracketSum, he]

theorem zero_cycle_iff (f : Cochains h (M := M) 0) :
    c.d 0 f = 0 ↔ f (CE.wedge k h 0 Fin.elim0) ∈ invariants h ρ := by
  constructor
  · intro hf a
    have ht := differential_zero_formula h ρ c f (Fin.cons a Fin.elim0)
    rw [hf, LinearMap.zero_apply] at ht
    exact ht.symm
  · intro hf
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change c.d 0 f (CE.wedge k h 1 x) = 0
    rw [differential_zero_formula h ρ c]
    exact hf (x 0)

/-- Cycles in degree zero identify with the original invariant subspace. -/
def zeroCyclesEquiv : LinearMap.ker (c.d 0) ≃ₗ[k] invariants h ρ where
  toFun f := ⟨f.val (CE.wedge k h 0 Fin.elim0), (zero_cycle_iff h ρ c f).mp f.property⟩
  invFun m := ⟨zeroCochain h m, (zero_cycle_iff h ρ c _).mpr (by
    rw [zeroCochain_wedge]
    exact m.property)⟩
  left_inv f := by
    apply Subtype.ext
    exact (zeroCochainEquiv h).apply_symm_apply f.val
  right_inv m := by apply Subtype.ext; exact zeroCochain_wedge h m.val _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree-zero CE cohomology is the invariant subspace, canonically. -/
def zeroCohomologyEquiv : Cohomology h c.d 0 ≃ₗ[k] invariants h ρ :=
  (Submodule.quotEquivOfEqBot (cocycleBoundaries h c.d 0) rfl).trans (zeroCyclesEquiv h ρ c)

/-- The degree-zero identification respects the quotient action used by
invariant modules, fixing the augmentation for the resolution comparison. -/
theorem zeroCohomologyEquiv_intertwines :
    LieIntertwines (cohomologyQuotient h ρ c 0) (invariantQuotient h ρ)
      (zeroCohomologyEquiv h ρ c).toLinearMap := by
  intro z f
  induction z using Submodule.Quotient.induction_on with | _ y =>
  induction f using Submodule.Quotient.induction_on with | _ f =>
  apply Subtype.ext
  change c.L 0 y f (CE.wedge k h 0 Fin.elim0) =
    ρ y (f.val (CE.wedge k h 0 Fin.elim0))
  rw [c.L_formula]
  simp

section Coefficients
variable {P : Type w'} [AddCommGroup P] [Module k P]
variable (ρ' : Representation k g P) (c' : CochainCalculus h ρ') (a : Morphism ρ ρ')

/-- Coefficient maps act by postcomposition on exterior-power cochains. -/
def cochainPost (n : ℕ) : Cochains h (M := M) n →ₗ[k] Cochains h (M := P) n where
  toFun f := a.val.comp f
  map_add' _ _ := by ext x; exact map_add a.val _ _
  map_smul' _ _ := by ext x; exact map_smul a.val _ _

/-- Every coefficient intertwiner commutes with the displayed differential. -/
theorem cochainPost_d (n : ℕ) (f : Cochains h (M := M) n) :
    cochainPost h ρ ρ' a (n+1) (c.d n f) =
      c'.d n (cochainPost h ρ ρ' a n f) := by
  have ha : ∀ y m, a.val (ρ y m) = ρ' y (a.val m) := a.property
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change a.val (c.d n f (CE.wedge k h (n+1) x)) =
    c'.d n (a.val.comp f) (CE.wedge k h (n+1) x)
  rw [c.d_formula, c'.d_formula]
  simp only [map_add, map_sum, map_zsmul, LinearMap.comp_apply, ha]
  congr 1
  cases n <;> simp only [CE.cochainBracketSum, map_zero, map_sum,
    map_zsmul, LinearMap.comp_apply]

/-- Coefficient intertwiners also commute with the ambient Lie action. -/
theorem cochainPost_L (n : ℕ) (y : g) (f : Cochains h (M := M) n) :
    cochainPost h ρ ρ' a n (c.L n y f) =
      c'.L n y (cochainPost h ρ ρ' a n f) := by
  have ha : ∀ y m, a.val (ρ y m) = ρ' y (a.val m) := a.property
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change a.val (c.L n y f (CE.wedge k h n x)) =
    c'.L n y (a.val.comp f) (CE.wedge k h n x)
  rw [c.L_formula, c'.L_formula]
  simp only [map_sub, map_sum, LinearMap.comp_apply, ha]

/-- The actual map of cocycle subspaces induced by a coefficient map. -/
def coefficientCycles (n : ℕ) : LinearMap.ker (c.d n) →ₗ[k] LinearMap.ker (c'.d n) where
  toFun f := ⟨cochainPost h ρ ρ' a n f, by
    change c'.d n (cochainPost h ρ ρ' a n f) = 0
    rw [← cochainPost_d h ρ c ρ' c' a, f.property, map_zero]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem coefficient_boundaries (n : ℕ) (f : LinearMap.ker (c.d n))
    (hf : f ∈ cocycleBoundaries h c.d n) :
    coefficientCycles h ρ c ρ' c' a n f ∈ cocycleBoundaries h c'.d n := by
  cases n with
  | zero =>
    change f = 0 at hf
    rw [hf, map_zero]
    exact Submodule.zero_mem _
  | succ n =>
    change (f : Cochains h (n+1)) ∈ LinearMap.range (c.d n) at hf
    obtain ⟨t, ht⟩ := hf
    change cochainPost h ρ ρ' a (n+1) f ∈ LinearMap.range (c'.d n)
    exact ⟨cochainPost h ρ ρ' a n t, by rw [← cochainPost_d h ρ c ρ' c' a, ht]⟩

/-- The induced linear map on cycles modulo boundaries. -/
def coefficientCohomology (n : ℕ) : Cohomology h c.d n →ₗ[k] Cohomology h c'.d n :=
  (cocycleBoundaries h c.d n).mapQ (cocycleBoundaries h c'.d n)
    (coefficientCycles h ρ c ρ' c' a n) (coefficient_boundaries h ρ c ρ' c' a n)

/-- Naturality of the quotient action for every coefficient intertwiner. -/
theorem coefficientCohomology_intertwines (n : ℕ) :
    LieIntertwines (cohomologyQuotient h ρ c n) (cohomologyQuotient h ρ' c' n)
      (coefficientCohomology h ρ c ρ' c' a n) := by
  intro y z
  induction y using Submodule.Quotient.induction_on with | _ y =>
  induction z using Submodule.Quotient.induction_on with | _ f =>
  change cohomologyClass h c'.d n
    (coefficientCycles h ρ c ρ' c' a n (CochainCalculus.cycleAction h c n y f)) =
      cohomologyClass h c'.d n
        (CochainCalculus.cycleAction h c' n y (coefficientCycles h ρ c ρ' c' a n f))
  congr 1
  apply Subtype.ext
  exact cochainPost_L h ρ c ρ' c' a n y f

end Coefficients

end Cohomology

/-- The constructed full calculus, with the genuine restricted U(h)-action. -/
def cochainCalculus {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
    (ρ : Representation k g M) : CochainCalculus h ρ := by
  letI := actionModule k h M (representationEquiv k h M (ρ.comp h.incl))
  letI : IsScalarTower k (CE.U k h) M :=
    action_tower k h M (representationEquiv k h M (ρ.comp h.incl))
  have hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m :=
    fun a m => (representation_properties k h M).1 (ρ.comp h.incl) a m
  exact
    { d := differential h (M := M)
      L := cochainRepresentation h ρ
      i := insertion h
      d_formula := differential_formula h ρ hρ
      d_squared := differential_squared h
      L_formula := derivative_formula h ρ
      i_formula := insertion_formula h
      commute := differential_derivative h ρ hρ
      cartan_zero := cartan_zero h ρ hρ
      cartan_succ := cartan_succ h ρ hρ }

theorem calculus_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.calculusExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ
  exact ⟨cochainCalculus h ρ⟩

theorem quotientCohomology_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.quotientCohomologyExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ
  let c := cochainCalculus h ρ
  exact ⟨c, cohomologyQuotient h ρ c, cohomologyQuotient_formula h ρ c⟩


theorem degreeZero_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.degreeZeroExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ ρ c
  exact ⟨cohomologyQuotient h ρ c, invariantQuotient h ρ, zeroCohomologyEquiv h ρ c,
    cohomologyQuotient_formula h ρ c, invariantQuotient_formula h ρ,
    (fun _ => rfl), zeroCohomologyEquiv_intertwines h ρ c⟩

theorem coefficientNaturality_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.coefficientNaturalityExpected.{u,v,w,w'} := by
  intro k g _ _ _ h M _ _ ρ c P _ _ ρ' c'
  refine ⟨cohomologyQuotient h ρ c, cohomologyQuotient h ρ' c',
    cohomologyQuotient_formula h ρ c, cohomologyQuotient_formula h ρ' c', ?_⟩
  intro a
  refine ⟨coefficientCohomology h ρ c ρ' c' a, ?_,
    coefficientCohomology_intertwines h ρ c ρ' c' a⟩
  intro n f
  exact ⟨coefficientCycles h ρ c ρ' c' a n f, rfl, rfl⟩

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
open CategoryTheory
open P103.Specs.Ch10.Comparison
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module (U k g) M]

abbrev restrictedModule : Module (U k h) M :=
  Module.compHom M (IdealEnveloping.inducedMap k g h).toRingHom

attribute [local instance] restrictedModule

/-- Restrict a genuine ambient injective resolution along the ideal inclusion. -/
def restrictedInjectiveResolution (I : InjectiveResolution (U k g) M) :
    InjectiveResolution (U k h) M where
  complex := ((ModuleCat.restrictScalars (IdealEnveloping.inducedMap k g h).toRingHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.complex
  injectiveTerm n := by
    letI := I.injectiveTerm n
    exact IdealEnveloping.restriction_spec k g h (I.complex.X n)
  η :=
    { I.η with
      map_smul' := fun a m => I.η.map_smul ((IdealEnveloping.inducedMap k g h) a) m }
  injective_η := I.injective_η
  exact_zero := I.exact_zero
  exact_succ := I.exact_succ

@[simp] theorem restrictedInjectiveResolution_η (I : InjectiveResolution (U k g) M) (m : M) :
    (restrictedInjectiveResolution h I).η m = I.η m := rfl

@[simp] theorem restrictedInjectiveResolution_d (I : InjectiveResolution (U k g) M)
    (p q : ℕ) (x : I.complex.X p) :
    ((restrictedInjectiveResolution h I).complex.d p q).hom x =
      (I.complex.d p q).hom x := rfl


section Underlying
variable [Module k M] [IsScalarTower k (U k g) M]

@[simp] theorem moduleRepresentation_apply (y : g) (m : M) :
    moduleRepresentation (k := k) g M y m = inclusion k g y • m := rfl

instance restrictedModule_tower : IsScalarTower k (U k h) M := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (IdealEnveloping.inducedMap k g h) (algebraMap k (U k h) r) • m = r • m
  rw [AlgHom.commutes]
  exact algebraMap_smul (U k g) r m

@[simp] theorem restrictedModule_inclusion (a : h) (m : M) :
    inclusion k h a • m = moduleRepresentation (k := k) g M a m := by
  change (IdealEnveloping.inducedMap k g h) (inclusion k h a) • m = _
  rw [IdealEnveloping.inducedMap_inclusion, moduleRepresentation_apply]

end Underlying

/-- The ideal and ambient actions agree on every resolution term. -/
theorem resolutionTerm_restriction (I : InjectiveResolution (U k g) M)
    (n : ℕ) (a : h) (m : I.complex.X n) :
    inclusion k h a • m = resolutionTermRepresentation I n a m :=
  restrictedModule_inclusion h a m


/-- The coefficient differentials intertwine the original ambient module actions. -/
theorem resolutionDifferential_intertwines (I : InjectiveResolution (U k g) M)
    (p q : ℕ) :
    LieIntertwines (resolutionTermRepresentation I p) (resolutionTermRepresentation I q)
      ((I.complex.d p q).hom.restrictScalars k) := by
  intro y m
  exact (I.complex.d p q).hom.map_smul (inclusion k g y) m

section Augmentation
variable [Module k M] [IsScalarTower k (U k g) M]

/-- The resolution augmentation intertwines the actual g-module actions. -/
theorem resolutionAugmentation_intertwines (I : InjectiveResolution (U k g) M) :
    LieIntertwines (moduleRepresentation g M) (resolutionTermRepresentation I 0)
      (I.η.restrictScalars k) := by
  intro y m
  exact I.η.map_smul (inclusion k g y) m

end Augmentation


section DifferentialUniqueness
variable [Module k M] [IsScalarTower k (U k g) M]
variable (ρ : Representation k g M)

/-- The displayed exterior-power formula fixes every cochain differential. -/
theorem differential_unique (δ ε : Differential h (M := M))
    (hδ : HasDifferentialFormula h ρ δ) (hε : HasDifferentialFormula h ρ ε) : δ = ε := by
  funext n
  apply LinearMap.ext
  intro f
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change δ n f (CE.wedge k h (n+1) x) = ε n f (CE.wedge k h (n+1) x)
  rw [hδ, hε]

/-- Every calculus uses the actual CE differential of the restricted U(h)-module. -/
theorem calculus_d_eq_restricted (c : CochainCalculus h (moduleRepresentation g M)) :
    c.d = differential h (M := M) := by
  exact differential_unique h _ _ _ c.d_formula
    (differential_formula h _ (restrictedModule_inclusion h))

end DifferentialUniqueness

end AdvancedHomologicalAlgebra.LieQuotientAction



set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable (ρ : Representation k g M) (c : CochainCalculus h ρ)

abbrev calculusComplex := CE.Ext.cochain k h M c.d c.d_squared

def cochainEndomorphism (y : g) : calculusComplex h ρ c ⟶ calculusComplex h ρ c :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (c.L n y).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simpa only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe] using c.commute n y f)

@[simp] theorem cochainEndomorphism_apply (y : g) (n : ℕ) (f : Cochains h (M := M) n) :
    ((cochainEndomorphism h ρ c y).f n).hom f = c.L n y f := rfl

def cochainCyclesEquiv (n : ℕ) :
    LinearMap.ker (c.d n) ≃ₗ[ℤ] cycles (calculusComplex h ρ c) n where
  toFun f := ⟨f.val, by
    change ((calculusComplex h ρ c).d n ((ComplexShape.up ℕ).next n)).hom f.val = 0
    rw [CochainComplex.next]
    simpa only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d, ModuleCat.hom_ofHom, LinearMap.mem_ker,
      AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe]
      using f.property⟩
  invFun f := ⟨f.val, by
    have hf := f.property
    change ((calculusComplex h ρ c).d n ((ComplexShape.up ℕ).next n)).hom f.val = 0 at hf
    rw [CochainComplex.next] at hf
    simpa only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d, ModuleCat.hom_ofHom, LinearMap.mem_ker,
      AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe]
      using hf⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cochainCyclesEquiv_boundaries (n : ℕ) (f : LinearMap.ker (c.d n)) :
    cochainCyclesEquiv h ρ c n f ∈ cycleBoundaries (calculusComplex h ρ c) n ↔
      f ∈ cocycleBoundaries h c.d n := by
  cases n with
  | zero =>
    change (∃ x, ((calculusComplex h ρ c).d ((ComplexShape.up ℕ).prev 0) 0).hom x = f.val) ↔ f = 0
    rw [CochainComplex.prev_nat_zero]
    have hd : (calculusComplex h ρ c).d 0 0 = 0 :=
      (calculusComplex h ρ c).shape _ _ (by decide)
    rw [hd]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const]
    exact ⟨fun he => Subtype.ext he.symm, fun he => by rw [he]; rfl⟩
  | succ n =>
    change (∃ x, ((calculusComplex h ρ c).d ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom x = f.val) ↔
      ∃ x, c.d n x = f.val
    rw [CochainComplex.prev_nat_succ]
    simp only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d, ModuleCat.hom_ofHom]
    rfl


def cochainCohomologyEquiv (n : ℕ) :
    Cohomology h c.d n ≃ₗ[ℤ] Homology (calculusComplex h ρ c) n :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ (cocycleBoundaries h c.d n)).symm.trans
    (Submodule.Quotient.equiv _ _ (cochainCyclesEquiv h ρ c n) (by
      ext f
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (cochainCyclesEquiv_boundaries h ρ c n z).mpr hz
      · intro hf
        refine ⟨(cochainCyclesEquiv h ρ c n).symm f, ?_, ?_⟩
        · exact (cochainCyclesEquiv_boundaries h ρ c n _).mp
            (by simpa only [LinearEquiv.apply_symm_apply] using hf)
        · exact (cochainCyclesEquiv h ρ c n).apply_symm_apply f))

@[simp] theorem cochainCohomologyEquiv_class (n : ℕ) (f : LinearMap.ker (c.d n)) :
    cochainCohomologyEquiv h ρ c n (cohomologyClass h c.d n f) =
      homologyClass _ n (cochainCyclesEquiv h ρ c n f) := rfl

theorem cochainCohomologyEquiv_action (n : ℕ) (y : g) (z : Cohomology h c.d n) :
    cochainCohomologyEquiv h ρ c n (cohomologyAmbient h ρ c n y z) =
      homologyMap (cochainEndomorphism h ρ c y) n (cochainCohomologyEquiv h ρ c n z) := by
  induction z using Submodule.Quotient.induction_on with | _ f =>
  rfl


theorem cochainCohomologyEquiv_quotientAction (n : ℕ) (y : g) (z : Cohomology h c.d n) :
    cochainCohomologyEquiv h ρ c n
        (cohomologyQuotient h ρ c n (quotientMap k g h y) z) =
      homologyMap (cochainEndomorphism h ρ c y) n (cochainCohomologyEquiv h ρ c n z) :=
  cochainCohomologyEquiv_action h ρ c n y z

section Coefficients
variable {P : Type w} [AddCommGroup P] [Module k P]
variable (ρ' : Representation k g P) (c' : CochainCalculus h ρ') (a : Morphism ρ ρ')

def coefficientComplexMap : calculusComplex h ρ c ⟶ calculusComplex h ρ' c' :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (cochainPost h ρ ρ' a n).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simpa only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe]
        using (cochainPost_d h ρ c ρ' c' a n f).symm)

@[simp] theorem coefficientComplexMap_apply (n : ℕ) (f : Cochains h (M := M) n) :
    ((coefficientComplexMap h ρ c ρ' c' a).f n).hom f = cochainPost h ρ ρ' a n f := rfl

theorem cochainCohomologyEquiv_natural (n : ℕ) (z : Cohomology h c.d n) :
    cochainCohomologyEquiv h ρ' c' n (coefficientCohomology h ρ c ρ' c' a n z) =
      homologyMap (coefficientComplexMap h ρ c ρ' c' a) n
        (cochainCohomologyEquiv h ρ c n z) := by
  induction z using Submodule.Quotient.induction_on with | _ f =>
  rfl

end Coefficients

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtBalance
universe u v w

/-- A common target identifies commuting source endomorphisms under the
canonical comparison. The first augmentation need only be injective on H. -/
theorem homology_comparison_intertwines
    {R : Type u} [Ring R]
    {C D T : CochainComplex (ModuleCat.{v} R) ℕ}
    (α : C ⟶ T) (β : D ⟶ T) (a : C ⟶ C) (b : D ⟶ D) (t : T ⟶ T)
    (ha : a ≫ α = α ≫ t) (hb : b ≫ β = β ≫ t)
    (n : ℕ) (hinj : Function.Injective (homologyMap α n))
    (e : Homology D n →ₗ[R] Homology C n)
    (he : (homologyMap α n).comp e = homologyMap β n) :
    e.comp (homologyMap b n) = (homologyMap a n).comp e := by
  apply LinearMap.ext
  intro x
  apply hinj
  have hax : (homologyMap α n).comp (homologyMap a n) =
      (homologyMap t n).comp (homologyMap α n) := by
    simpa only [P103.Ch10.Complexes.homologyMap_comp] using congrArg (fun f => homologyMap f n) ha
  have hbx : (homologyMap β n).comp (homologyMap b n) =
      (homologyMap t n).comp (homologyMap β n) := by
    simpa only [P103.Ch10.Complexes.homologyMap_comp] using congrArg (fun f => homologyMap f n) hb
  change homologyMap α n (e (homologyMap b n x)) =
    homologyMap α n (homologyMap a n (e x))
  calc
    _ = homologyMap β n (homologyMap b n x) := LinearMap.congr_fun he _
    _ = homologyMap t n (homologyMap β n x) := LinearMap.congr_fun hbx _
    _ = homologyMap t n (homologyMap α n (e x)) := by simpa only [LinearMap.comp_apply] using congrArg (homologyMap t n) (LinearMap.congr_fun he x).symm
    _ = _ := (LinearMap.congr_fun hax _).symm

/-- Any family of additive operators commuting with the two Hom differentials
is an endomorphism of the actual first-quadrant Hom bicomplex. -/
def homBicomplexEnd
    {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : CochainComplex (ModuleCat.{w} R) ℕ)
    (T : ∀ p q, Module.End ℤ (C.X p →ₗ[R] D.X q))
    (hv : ∀ p q q' (h : q+1=q') f,
      T p q' ((D.d q q').hom.comp f) = (D.d q q').hom.comp (T p q f))
    (hh : ∀ p p' q (h : p+1=p') f,
      T p' q (f.comp (C.d p' p).hom) = (T p q f).comp (C.d p' p).hom) :
    homBicomplex C D ⟶ homBicomplex C D where
  f p :=
    { f q := ModuleCat.ofHom (T p q)
      comm' q q' h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        exact (hv p q q' h f).symm }
  comm' p p' h := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (hh p p' q h f).symm

section Augmentations
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
open P103.Ch11.ExtBalance P103.HomTensorExactness
variable {R : Type u} [Ring R]
  {A : Type v} {B : Type w}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Equivariance of the left augmentation is checked before the total
inclusion, hence directly on the coefficient augmentation. -/
theorem projectiveAugmentation_intertwines
    (P : LeftResolution R A) (I : InjectiveResolution R B)
    (a : homComplex P.complex B ⟶ homComplex P.complex B)
    (t : homBicomplex P.complex I.complex ⟶ homBicomplex P.complex I.complex)
    (h : ∀ n f, ((t.f n).f 0).hom (I.η.comp f) =
      I.η.comp ((a.f n).hom f)) :
    a ≫ projectiveAugmentation P I =
      projectiveAugmentation P I ≫ HomologicalComplex₂.total.map t (ComplexShape.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change a.f n ≫ (projectiveAugmentation P I).f n =
    (projectiveAugmentation P I).f n ≫ _
  rw [projectiveAugmentation_formula P I n]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map,
    ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (h n f).symm

/-- Equivariance of the right augmentation is checked before its total
inclusion, directly on precomposition with the projective augmentation. -/
theorem injectiveAugmentation_intertwines
    (P : LeftResolution R A) (I : InjectiveResolution R B)
    (b : injectiveHom A I.complex ⟶ injectiveHom A I.complex)
    (t : homBicomplex P.complex I.complex ⟶ homBicomplex P.complex I.complex)
    (h : ∀ n f, ((t.f 0).f n).hom (f.comp P.ε) =
      ((b.f n).hom f).comp P.ε) :
    b ≫ injectiveAugmentation P I =
      injectiveAugmentation P I ≫ HomologicalComplex₂.total.map t (ComplexShape.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change b.f n ≫ (injectiveAugmentation P I).f n =
    (injectiveAugmentation P I).f n ≫ _
  rw [injectiveAugmentation_formula P I n]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map,
    ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (h n f).symm

end Augmentations
end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable [Module (U k h) M] [IsScalarTower k (U k h) M]
variable (ρ : Representation k g M) (hρ : ∀ a : h, ∀ m : M, inclusion k h a • m = ρ a m)

include hρ in
/-- An ideal-invariant vector has its entire enveloping action through augmentation. -/
theorem invariant_enveloping_smul (m : invariants h ρ) (a : U k h) :
    a • (m : M) = augmentation k h a • (m : M) := by
  induction a using enveloping_induction k h with
  | scalar r =>
    rw [(augmentation_properties k h).2 r]
    exact IsScalarTower.algebraMap_smul (U k h) r m.val
  | generator a =>
    rw [(augmentation_properties k h).1 a, hρ, m.property a, zero_smul]
  | mul a b ha hb =>
    rw [mul_smul, hb, smul_comm a (augmentation k h b), ha, smul_smul, map_mul]
    rw [mul_comm]
  | add a b ha hb => rw [add_smul, ha, hb, map_add, add_smul]

attribute [local instance] CE.Ext.trivialModule

instance trivialModuleTower : IsScalarTower k (U k h) k := by
  apply IsScalarTower.of_algebraMap_smul
  intro r s
  change augmentation k h (algebraMap k (U k h) r) * s = r * s
  rw [(augmentation_properties k h).2]

/-- Evaluation of a homomorphism out of the trivial module is ideal-invariant. -/
def trivialHomEvaluation (f : k →ₗ[U k h] M) : invariants h ρ :=
  ⟨f 1, by
    intro a
    rw [← hρ]
    have hf := f.map_smul (inclusion k h a) (1 : k)
    have hz : (inclusion k h a) • (1 : k) = 0 := by
      change augmentation k h (inclusion k h a) * 1 = 0
      rw [(augmentation_properties k h).1, zero_mul]
    rw [hz, map_zero] at hf
    exact hf.symm⟩

/-- The inverse homomorphism sends r to r times the invariant vector. -/
def trivialHomOfInvariant (m : invariants h ρ) : k →ₗ[U k h] M where
  toFun r := r • (m : M)
  map_add' r s := add_smul r s _
  map_smul' a r := by
    change (augmentation k h a * r) • (m : M) = a • (r • (m : M))
    rw [smul_comm a r, invariant_enveloping_smul h ρ hρ m, smul_smul, mul_comm]

/-- The Hom/invariants identification has no dimension or basis condition. -/
def trivialHomEquiv : (k →ₗ[U k h] M) ≃ₗ[k] invariants h ρ where
  toFun := trivialHomEvaluation h ρ hρ
  invFun := trivialHomOfInvariant h ρ hρ
  left_inv f := by
    apply LinearMap.ext
    intro r
    change r • f 1 = f r
    have hr := f.map_smul (algebraMap k (U k h) r) (1 : k)
    change f (augmentation k h (algebraMap k (U k h) r) * 1) =
      algebraMap k (U k h) r • f 1 at hr
    rw [(augmentation_properties k h).2, mul_one, IsScalarTower.algebraMap_smul] at hr
    exact hr.symm
  right_inv m := by apply Subtype.ext; exact one_smul k m.val
  map_add' f t := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; rfl

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w z
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
variable {M : Type w} [AddCommGroup M] [Module k M]
  [Module (CE.U k h) M] [IsScalarTower k (CE.U k h) M]
variable (ρ : Representation k g M)

/-- The printed Lie operator transported to free-resolution Hom coordinates. -/
def resolutionHomAction (n : ℕ) (y : g) :
    Module.End k (CE.V k h n →ₗ[CE.U k h] M) :=
  ((CE.homEquiv k h M n).symm.toLinearMap.comp (derivative h ρ n y)).comp
    (CE.homEquiv k h M n).toLinearMap

@[simp] theorem resolutionHomAction_evaluate (n : ℕ) (y : g)
    (F : CE.V k h n →ₗ[CE.U k h] M) :
    CE.homEquiv k h M n (resolutionHomAction h ρ n y F) =
      derivative h ρ n y (CE.homEquiv k h M n F) := by
  simp only [resolutionHomAction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

variable (hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m)

include hρ in
theorem resolutionHomAction_boundary (n : ℕ) (y : g)
    (F : CE.V k h n →ₗ[CE.U k h] M) :
    resolutionHomAction h ρ (n+1) y (F.comp (CE.boundary k h n)) =
      (resolutionHomAction h ρ n y F).comp (CE.boundary k h n) := by
  apply (CE.homEquiv k h M (n+1)).injective
  change CE.homEquiv k h M (n+1) (resolutionHomAction h ρ (n+1) y
      (CE.homCoboundary k h M (CE.boundary k h) n F)) =
    CE.homEquiv k h M (n+1) (CE.homCoboundary k h M (CE.boundary k h) n
      (resolutionHomAction h ρ n y F))
  rw [resolutionHomAction_evaluate,
    ← CE.coboundary_comparison k h M (CE.boundary k h) n,
    ← CE.coboundary_comparison k h M (CE.boundary k h) n,
    resolutionHomAction_evaluate]
  exact (differential_derivative h ρ hρ n y _).symm

section Naturality
variable {N : Type z} [AddCommGroup N] [Module k N]
  [Module (CE.U k h) N] [IsScalarTower k (CE.U k h) N]
variable (σ : Representation k g N)
variable (a : M →ₗ[CE.U k h] N)
variable (ha : LieIntertwines ρ σ (a.restrictScalars k))

include ha in
theorem resolutionHomAction_post (n : ℕ) (y : g)
    (F : CE.V k h n →ₗ[CE.U k h] M) :
    resolutionHomAction h σ n y (a.comp F) =
      a.comp (resolutionHomAction h ρ n y F) := by
  apply (CE.homEquiv k h N n).injective
  rw [resolutionHomAction_evaluate, CE.homEquiv_natural,
    CE.homEquiv_natural, resolutionHomAction_evaluate]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change derivative h σ n y ((a.restrictScalars k).comp (CE.homEquiv k h M n F))
    (CE.wedge k h n x) =
      a (derivative h ρ n y (CE.homEquiv k h M n F) (CE.wedge k h n x))
  rw [derivative_formula h σ, derivative_formula h ρ]
  simp only [LinearMap.comp_apply, map_sub, map_sum]
  congr 1
  exact (ha y _).symm

end Naturality
end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
open scoped TensorProduct
universe u v w z
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable [Module (U k h) M] [IsScalarTower k (U k h) M]
variable (ρ : Representation k g M) (hρ : ∀ a : h, ∀ m : M, inclusion k h a • m = ρ a m)
attribute [local instance] CE.Ext.trivialModule

/-- The ambient action on trivial-module Hom, in invariant-vector coordinates. -/
def trivialHomAction (y : g) : Module.End k (k →ₗ[U k h] M) :=
  ((trivialHomEquiv h ρ hρ).symm.toLinearMap.comp (invariantAmbient h ρ y)).comp
    (trivialHomEquiv h ρ hρ).toLinearMap

@[simp] theorem trivialHomAction_evaluate (y : g) (f : k →ₗ[U k h] M) :
    trivialHomAction h ρ hρ y f 1 = ρ y (f 1) := by
  have he := (trivialHomEquiv h ρ hρ).apply_symm_apply
    (invariantAmbient h ρ y (trivialHomEquiv h ρ hρ f))
  exact congrArg (fun m : invariants h ρ => (m : M)) he

variable [Module.Free k h]

/-- Precomposition with the free-resolution augmentation is the zero cochain
of the invariant vector obtained by evaluation at 1. -/
theorem trivialHom_augmentation_evaluate (f : k →ₗ[U k h] M) :
    CE.homEquiv k h M 0
      (f.comp (CE.Ext.augmentationLinear k h (CE.boundary k h) (CE.boundary_augmented k h))) =
      zeroCochain h (f 1) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change f (CE.augmentation k h ((1 : U k h) ⊗ₜ[k] CE.wedge k h 0 x)) =
    zeroCochain h (f 1) (CE.wedge k h 0 x)
  rw [zeroCochain_wedge]
  congr 1
  simp [CE.augmentation, CE.wedge]

end AdvancedHomologicalAlgebra.LieQuotientAction




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module (U k g) M]

abbrev idealChain := CE.Ext.chain k h (CE.boundary k h) (CE.boundary_augmented k h)

attribute [local instance] restrictedModule resolutionTermModule

def resolutionBicomplexAction (I : InjectiveResolution (U k g) M) (y : g) :
    homBicomplex (idealChain h) (restrictedInjectiveResolution h I).complex ⟶
      homBicomplex (idealChain h) (restrictedInjectiveResolution h I).complex := by
  apply homBicomplexEnd (idealChain h) (restrictedInjectiveResolution h I).complex
    (fun p q => (resolutionHomAction h (resolutionTermRepresentation I q) p y).toAddMonoidHom.toIntLinearMap)
  · intro p q q' he f
    subst q'
    change resolutionHomAction h (resolutionTermRepresentation I (q+1)) p y
      (((restrictedInjectiveResolution h I).complex.d q (q+1)).hom.comp f) =
        ((restrictedInjectiveResolution h I).complex.d q (q+1)).hom.comp
          (resolutionHomAction h (resolutionTermRepresentation I q) p y f)
    exact resolutionHomAction_post h (resolutionTermRepresentation I q)
      (resolutionTermRepresentation I (q+1))
      ((restrictedInjectiveResolution h I).complex.d q (q+1)).hom
      (resolutionDifferential_intertwines I q (q+1)) p y f
  · intro p p' q he f
    subst p'
    simp only [idealChain, CE.Ext.chain, ChainComplex.of_d, ModuleCat.hom_ofHom]
    exact resolutionHomAction_boundary h (resolutionTermRepresentation I q)
        (resolutionTerm_restriction h I q) p y f

end AdvancedHomologicalAlgebra.LieQuotientAction


namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable (ρ : Representation k g M) (c : CochainCalculus h ρ)

section CalculusEvaluation
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
variable [Module.Free k h]
variable [Module (CE.U k h) M] [IsScalarTower k (CE.U k h) M]
variable (hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m)

/-- Evaluation identifies the actual restricted CE Hom complex with the
complex from any calculus satisfying the printed formula. -/
def calculusEvaluationIso :
    homComplex (CE.Ext.chain k h (CE.boundary k h) (CE.boundary_augmented k h)) M ≅
      calculusComplex h ρ c := by
  have hd : c.d = differential h (M := M) := by
    funext n
    apply LinearMap.ext
    intro f
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change c.d n f (CE.wedge k h (n+1) x) =
      differential h (M := M) n f (CE.wedge k h (n+1) x)
    rw [c.d_formula, differential_formula h ρ hρ]
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n => (CE.homEquiv k h M n).toAddEquiv.toIntLinearEquiv.toModuleIso)
    (by
      intro i j hij
      change i+1=j at hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro F
      simp only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      change c.d i (CE.homEquiv k h M i F) =
        CE.homEquiv k h M (i+1)
          (((homComplex (CE.Ext.chain k h (CE.boundary k h)
            (CE.boundary_augmented k h)) M).d i (i+1)).hom F)
      rw [hd, differential, P103.Ch11.ExtTorDefinitions.hom_differential,
        CE.coboundary_comparison]
      simp only [CE.Ext.chain, ChainComplex.of_d, ModuleCat.hom_ofHom, CE.homCoboundary])

@[simp] theorem calculusEvaluationIso_apply (n : ℕ)
    (F : CE.V k h n →ₗ[CE.U k h] M) :
    ((calculusEvaluationIso h ρ c hρ).hom.f n).hom F = CE.homEquiv k h M n F := rfl

end CalculusEvaluation

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
section HomCoordinates
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
  [Module (CE.U k h) M] [IsScalarTower k (CE.U k h) M]
variable (ρ : Representation k g M) (hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m)

/-- The Lie derivative as an endomorphism of the CE free-resolution Hom complex. -/
def resolutionCochainAction (y : g) :
    homComplex (idealChain h) M ⟶ homComplex (idealChain h) M :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom
      (resolutionHomAction h ρ n y).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [P103.Ch11.ExtTorDefinitions.hom_differential,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      change ((resolutionHomAction h ρ n y f).comp
        ((idealChain h).d (n+1) n).hom) =
          resolutionHomAction h ρ (n+1) y (f.comp ((idealChain h).d (n+1) n).hom)
      simp only [idealChain, CE.Ext.chain, ChainComplex.of_d, ModuleCat.hom_ofHom]
      exact (resolutionHomAction_boundary h ρ hρ n y f).symm)

end HomCoordinates

variable (h : LieIdeal k g)
attribute [local instance 2000] CE.Ext.trivialModule

abbrev idealResolution : LeftResolution (CE.U k h) k :=
  @CE.Ext.resolution k h _ _ _ (CE.boundary k h) (CE.boundary_augmented k h)
    (CE.Ext.boundary_exact k h)

section AmbientResolution
variable {M : Type w} [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule

/-- The coefficient augmentation respects the printed Lie derivative. -/
theorem resolutionProjectiveAugmentation_intertwines
    (I : InjectiveResolution (U k g) M) (y : g) :
    resolutionCochainAction h (moduleRepresentation g M) (restrictedModule_inclusion h) y ≫
        P103.Ch11.ExtBalance.projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I) =
      P103.Ch11.ExtBalance.projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I) ≫
        HomologicalComplex₂.total.map (resolutionBicomplexAction h I y) (ComplexShape.up ℕ) := by
  apply projectiveAugmentation_intertwines (idealResolution h) (restrictedInjectiveResolution h I)
  intro n f
  change resolutionHomAction h (resolutionTermRepresentation I 0) n y
      ((restrictedInjectiveResolution h I).η.comp f) =
    (restrictedInjectiveResolution h I).η.comp
      (resolutionHomAction h (moduleRepresentation g M) n y f)
  exact resolutionHomAction_post h (moduleRepresentation g M) (resolutionTermRepresentation I 0)
    (restrictedInjectiveResolution h I).η (resolutionAugmentation_intertwines I) n y f

end AmbientResolution
end AdvancedHomologicalAlgebra.LieQuotientAction




noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w z
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable [Module (U k h) M] [IsScalarTower k (U k h) M]
variable (ρ : Representation k g M) (hρ : ∀ a : h, ∀ m : M, inclusion k h a • m = ρ a m)
attribute [local instance 2000] CE.Ext.trivialModule
variable {N : Type z} [AddCommGroup N] [Module k N]
variable [Module (U k h) N] [IsScalarTower k (U k h) N]
variable (σ : Representation k g N) (hσ : ∀ a : h, ∀ m : N, inclusion k h a • m = σ a m)

/-- Evaluation identifies coefficient postcomposition with the invariant map. -/
theorem trivialHomAction_post (a : M →ₗ[U k h] N)
    (ha : LieIntertwines ρ σ (a.restrictScalars k)) (y : g) (f : k →ₗ[U k h] M) :
    trivialHomAction h σ hσ y (a.comp f) = a.comp (trivialHomAction h ρ hρ y f) := by
  apply (trivialHomEquiv h σ hσ).injective
  apply Subtype.ext
  change trivialHomAction h σ hσ y (a.comp f) 1 = a (trivialHomAction h ρ hρ y f 1)
  rw [trivialHomAction_evaluate, trivialHomAction_evaluate]
  exact (ha y (f 1)).symm

/-- The printed action on constant degree-zero cochains is the coefficient action. -/
theorem derivative_zeroCochain (y : g) (m : M) :
    derivative h ρ 0 y (zeroCochain h m) = zeroCochain h (ρ y m) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change derivative h ρ 0 y (zeroCochain h m) (CE.wedge k h 0 x) =
    zeroCochain h (ρ y m) (CE.wedge k h 0 x)
  rw [derivative_formula, zeroCochain_wedge, zeroCochain_wedge]
  simp

variable [Module.Free k h]
/-- The two actions agree on the actual injective augmentation, before totalization. -/
theorem resolutionHomAction_augmentation (y : g) (f : k →ₗ[U k h] M) :
    resolutionHomAction h ρ 0 y
      (f.comp (CE.Ext.augmentationLinear k h (CE.boundary k h) (CE.boundary_augmented k h))) =
      (trivialHomAction h ρ hρ y f).comp
        (CE.Ext.augmentationLinear k h (CE.boundary k h) (CE.boundary_augmented k h)) := by
  apply (CE.homEquiv k h M 0).injective
  rw [resolutionHomAction_evaluate, trivialHom_augmentation_evaluate,
    trivialHom_augmentation_evaluate, derivative_zeroCochain, trivialHomAction_evaluate]

end AdvancedHomologicalAlgebra.LieQuotientAction

noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule
attribute [local instance 2000] CE.Ext.trivialModule

/-- The ambient action on the invariant complex, expressed as trivial-module Hom. -/
def injectiveHomEndomorphism (I : InjectiveResolution (U k g) M) (y : g) :
    injectiveHom k (restrictedInjectiveResolution h I).complex ⟶
      injectiveHom k (restrictedInjectiveResolution h I).complex :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom
      (trivialHomAction h (resolutionTermRepresentation I n) (resolutionTerm_restriction h I n) y).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (trivialHomAction_post h (resolutionTermRepresentation I n)
        (resolutionTerm_restriction h I n) (resolutionTermRepresentation I (n+1))
        (resolutionTerm_restriction h I (n+1))
        ((restrictedInjectiveResolution h I).complex.d n (n+1)).hom
        (resolutionDifferential_intertwines I n (n+1)) y f).symm)

/-- The invariant-complex augmentation into the Hom total is equivariant. -/
theorem injectiveAugmentation_action (I : InjectiveResolution (U k g) M) (y : g) :
    injectiveHomEndomorphism h I y ≫
        P103.Ch11.ExtBalance.injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I) =
      P103.Ch11.ExtBalance.injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I) ≫
        HomologicalComplex₂.total.map (resolutionBicomplexAction h I y) (ComplexShape.up ℕ) := by
  apply injectiveAugmentation_intertwines
  intro n f
  exact resolutionHomAction_augmentation h (resolutionTermRepresentation I n)
    (resolutionTerm_restriction h I n) y f

end AdvancedHomologicalAlgebra.LieQuotientAction



set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie CategoryTheory
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable (ρ : Representation k g M) (c : CochainCalculus h ρ)
/-- The displayed formula uniquely determines each infinitesimal operator. -/
theorem calculus_derivative_eq (n : ℕ) (y : g) (f : Cochains h (M := M) n) :
    derivative h ρ n y f = c.L n y f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change derivative h ρ n y f (CE.wedge k h n x) = c.L n y f (CE.wedge k h n x)
  rw [derivative_formula, c.L_formula]






section EvaluationAction
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
variable [Module (CE.U k h) M] [IsScalarTower k (CE.U k h) M]
variable (hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m)

/-- Evaluation respects the actual Lie endomorphisms in every degree. -/
theorem calculusEvaluationIso_resolutionAction (n : ℕ) (y : g)
    (F : CE.V k h n →ₗ[CE.U k h] M) :
    ((calculusEvaluationIso h ρ c hρ).hom.f n).hom (resolutionHomAction h ρ n y F) =
      c.L n y (((calculusEvaluationIso h ρ c hρ).hom.f n).hom F) := by
  change CE.homEquiv k h M n (resolutionHomAction h ρ n y F) =
    c.L n y (CE.homEquiv k h M n F)
  rw [resolutionHomAction_evaluate]
  exact calculus_derivative_eq h ρ c n y _


theorem calculusEvaluationIso_equivariant (y : g) :
    resolutionCochainAction h ρ hρ y ≫ (calculusEvaluationIso h ρ c hρ).hom =
      (calculusEvaluationIso h ρ c hρ).hom ≫ cochainEndomorphism h ρ c y := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  exact calculusEvaluationIso_resolutionAction h ρ c hρ n y F


theorem calculusEvaluationIso_homologyAction (n : ℕ) (y : g)
    (z : Homology (homComplex (CE.Ext.chain k h (CE.boundary k h)
      (CE.boundary_augmented k h)) M) n) :
    homologyMap (calculusEvaluationIso h ρ c hρ).hom n
        (homologyMap (resolutionCochainAction h ρ hρ y) n z) =
      homologyMap (cochainEndomorphism h ρ c y) n
        (homologyMap (calculusEvaluationIso h ρ c hρ).hom n z) := by
  induction z using Submodule.Quotient.induction_on with | _ f =>
  change homologyClass _ n (cyclesMap (calculusEvaluationIso h ρ c hρ).hom n
      (cyclesMap (resolutionCochainAction h ρ hρ y) n f)) =
    homologyClass _ n (cyclesMap (cochainEndomorphism h ρ c y) n
      (cyclesMap (calculusEvaluationIso h ρ c hρ).hom n f))
  congr 1
  apply Subtype.ext
  exact calculusEvaluationIso_resolutionAction h ρ c hρ n y f.val

end EvaluationAction

end AdvancedHomologicalAlgebra.LieQuotientAction




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
attribute [local instance] restrictedModule resolutionTermModule

/-- The actual CE resolution consists of projective U(h)-modules. -/
theorem idealResolution_projective : (idealResolution h).IsProjective := by
  intro n
  change Module.Projective (CE.U k h) (CE.V k h n)
  letI := CE.term_free k h n
  exact Module.Projective.of_free

variable {M : Type w} [AddCommGroup M] [Module (U k g) M]

/-- The comparison fixed by the two actual augmentations of the Hom bicomplex. -/
def resolutionBalance (I : InjectiveResolution (U k g) M) (n : ℕ) :
    Homology (injectiveHom k (restrictedInjectiveResolution h I).complex) n ≃ₗ[ℤ]
      ExtWith (idealResolution h) M n :=
  comparisonOfQuasiIsomorphisms (idealResolution h) (restrictedInjectiveResolution h I)
    (projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I))
    (injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I))
    (projectiveAugmentation_quasiIso _ _ (idealResolution_projective h))
    (injectiveAugmentation_quasiIso _ _) n

/-- The augmentation equation determines this comparison, before taking actions. -/
theorem resolutionBalance_formula (I : InjectiveResolution (U k g) M) (n : ℕ) :
    (homologyMap (projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I)) n).comp
      (resolutionBalance h I n).toLinearMap =
        homologyMap (injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I)) n :=
  comparisonOfQuasiIsomorphisms_formula _ _ _ _ _ _ n

end AdvancedHomologicalAlgebra.LieQuotientAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule

/-- The canonical balanced comparison respects each printed infinitesimal operator. -/
theorem resolutionBalance_action (I : InjectiveResolution (U k g) M) (y : g) (n : ℕ)
    (x : Homology (injectiveHom k (restrictedInjectiveResolution h I).complex) n) :
    resolutionBalance h I n (homologyMap (injectiveHomEndomorphism h I y) n x) =
      homologyMap
        (resolutionCochainAction h (moduleRepresentation g M) (restrictedModule_inclusion h) y) n
        (resolutionBalance h I n x) := by
  have hh := homology_comparison_intertwines
    (projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I))
    (injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I))
    (resolutionCochainAction h (moduleRepresentation g M) (restrictedModule_inclusion h) y)
    (injectiveHomEndomorphism h I y)
    (HomologicalComplex₂.total.map (resolutionBicomplexAction h I y) (ComplexShape.up ℕ))
    (resolutionProjectiveAugmentation_intertwines h I y)
    (injectiveAugmentation_action h I y) n
    ((projectiveAugmentation_quasiIso _ _ (idealResolution_projective h) n).1)
    (resolutionBalance h I n).toLinearMap (resolutionBalance_formula h I n)
  exact LinearMap.congr_fun hh x

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g)
attribute [local instance] restrictedModule resolutionTermModule
variable {M N : Type w} [AddCommGroup M] [Module (U k g) M]
  [AddCommGroup N] [Module (U k g) N]

/-- Restriction changes no values of a module map. -/
def restrictedCoefficientMap (f : M →ₗ[U k g] N) : M →ₗ[U k h] N :=
  { f with map_smul' := fun a m => f.map_smul ((IdealEnveloping.inducedMap k g h) a) m }

/-- Restriction of any actual ambient comparison lift. -/
def restrictedResolutionMap
    {I : InjectiveResolution (U k g) M} {J : InjectiveResolution (U k g) N}
    (m : I.complex ⟶ J.complex) :
    (restrictedInjectiveResolution h I).complex ⟶ (restrictedInjectiveResolution h J).complex :=
  ((ModuleCat.restrictScalars (IdealEnveloping.inducedMap k g h).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℕ)).map m

/-- Naturality for every ambient coefficient map and every augmented lift,
including independence of the chosen injective resolutions. -/
theorem resolutionBalance_natural
    (I : InjectiveResolution (U k g) M) (J : InjectiveResolution (U k g) N)
    (f : M →ₗ[U k g] N) (m : I.complex ⟶ J.complex)
    (hm : CochainLift (ofInjective I) J f m) (n : ℕ) :
    (resolutionBalance h J n).toLinearMap.comp
        (homologyMap (injectiveHomMap (LinearMap.id : k →ₗ[U k h] k)
          (restrictedResolutionMap h m)) n) =
      (homologyMap (homPostMap (idealChain h) (restrictedCoefficientMap h f)) n).comp
        (resolutionBalance h I n).toLinearMap := by
  have hm' : CochainLift (ofInjective (restrictedInjectiveResolution h I))
      (restrictedInjectiveResolution h J) (restrictedCoefficientMap h f)
      (restrictedResolutionMap h m) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hm x
  have hl : ChainLift (idealResolution h) (idealResolution h) LinearMap.id
      (𝟙 (idealChain h)) := by
    apply LinearMap.ext
    intro x
    rfl
  have hh := balance_natural (U k h) k k M N
    (idealResolution h) (idealResolution h)
    (restrictedInjectiveResolution h I) (restrictedInjectiveResolution h J)
    (idealResolution_projective h) (idealResolution_projective h)
    LinearMap.id (restrictedCoefficientMap h f) (𝟙 (idealChain h))
    (restrictedResolutionMap h m) hl hm'
    (projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I))
    (injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I))
    (projectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h J))
    (injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h J))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (projectiveAugmentation_quasiIso _ _ (idealResolution_projective h))
    (projectiveAugmentation_quasiIso _ _ (idealResolution_projective h)) n
    (resolutionBalance h I n) (resolutionBalance h J n)
    (resolutionBalance_formula h I n) (resolutionBalance_formula h J n)
  have hcomp : homPreMap (𝟙 (idealChain h)) M ≫
      homPostMap (idealResolution h).complex (restrictedCoefficientMap h f) =
      homPostMap (idealChain h) (restrictedCoefficientMap h f) := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro F
    rfl
  rw [hcomp] at hh
  exact hh

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open scoped ModuleCat.Algebra
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule

/-- The scalar endomorphism on the invariant complex in trivial-Hom coordinates. -/
def injectiveHomScalar (I : InjectiveResolution (U k g) M) (r : k) :
    injectiveHom k (restrictedInjectiveResolution h I).complex ⟶
      injectiveHom k (restrictedInjectiveResolution h I).complex :=
  injectiveHomMap LinearMap.id (restrictedResolutionMap h (r • 𝟙 I.complex))

@[simp] theorem injectiveHomScalar_apply (I : InjectiveResolution (U k g) M) (r : k)
    (n : ℕ) (F : k →ₗ[U k h] I.complex.X n) :
    ((injectiveHomScalar h I r).f n).hom F = r • F := by
  apply LinearMap.ext
  intro x
  rfl

/-- Scalar naturality of the canonical comparison, without assigning an
artificial scalar action to either integer-valued Homology quotient. -/
theorem resolutionBalance_scalar (I : InjectiveResolution (U k g) M) (r : k) (n : ℕ)
    (x : Homology (injectiveHom k (restrictedInjectiveResolution h I).complex) n) :
    resolutionBalance h I n (homologyMap (injectiveHomScalar h I r) n x) =
      homologyMap (homPostMap (idealChain h) (r • (LinearMap.id : M →ₗ[U k h] M))) n
        (resolutionBalance h I n x) := by
  have hm : CochainLift (ofInjective I) I (r • (LinearMap.id : M →ₗ[U k g] M))
      (r • 𝟙 I.complex) := by
    apply LinearMap.ext
    intro m
    change r • I.η m = I.η (r • m)
    exact ((I.η.restrictScalars k).map_smul r m).symm
  have hh := resolutionBalance_natural h I I
    (r • (LinearMap.id : M →ₗ[U k g] M)) (r • 𝟙 I.complex) hm n
  have hf : restrictedCoefficientMap h (r • (LinearMap.id : M →ₗ[U k g] M)) =
      r • (LinearMap.id : M →ₗ[U k h] M) := by
    apply LinearMap.ext
    intro m
    rfl
  rw [hf] at hh
  exact LinearMap.congr_fun hh x

end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtBalance
universe u v w
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule
attribute [local instance 2000] CE.Ext.trivialModule
variable (I : InjectiveResolution (U k g) M)

/-- The differential on ideal-invariants is the original resolution differential. -/
def invariantResolutionDifferential (p q : ℕ) :
    invariants h (resolutionTermRepresentation I p) →ₗ[k]
      invariants h (resolutionTermRepresentation I q) :=
  invariantsMap h (resolutionTermRepresentation I p) (resolutionTermRepresentation I q)
    ⟨(I.complex.d p q).hom.restrictScalars k, resolutionDifferential_intertwines I p q⟩

/-- Apply actual ideal-invariants to the given ambient injective resolution. -/
def invariantResolutionComplex : CochainComplex (ModuleCat.{max u v w} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (invariants h (resolutionTermRepresentation I n)))
    (fun n => ModuleCat.ofHom (invariantResolutionDifferential h I n (n+1))) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      apply Subtype.ext
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (I.complex.d_comp_d n (n+1) (n+2))) m.val)

/-- Integer coordinates preserve the same invariant vectors and differential. -/
def invariantResolutionIntegerComplex : CochainComplex (ModuleCat.{max u v w} ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (invariants h (resolutionTermRepresentation I n)))
    (fun n => ModuleCat.ofHom (invariantResolutionDifferential h I n (n+1)).toAddMonoidHom.toIntLinearMap)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      apply Subtype.ext
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (I.complex.d_comp_d n (n+1) (n+2))) m.val)

/-- The injective Hom computation is exactly the invariant-resolution complex,
by evaluation at 1 in every degree. -/
def invariantResolutionIso :
    injectiveHom k (restrictedInjectiveResolution h I).complex ≅
      invariantResolutionIntegerComplex h I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (trivialHomEquiv h (resolutionTermRepresentation I n)
      (resolutionTerm_restriction h I n)).toAddEquiv.toIntLinearEquiv.toModuleIso)
    (by
      intro p q hpq
      change p+1=q at hpq
      subst q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      simp only [invariantResolutionIntegerComplex, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      rfl)

@[simp] theorem invariantResolutionIso_apply (n : ℕ) (f : k →ₗ[U k h] I.complex.X n) :
    ((show invariants h (resolutionTermRepresentation I n) from
      ((invariantResolutionIso h I).hom.f n).hom f).val) = f 1 := rfl

/-- The quotient acts on each term by the previously constructed invariant action. -/
abbrev invariantResolutionTermAction (n : ℕ) :=
  invariantQuotient h (resolutionTermRepresentation I n)

/-- The canonical quotient actions commute with the invariant-resolution maps. -/
theorem invariantResolutionDifferential_intertwines (p q : ℕ) :
    LieIntertwines (invariantResolutionTermAction h I p) (invariantResolutionTermAction h I q)
      (invariantResolutionDifferential h I p q) :=
  invariantsMap_intertwines h (resolutionTermRepresentation I p)
    (invariantQuotient h (resolutionTermRepresentation I p))
    (invariantQuotient_formula h (resolutionTermRepresentation I p))
    (resolutionTermRepresentation I q)
    (invariantQuotient h (resolutionTermRepresentation I q))
    (invariantQuotient_formula h (resolutionTermRepresentation I q))
    ⟨(I.complex.d p q).hom.restrictScalars k, resolutionDifferential_intertwines I p q⟩

/-- Every quotient element acts by an actual cochain endomorphism. -/
def invariantResolutionEndomorphism (z : g ⧸ h) :
    invariantResolutionComplex h I ⟶ invariantResolutionComplex h I :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (invariantResolutionTermAction h I n z))
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      simpa only [invariantResolutionComplex, invariantResolutionIntegerComplex,
        CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe] using
        invariantResolutionDifferential_intertwines h I n (n+1) z m)

/-- The quotient action preserves the cycles in the invariant-resolution complex. -/
theorem invariantResolutionCycles_stable (n : ℕ) (z : g ⧸ h)
    (m : (invariantResolutionComplex h I).X n) (hm : m ∈ cycles (invariantResolutionComplex h I) n) :
    invariantResolutionTermAction h I n z m ∈ cycles (invariantResolutionComplex h I) n := by
  have hc := (cyclesMap (invariantResolutionEndomorphism h I z) n ⟨m,hm⟩).property
  exact hc

/-- The quotient representation on actual cycles. -/
def invariantResolutionCycleAction (n : ℕ) :
    Representation k (g ⧸ h) (cycles (invariantResolutionComplex h I) n) :=
  subspaceRepresentation (invariantResolutionTermAction h I n)
    (cycles (invariantResolutionComplex h I) n) (invariantResolutionCycles_stable h I n)

/-- The same quotient action preserves the actual boundaries inside cycles. -/
theorem invariantResolutionBoundaries_stable (n : ℕ) (z : g ⧸ h)
    (m : cycles (invariantResolutionComplex h I) n)
    (hm : m ∈ cycleBoundaries (invariantResolutionComplex h I) n) :
    invariantResolutionCycleAction h I n z m ∈ cycleBoundaries (invariantResolutionComplex h I) n := by
  exact mapBoundary (invariantResolutionEndomorphism h I z) n hm

/-- The derived invariant action is the action induced from the canonical
quotient actions on the actual invariant-resolution complex. -/
def invariantResolutionCohomologyAction (n : ℕ) :
    Representation k (g ⧸ h) (Homology (invariantResolutionComplex h I) n) :=
  quotientRepresentation (invariantResolutionCycleAction h I n)
    (cycleBoundaries (invariantResolutionComplex h I) n) (invariantResolutionBoundaries_stable h I n)

@[simp] theorem invariantResolutionCohomologyAction_class (n : ℕ) (z : g ⧸ h)
    (m : cycles (invariantResolutionComplex h I) n) :
    invariantResolutionCohomologyAction h I n z (homologyClass _ n m) =
      homologyClass _ n (cyclesMap (invariantResolutionEndomorphism h I z) n m) := rfl


/-- Evaluation at 1 is k-linear even though the Hom complex is packaged over integers. -/
theorem invariantResolutionIso_smul (n : ℕ) (r : k)
    (f : k →ₗ[U k h] I.complex.X n) :
    (show invariants h (resolutionTermRepresentation I n) from
      ((invariantResolutionIso h I).hom.f n).hom (r • f)) =
      r • (show invariants h (resolutionTermRepresentation I n) from
        ((invariantResolutionIso h I).hom.f n).hom f) :=
  (trivialHomEquiv h (resolutionTermRepresentation I n)
    (resolutionTerm_restriction h I n)).map_smul r f

/-- The integer and k-cycle modules have exactly the same vectors. -/
def invariantResolutionCyclesEquiv (n : ℕ) :
    cycles (invariantResolutionComplex h I) n ≃ₗ[ℤ]
      cycles (invariantResolutionIntegerComplex h I) n where
  toFun m := ⟨m.val, by
    have hm := m.property
    change ((invariantResolutionComplex h I).d n ((ComplexShape.up ℕ).next n)).hom m.val = 0 at hm
    change ((invariantResolutionIntegerComplex h I).d n ((ComplexShape.up ℕ).next n)).hom m.val = 0
    rw [CochainComplex.next] at *
    simpa only [invariantResolutionComplex, invariantResolutionIntegerComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom, AddMonoidHom.coe_toIntLinearMap,
      LinearMap.toAddMonoidHom_coe] using hm⟩
  invFun m := ⟨m.val, by
    have hm := m.property
    change ((invariantResolutionIntegerComplex h I).d n ((ComplexShape.up ℕ).next n)).hom m.val = 0 at hm
    change ((invariantResolutionComplex h I).d n ((ComplexShape.up ℕ).next n)).hom m.val = 0
    rw [CochainComplex.next] at *
    simpa only [invariantResolutionComplex, invariantResolutionIntegerComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom, AddMonoidHom.coe_toIntLinearMap,
      LinearMap.toAddMonoidHom_coe] using hm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invariantResolutionCyclesEquiv_boundaries (n : ℕ)
    (m : cycles (invariantResolutionComplex h I) n) :
    invariantResolutionCyclesEquiv h I n m ∈ cycleBoundaries (invariantResolutionIntegerComplex h I) n ↔
      m ∈ cycleBoundaries (invariantResolutionComplex h I) n := by
  cases n with
  | zero =>
    change (∃ x, ((invariantResolutionIntegerComplex h I).d ((ComplexShape.up ℕ).prev 0) 0).hom x = m.val) ↔
      ∃ x, ((invariantResolutionComplex h I).d ((ComplexShape.up ℕ).prev 0) 0).hom x = m.val
    rw [CochainComplex.prev_nat_zero]
    rw [(invariantResolutionIntegerComplex h I).shape 0 0 (by decide),
      (invariantResolutionComplex h I).shape 0 0 (by decide)]
    rfl
  | succ n =>
    change (∃ x, ((invariantResolutionIntegerComplex h I).d ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom x = m.val) ↔
      ∃ x, ((invariantResolutionComplex h I).d ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom x = m.val
    rw [CochainComplex.prev_nat_succ]
    simp only [invariantResolutionComplex, invariantResolutionIntegerComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom]
    rfl

/-- Changing only scalar packaging preserves the actual quotient cohomology. -/
def invariantResolutionCohomologyEquiv (n : ℕ) :
    Homology (invariantResolutionComplex h I) n ≃ₗ[ℤ]
      Homology (invariantResolutionIntegerComplex h I) n :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ
    (cycleBoundaries (invariantResolutionComplex h I) n)).symm.trans
    (Submodule.Quotient.equiv _ _ (invariantResolutionCyclesEquiv h I n) (by
      ext f
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (invariantResolutionCyclesEquiv_boundaries h I n z).mpr hz
      · intro hf
        refine ⟨(invariantResolutionCyclesEquiv h I n).symm f, ?_, ?_⟩
        · exact (invariantResolutionCyclesEquiv_boundaries h I n _).mp
            (by simpa only [LinearEquiv.apply_symm_apply] using hf)
        · exact (invariantResolutionCyclesEquiv h I n).apply_symm_apply f))

@[simp] theorem invariantResolutionCohomologyEquiv_class (n : ℕ)
    (m : cycles (invariantResolutionComplex h I) n) :
    invariantResolutionCohomologyEquiv h I n (homologyClass _ n m) =
      homologyClass _ n (invariantResolutionCyclesEquiv h I n m) := rfl

/-- The same canonical quotient element acts in integer coordinates. -/
def invariantResolutionIntegerEndomorphism (z : g ⧸ h) :
    invariantResolutionIntegerComplex h I ⟶ invariantResolutionIntegerComplex h I :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (invariantResolutionTermAction h I n z).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      simpa only [invariantResolutionComplex, invariantResolutionIntegerComplex,
        CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe] using
        invariantResolutionDifferential_intertwines h I n (n+1) z m)

/-- Integer packaging carries the canonical action on actual k-cohomology. -/
theorem invariantResolutionCohomologyEquiv_action (n : ℕ) (z : g ⧸ h)
    (m : Homology (invariantResolutionComplex h I) n) :
    invariantResolutionCohomologyEquiv h I n (invariantResolutionCohomologyAction h I n z m) =
      homologyMap (invariantResolutionIntegerEndomorphism h I z) n
        (invariantResolutionCohomologyEquiv h I n m) := by
  induction m using Submodule.Quotient.induction_on with | _ m =>
  rfl

/-- The scalar endomorphism of the same integer complex. -/
def invariantResolutionScalarEndomorphism (r : k) :
    invariantResolutionIntegerComplex h I ⟶ invariantResolutionIntegerComplex h I :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom
      (r • (LinearMap.id : Module.End k (invariants h (resolutionTermRepresentation I n)))).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      simpa only [invariantResolutionIntegerComplex, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe] using
        (invariantResolutionDifferential h I n (n+1)).map_smul r m)

/-- Scalar multiplication on actual k-cohomology is induced on the resolution terms. -/
theorem invariantResolutionCohomologyEquiv_smul (n : ℕ) (r : k)
    (m : Homology (invariantResolutionComplex h I) n) :
    invariantResolutionCohomologyEquiv h I n (r • m) =
      homologyMap (invariantResolutionScalarEndomorphism h I r) n
        (invariantResolutionCohomologyEquiv h I n m) := by
  induction m using Submodule.Quotient.induction_on with | _ m =>
  rfl

end AdvancedHomologicalAlgebra.LieQuotientAction


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
variable (ρ : Representation k g M) (c : CochainCalculus h ρ)

/-- Scalar multiplication is an endomorphism of the displayed cochain complex. -/
def cochainScalar (r : k) : calculusComplex h ρ c ⟶ calculusComplex h ρ c :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom
      (r • (LinearMap.id : Module.End k (Cochains h (M := M) n))).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [calculusComplex, CE.Ext.cochain, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
        LinearMap.smul_apply, LinearMap.id_apply]
      exact map_smul (c.d n) r f)

@[simp] theorem cochainScalar_apply (r : k) (n : ℕ) (f : Cochains h (M := M) n) :
    ((cochainScalar h ρ c r).f n).hom f = r • f := rfl

theorem cochainCohomologyEquiv_scalar (r : k) (n : ℕ) (z : Cohomology h c.d n) :
    cochainCohomologyEquiv h ρ c n (r • z) =
      homologyMap (cochainScalar h ρ c r) n (cochainCohomologyEquiv h ρ c n z) := by
  induction z using Submodule.Quotient.induction_on with | _ f =>
  change homologyClass _ n (cochainCyclesEquiv h ρ c n (r • f)) =
    homologyClass _ n (cyclesMap (cochainScalar h ρ c r) n (cochainCyclesEquiv h ρ c n f))
  congr 1

section Evaluation
variable [Module (CE.U k h) M] [IsScalarTower k (CE.U k h) M]
variable (hρ : ∀ (a : h) (m : M), inclusion k h a • m = ρ a m)

/-- The scalar endomorphism in the actual CE resolution Hom complex. -/
def resolutionCochainScalar (r : k) :
    homComplex (idealChain h) M ⟶ homComplex (idealChain h) M :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom
      (r • (LinearMap.id : Module.End k (CE.V k h n →ₗ[CE.U k h] M))).toAddMonoidHom.toIntLinearMap)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro F
      change CE.V k h n →ₗ[CE.U k h] M at F
      simp only [P103.Ch11.ExtTorDefinitions.hom_differential,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      change (r • F).comp ((idealChain h).d (n+1) n).hom =
        r • F.comp ((idealChain h).d (n+1) n).hom
      rfl)

@[simp] theorem resolutionCochainScalar_apply (r : k) (n : ℕ)
    (F : CE.V k h n →ₗ[CE.U k h] M) :
    ((resolutionCochainScalar h (M := M) r).f n).hom F = r • F := rfl

theorem resolutionCochainScalar_eq_post (r : k) :
    resolutionCochainScalar h (M := M) r =
      homPostMap (idealChain h) (r • (LinearMap.id : M →ₗ[CE.U k h] M)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  rfl

theorem calculusEvaluationIso_scalar (r : k) :
    resolutionCochainScalar h (M := M) r ≫ (calculusEvaluationIso h ρ c hρ).hom =
      (calculusEvaluationIso h ρ c hρ).hom ≫ cochainScalar h ρ c r := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  change CE.V k h n →ₗ[CE.U k h] M at F
  change CE.homEquiv k h M n (r • F) = r • CE.homEquiv k h M n F
  exact map_smul (CE.homEquiv k h M n) r F

end Evaluation
end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtBalance
universe u v w
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule
attribute [local instance 2000] CE.Ext.trivialModule
variable (I : InjectiveResolution (U k g) M)

/-- Evaluation identifies the actual Hom action with the canonical quotient action on invariants. -/
theorem invariantResolutionIso_action (y : g) :
    injectiveHomEndomorphism h I y ≫ (invariantResolutionIso h I).hom =
      (invariantResolutionIso h I).hom ≫
        invariantResolutionIntegerEndomorphism h I (quotientMap k g h y) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change trivialHomAction h (resolutionTermRepresentation I n)
      (resolutionTerm_restriction h I n) y f 1 =
    (invariantQuotient h (resolutionTermRepresentation I n) (quotientMap k g h y)
      (trivialHomEquiv h (resolutionTermRepresentation I n)
        (resolutionTerm_restriction h I n) f) : I.complex.X n)
  rw [trivialHomAction_evaluate, invariantQuotient_formula]
  rfl

/-- Any actual scalar cochain map induces the scalar operator under evaluation. -/
theorem invariantResolutionIso_scalar_map (r : k)
    (s : (restrictedInjectiveResolution h I).complex ⟶ (restrictedInjectiveResolution h I).complex)
    (hs : ∀ n (x : I.complex.X n), (s.f n).hom x = r • x) :
    injectiveHomMap (LinearMap.id : k →ₗ[U k h] k) s ≫ (invariantResolutionIso h I).hom =
      (invariantResolutionIso h I).hom ≫ invariantResolutionScalarEndomorphism h I r := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change k →ₗ[U k h] I.complex.X n at f
  change (s.f n).hom (f 1) = r • f 1
  exact hs n (f 1)


section Scalar
variable [Module k M] [IsScalarTower k (U k g) M]

/-- The actual scalar lift used in balanced naturality is k-linear under evaluation. -/
theorem invariantResolutionIso_scalar (r : k) :
    injectiveHomScalar h I r ≫ (invariantResolutionIso h I).hom =
      (invariantResolutionIso h I).hom ≫ invariantResolutionScalarEndomorphism h I r := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change k →ₗ[U k h] I.complex.X n at f
  change (trivialHomEquiv h (resolutionTermRepresentation I n)
      (resolutionTerm_restriction h I n)) (((injectiveHomScalar h I r).f n).hom f) =
    r • (trivialHomEquiv h (resolutionTermRepresentation I n)
      (resolutionTerm_restriction h I n)) f
  rw [injectiveHomScalar_apply]
  exact (trivialHomEquiv h (resolutionTermRepresentation I n)
    (resolutionTerm_restriction h I n)).map_smul r f

end Scalar

end AdvancedHomologicalAlgebra.LieQuotientAction


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
universe u v w z
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The explicit quotient-homology equivalence induced by a complex isomorphism. -/
def complexHomologyEquiv {R : Type*} [Ring R] {ι : Type*} {s : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{z} R) s} (e : C ≅ D) (n : ι) :
    Homology C n ≃ₗ[R] Homology D n :=
  ((quotientHomology s n).mapIso e).toLinearEquiv

@[simp] theorem complexHomologyEquiv_apply {R : Type*} [Ring R]
    {ι : Type*} {s : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{z} R) s}
    (e : C ≅ D) (n : ι) (x : Homology C n) :
    complexHomologyEquiv e n x = homologyMap e.hom n x := rfl

@[simp] theorem complexHomologyEquiv_symm_apply {R : Type*} [Ring R]
    {ι : Type*} {s : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{z} R) s}
    (e : C ≅ D) (n : ι) (x : Homology D n) :
    (complexHomologyEquiv e n).symm x = homologyMap e.inv n x := rfl

/-- A square of complex endomorphisms gives its square on quotient homology. -/
theorem complexHomologyEquiv_intertwines {R : Type*} [Ring R]
    {ι : Type*} {s : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{z} R) s}
    (e : C ≅ D) (a : C ⟶ C) (b : D ⟶ D) (h : a ≫ e.hom = e.hom ≫ b)
    (n : ι) (x : Homology C n) :
    complexHomologyEquiv e n (homologyMap a n x) =
      homologyMap b n (complexHomologyEquiv e n x) := by
  have he := congrArg (fun f => (quotientHomology s n).map f) h
  simp only [Functor.map_comp] at he
  exact congrArg (fun f => f.hom x) he

private theorem linearEquiv_symm_intertwines {R : Type*} [Semiring R]
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    (e : A ≃ₗ[R] B) (a : A → A) (b : B → B)
    (he : ∀ x, e (a x) = b (e x)) (y : B) :
    e.symm (b y) = a (e.symm y) := by
  apply e.injective
  simpa only [LinearEquiv.apply_symm_apply] using (he (e.symm y)).symm

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule
attribute [local instance 2000] CE.Ext.trivialModule
variable (I : InjectiveResolution (U k g) M)
variable (c : CochainCalculus h (moduleRepresentation g M))

/-- The canonical balanced comparison, in the direction from actual derived
invariants to the printed cycle/boundary quotient. -/
def resolutionComparisonBack (n : ℕ) :
    Homology (invariantResolutionComplex h I) n ≃ₗ[ℤ] Cohomology h c.d n :=
  (invariantResolutionCohomologyEquiv h I n).trans
    ((complexHomologyEquiv (invariantResolutionIso h I) n).symm.trans
      ((resolutionBalance h I n).trans
        ((complexHomologyEquiv
          (calculusEvaluationIso h (moduleRepresentation g M) c (restrictedModule_inclusion h)) n).trans
            (cochainCohomologyEquiv h (moduleRepresentation g M) c n).symm)))


theorem resolutionComparisonBack_smul (n : ℕ) (r : k)
    (z : Homology (invariantResolutionComplex h I) n) :
    resolutionComparisonBack h I c n (r • z) = r • resolutionComparisonBack h I c n z := by
  let E := complexHomologyEquiv
    (calculusEvaluationIso h (moduleRepresentation g M) c (restrictedModule_inclusion h)) n
  let G := complexHomologyEquiv (invariantResolutionIso h I) n
  apply (cochainCohomologyEquiv h (moduleRepresentation g M) c n).injective
  rw [cochainCohomologyEquiv_scalar]
  simp only [resolutionComparisonBack, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change E (resolutionBalance h I n (G.symm
      (invariantResolutionCohomologyEquiv h I n (r • z)))) =
    homologyMap (cochainScalar h (moduleRepresentation g M) c r) n
      (E (resolutionBalance h I n (G.symm (invariantResolutionCohomologyEquiv h I n z))))
  rw [invariantResolutionCohomologyEquiv_smul]
  rw [linearEquiv_symm_intertwines G
    (homologyMap (injectiveHomScalar h I r) n)
    (homologyMap (invariantResolutionScalarEndomorphism h I r) n)
    (complexHomologyEquiv_intertwines (invariantResolutionIso h I) _ _
      (invariantResolutionIso_scalar h I r) n)]
  rw [resolutionBalance_scalar, ← resolutionCochainScalar_eq_post]
  exact complexHomologyEquiv_intertwines
    (calculusEvaluationIso h (moduleRepresentation g M) c (restrictedModule_inclusion h)) _ _
    (calculusEvaluationIso_scalar h (moduleRepresentation g M) c (restrictedModule_inclusion h) r) n _

theorem resolutionComparisonBack_action (n : ℕ) (y : g)
    (z : Homology (invariantResolutionComplex h I) n) :
    resolutionComparisonBack h I c n
        (invariantResolutionCohomologyAction h I n (quotientMap k g h y) z) =
      cohomologyQuotient h (moduleRepresentation g M) c n (quotientMap k g h y)
        (resolutionComparisonBack h I c n z) := by
  let E := complexHomologyEquiv
    (calculusEvaluationIso h (moduleRepresentation g M) c (restrictedModule_inclusion h)) n
  let G := complexHomologyEquiv (invariantResolutionIso h I) n
  apply (cochainCohomologyEquiv h (moduleRepresentation g M) c n).injective
  rw [cochainCohomologyEquiv_quotientAction]
  simp only [resolutionComparisonBack, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change E (resolutionBalance h I n (G.symm
      (invariantResolutionCohomologyEquiv h I n
        (invariantResolutionCohomologyAction h I n (quotientMap k g h y) z)))) =
    homologyMap (cochainEndomorphism h (moduleRepresentation g M) c y) n
      (E (resolutionBalance h I n (G.symm (invariantResolutionCohomologyEquiv h I n z))))
  rw [invariantResolutionCohomologyEquiv_action]
  rw [linearEquiv_symm_intertwines G
    (homologyMap (injectiveHomEndomorphism h I y) n)
    (homologyMap (invariantResolutionIntegerEndomorphism h I (quotientMap k g h y)) n)
    (complexHomologyEquiv_intertwines (invariantResolutionIso h I) _ _
      (invariantResolutionIso_action h I y) n)]
  rw [resolutionBalance_action]
  exact complexHomologyEquiv_intertwines
    (calculusEvaluationIso h (moduleRepresentation g M) c (restrictedModule_inclusion h)) _ _
    (calculusEvaluationIso_equivariant h (moduleRepresentation g M) c (restrictedModule_inclusion h) y) n _

/-- The two cohomology computations are canonically k-linearly isomorphic. -/
def resolutionComparison (n : ℕ) :
    Cohomology h c.d n ≃ₗ[k] Homology (invariantResolutionComplex h I) n :=
  (show Homology (invariantResolutionComplex h I) n ≃ₗ[k] Cohomology h c.d n from
    { (resolutionComparisonBack h I c n).toAddEquiv with
      map_smul' := resolutionComparisonBack_smul h I c n }).symm

theorem resolutionComparison_intertwines (n : ℕ) :
    LieIntertwines (cohomologyQuotient h (moduleRepresentation g M) c n)
      (invariantResolutionCohomologyAction h I n) (resolutionComparison h I c n).toLinearMap := by
  intro y z
  induction y using Submodule.Quotient.induction_on with | _ y =>
  apply (resolutionComparisonBack h I c n).injective
  change resolutionComparisonBack h I c n
      ((resolutionComparisonBack h I c n).symm
        (cohomologyQuotient h (moduleRepresentation g M) c n (quotientMap k g h y) z)) =
    resolutionComparisonBack h I c n
      (invariantResolutionCohomologyAction h I n (quotientMap k g h y)
        ((resolutionComparisonBack h I c n).symm z))
  rw [LinearEquiv.apply_symm_apply, resolutionComparisonBack_action,
    LinearEquiv.apply_symm_apply]


end AdvancedHomologicalAlgebra.LieQuotientAction



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Ch11.ExtBalance
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 2000] CE.Ext.trivialModule
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]
variable (h : LieIdeal k g) {M : Type w} [AddCommGroup M] [Module (U k g) M]
attribute [local instance] restrictedModule resolutionTermModule

/-- An invariant vector in degree zero enters an injective resolution by η. -/
def augmentedInvariantZeroCycle (I : InjectiveResolution (U k g) M)
    (f : k →ₗ[U k h] M) :
    cycles (injectiveHom k (restrictedInjectiveResolution h I).complex) 0 :=
  ⟨(restrictedInjectiveResolution h I).η.comp f, by
    change ((injectiveHom k (restrictedInjectiveResolution h I).complex).d 0
      ((ComplexShape.up ℕ).next 0)).hom ((restrictedInjectiveResolution h I).η.comp f) = 0
    rw [CochainComplex.next]
    change (((restrictedInjectiveResolution h I).complex.d 0 1).hom.comp
      ((restrictedInjectiveResolution h I).η.comp f)) = 0
    apply LinearMap.ext
    intro x
    exact I.exact_zero.apply_apply_eq_zero (f x)⟩

/-- The degree-zero comparison is the original augmentation on invariant
vectors, not a chosen automorphism of cohomology. -/
theorem resolutionBalance_zero (I : InjectiveResolution (U k g) M)
    (f : k →ₗ[U k h] M) :
    resolutionBalance h I 0
      (homologyClass _ 0 (augmentedInvariantZeroCycle h I f)) =
        homologyClass _ 0 (P103.Ch11.ExtTorDefinitions.homToZeroCycles (idealResolution h) M f) := by
  apply (projectiveAugmentation_quasiIso _ _ (idealResolution_projective h) 0).1
  calc
    _ = homologyMap (injectiveAugmentation (idealResolution h) (restrictedInjectiveResolution h I)) 0
      (homologyClass _ 0 (augmentedInvariantZeroCycle h I f)) :=
        DFunLike.congr_fun (resolutionBalance_formula h I 0) _
    _ = _ := by
      rw [P103.Ch10.Complexes.homologyMap_apply, P103.Ch10.Complexes.homologyMap_apply]
      congr 1

end AdvancedHomologicalAlgebra.LieQuotientAction


noncomputable section
namespace AdvancedHomologicalAlgebra.LieQuotientAction
open Shared.Lie
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
variable {M : Type w} [AddCommGroup M] [Module k M]

/-- Interpreting a representation as its actual unital U(g)-module and back
recovers the original representation on the same underlying k-module. -/
theorem moduleRepresentation_ofRepresentation (ρ : Representation k g M) :
    letI := actionModule k g M (representationEquiv k g M ρ)
    letI := action_tower k g M (representationEquiv k g M ρ)
    moduleRepresentation g M = ρ := by
  letI := actionModule k g M (representationEquiv k g M ρ)
  letI := action_tower k g M (representationEquiv k g M ρ)
  change (representationEquiv k g M).symm (Algebra.lsmul k k M) = ρ
  rw [action_roundtrip k g M (representationEquiv k g M ρ)
    (action_tower k g M (representationEquiv k g M ρ))]
  exact (representationEquiv k g M).symm_apply_apply ρ

end AdvancedHomologicalAlgebra.LieQuotientAction

namespace AdvancedHomologicalAlgebra.LieQuotientAction
open CategoryTheory Shared.Lie P103.Specs.Ch10.Complexes
universe u v w
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] resolutionTermModule

theorem resolutionComparison_spec :
    Specs.AdvancedHomologicalAlgebra.LieQuotientAction.resolutionComparisonExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ _ _ I
  let c := cochainCalculus h (moduleRepresentation g M)
  refine ⟨c, cohomologyQuotient h (moduleRepresentation g M) c,
    invariantResolutionComplex h I,
    (fun n => LinearEquiv.refl k (invariants h (resolutionTermRepresentation I n))),
    invariantResolutionTermAction h I, invariantResolutionCohomologyAction h I,
    resolutionComparison h I c, cohomologyQuotient_formula h (moduleRepresentation g M) c,
    ?_, ?_, ?_, resolutionComparison_intertwines h I c⟩
  · intro n y x
    exact invariantQuotient_formula h (resolutionTermRepresentation I n) y x
  · intro n x
    simp only [invariantResolutionComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
    rfl
  · intro n y z
    exact ⟨cyclesMap (invariantResolutionEndomorphism h I y) n z, rfl, rfl⟩

end AdvancedHomologicalAlgebra.LieQuotientAction
