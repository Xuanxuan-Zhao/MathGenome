import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfFiniteExt

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CommutativeAlgebraNotes.CompletionOfFiniteExt

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Diagram

variable {A U V W U' V' W' : Type u} [CommRing A]
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup W']
  [Module A U] [Module A V] [Module A W]
  [Module A U'] [Module A V'] [Module A W']
  {f : U →ₗ[A] V} {g : V →ₗ[A] W} {f' : U' →ₗ[A] V'} {g' : V' →ₗ[A] W'}
  {a : U →ₗ[A] U'} {b : V →ₗ[A] V'} {c : W →ₗ[A] W'}
  (hab : ∀ x, b (f x) = f' (a x)) (hbc : ∀ y, c (g y) = g' (b y))
  (h : Function.Exact f g) (h' : Function.Exact f' g')

include hab hbc h h' in
private lemma bijective_of_exact_left (hf : Function.Injective f)
    (hf' : Function.Injective f') (hb : Function.Bijective b) (hc : Function.Injective c) :
    Function.Bijective a := by
  constructor
  · intro x y hxy
    exact hf (hb.injective (by rw [hab, hab, hxy]))
  · intro x
    obtain ⟨y, hy⟩ := hb.surjective (f' x)
    have hz : g y = 0 := hc (by rw [hbc, hy, h'.apply_apply_eq_zero, map_zero])
    obtain ⟨z, hz⟩ := (h y).mp hz
    exact ⟨z, hf' (by rw [← hab, hz, hy])⟩

include hab hbc h h' in
private lemma bijective_of_exact_right (hg : Function.Surjective g)
    (hg' : Function.Surjective g') (ha : Function.Surjective a) (hb : Function.Bijective b) :
    Function.Bijective c := by
  constructor
  · apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
    intro x hx
    obtain ⟨y, rfl⟩ := hg x
    rw [hbc] at hx
    obtain ⟨z, hz⟩ := (h' _).mp hx
    obtain ⟨t, rfl⟩ := ha z
    have : f t = y := hb.injective (by rw [hab, hz])
    rw [← this, h.apply_apply_eq_zero]
  · intro x
    obtain ⟨y, rfl⟩ := hg' x
    obtain ⟨z, rfl⟩ := hb.surjective y
    exact ⟨g z, hbc z⟩

end Diagram

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- The comparison commutes with Yoneda precomposition, including the
connecting maps supplied by the class of a short exact sequence. -/
theorem baseChangeMap_precomp {X X' Y : ModuleCat.{u} R} {i j k : ℕ}
    (f : Ext X' X i) (h : i + j = k) (t : A ⊗[R] Ext X Y j) :
    baseChangeMap X' Y k
      (((f.precompOfLinear R Y h).baseChange A) t) =
    (f.mapExactFunctor (extend R A)).comp (baseChangeMap X Y j t) h := by
  induction t using TensorProduct.inductionOn with
  | tmul a e =>
    rw [LinearMap.baseChange_tmul, baseChangeMap_tmul, baseChangeMap_tmul]
    change a • (f.comp e h).mapExactFunctor (extend R A) = _
    rw [Ext.mapExactFunctor_comp, Ext.comp_smul]
  | add x y hx hy => simp only [map_add, Ext.comp_add, hx, hy]

theorem baseChangeMap_postcomp {X Y Y' : ModuleCat.{u} R} {i j k : ℕ}
    (f : Ext Y Y' i) (h : j + i = k) (t : A ⊗[R] Ext X Y j) :
    baseChangeMap X Y' k
      (((f.postcompOfLinear R X h).baseChange A) t) =
    (baseChangeMap X Y j t).comp (f.mapExactFunctor (extend R A)) h := by
  induction t using TensorProduct.inductionOn with
  | tmul a e =>
    rw [LinearMap.baseChange_tmul, baseChangeMap_tmul, baseChangeMap_tmul]
    change a • (e.comp f h).mapExactFunctor (extend R A) = _
    rw [Ext.mapExactFunctor_comp, Ext.smul_comp]
  | add x y hx hy => simp only [map_add, Ext.add_comp, hx, hy]


private lemma baseChangeMap_zero_free (P Y : ModuleCat.{u} R)
    [Module.Free R P] [Module.Finite R P] : Function.Bijective (baseChangeMap (A := A) P Y 0) := by
  let e : Ext P Y 0 ≃ₗ[R] (P →ₗ[R] Y) := Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
  let e' : Ext ((extend R A).obj P) ((extend R A).obj Y) 0 ≃ₗ[A]
      (A ⊗[R] P →ₗ[A] A ⊗[R] Y) :=
    Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
  let ibcP := TensorProduct.isBaseChange (R := R) (S := A) (M := P)
  let ibcY := TensorProduct.isBaseChange (R := R) (S := A) (M := Y)
  let ibc := IsBaseChange.linearMapLeftRight ibcP ibcY
  let E := (e.baseChange R A).trans (ibc.equiv.trans e'.symm)
  let : Module R (Ext ((extend R A).obj P) ((extend R A).obj Y) 0) :=
    Module.compHom _ (algebraMap R A)
  let : IsScalarTower R A (Ext ((extend R A).obj P) ((extend R A).obj Y) 0) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hE : baseChangeMap P Y 0 = E.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    apply e'.injective
    change e' (baseChangeMap P Y 0 (a ⊗ₜ[R] x)) = e' (E (a ⊗ₜ[R] x))
    obtain ⟨f, rfl⟩ := Ext.homEquiv₀.symm.surjective x
    have hf : Ext.homEquiv₀.symm f = Ext.mk₀ f := rfl
    rw [hf, baseChangeMap_tmul, Ext.mapExactFunctor_mk₀, map_smul]
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul]
    have he (f : P ⟶ Y) : e (Ext.mk₀ f) = f.hom := by
      change ModuleCat.homLinearEquiv (S := R) (Ext.linearEquiv₀ (R := R) (Ext.mk₀ f)) = f.hom
      rw [show Ext.linearEquiv₀ (R := R) (Ext.mk₀ f) = f from
        (Ext.linearEquiv₀ (R := R)).apply_symm_apply f]
      rfl
    have he' (f : (extend R A).obj P ⟶ (extend R A).obj Y) :
        e' (Ext.mk₀ f) = f.hom := by
      change ModuleCat.homLinearEquiv (S := A) (Ext.linearEquiv₀ (R := A) (Ext.mk₀ f)) = f.hom
      rw [show Ext.linearEquiv₀ (R := A) (Ext.mk₀ f) = f from
        (Ext.linearEquiv₀ (R := A)).apply_symm_apply f]
      rfl
    rw [he, he']
    change a • f.hom.baseChange A = a • IsBaseChange.linearMapLeftRightHom ibcP
      (TensorProduct.mk R A Y 1) f.hom
    congr 1
    apply TensorProduct.AlgebraTensorModule.ext
    intro b p
    have heq (z : A ⊗[R] P) : ibcP.equiv z = z := by
      induction z using TensorProduct.inductionOn with
      | tmul d q => simp [TensorProduct.smul_tmul']
      | add x y hx hy => simp [hx, hy]
    have hs (z : A ⊗[R] P) : ibcP.equiv.symm z = z :=
      ibcP.equiv.injective (by rw [LinearEquiv.apply_symm_apply, heq])
    simp [IsBaseChange.linearMapLeftRightHom_apply, hs, LinearMap.liftBaseChange_tmul,
      TensorProduct.smul_tmul']
  rw [hE]
  exact E.bijective

private abbrev pull (Y : ModuleCat.{u} R) {X X' : ModuleCat.{u} R}
    (f : X' ⟶ X) (n : ℕ) : Ext X Y n →ₗ[R] Ext X' Y n :=
  (Ext.mk₀ f).precompOfLinear R Y (zero_add n)

private lemma exact_pull (Y : ModuleCat.{u} R) {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (n : ℕ) : Function.Exact (pull Y S.g n) (pull Y S.f n) := by
  have h := Ext.contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

private lemma exact_connect (Y : ModuleCat.{u} R) {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (pull Y S.f n)
      (hS.extClass.precompOfLinear R Y (Nat.add_comm 1 n)) := by
  have h := Ext.contravariant_sequence_exact₁' hS Y n (n + 1) (Nat.add_comm 1 n)
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

private lemma baseChangeMap_pull {X X' Y : ModuleCat.{u} R} (f : X' ⟶ X)
    (n : ℕ) (t : A ⊗[R] Ext X Y n) :
    baseChangeMap X' Y n ((pull Y f n).baseChange A t) =
      pull ((extend R A).obj Y) ((extend R A).map f) n (baseChangeMap X Y n t) := by
  change _ = (Ext.mk₀ ((extend R A).map f)).comp (baseChangeMap X Y n t) (zero_add n)
  rw [← Ext.mapExactFunctor_mk₀]
  exact baseChangeMap_precomp (A := A) (Ext.mk₀ f) (zero_add n) t

private lemma pull_comp {X X' X'' Y : ModuleCat.{u} R} (f : X'' ⟶ X') (g : X' ⟶ X)
    (n : ℕ) : pull Y (f ≫ g) n = (pull Y f n).comp (pull Y g n) := by
  ext x
  exact (Ext.mk₀_comp_mk₀_assoc f g x).symm

private lemma baseChangeMap_zero [IsNoetherianRing R] (X Y : ModuleCat.{u} R)
    [Module.Finite R X] : Function.Bijective (baseChangeMap (A := A) X Y 0) := by
  obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R X
  let S := p.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
  let : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R p.ker)
  obtain ⟨Q, _, _, _, _, q, hq⟩ := Module.exists_finite_presentation R S.X₁
  let q' : ModuleCat.of R Q ⟶ S.X₁ := ModuleCat.ofHom q
  let F := extend R A
  let Y' := F.obj Y
  let hS' := hS.map_of_exact F
  let : Epi q' := (ModuleCat.epi_iff_surjective q').mpr hq
  let : Epi (F.map q') := (ModuleCat.epi_iff_surjective (F.map q')).mpr
    (LinearMap.lTensor_surjective A hq)
  let : Epi S.g := hS.epi_g
  let : Epi (S.map F).g := hS'.epi_g
  have h₁ : Function.Exact (pull Y S.g 0) (pull Y (q' ≫ S.f) 0) := by
    rw [pull_comp]
    exact (exact_pull Y hS 0).comp_injective _
        (Ext.precomp_mk₀_injective_of_epi Y q') (map_zero _)
  have h₂ : Function.Exact (pull Y' (S.map F).g 0) (pull Y' (F.map (q' ≫ S.f)) 0) := by
    rw [Functor.map_comp, pull_comp]
    exact (exact_pull Y' hS' 0).comp_injective _
      (Ext.precomp_mk₀_injective_of_epi Y' (F.map q')) (map_zero _)
  apply bijective_of_exact_left (baseChangeMap_pull (A := A) (Y := Y) S.g 0)
      (baseChangeMap_pull (A := A) (Y := Y) (q' ≫ S.f) 0)
      (Module.Flat.lTensor_exact A h₁) h₂
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) (pull Y S.g 0)
      (Ext.precomp_mk₀_injective_of_epi Y S.g)
  · exact Ext.precomp_mk₀_injective_of_epi Y' (S.map F).g
  · exact baseChangeMap_zero_free _ _
  · exact (baseChangeMap_zero_free _ _).injective

/-- The canonical Ext map is bijective after flat scalar extension. -/
theorem baseChangeMap_bijective [IsNoetherianRing R] (X Y : ModuleCat.{u} R)
    [Module.Finite R X] (n : ℕ) : Function.Bijective (baseChangeMap (A := A) X Y n) := by
  induction n generalizing X with
  | zero => exact baseChangeMap_zero X Y
  | succ n ih =>
    obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R X
    let S := p.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
    let : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R p.ker)
    let F := extend R A
    let Y' := F.obj Y
    let hS' := hS.map_of_exact F
    let ibc := TensorProduct.isBaseChange (R := R) (S := A) (M := S.X₂)
    let : Module.Free A (S.map F).X₂ := ibc.free
    let : Projective S.X₂ := inferInstance
    let : Projective (S.map F).X₂ := inferInstance
    have hδ (t : A ⊗[R] Ext S.X₁ Y n) :
        baseChangeMap X Y (n + 1)
          ((hS.extClass.precompOfLinear R Y (Nat.add_comm 1 n)).baseChange A t) =
        (hS'.extClass.precompOfLinear A Y' (Nat.add_comm 1 n))
          (baseChangeMap S.X₁ Y n t) := by
      have hh := baseChangeMap_precomp (A := A) hS.extClass (Nat.add_comm 1 n) t
      rw [Ext.mapExactFunctor_extClass] at hh
      exact hh
    apply bijective_of_exact_right (baseChangeMap_pull (A := A) (Y := Y) S.f n) hδ
      (Module.Flat.lTensor_exact A (exact_connect Y hS n)) (exact_connect Y' hS' n)
      (LinearMap.lTensor_surjective A (precomp_extClass_surjective_of_projective_X₂ Y hS n))
      (precomp_extClass_surjective_of_projective_X₂ Y' hS' n) (ih _).surjective (ih _)

theorem restrictedScalarAction : RestrictedScalarAction.{u} := by
  intro R A _ _ _ _ X Z n a e
  let adj := adjunction R A
  let h := adj.extEquiv (X := X) (Y := Z) (n := n)
  change h (a • h.symm e) = (show Ext X ((restrict R A).obj Z) n from e).comp _ _
  rw [Ext.smul_eq_comp_mk₀]
  change adj.extEquiv ((h.symm e).comp (Ext.mk₀ (a • 𝟙 Z)) (add_zero n)) = _
  rw [Adjunction.extEquiv_naturality_right₀]
  change (h (h.symm e)).comp _ _ = _
  rw [AddEquiv.apply_symm_apply]

theorem coefficientFormula : CoefficientFormula.{u} := by
  intro R A _ _ _ _ X Y n a e
  rw [coefficientMap, LinearMap.comp_apply, baseChangeMap_tmul, map_smul]
  congr 1
  let adj := adjunction R A
  let Z := (extend R A).obj Y
  change adj.extEquiv (e.mapExactFunctor (extend R A)) =
    e.comp (Ext.mk₀ (adj.unit.app Y)) (add_zero n)
  have h := adj.extEquiv_naturality_left e (Ext.mk₀ (𝟙 Z)) (add_zero n)
  rw [Ext.comp_mk₀_id, adj.extEquiv_mk₀, adj.homEquiv_id] at h
  exact h

section Completion

private lemma signedBaseChangeMap_bijective (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (X Y : ModuleCat.{u} R) [Module.Finite R X] (j : ℤ) :
    Function.Bijective (signedBaseChangeMap R X Y j) := by
  cases j with
  | ofNat n => exact baseChangeMap_bijective X Y n
  | negSucc n =>
    change Function.Bijective
      (0 : completionRing R ⊗[R] PUnit.{u+1} →ₗ[completionRing R] PUnit.{u+1})
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro x
      exact ⟨0, Subsingleton.elim _ _⟩

/-- Completion of Ext computes Ext of the completed modules. -/
theorem completionComparison : CompletionComparison.{u} := by
  intro R _ _ _ X Y _ _ j
  exact (extCompletionIso R X Y j).toLinearEquiv.bijective.comp
    ((signedBaseChangeMap_bijective R X Y j).comp
      (tensorCompletion R (extModule R j X Y)).symm.bijective)

/-- Tensoring Ext with the completed ring computes Ext into the completed
coefficient tensor over the original ring. -/
theorem coefficientComparison : CoefficientComparison.{u} := by
  intro R _ _ _ X Y _ _ j
  exact (signedAdjunction R X ((extend R (completionRing R)).obj Y) j).bijective.comp
    (signedBaseChangeMap_bijective R X Y j)

theorem completionAdjunctionCompatibility : CompletionAdjunctionCompatibility.{u} := by
  intro R _ _ _ X Y _ _ j t
  simp only [completionMap, signedCoefficientMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ← ModuleCat.comp_apply,
    Iso.hom_inv_id, ModuleCat.id_apply]

/-- The completion comparison as a linear equivalence. -/
def completionEquiv (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ) :
    (complete R).obj (extModule R j X Y) ≃ₗ[completionRing R]
      extModule (completionRing R) j ((complete R).obj X) ((complete R).obj Y) :=
  LinearEquiv.ofBijective _ (completionComparison R X Y j)

/-- The comparison into the scalar extension of the coefficient module as a
linear equivalence. -/
def coefficientEquiv (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X Y : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R Y] (j : ℤ) :
    completionRing R ⊗[R] extModule R j X Y ≃ₗ[completionRing R]
      signedRestrictedExt R X ((extend R (completionRing R)).obj Y) j :=
  LinearEquiv.ofBijective _ (coefficientComparison R X Y j)


section Naturality

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private lemma tensorCompletionIso_natural {X Y : ModuleCat.{u} R}
    [Module.Finite R X] [Module.Finite R Y] (f : X ⟶ Y) :
    (extend R (completionRing R)).map f ≫ (tensorCompletionIso R Y).hom =
      (tensorCompletionIso R X).hom ≫ (complete R).map f := by
  apply ModuleCat.hom_ext
  exact (AdicCompletion.ofTensorProduct_naturality (IsLocalRing.maximalIdeal R) f.hom).symm

@[reassoc]
private lemma tensorCompletionIso_inv_natural {X Y : ModuleCat.{u} R}
    [Module.Finite R X] [Module.Finite R Y] (f : X ⟶ Y) :
    (tensorCompletionIso R X).inv ≫ (extend R (completionRing R)).map f =
      (complete R).map f ≫ (tensorCompletionIso R Y).inv := by
  calc
    _ = (tensorCompletionIso R X).inv ≫
        ((extend R (completionRing R)).map f ≫ (tensorCompletionIso R Y).hom) ≫
        (tensorCompletionIso R Y).inv := by simp
    _ = _ := by rw [tensorCompletionIso_natural]; simp

private lemma extPull_comp {B : Type u} [CommRing B] {X X' X'' : ModuleCat.{u} B}
    (f : X'' ⟶ X') (g : X' ⟶ X) (Y : ModuleCat.{u} B) (j : ℤ) :
    extPull (f ≫ g) Y j = extPull g Y j ≫ extPull f Y j := by
  change ((signedExt B j).map (g.op ≫ f.op)).app Y = _
  rw [Functor.map_comp, NatTrans.comp_app]

private lemma extPush_comp {B : Type u} [CommRing B] (X : ModuleCat.{u} B)
    {Y Y' Y'' : ModuleCat.{u} B} (f : Y ⟶ Y') (g : Y' ⟶ Y'') (j : ℤ) :
    extPush X (f ≫ g) j = extPush X f j ≫ extPush X g j :=
  ((signedExt B j).obj (Opposite.op X)).map_comp f g

@[reassoc]
private lemma extPull_push {B : Type u} [CommRing B] {X X' Y Y' : ModuleCat.{u} B}
    (f : X' ⟶ X) (g : Y ⟶ Y') (j : ℤ) :
    extPull f Y j ≫ extPush X' g j = extPush X g j ≫ extPull f Y' j :=
  (((signedExt B j).map f.op).naturality g).symm

private lemma extCompletionIso_natural_left {X X' Y : ModuleCat.{u} R}
    [Module.Finite R X] [Module.Finite R X'] [Module.Finite R Y] (f : X' ⟶ X) (j : ℤ) :
    (extCompletionIso R X Y j).hom ≫ extPull ((complete R).map f) ((complete R).obj Y) j =
      extPull ((extend R (completionRing R)).map f) ((extend R (completionRing R)).obj Y) j ≫
        (extCompletionIso R X' Y j).hom := by
  change (extPull (tensorCompletionIso R X).inv _ j ≫
      extPush _ (tensorCompletionIso R Y).hom j) ≫ _ =
    _ ≫ (extPull (tensorCompletionIso R X').inv _ j ≫
      extPush _ (tensorCompletionIso R Y).hom j)
  rw [Category.assoc, ← extPull_push, ← Category.assoc, ← extPull_comp,
    ← tensorCompletionIso_inv_natural, extPull_comp, Category.assoc]

private lemma extCompletionIso_natural_right {X Y Y' : ModuleCat.{u} R}
    [Module.Finite R X] [Module.Finite R Y] [Module.Finite R Y'] (g : Y ⟶ Y') (j : ℤ) :
    (extCompletionIso R X Y j).hom ≫ extPush ((complete R).obj X) ((complete R).map g) j =
      extPush ((extend R (completionRing R)).obj X) ((extend R (completionRing R)).map g) j ≫
        (extCompletionIso R X Y' j).hom := by
  change (extPull (tensorCompletionIso R X).inv _ j ≫
      extPush _ (tensorCompletionIso R Y).hom j) ≫ _ =
    _ ≫ (extPull (tensorCompletionIso R X).inv _ j ≫
      extPush _ (tensorCompletionIso R Y').hom j)
  rw [Category.assoc, ← extPush_comp, ← tensorCompletionIso_natural, extPush_comp,
    extPull_push_assoc]

@[reassoc]
private lemma signedBaseChange_natural_left {X X' Y : ModuleCat.{u} R}
    (f : X' ⟶ X) (j : ℤ) :
    ModuleCat.ofHom (signedBaseChangeMap R X Y j) ≫
        extPull ((extend R (completionRing R)).map f) ((extend R (completionRing R)).obj Y) j =
      (extend R (completionRing R)).map (extPull f Y j) ≫
        ModuleCat.ofHom (signedBaseChangeMap R X' Y j) := by
  cases j with
  | ofNat n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact (baseChangeMap_pull f n t).symm
  | negSucc n => apply ModuleCat.hom_ext; apply LinearMap.ext; intro t; exact Subsingleton.elim (α := PUnit.{u+1}) _ _

@[reassoc]
private lemma signedBaseChange_natural_right {X Y Y' : ModuleCat.{u} R}
    (g : Y ⟶ Y') (j : ℤ) :
    ModuleCat.ofHom (signedBaseChangeMap R X Y j) ≫
        extPush ((extend R (completionRing R)).obj X) ((extend R (completionRing R)).map g) j =
      (extend R (completionRing R)).map (extPush X g j) ≫
        ModuleCat.ofHom (signedBaseChangeMap R X Y' j) := by
  cases j with
  | ofNat n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change (baseChangeMap X Y n t).comp
      (Ext.mk₀ ((extend R (completionRing R)).map g)) (add_zero n) = _
    rw [← Ext.mapExactFunctor_mk₀]
    exact (baseChangeMap_postcomp (Ext.mk₀ g) (add_zero n) t).symm
  | negSucc n => apply ModuleCat.hom_ext; apply LinearMap.ext; intro t; exact Subsingleton.elim (α := PUnit.{u+1}) _ _

private lemma completionMap_hom (X Y : ModuleCat.{u} R)
    [Module.Finite R X] [Module.Finite R Y] (j : ℤ) :
    ModuleCat.ofHom (completionMap R X Y j) =
      (tensorCompletionIso R (extModule R j X Y)).inv ≫
        ModuleCat.ofHom (signedBaseChangeMap R X Y j) ≫ (extCompletionIso R X Y j).hom := rfl

theorem completionNaturality : CompletionNaturality.{u} := by
  intro R _ _ _ X X' Y Y' _ _ _ _ f g j
  constructor
  · rw [completionMap_hom, completionMap_hom]
    simp only [Category.assoc]
    rw [extCompletionIso_natural_left R f j, signedBaseChange_natural_left_assoc R f j,
      tensorCompletionIso_inv_natural_assoc R (extPull f Y j)]
  · rw [completionMap_hom, completionMap_hom]
    simp only [Category.assoc]
    rw [extCompletionIso_natural_right R g j, signedBaseChange_natural_right_assoc R g j,
      tensorCompletionIso_inv_natural_assoc R (extPush X g j)]

/-- The adjunction identifies the transported maps with the Ext maps
induced by the original first argument and the restricted second argument. -/
theorem restrictedExtMaps : RestrictedExtMaps.{u} := by
  intro R _ _ _ X X' Z Z' f g n e
  let adj := adjunction R (completionRing R)
  let h := adj.extEquiv (X := X) (Y := Z) (n := n)
  constructor
  · change adj.extEquiv ((Ext.mk₀ ((extend R (completionRing R)).map f)).comp
      (h.symm e) (zero_add n)) = _
    rw [adj.extEquiv_naturality_left₀]
    change (Ext.mk₀ f).comp (h (h.symm e)) (zero_add n) = _
    rw [AddEquiv.apply_symm_apply]
  · change adj.extEquiv ((h.symm e).comp (Ext.mk₀ g) (add_zero n)) = _
    rw [adj.extEquiv_naturality_right₀]
    change (h (h.symm e)).comp _ (add_zero n) = _
    rw [AddEquiv.apply_symm_apply]

theorem coefficientNaturality : CoefficientNaturality.{u} := by
  intro R _ _ _ X X' Y Y' f g j
  dsimp only
  let F := extend R (completionRing R)
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change (signedAdjunction R X' (F.obj Y) j)
      ((extPull (F.map f) (F.obj Y) j).hom
        ((signedAdjunction R X (F.obj Y) j).symm
          (signedAdjunction R X (F.obj Y) j (signedBaseChangeMap R X Y j t)))) =
      (signedAdjunction R X' (F.obj Y) j)
        (signedBaseChangeMap R X' Y j ((F.map (extPull f Y j)).hom t))
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    exact congrArg (fun k => k.hom t) (signedBaseChange_natural_left R f j)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change (signedAdjunction R X (F.obj Y') j)
      ((extPush (F.obj X) (F.map g) j).hom
        ((signedAdjunction R X (F.obj Y) j).symm
          (signedAdjunction R X (F.obj Y) j (signedBaseChangeMap R X Y j t)))) =
      (signedAdjunction R X (F.obj Y') j)
        (signedBaseChangeMap R X Y' j ((F.map (extPush X g j)).hom t))
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    exact congrArg (fun k => k.hom t) (signedBaseChange_natural_right R g j)

end Naturality

end Completion

end

end CommutativeAlgebraNotes.CompletionOfFiniteExt
