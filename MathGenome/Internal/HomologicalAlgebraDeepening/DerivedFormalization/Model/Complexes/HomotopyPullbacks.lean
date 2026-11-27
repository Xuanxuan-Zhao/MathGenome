import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.HomotopyPullbacks
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open CochainComplex CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

universe u

namespace DerivedFormalization.Model.Complexes
open Specs.ComplexHomotopyPullbacks

variable {A : Type u} [Ring A] {T S X Y Z W P : Cochains A}

/-- The shifted-cone model for the homotopy pullback of two cochain maps. -/
noncomputable def homotopyPullback (f : X ⟶ Z) (g : Y ⟶ Z) : Cochains A := modelValue f g

/-- The model and its strict maps, as a functor on cospans. -/
noncomputable def homotopyPullbackFunctor (A : Type u) [Ring A] :
    (WalkingCospan ⥤ Cochains A) ⥤ Cochains A := functorValue A

/-- The contractible summand used to replace a leg by a surjection. -/
noncomputable def pullbackReplacementSummand (Z : Cochains A) : Cochains A :=
  contractibleValue Z

/-- Replace the left leg by adjoining the contractible summand. -/
noncomputable def pullbackReplacement (f : X ⟶ Z) : X ⊞ pullbackReplacementSummand Z ⟶ Z :=
  replacementValue f

/-- The comparison from the ordinary pullback with zero last coordinate. -/
noncomputable def strictToHomotopyPullback (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ⟶ homotopyPullback f g := comparisonValue f g

private theorem cocone_δ_snd (h : T ⟶ Z) :
    δ (-1) 0 (mappingCocone.snd h) = -Cochain.ofHom (mappingCocone.fst h ≫ h) := by
  change δ (-1) 0 ((mappingCone.snd h).leftShift (-1) (-1) (zero_add _)) =
    -Cochain.ofHom (mappingCocone.fst h ≫ h)
  rw [Cochain.δ_leftShift _ (-1) (-1) 0 (zero_add _) 1 (by omega),
    mappingCone.δ_snd, Cochain.leftShift_neg, Cochain.leftShift_comp_zero_cochain]
  simp [mappingCocone.fst, Cocycle.leftShift_coe, Cocycle.cochain_ofHom_homOf_eq_coe]

private theorem coconeComponentExt (h : T ⟶ Z) (n : ℤ) {M : ModuleCat A}
    {a b : M ⟶ (mappingCocone h).X n}
    (h₁ : a ≫ (mappingCocone.fst h).f n = b ≫ (mappingCocone.fst h).f n)
    (h₂ : a ≫ (mappingCocone.snd h).v n (n + -1) rfl =
      b ≫ (mappingCocone.snd h).v n (n + -1) rfl) : a = b := by
  rw [← Category.comp_id a, ← Category.comp_id b, ← mappingCocone.id_X h n (n + -1) rfl,
    comp_add, comp_add, ← Category.assoc, ← Category.assoc, h₁, ← Category.assoc,
    ← Category.assoc, h₂]

private theorem coconeHomExt (h : T ⟶ Z) {a b : P ⟶ mappingCocone h}
    (h₁ : a ≫ mappingCocone.fst h = b ≫ mappingCocone.fst h)
    (h₂ : (Cochain.ofHom a).comp (mappingCocone.snd h) (zero_add _) =
      (Cochain.ofHom b).comp (mappingCocone.snd h) (zero_add _)) : a = b := by
  apply HomologicalComplex.hom_ext
  intro n
  apply coconeComponentExt h
  · exact congrArg (fun m : P ⟶ T => m.f n) h₁
  · simpa using Cochain.congr_v h₂ n (n + -1) rfl

private theorem coconeLift_snd (h : T ⟶ Z) (a : P ⟶ T) (b : Cochain P Z (-1))
    (w : δ (-1) 0 b + Cochain.ofHom (a ≫ h) = 0) :
    (Cochain.ofHom (mappingCocone.lift h a b w)).comp (mappingCocone.snd h) (zero_add _) =
      b := by
  ext n m e
  simp

private theorem δ_precomp_snd (h : T ⟶ Z) (a : P ⟶ mappingCocone h) :
    δ (-1) 0 ((Cochain.ofHom a).comp (mappingCocone.snd h) (zero_add _)) =
      -Cochain.ofHom (a ≫ mappingCocone.fst h ≫ h) := by
  rw [δ_zero_cochain_comp _ _ 0 (by omega), cocone_δ_snd]
  simp [← Cochain.ofHom_comp]

theorem shiftedCone_differential : coconeDifferentialType.{u} := by
  intro A _ T Z h n
  have eq := Cochain.congr_v (cocone_δ_snd h) n n (add_zero n)
  rw [δ_v (-1) 0 (by omega) _ n n (add_zero n) (n - 1) (n + 1) rfl rfl] at eq
  simp only [Cochain.neg_v, Cochain.ofHom_v, comp_f, Int.negOnePow_zero, one_smul] at eq
  exact eq_sub_of_add_eq (by simpa only [add_comm] using eq)

private noncomputable def contractSummand (Z : Cochains A) :
    Homotopy (𝟙 (contractibleValue Z)) 0 := by
  let h : Z ⟶ Z := -𝟙 Z
  change Homotopy (𝟙 (mappingCocone h)) 0
  let b : Cochain (mappingCocone h) Z (-2) := 0
  refine (Cochain.equivHomotopy _ _).symm
    ⟨mappingCocone.liftCochain h (mappingCocone.snd h) b (by omega), ?_⟩
  rw [mappingCocone.δ_liftCochain _ _ _ _ 0 (by omega), cocone_δ_snd]
  apply Cochain.ext₀
  intro n
  have hn : n + -1 + 1 = n := by omega
  simpa [b, h, Cochain.comp_v (n₁ := -1) (n₂ := 1) (n₁₂ := 0) _ _ (by omega) n (n + -1) n rfl hn,
    sub_eq_add_neg] using (mappingCocone.id_X h n (n + -1) rfl).symm

theorem pullbackReplacementSummand_contractible : contractibilityType.{u} :=
  fun _ _ Z => ⟨contractSummand Z⟩

private theorem quasiIso_biprod_inl (X C : Cochains A) (h : Homotopy (𝟙 C) 0) :
    QuasiIso (biprod.inl : X ⟶ X ⊞ C) := by
  let p : X ⊞ C ⟶ X := biprod.fst
  let q : X ⊞ C ⟶ C := biprod.snd
  have hsum : p ≫ biprod.inl + q ≫ biprod.inr = 𝟙 (X ⊞ C) := by
    apply biprod.hom_ext' <;> simp [p, q]
  have hq : Homotopy (q ≫ (biprod.inr : C ⟶ X ⊞ C)) 0 := by
    simpa using (h.compLeft q).compRight (biprod.inr : C ⟶ X ⊞ C)
  let e : HomotopyEquiv X (X ⊞ C) :=
    { hom := biprod.inl
      inv := p
      homotopyHomInvId := Homotopy.ofEq (by simp [p])
      homotopyInvHomId := by
        simpa only [add_zero, hsum] using
          (Homotopy.refl (p ≫ biprod.inl)).add hq.symm }
  exact e.quasiIso_hom

theorem pullbackReplacement_properties : replacementType.{u} := by
  intro A _ X Z f
  refine ⟨biprod.inl_desc _ _, quasiIso_biprod_inl X _ (contractSummand Z), ?_⟩
  intro n
  change Function.Surjective ((biprod.desc f (mappingCocone.fst (-𝟙 Z))).f n)
  intro z
  let i : Z.X n ⟶ (X ⊞ mappingCocone (-𝟙 Z)).X n :=
    (mappingCocone.inl (-𝟙 Z)).v n n (add_zero n) ≫ (biprod.inr : mappingCocone (-𝟙 Z) ⟶ X ⊞ mappingCocone (-𝟙 Z)).f n
  refine ⟨i z, ?_⟩
  have e := congrArg (fun m : mappingCocone (-𝟙 Z) ⟶ Z => m.f n)
    (biprod.inr_desc f (mappingCocone.fst (-𝟙 Z)))
  rw [comp_f] at e
  have hi : i ≫ (biprod.desc f (mappingCocone.fst (-𝟙 Z))).f n = 𝟙 _ := by
    simp only [i, Category.assoc, e, mappingCocone.inl_v_fst_f]
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
    congrArg (fun m : Z.X n ⟶ Z.X n => m z) hi


/-- Retain the last coordinate and record minus the image of the first one in
the contractible summand. -/
private noncomputable def toReplacementSummand (h : T ⟶ Z) :
    mappingCocone h ⟶ mappingCocone (-𝟙 Z) :=
  mappingCocone.lift (-𝟙 Z) (-(mappingCocone.fst h ≫ h)) (mappingCocone.snd h) (by
    rw [cocone_δ_snd]
    simp)

@[reassoc (attr := simp)]
private theorem toReplacementSummand_fst (h : T ⟶ Z) :
    toReplacementSummand h ≫ mappingCocone.fst (-𝟙 Z) = -(mappingCocone.fst h ≫ h) :=
  mappingCocone.lift_fst _ _ _ _

@[simp]
private theorem toReplacementSummand_f_snd (h : T ⟶ Z) (n : ℤ) :
    (toReplacementSummand h).f n ≫ (mappingCocone.snd (-𝟙 Z)).v n (n + -1) rfl =
      (mappingCocone.snd h).v n (n + -1) rfl :=
  mappingCocone.lift_f_snd_v _ _ _ _ _ _ _

theorem homotopyPullback_iso_replacedPullback : replacementPullbackType.{u} := by
  intro A _ X Y Z f g
  let h : X ⊞ Y ⟶ Z := biprod.desc f (-g)
  let p : X ⊞ contractibleValue Z ⟶ Z := replacementValue f
  let u : pullback p g ⟶ X := pullback.fst p g ≫ biprod.fst
  let v : pullback p g ⟶ Y := pullback.snd p g
  let c : pullback p g ⟶ mappingCocone (-𝟙 Z) := pullback.fst p g ≫ biprod.snd
  have hrel : u ≫ f + c ≫ mappingCocone.fst (-𝟙 Z) = v ≫ g := by
    have e := pullback.condition (f := p) (g := g)
    change pullback.fst p g ≫ biprod.desc f (mappingCocone.fst (-𝟙 Z)) =
      pullback.snd p g ≫ g at e
    simpa only [biprod.desc_eq, comp_add, Category.assoc, u, v, c] using e
  have hsum : biprod.lift u v ≫ h = -(c ≫ mappingCocone.fst (-𝟙 Z)) := by
    dsimp only [h]
    rw [biprod.lift_desc, comp_neg, ← sub_eq_add_neg, ← hrel, sub_add_cancel_left]
  let b := (Cochain.ofHom c).comp (mappingCocone.snd (-𝟙 Z)) (zero_add (-1))
  have hb : δ (-1) 0 b + Cochain.ofHom (biprod.lift u v ≫ h) = 0 := by
    dsimp only [b]
    rw [δ_precomp_snd, hsum]
    simp
  let F : pullback p g ⟶ mappingCocone h := mappingCocone.lift h (biprod.lift u v) b hb
  have F_fst : F ≫ mappingCocone.fst h = biprod.lift u v := mappingCocone.lift_fst _ _ _ _
  let a : mappingCocone h ⟶ X ⊞ contractibleValue Z :=
    biprod.lift (mappingCocone.fst h ≫ biprod.fst) (toReplacementSummand h)
  have ha : a ≫ p = mappingCocone.fst h ≫ biprod.snd ≫ g := by
    simp only [a, p, replacementValue, biprod.lift_desc, toReplacementSummand_fst]
    have e := congrArg (fun k : X ⊞ Y ⟶ Z => -(mappingCocone.fst h) ≫ k)
      (biprod.desc_eq (f := f) (g := -g))
    change -(mappingCocone.fst h) ≫ h = _ at e
    rw [e]
    simp only [comp_add, comp_neg, Category.assoc]
    abel
  let G : mappingCocone h ⟶ pullback p g :=
    pullback.lift a (mappingCocone.fst h ≫ biprod.snd) ha
  have G_c : G ≫ c = toReplacementSummand h := by
    dsimp only [G, c]
    rw [pullback.lift_fst_assoc]
    exact biprod.lift_snd _ _
  have G_u : G ≫ u = mappingCocone.fst h ≫ biprod.fst := by
    simp only [G, u, pullback.lift_fst_assoc, a, biprod.lift_fst]
  have G_v : G ≫ v = mappingCocone.fst h ≫ biprod.snd := by
    simp [G, v]
  have F_c : F ≫ toReplacementSummand h = c := by
    apply coconeHomExt (-𝟙 Z)
    · rw [Category.assoc, toReplacementSummand_fst, comp_neg, ← Category.assoc, F_fst,
        hsum, neg_neg]
    · apply Cochain.ext
      intro n m e
      subst m
      simp [F, b, toReplacementSummand_f_snd]
  have FG : F ≫ G = 𝟙 _ := by
    apply pullback.hom_ext
    · apply biprod.hom_ext
      · simpa [Category.assoc, u] using
          (show (F ≫ G) ≫ u = u by rw [Category.assoc, G_u, ← Category.assoc, F_fst,
            biprod.lift_fst])
      · simpa [Category.assoc, c] using
          (show (F ≫ G) ≫ c = c by rw [Category.assoc, G_c, F_c])
    · change (F ≫ G) ≫ v = 𝟙 _ ≫ v
      rw [Category.assoc, G_v, ← Category.assoc, F_fst, biprod.lift_snd, Category.id_comp]
  have GF : G ≫ F = 𝟙 _ := by
    apply coconeHomExt h
    · rw [Category.assoc, F_fst, Category.id_comp]
      apply biprod.hom_ext <;> simp [G_u, G_v]
    · apply Cochain.ext
      intro n m e
      subst m
      have he := congrArg (fun k : mappingCocone h ⟶ mappingCocone (-𝟙 Z) => k.f n) G_c
      rw [comp_f] at he
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, comp_f, Category.assoc,
        id_f, Category.id_comp]
      change G.f n ≫ (mappingCocone.lift h (biprod.lift u v) b hb).f n ≫ _ = _
      rw [mappingCocone.lift_f_snd_v]
      simp only [b, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, he,
        toReplacementSummand_f_snd]
  refine ⟨⟨F, G, FG, GF⟩, F_fst, ?_⟩
  exact (coconeLift_snd h (biprod.lift u v) b hb).symm

private theorem quasiIso_biprod_map (a : X ⟶ Y) (b : Z ⟶ W) [QuasiIso a] [QuasiIso b] :
    QuasiIso (biprod.map a b) := by
  refine ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ _).2 ?_⟩
  let H := homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n
  have : H.Additive := inferInstanceAs ((homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n).Additive)
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  change IsIso (H.map (biprod.map a b))
  have h : H.map (biprod.map a b) ≫ (H.mapBiprod Y W).hom =
      (H.mapBiprod X Z).hom ≫ biprod.map (H.map a) (H.map b) := by
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.map_fst, biprod.map_snd, Functor.mapBiprod_hom,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
        ← Functor.map_comp, biprod.map_fst, biprod.map_snd]
  have ha : IsIso (H.map a) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  have hb : IsIso (H.map b) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  have hi : IsIso (biprod.map (H.map a) (H.map b)) :=
    (biprod.mapIso (asIso (H.map a)) (asIso (H.map b))).isIso_hom
  rw [← isIso_comp_right_iff _ (H.mapBiprod Y W).hom, h]
  infer_instance

private theorem quasiIso_coconeMap (h : T ⟶ Z) (k : S ⟶ W)
    (a : T ⟶ S) (c : Z ⟶ W) (w : h ≫ c = a ≫ k) [QuasiIso a] [QuasiIso c] :
    QuasiIso (coconeMapValue h k a c w) := by
  unfold coconeMapValue
  rw [quasiIso_shift_iff]
  let := HasDerivedCategory.standard (ModuleCat A)
  let Q := DerivedCategory.Q (C := ModuleCat A)
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) _).1
  exact Pretriangulated.isIso₃_of_isIso₁₂
    (Q.mapTriangle.map (mappingCone.triangleMap h k a c w))
    (DerivedCategory.mappingCone_triangle_distinguished h)
    (DerivedCategory.mappingCone_triangle_distinguished k)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) a).2 inferInstance)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) c).2 inferInstance)

theorem homotopyPullback_preserves_quasiIso : invarianceType.{u} := by
  intro A _ D E a ha
  have := ha WalkingCospan.left
  have := ha WalkingCospan.right
  have := ha WalkingCospan.one
  have := quasiIso_biprod_map (a.app WalkingCospan.left) (a.app WalkingCospan.right)
  exact quasiIso_coconeMap _ _ _ _ _


@[reassoc (attr := simp)]
private theorem toReplacementSummand_f_fst (h : T ⟶ Z) (n : ℤ) :
    (toReplacementSummand h).f n ≫ (mappingCocone.fst (-𝟙 Z)).f n =
      -((mappingCocone.fst h).f n ≫ h.f n) := by
  simpa only [comp_f, neg_f_apply] using
    congrArg (fun k : mappingCocone h ⟶ Z => k.f n) (toReplacementSummand_fst h)

private theorem toReplacementSummand_epi (h : T ⟶ Z)
    (hs : Specs.ComplexGenerators.degreewiseSurjectiveValue A h) :
    Epi (toReplacementSummand h) := by
  apply epi_of_epi_f
  intro n
  have : Epi (h.f n) := (ModuleCat.epi_iff_surjective _).2 (hs n)
  let i := (mappingCocone.inl h).v n n (add_zero n)
  let j := (mappingCocone.inr h).1.v (n + -1) n (by omega)
  let i' := (mappingCocone.inl (-𝟙 Z)).v n n (add_zero n)
  let j' := (mappingCocone.inr (-𝟙 Z)).1.v (n + -1) n (by omega)
  have ei : i ≫ (toReplacementSummand h).f n = -(h.f n) ≫ i' := by
    apply coconeComponentExt (-𝟙 Z)
    · simp [i, i']
    · simp [i, i', Category.assoc, toReplacementSummand_f_snd]
  have ej : j ≫ (toReplacementSummand h).f n = j' := by
    apply coconeComponentExt (-𝟙 Z)
    · simp [j, j']
    · simp [j, j', Category.assoc, toReplacementSummand_f_snd]
  constructor
  intro U r s eq
  have h₁ := congrArg (fun k => i ≫ k) eq
  have h₂ := congrArg (fun k => j ≫ k) eq
  simp only [← Category.assoc, ei, ej, neg_comp, neg_inj] at h₁ h₂
  have h₁' : i' ≫ r = i' ≫ s := by
    apply (cancel_epi (h.f n)).1
    simpa only [Category.assoc] using h₁
  rw [← Category.id_comp r, ← Category.id_comp s, ← mappingCocone.id_X (-𝟙 Z) n (n + -1) rfl,
    add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc]
  change _ ≫ (i' ≫ r) + _ ≫ (j' ≫ r) = _ ≫ (i' ≫ s) + _ ≫ (j' ≫ s)
  rw [h₁', h₂]

private noncomputable def kernelIntoCocone (h : T ⟶ Z) :
    kernel h ⟶ mappingCocone h :=
  mappingCocone.lift h (kernel.ι h) 0 (by simp)

private theorem kernelIntoCocone_fac (h : T ⟶ Z) :
    kernelIntoCocone h ≫ toReplacementSummand h = 0 := by
  apply coconeHomExt (-𝟙 Z)
  · rw [Category.assoc, toReplacementSummand_fst, comp_neg, ← Category.assoc,
      kernelIntoCocone, mappingCocone.lift_fst, kernel.condition, neg_zero, zero_comp]
  · apply Cochain.ext
    intro n m e
    subst m
    simp [kernelIntoCocone, toReplacementSummand_f_snd]

private noncomputable def kernelIntoCocone_isKernel (h : T ⟶ Z) :
    IsLimit (KernelFork.ofι (kernelIntoCocone h) (kernelIntoCocone_fac h)) := by
  have hi : Mono (kernelIntoCocone h) :=
    mono_of_mono_fac (mappingCocone.lift_fst h (kernel.ι h) 0 (by simp))
  apply KernelFork.IsLimit.ofι'
  intro L l hl
  have hh : l ≫ mappingCocone.fst h ≫ h = 0 := by
    have eq := congrArg (fun k => k ≫ mappingCocone.fst (-𝟙 Z)) hl
    simpa using eq
  refine ⟨kernel.lift h (l ≫ mappingCocone.fst h) (by simpa only [Category.assoc] using hh), ?_⟩
  apply coconeHomExt h
  · simp [kernelIntoCocone]
  · apply Cochain.ext
    intro n m e
    subst m
    have eq := congrArg (fun k : L ⟶ mappingCocone (-𝟙 Z) => k.f n ≫
      (mappingCocone.snd (-𝟙 Z)).v n (n + -1) rfl) hl
    have hz : l.f n ≫ (mappingCocone.snd h).v n (n + -1) rfl = 0 := by
      simpa [Category.assoc, toReplacementSummand_f_snd] using eq
    simp [kernelIntoCocone, hz]

theorem kernelToShiftedCone_quasiIso : kernelComparisonType.{u} := by
  intro A _ T Z h hs
  change QuasiIso (kernelIntoCocone h)
  let S := ShortComplex.mk (kernelIntoCocone h) (toReplacementSummand h) (kernelIntoCocone_fac h)
  have lim := kernelIntoCocone_isKernel h
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel lim
      mono_f := mono_of_isLimit_fork lim
      epi_g := toReplacementSummand_epi h hs }
  refine ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ _).2 ?_⟩
  have hz (i : ℤ) : IsZero ((mappingCocone (-𝟙 Z)).homology i) := by
    rw [IsZero.iff_id_eq_zero]
    change 𝟙 ((contractibleValue Z).homology i) = 0
    simpa only [homologyMap_id, homologyMap_zero] using (contractSummand Z).homologyMap_eq i
  have hm : Mono (homologyMap S.f n) :=
    (hS.homology_exact₁ (n - 1) n (by simp)).mono_g_iff.2 ((hz (n - 1)).eq_of_src _ _)
  have he : Epi (homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f_iff.2 ((hz n).eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi (homologyMap S.f n)

open HomotopicalAlgebra CategoryTheory.Abelian.PullbackToBiproductIsKernel in
theorem strictToHomotopyPullback_quasiIso : strictComparisonType.{u} := by
  intro A _ M
  let := M.model
  intro X Y Z f g hf
  let h : X ⊞ Y ⟶ Z := biprod.desc f (-g)
  have hs : Specs.ComplexGenerators.degreewiseSurjectiveValue A h := by
    have e₁ : biprod.inl ≫ h = f := biprod.inl_desc _ _
    have e₂ : biprod.inr ≫ h = -g := biprod.inr_desc _ _
    have fibSurj {V : Cochains A} (l : V ⟶ Z) (hl : Fibration l) :
        Specs.ComplexGenerators.degreewiseSurjectiveValue A l := by
      rwa [fibration_iff, M.fibrations_eq] at hl
    intro n z
    rcases hf with hf | hg
    · obtain ⟨x, hx⟩ := fibSurj f hf n z
      refine ⟨(biprod.inl : X ⟶ X ⊞ Y).f n x, ?_⟩
      have e := congrArg (fun k : X ⟶ Z => k.f n x) e₁
      exact e.trans hx
    · obtain ⟨y, hy⟩ := fibSurj g hg n (-z)
      refine ⟨(biprod.inr : Y ⟶ X ⊞ Y).f n y, ?_⟩
      have e := congrArg (fun k : Y ⟶ Z => k.f n y) e₂
      simpa [hy, neg_f_apply] using e
  let e : pullback f g ≅ kernel h :=
    IsLimit.conePointUniqueUpToIso (isLimitPullbackToBiproduct f g) (limit.isLimit (parallelPair h 0))
  have he : e.hom ≫ kernel.ι h = biprod.lift (pullback.fst f g) (pullback.snd f g) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have eq : e.hom ≫ kernelIntoCocone h = comparisonValue f g := by
    let l := biprod.lift (pullback.fst f g) (pullback.snd f g)
    have hl : δ (-1) 0 (0 : Cochain (pullback f g) Z (-1)) + Cochain.ofHom (l ≫ h) = 0 := by
      simp [l, h, biprod.lift_desc, comp_neg, pullback.condition]
    change e.hom ≫ kernelIntoCocone h = mappingCocone.lift h l 0 hl
    apply coconeHomExt h
    · simp [kernelIntoCocone, he, l]
    · apply Cochain.ext
      intro n m en
      subst m
      simp [kernelIntoCocone]
  have hi : QuasiIso (kernelIntoCocone h) := kernelToShiftedCone_quasiIso A h hs
  rw [← eq]
  exact quasiIso_comp e.hom (kernelIntoCocone h)

end DerivedFormalization.Model.Complexes
