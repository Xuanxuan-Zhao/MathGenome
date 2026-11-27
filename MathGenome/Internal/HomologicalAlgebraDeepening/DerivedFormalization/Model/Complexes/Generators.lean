import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Generators

open CategoryTheory CategoryTheory.Limits ZeroObject HomologicalComplex

universe u

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexGenerators

noncomputable def sphere (A : Type u) [Ring A] (n : ℤ) : Cochains A :=
  sphereValue A n

noncomputable def disk (A : Type u) [Ring A] (n : ℤ) : Cochains A :=
  diskValue A n

noncomputable def iGenerator (A : Type u) [Ring A] (n : ℤ) :
    sphere A (n + 1) ⟶ disk A n :=
  iGeneratorValue A n

noncomputable def jGenerator (A : Type u) [Ring A] (n : ℤ) : 0 ⟶ disk A n :=
  jGeneratorValue A n

noncomputable def I (A : Type u) [Ring A] : MorphismProperty (Cochains A) :=
  MorphismProperty.ofHoms (iGenerator A)

noncomputable def J (A : Type u) [Ring A] : MorphismProperty (Cochains A) :=
  MorphismProperty.ofHoms (jGenerator A)

/-- Surjectivity of each component of a cochain map. -/
def degreewiseSurjective (A : Type u) [Ring A] : MorphismProperty (Cochains A) :=
  fun _ _ f ↦ ∀ n : ℤ, Function.Surjective (f.f n)

/-- Small limits and colimits of cochain complexes are computed degreewise. -/
theorem degreewiseLimitsAndColimits : degreewiseLimitsAndColimitsType.{u} := by
  intro A _
  exact ⟨⟨by intros; infer_instance⟩, ⟨by intros; infer_instance⟩,
    fun _ ↦ ⟨⟨by intros; infer_instance⟩, ⟨by intros; infer_instance⟩⟩⟩

section Generators

variable {A : Type u} [Ring A] {X Y : Cochains A}

private def regularHomEquiv (M : ModuleCat.{u} A) : (ModuleCat.of A A ⟶ M) ≃ M where
  toFun f := f 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton A M x)
  left_inv _f := ModuleCat.hom_ext (LinearMap.ext_ring (LinearMap.toSpanSingleton_apply_one A M _))
  right_inv := LinearMap.toSpanSingleton_apply_one A M

/-- Maps from a disk are determined by the image of its lower generator. -/
noncomputable def diskHomEquiv (n : ℤ) : (disk A n ⟶ X) ≃ X.X n :=
  (evalCompCoyonedaCorepresentableByDoubleId (ComplexShape.up_mk n (n + 1) rfl)
    (by omega) (ModuleCat.of A A)).homEquiv.trans (regularHomEquiv (X.X n))

@[simp]
theorem diskHomEquiv_comp (n : ℤ) (f : disk A n ⟶ X) (p : X ⟶ Y) :
    diskHomEquiv n (f ≫ p) = p.f n (diskHomEquiv n f) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Maps from a sphere are determined by the image of its generator, which is a cycle. -/
noncomputable def sphereHomEquiv (n : ℤ) :
    (sphere A n ⟶ X) ≃ {z : X.X n // X.d n (n + 1) z = 0} where
  toFun f := by
    let e := singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)
    refine ⟨(e.inv ≫ f.f n) 1, ?_⟩
    have h : e.inv ≫ f.f n ≫ X.d n (n + 1) = 0 := by
      rw [f.comm]
      simp [sphere, sphereValue]
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) (1 : A)
  invFun z := by
    let m := (regularHomEquiv (X.X n)).symm z.val
    refine mkHomFromSingle m ?_
    intro k hk
    have he : n + 1 = k := hk
    subst k
    apply (regularHomEquiv (X.X (n + 1))).injective
    change X.d n (n + 1) (m 1) = 0
    rw [show m 1 = z.val from (regularHomEquiv (X.X n)).apply_symm_apply z.val]
    exact z.property
  left_inv f := by
    apply from_single_hom_ext
    rw [mkHomFromSingle_f]
    let e := singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)
    change e.hom ≫ (regularHomEquiv (X.X n)).symm
      (regularHomEquiv (X.X n) (e.inv ≫ f.f n)) = f.f n
    simp
  right_inv z := by
    apply Subtype.ext
    let e := singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)
    change regularHomEquiv (X.X n) (e.inv ≫ (mkHomFromSingle _ _).f n) = z.val
    rw [mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    exact (regularHomEquiv (X.X n)).apply_symm_apply z.val

theorem sphereHomEquiv_comp (n : ℤ) (f : sphere A n ⟶ X) (p : X ⟶ Y) :
    (sphereHomEquiv n (f ≫ p)).val = p.f n (sphereHomEquiv n f).val := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sphereHomEquiv_iGenerator_comp (n : ℤ) (f : disk A n ⟶ X) :
    (sphereHomEquiv (n + 1) (iGenerator A n ≫ f)).val =
      X.d n (n + 1) (diskHomEquiv n f) := by
  let e := singleObjXSelf (ComplexShape.up ℤ) (n + 1) (ModuleCat.of A A)
  let r := ComplexShape.up_mk n (n + 1) rfl
  let e₀ := doubleXIso₀ (𝟙 (ModuleCat.of A A)) r
  let e₁ := doubleXIso₁ (𝟙 (ModuleCat.of A A)) r (by omega)
  change (e.inv ≫ (iGenerator A n).f (n + 1) ≫ f.f (n + 1)) 1 =
    (e₀.inv ≫ f.f n ≫ X.d n (n + 1)) 1
  have hi : (iGenerator A n).f (n + 1) = e.hom ≫ e₁.inv := by
    exact mkHomFromSingle_f e₁.inv (fun k _ ↦ by
      rw [double_d_eq_zero₀ _ _ _ _ (by omega : n + 1 ≠ n), comp_zero])
  rw [hi, Category.assoc, Iso.inv_hom_id_assoc, f.comm]
  change (e₁.inv ≫ f.f (n + 1)) 1 =
    (e₀.inv ≫ (double (𝟙 (ModuleCat.of A A)) r).d n (n + 1) ≫ f.f (n + 1)) 1
  rw [double_d _ _ (by omega : n ≠ n + 1)]
  simp [e₀, e₁]

theorem iGenerator_lifting_iff (A : Type u) [Ring A] {X Y : Cochains A} (p : X ⟶ Y)
    (n : ℤ) :
    HasLiftingProperty (iGenerator A n) p ↔
      ∀ (z : X.X (n + 1)) (y : Y.X n),
        X.d (n + 1) (n + 1 + 1) z = 0 →
        p.f (n + 1) z = Y.d n (n + 1) y →
        ∃ x : X.X n, p.f n x = y ∧ X.d n (n + 1) x = z := by
  rw [Model.hasLiftingProperty_iff_exists_diagonal]
  constructor
  · intro lift z y hz hp
    let a := (sphereHomEquiv (n + 1)).symm ⟨z, hz⟩
    let b := (diskHomEquiv n).symm y
    have ha : sphereHomEquiv (n + 1) a = ⟨z, hz⟩ := Equiv.apply_symm_apply _ _
    have hb : diskHomEquiv n b = y := Equiv.apply_symm_apply _ _
    have hs : a ≫ p = iGenerator A n ≫ b := by
      apply (sphereHomEquiv (n + 1)).injective
      apply Subtype.ext
      rw [sphereHomEquiv_iGenerator_comp, sphereHomEquiv_comp, ha, hb]
      exact hp
    obtain ⟨l, hl, hr⟩ := lift a b hs
    refine ⟨diskHomEquiv n l, ?_, ?_⟩
    · simpa only [diskHomEquiv_comp, hb] using congrArg (diskHomEquiv n) hr
    · simpa only [sphereHomEquiv_iGenerator_comp, ha] using
        congrArg (fun f ↦ (sphereHomEquiv (n + 1) f).val) hl
  · intro lift a b hs
    let z := sphereHomEquiv (n + 1) a
    have hp : p.f (n + 1) z.val = Y.d n (n + 1) (diskHomEquiv n b) := by
      have he := congrArg (fun f ↦ (sphereHomEquiv (n + 1) f).val) hs
      rw [sphereHomEquiv_iGenerator_comp, sphereHomEquiv_comp] at he
      exact he
    obtain ⟨x, hx, hd⟩ := lift z.val (diskHomEquiv n b) z.property hp
    let l := (diskHomEquiv n).symm x
    have hl : diskHomEquiv n l = x := Equiv.apply_symm_apply _ _
    refine ⟨l, ?_, ?_⟩
    · apply (sphereHomEquiv (n + 1)).injective
      apply Subtype.ext
      simpa only [sphereHomEquiv_iGenerator_comp, hl] using hd
    · apply (diskHomEquiv n).injective
      simpa only [diskHomEquiv_comp, hl] using hx

private theorem jGenerator_lifting_iff (p : X ⟶ Y) (n : ℤ) :
    HasLiftingProperty (jGenerator A n) p ↔ Function.Surjective (p.f n) := by
  rw [Model.hasLiftingProperty_iff_exists_diagonal]
  constructor
  · intro lift y
    let b := (diskHomEquiv n).symm y
    obtain ⟨l, _, hr⟩ := lift 0 b ((isZero_zero (Cochains A)).eq_of_src _ _)
    refine ⟨diskHomEquiv n l, ?_⟩
    simpa only [diskHomEquiv_comp, b, Equiv.apply_symm_apply] using
      congrArg (diskHomEquiv n) hr
  · intro surj a b _
    obtain ⟨x, hx⟩ := surj (diskHomEquiv n b)
    refine ⟨(diskHomEquiv n).symm x, (isZero_zero (Cochains A)).eq_of_src _ _, ?_⟩
    apply (diskHomEquiv n).injective
    simpa only [diskHomEquiv_comp, Equiv.apply_symm_apply] using hx

private theorem rlp_ofHoms_iff {S T : ℤ → Cochains A} (g : ∀ n, S n ⟶ T n) (p : X ⟶ Y) :
    (MorphismProperty.ofHoms g).rlp p ↔ ∀ n, HasLiftingProperty (g n) p :=
  ⟨fun hp n ↦ hp _ ⟨n⟩, by rintro hp _ _ _ ⟨n⟩; exact hp n⟩

theorem j_rlp (A : Type u) [Ring A] : (J A).rlp = degreewiseSurjective A := by
  apply MorphismProperty.ext
  intro X Y p
  change (MorphismProperty.ofHoms (jGenerator A)).rlp p ↔ ∀ n, Function.Surjective (p.f n)
  simp only [rlp_ofHoms_iff, jGenerator_lifting_iff]

end Generators

section Kernel

variable {A : Type u} [Ring A] {X Y : Cochains A}

private theorem cochainMap_d_apply (p : X ⟶ Y) (n m : ℤ) (x : X.X n) :
    p.f m (X.d n m x) = Y.d n m (p.f n x) :=
  congrArg (fun f : X.X n ⟶ Y.X m ↦ f x) (p.comm n m).symm

private theorem differential_squared_apply (X : Cochains A) (n m k : ℤ) (x : X.X n) :
    X.d m k (X.d n m x) = 0 := by
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
    congrArg (fun f : X.X n ⟶ X.X k ↦ f x) (X.d_comp_d n m k)

private theorem exactAt_succ_iff (X : Cochains A) (n : ℤ) :
    X.ExactAt (n + 1) ↔
      ∀ z : X.X (n + 1), X.d (n + 1) (n + 1 + 1) z = 0 →
        ∃ x : X.X n, X.d n (n + 1) x = z := by
  rw [X.exactAt_iff' n (n + 1) (n + 1 + 1)
    ((ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk n (n + 1) rfl))
    ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl))]
  exact ShortComplex.moduleCat_exact_iff _

private theorem kernel_component_eq_zero (p : X ⟶ Y) (n : ℤ) (x : (kernel p).X n) :
    p.f n ((kernel.ι p).f n x) = 0 := by
  simpa only [comp_f, zero_f, ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
    congrArg (fun f : kernel p ⟶ Y ↦ f.f n x) (kernel.condition p)

private theorem exists_kernel_component (p : X ⟶ Y) (n : ℤ) (z : X.X n)
    (hz : p.f n z = 0) : ∃ x : (kernel p).X n, (kernel.ι p).f n x = z := by
  have h := (ShortComplex.exact_kernel p).map (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)
  exact (ShortComplex.moduleCat_exact_iff _).mp h z hz

private theorem kernel_acyclic_iff (p : X ⟶ Y) :
    (kernel p).Acyclic ↔
      ∀ (n : ℤ) (z : X.X (n + 1)),
        X.d (n + 1) (n + 1 + 1) z = 0 → p.f (n + 1) z = 0 →
        ∃ x : X.X n, p.f n x = 0 ∧ X.d n (n + 1) x = z := by
  have inj (n : ℤ) : Function.Injective ((kernel.ι p).f n) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro acyclic n z hdz hpz
    obtain ⟨z', hz'⟩ := exists_kernel_component p (n + 1) z hpz
    have hdz' : (kernel p).d (n + 1) (n + 1 + 1) z' = 0 := by
      apply inj (n + 1 + 1)
      rw [cochainMap_d_apply, hz', hdz, map_zero]
    obtain ⟨x', hx'⟩ := (exactAt_succ_iff (kernel p) n).mp (acyclic (n + 1)) z' hdz'
    refine ⟨(kernel.ι p).f n x', kernel_component_eq_zero p n x', ?_⟩
    rw [← cochainMap_d_apply, hx', hz']
  · intro boundaries j
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = j := ⟨j - 1, by omega⟩
    apply (exactAt_succ_iff (kernel p) n).mpr
    intro z hz
    have hdz : X.d (n + 1) (n + 1 + 1) ((kernel.ι p).f (n + 1) z) = 0 := by
      rw [← cochainMap_d_apply, hz, map_zero]
    obtain ⟨x, hx, hdx⟩ :=
      boundaries n _ hdz (kernel_component_eq_zero p (n + 1) z)
    obtain ⟨x', hx'⟩ := exists_kernel_component p n x hx
    refine ⟨x', inj (n + 1) ?_⟩
    rw [cochainMap_d_apply, hx', hdx]

/-- For a degreewise surjection, its kernel is acyclic exactly when it is a
quasi-isomorphism. -/
theorem kernel_acyclic_iff_quasiIso (p : X ⟶ Y) (hp : degreewiseSurjective A p) :
    (kernel p).Acyclic ↔ QuasiIso p := by
  have : Epi p := epi_of_epi_f p fun n ↦ (ModuleCat.epi_iff_surjective _).mpr (hp n)
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
  constructor
  · intro acyclic
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have h₀ (j : ℤ) : IsZero ((kernel p).homology j) :=
      (exactAt_iff_isZero_homology _ _).mp (acyclic j)
    have : Mono (homologyMap p n) :=
      (hS.homology_exact₂ n).mono_g ((h₀ n).eq_of_src _ _)
    have : Epi (homologyMap p n) :=
      (hS.homology_exact₃ n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)).epi_f
        ((h₀ (n + 1)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  · exact hS.acyclic_X₁

theorem i_rlp (A : Type u) [Ring A] :
    (I A).rlp = degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ) := by
  apply MorphismProperty.ext
  intro X Y p
  change (MorphismProperty.ofHoms (iGenerator A)).rlp p ↔
    degreewiseSurjective A p ∧ QuasiIso p
  rw [rlp_ofHoms_iff]
  simp only [iGenerator_lifting_iff]
  constructor
  · intro lift
    have surj : degreewiseSurjective A p := by
      intro n y
      obtain ⟨z, hz, hdz⟩ := lift (n + 1) 0 (Y.d n (n + 1) y) (map_zero _)
        (by rw [map_zero, differential_squared_apply])
      exact (lift n z y hdz hz).imp fun _ h ↦ h.1
    refine ⟨surj, (kernel_acyclic_iff_quasiIso p surj).mp ?_⟩
    apply (kernel_acyclic_iff p).mpr
    intro n z hdz hpz
    exact lift n z 0 hdz (by rw [hpz, map_zero])
  · rintro ⟨surj, quasi⟩ n z y hdz hpz
    obtain ⟨x₀, hx₀⟩ := surj n y
    have hcycles : X.d (n + 1) (n + 1 + 1) (z - X.d n (n + 1) x₀) = 0 := by
      rw [map_sub, hdz, differential_squared_apply, sub_zero]
    have hk : p.f (n + 1) (z - X.d n (n + 1) x₀) = 0 := by
      rw [map_sub, cochainMap_d_apply, hpz, hx₀, sub_self]
    have acyclic := (kernel_acyclic_iff_quasiIso p surj).mpr quasi
    obtain ⟨v, hv, hdv⟩ := (kernel_acyclic_iff p).mp acyclic n _ hcycles hk
    refine ⟨x₀ + v, ?_, ?_⟩
    · rw [map_add, hx₀, hv, add_zero]
    · rw [map_add, hdv, add_sub_cancel]

end Kernel

end DerivedFormalization.Model.Complexes
