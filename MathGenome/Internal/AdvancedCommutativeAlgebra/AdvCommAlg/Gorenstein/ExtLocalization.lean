import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.ExtLocalization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtScalarActions
import Mathlib.RingTheory.LocalProperties.InjectiveDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
Localization of categorical Ext, by dimension shifting in the coefficient
module. Localization preserves injectives over a Noetherian ring. The degree
zero comparison is localization of Hom for finitely presented modules.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace AdvCommAlg.Gorenstein.ExtLocalization

section RightExact
variable {R : Type*} [CommRing R] (S : Submonoid R)
  {A B C A' B' C' : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A']
  [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']

/-- A right exact ladder whose first two vertical maps are localizations
also localizes its cokernel. -/
theorem isLocalizedModule_of_right_exact
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (a : A →ₗ[R] A') (b : B →ₗ[R] B') (c : C →ₗ[R] C')
    [ha : IsLocalizedModule S a] [hb : IsLocalizedModule S b]
    (comm₁ : ∀ x, b (f x) = f' (a x))
    (comm₂ : ∀ x, c (g x) = g' (b x))
    (ex : Function.Exact f g) (ex' : Function.Exact f' g')
    (surj : Function.Surjective g) (surj' : Function.Surjective g')
    (units : ∀ s : S, IsUnit (algebraMap R (Module.End R C') s)) :
    IsLocalizedModule S c where
  map_units := units
  surj z := by
    obtain ⟨y, rfl⟩ := surj' z
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S b y
    refine ⟨⟨g x, s⟩, ?_⟩
    simpa only [Submonoid.smul_def, map_smul, comm₂] using congrArg g' hs
  exists_of_eq {x y} h := by
    obtain ⟨z, hz⟩ := surj (x - y)
    have hzero : g' (b z) = 0 := by rw [← comm₂, hz, map_sub, h, sub_self]
    obtain ⟨w, hw⟩ := (ex' _).mp hzero
    obtain ⟨⟨v, s⟩, hs⟩ := IsLocalizedModule.surj S a w
    change (s : R) • w = a v at hs
    have hb : b ((s : R) • z - f v) = b 0 := by
      simp only [map_sub, map_smul, comm₁, map_zero]
      rw [← hs, map_smul, hw, sub_self]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) hb
    have hf : g (f v) = 0 := (ex _).mpr ⟨v, rfl⟩
    have hh := congrArg g ht
    simp only [Submonoid.smul_def, map_smul, map_sub, hf, sub_zero, hz,
      smul_zero, map_zero] at hh
    refine ⟨t * s, ?_⟩
    simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, smul_sub,
      sub_eq_zero] using hh

end RightExact

variable {R : Type u} [CommRing R]

/-- The canonical Ext map in degree zero is the usual Hom localization map. -/
theorem isLocalizedExt_zero (S : Submonoid R) (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M] : IsLocalizedModule S (localizeExt S M N 0) := by
  let a : Ext M N 0 ≃ₗ[R] (M →ₗ[R] N) :=
    Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
  let b : Ext (M.localizedModule S) (N.localizedModule S) 0 ≃ₗ[R]
      ((M.localizedModule S) →ₗ[Localization S] (N.localizedModule S)) :=
    ((Ext.linearEquiv₀ (R := Localization S)).trans
      (ModuleCat.homLinearEquiv (S := Localization S))).restrictScalars R
  let h := IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S)
  have : IsLocalizedModule S h := inferInstance
  have : IsLocalizedModule S (b.symm.toLinearMap.comp (h.comp a.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv S _ b.symm
  convert this using 1
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Ext.mk₀_bijective M N |>.2 x
  change (Ext.mk₀ f).mapExactFunctor (ModuleCat.localizedModuleFunctor S) = _
  rw [Ext.mapExactFunctor_mk₀]
  have ha : a (Ext.mk₀ f) = f.hom := by
    change (Ext.homEquiv₀ (Ext.mk₀ f)).hom = f.hom
    exact congrArg ModuleCat.Hom.hom (Ext.homEquiv₀.apply_symm_apply f)
  change Ext.mk₀ _ = b.symm (h (a (Ext.mk₀ f)))
  rw [ha]
  rfl

/-- Over a Noetherian ring the canonical map is localization in every degree.
Dimension shifting uses injective coefficients, which need not be finite. -/
theorem isLocalizedExt (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (N : ModuleCat.{u} R) (n : ℕ) : IsLocalizedModule S (localizeExt S M N n) := by
  induction n generalizing N with
  | zero =>
    let := Module.finitePresentation_of_finite R M
    exact isLocalizedExt_zero S M N
  | succ n ih =>
    let F := ModuleCat.localizedModuleFunctor.{u} S
    let I : InjectivePresentation N := Classical.arbitrary _
    let T := ShortComplex.mk I.f (Limits.cokernel.π I.f) (Limits.cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hTF : (T.map F).ShortExact := hT.map_of_exact F
    have : Injective (T.map F).X₂ := F.injective_obj I.J
    apply isLocalizedModule_of_right_exact S
      ((Ext.mk₀ T.g).postcompOfLinear R M (add_zero n))
      (hT.extClass.postcompOfLinear R M rfl)
      ((Ext.mk₀ (F.map T.g)).postcompOfLinear R (F.obj M) (add_zero n))
      (hTF.extClass.postcompOfLinear R (F.obj M) rfl)
      (localizeExt S M T.X₂ n) (localizeExt S M T.X₃ n)
      (ha := ih _) (hb := ih _)
    · intro x
      exact (Ext.mapExactFunctor_comp F x (Ext.mk₀ T.g) (add_zero n)).trans
        (by rw [Ext.mapExactFunctor_mk₀]; rfl)
    · intro x
      exact (Ext.mapExactFunctor_comp F x hT.extClass rfl).trans
        (by rw [Ext.mapExactFunctor_extClass]; rfl)
    · exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' M hT n (n + 1) rfl)
    · exact (ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj M) hTF n (n + 1) rfl)
    · intro x
      exact Ext.covariant_sequence_exact₁ M hT x (Ext.eq_zero_of_injective _) rfl
    · intro x
      exact Ext.covariant_sequence_exact₁ (F.obj M) hTF x (Ext.eq_zero_of_injective _) rfl
    · intro s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun x : Ext (M.localizedModule S)
        (N.localizedModule S) (n + 1) => (s : R) • x)
      simpa only [algebraMap_smul] using
        (IsLocalization.map_units (Localization S) s).smul_bijective
          (β := Ext (M.localizedModule S) (N.localizedModule S) (n + 1))

/-- The canonical linear comparison, for arbitrary coefficients and arbitrary
multiplicative sets. No finite projective-dimension hypothesis is needed. -/
def comparisonEquiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (N : ModuleCat.{u} R) (n : ℕ) :
    LocalizedModule S (Ext M N n) ≃ₗ[Localization S]
      Ext (M.localizedModule S) (N.localizedModule S) n := by
  letI := isLocalizedExt R S M N n
  exact (IsLocalizedModule.iso S (localizeExt S M N n)).extendScalarsOfIsLocalization S _

@[simp] theorem comparisonEquiv_mk (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (N : ModuleCat.{u} R) (n : ℕ) (x : Ext M N n) :
    comparisonEquiv R S M N n (LocalizedModule.mk x 1) = localizeExt S M N n x := by
  let := isLocalizedExt R S M N n
  exact IsLocalizedModule.iso_mk_one S (localizeExt S M N n) x

theorem comparison : Specs.AdvCommAlg.Gorenstein.ExtLocalization.comparison := by
  intro R _ _ S M _ N n
  exact ⟨comparisonEquiv R S M N n, comparisonEquiv_mk R S M N n⟩

/-- The exact localization functor commutes with both Ext actions. -/
theorem localizeExt_mapExt (S : Submonoid R)
    {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N')
    (n : ℕ) (x : Ext M N n) :
    localizeExt S M' N' n (mapExt f g n x) =
      mapExt ((ModuleCat.localizedModuleFunctor S).map f)
        ((ModuleCat.localizedModuleFunctor S).map g) n (localizeExt S M N n x) := by
  change ((Ext.mk₀ f).comp (x.comp (Ext.mk₀ g) (add_zero n)) (zero_add n)).mapExactFunctor
    (ModuleCat.localizedModuleFunctor S) =
      (Ext.mk₀ ((ModuleCat.localizedModuleFunctor S).map f)).comp
        ((x.mapExactFunctor (ModuleCat.localizedModuleFunctor S)).comp
          (Ext.mk₀ ((ModuleCat.localizedModuleFunctor S).map g)) (add_zero n)) (zero_add n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- Naturality on all localized classes, in both variables. -/
theorem comparisonEquiv_natural (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) {M M' : ModuleCat.{u} R} [Module.Finite R M] [Module.Finite R M']
    {N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ)
    (z : LocalizedModule S (Ext M N n)) :
    comparisonEquiv R S M' N' n (LocalizedModule.map S (mapExt f g n) z) =
      mapExt ((ModuleCat.localizedModuleFunctor S).map f)
        ((ModuleCat.localizedModuleFunctor S).map g) n (comparisonEquiv R S M N n z) := by
  let := isLocalizedExt R S M' N' n
  let lhs := ((comparisonEquiv R S M' N' n).toLinearMap.comp
    (LocalizedModule.map S (mapExt f g n))).restrictScalars R
  let rhs := ((mapExt ((ModuleCat.localizedModuleFunctor S).map f)
    ((ModuleCat.localizedModuleFunctor S).map g) n).comp
      (comparisonEquiv R S M N n).toLinearMap).restrictScalars R
  have h : lhs = rhs := by
    apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S (Ext M N n))
      (localizeExt S M' N' n)
    apply LinearMap.ext
    intro x
    change comparisonEquiv R S M' N' n
      (LocalizedModule.map S (mapExt f g n) (LocalizedModule.mk x 1)) =
        mapExt ((ModuleCat.localizedModuleFunctor S).map f)
          ((ModuleCat.localizedModuleFunctor S).map g) n
          (comparisonEquiv R S M N n (LocalizedModule.mk x 1))
    rw [LocalizedModule.map_mk, comparisonEquiv_mk, comparisonEquiv_mk]
    exact localizeExt_mapExt S f g n x
  exact LinearMap.congr_fun h z

theorem naturalComparison : Specs.AdvCommAlg.Gorenstein.ExtLocalization.naturalComparison := by
  intro R _ _ S n
  refine ⟨fun M _ N => comparisonEquiv R S M N n, ?_, ?_⟩
  · intro M _ N x
    exact comparisonEquiv_mk R S M N n x
  · intro M M' _ _ N N' f g z
    exact comparisonEquiv_natural R S f g n z

/-- Transport categorical Ext along module isomorphisms, retaining its
coefficient-ring scalar action. -/
def extEquivOfIso {A : Type u} [CommRing A] {M M' N N' : ModuleCat.{u} A}
    (i : M ≅ M') (j : N ≅ N') (n : ℕ) : Ext M N n ≃ₗ[A] Ext M' N' n where
  toLinearMap := mapExt i.inv j.hom n
  invFun := mapExt i.hom j.inv n
  left_inv x := by
    change (Ext.mk₀ i.hom).comp
      (((Ext.mk₀ i.inv).comp (x.comp (Ext.mk₀ j.hom) (add_zero n)) (zero_add n)).comp
        (Ext.mk₀ j.inv) (add_zero n)) (zero_add n) = x
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Ext.comp_mk₀_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ i.inv).comp
      (((Ext.mk₀ i.hom).comp (x.comp (Ext.mk₀ j.inv) (add_zero n)) (zero_add n)).comp
        (Ext.mk₀ j.hom) (add_zero n)) (zero_add n) = x
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
      Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
      Ext.comp_mk₀_id, Ext.mk₀_id_comp]

@[simp] theorem mapExt_apply {A : Type u} [CommRing A] {M M' N N' : ModuleCat.{u} A}
    (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ) (x : Ext M N n) :
    mapExt f g n x = (Ext.mk₀ f).comp (x.comp (Ext.mk₀ g) (add_zero n)) (zero_add n) := rfl

@[simp] theorem extEquivOfIso_apply {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat.{u} A} (i : M ≅ M') (j : N ≅ N')
    (n : ℕ) (x : Ext M N n) : extEquivOfIso i j n x = mapExt i.inv j.hom n x := rfl

/-- Coefficient R specializes the comparison to the exact ring appearing
in GC-07 and GC-09. -/
def primeComparisonEquiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    LocalizedModule p.primeCompl (Ext M (ModuleCat.of R R) n) ≃ₗ[Localization.AtPrime p]
      Ext (M.localizedModule p.primeCompl)
        (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) n :=
  (comparisonEquiv R p.primeCompl M (ModuleCat.of R R) n).trans
    (extEquivOfIso (Iso.refl _) (localizedRingIso p.primeCompl) n)

theorem primeComparison : Specs.AdvCommAlg.Gorenstein.ExtLocalization.primeComparison := by
  intro R _ _ p _ M _ n
  refine ⟨primeComparisonEquiv R p M n, ?_⟩
  intro x
  change extEquivOfIso (Iso.refl _) (localizedRingIso p.primeCompl) n
    (comparisonEquiv R p.primeCompl M (ModuleCat.of R R) n (LocalizedModule.mk x 1)) = _
  rw [comparisonEquiv_mk]
  change (Ext.mk₀ (𝟙 _)).comp _ (zero_add n) = _
  simp

set_option maxHeartbeats 800000 in
/-- Naturality after identifying the localized coefficient R with R_p. -/
theorem primeComparisonEquiv_natural (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] {M M' : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Finite R M'] (f : M' ⟶ M) (n : ℕ)
    (z : LocalizedModule p.primeCompl (Ext M (ModuleCat.of R R) n)) :
    primeComparisonEquiv R p M' n
      (LocalizedModule.map p.primeCompl (mapExt f (𝟙 (ModuleCat.of R R)) n) z) =
      mapExt ((ModuleCat.localizedModuleFunctor p.primeCompl).map f)
        (𝟙 (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) n
        (primeComparisonEquiv R p M n z) := by
  have h := comparisonEquiv_natural R p.primeCompl f (𝟙 (ModuleCat.of R R)) n z
  dsimp only [primeComparisonEquiv, LinearEquiv.trans_apply]
  rw [h]
  have hi : ModuleCat.localizedModuleMap p.primeCompl (𝟙 (ModuleCat.of R R)) = 𝟙 _ :=
    (ModuleCat.localizedModuleFunctor p.primeCompl).map_id _
  dsimp (config := { instances := true }) only [ModuleCat.localizedModuleFunctor]
  simp only [extEquivOfIso_apply, mapExt_apply, hi, Iso.refl_inv,
    Ext.mk₀_id_comp, Ext.comp_mk₀_id, Ext.comp_assoc_of_third_deg_zero]

theorem primeNaturalComparison :
    Specs.AdvCommAlg.Gorenstein.ExtLocalization.primeNaturalComparison := by
  intro R _ _ p _ n
  refine ⟨fun M _ => primeComparisonEquiv R p M n, ?_, ?_⟩
  · intro M _ x
    change extEquivOfIso (Iso.refl _) (localizedRingIso p.primeCompl) n
      (comparisonEquiv R p.primeCompl M (ModuleCat.of R R) n (LocalizedModule.mk x 1)) = _
    rw [comparisonEquiv_mk]
    change (Ext.mk₀ (𝟙 _)).comp _ (zero_add n) = _
    simp
  · intro M M' _ _ f z
    exact primeComparisonEquiv_natural R p f n z

/-- Explicit comparison for the quotient by the extended ideal. -/
def idealQuotientComparisonEquiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (I : Ideal R) (n : ℕ) :
    LocalizedModule p.primeCompl
      (Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) n) ≃ₗ[Localization.AtPrime p]
      Ext (ModuleCat.of (Localization.AtPrime p)
        ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))))
        (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) n :=
  (comparisonEquiv R p.primeCompl (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) n).trans
    (extEquivOfIso (localizedQuotientIso p.primeCompl I) (localizedRingIso p.primeCompl) n)

theorem idealQuotientComparison :
    Specs.AdvCommAlg.Gorenstein.ExtLocalization.idealQuotientComparison := by
  intro R _ _ p _ I n
  refine ⟨idealQuotientComparisonEquiv R p I n, ?_⟩
  intro x
  change extEquivOfIso (localizedQuotientIso p.primeCompl I) (localizedRingIso p.primeCompl) n
    (comparisonEquiv R p.primeCompl (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) n
      (LocalizedModule.mk x 1)) = _
  rw [comparisonEquiv_mk]
  rfl

/-- Vanishing after localization of the first module forces localized Ext
to vanish, including degree zero. -/
theorem localizedExt_subsingleton (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (N : ModuleCat.{u} R) (n : ℕ) [Subsingleton (LocalizedModule S M)] :
    Subsingleton (LocalizedModule S (Ext M N n)) := by
  have : Subsingleton (M.localizedModule S) :=
    (equivShrink (LocalizedModule S M)).symm.subsingleton
  have hid : 𝟙 (M.localizedModule S) = 0 := by ext x; exact Subsingleton.elim _ _
  have : Subsingleton (Ext (M.localizedModule S) (N.localizedModule S) n) := by
    apply subsingleton_of_forall_eq 0
    intro x
    calc x = (Ext.mk₀ (𝟙 (M.localizedModule S))).comp x (zero_add n) := by simp
         _ = 0 := by rw [hid]; simp
  exact (comparisonEquiv R S M N n).injective.subsingleton

theorem support_subset : Specs.AdvCommAlg.Gorenstein.ExtLocalization.support_subset := by
  intro R _ _ M _ N n p hp
  by_contra h
  have := (Module.notMem_support_iff (R := R) (M := M)).mp h
  have := localizedExt_subsingleton R p.asIdeal.primeCompl M N n
  exact (Module.notMem_support_iff (R := R) (M := Ext M N n)).mpr inferInstance hp

end AdvCommAlg.Gorenstein.ExtLocalization
