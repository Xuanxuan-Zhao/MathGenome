import Specs.LinearAlgebraicGroups.Cohomology.AffineAcyclicity
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Positive cohomology of a quasi-coherent sheaf vanishes on affine opens.

Given a cycle on a principal open, the elements defining smaller principal opens
on which it is a boundary form an ideal. To prove closure under addition we glue
two local primitives. In degree one the overlap correction comes from localization
of the original coefficient module. In higher degrees the correction comes from
exactness in the preceding degree and surjectivity of restriction for the
resolution terms.
-/

noncomputable section

open CategoryTheory hiding evaluation
open AlgebraicGeometry Limits Opposite TopologicalSpace PrimeSpectrum
open Scheme.Modules

namespace LinearAlgebraicGroups.Cohomology

universe u

open Specs.LinearAlgebraicGroups.Cohomology (evaluation)

set_option backward.isDefEq.respectTransparency false

private abbrev res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : U ≤ V) : Γ(M, V) ⟶ Γ(M, U) :=
  M.presheaf.map (homOfLE h).op

@[simp] private lemma res_res {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (h : U ≤ V) (k : V ≤ W) (s : Γ(M, W)) :
    res M h (res M k s) = res M (h.trans k) s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] private lemma app_res {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    {U V : X.Opens} (h : U ≤ V) (s : Γ(M, V)) :
    g.app U (res M h s) = res N h (g.app V s) :=
  congr($(g.mapPresheaf.naturality (homOfLE h).op) s)

private abbrev abSheaf {X : Scheme.{u}} (M : X.Modules) : TopCat.Sheaf Ab X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

private lemma exists_gluing₂ {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (hU : U ≤ W) (hV : V ≤ W) (hW : W ≤ U ⊔ V) (s : Γ(M, U)) (t : Γ(M, V))
    (h : res M inf_le_left s = res M inf_le_right t) :
    ∃ z : Γ(M, W), res M hU z = s ∧ res M hV z = t := by
  let cover : Fin 2 → X.Opens := ![U, V]
  let sections : (i : Fin 2) → Γ(M, cover i)
    | 0 => s
    | 1 => t
  have compat : TopCat.Presheaf.IsCompatible M.presheaf cover sections := by
    simp only [TopCat.Presheaf.IsCompatible, Fin.forall_fin_two]
    refine ⟨⟨rfl, h⟩, ?_, rfl⟩
    have eq := congrArg (res M (le_of_eq (inf_comm V U))) h
    change res M (inf_le_left : V ⊓ U ≤ V) t = res M (inf_le_right : V ⊓ U ≤ U) s
    simpa only [res_res] using eq.symm
  have cover_eq : (⨆ i, cover i) = U ⊔ V := by
    apply le_antisymm
    · exact iSup_le (Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩)
    · exact sup_le (le_iSup cover 0) (le_iSup cover 1)
  let inc : ∀ i, cover i ⟶ W := fun
    | 0 => homOfLE hU
    | 1 => homOfLE hV
  obtain ⟨z, hz, _⟩ := (abSheaf M).existsUnique_gluing' cover W inc
    (by rwa [cover_eq]) sections compat
  exact ⟨z, hz 0, hz 1⟩

private lemma le_basicOpen_sup_add {R : Type u} [CommRing R] (a b : R) :
    basicOpen (a + b) ≤ basicOpen a ⊔ basicOpen b := by
  intro x hx
  change a + b ∉ x.asIdeal at hx
  change a ∉ x.asIdeal ∨ b ∉ x.asIdeal
  by_contra! hn
  exact hx (x.asIdeal.add_mem hn.1 hn.2)

private lemma mem_radical_of_basicOpen {R : Type u} [CommRing R] {a : R} {I : Ideal R}
    (h : basicOpen a ≤ ⨆ r : I, basicOpen (r : R)) : a ∈ I.radical := by
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro x hx
  by_contra ha
  obtain ⟨r, hr⟩ := Opens.mem_iSup.mp (h (show x ∈ basicOpen a from ha))
  exact hr ((PrimeSpectrum.mem_zeroLocus _ _).mp hx r.property)

section Spectrum

variable {R : CommRingCat.{u}}

private abbrev D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r

private abbrev leftOpen (a b : R) : (Spec R).Opens := D a ⊓ D (a+b)
private abbrev rightOpen (a b : R) : (Spec R).Opens := D b ⊓ D (a+b)

private lemma overlap_eq (a b : R) :
    leftOpen a b ⊓ rightOpen a b = D (a * b * (a+b)) := by
  simp only [leftOpen, rightOpen, PrimeSpectrum.basicOpen_mul]
  ac_rfl

private lemma smul_bijective {M : (Spec R).Modules} {U : (Spec R).Opens} {r : R}
    (hr : U ≤ D r) (n : ℕ) : Function.Bijective (fun x : Γ(M, U) => r ^ n • x) := by
  let e : Module.End R Γ(M, U) := algebraMap R _ r
  have he : IsUnit (e ^ n) := (M.isUnit_algebraMap_end_of_le_basicOpen r hr).pow n
  have h := (Module.End.isUnit_iff _).mp he
  change Function.Bijective (fun x : Γ(M, U) => (algebraMap R (Module.End R Γ(M, U)) (r^n)) x)
  simpa only [e, ← map_pow] using h

private lemma tilde_res_toOpen (M : ModuleCat.{u} R) {U V : (Spec R).Opens}
    (h : U ≤ V) (m : M) :
    res (tilde M) h (tilde.toOpen M V m) = tilde.toOpen M U m :=
  congr($(tilde.toOpen_res M V U (homOfLE h)) m)

/-- A section of a localized module on the overlap of the two principal opens
can be written as the difference of sections on those opens. -/
private lemma split_tilde (M : ModuleCat.{u} R) (a b : R)
    (w : Γ(tilde M, leftOpen a b ⊓ rightOpen a b)) :
    ∃ x : Γ(tilde M, leftOpen a b), ∃ y : Γ(tilde M, rightOpen a b),
      res (tilde M) inf_le_left x - res (tilde M) inf_le_right y = w := by
  let c := a+b
  let U := leftOpen a b
  let V := rightOpen a b
  let W := U ⊓ V
  have loc : IsLocalizedModule.Away (a*b*c) (tilde.toOpen M W).hom := by
    rw [show W = D (a*b*c) from overlap_eq a b]
    infer_instance
  obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj (tilde.toOpen M W).hom (a*b*c) w
  have hU : U ≤ D (a*c) := le_of_eq (PrimeSpectrum.basicOpen_mul a c).symm
  have hV : V ≤ D (b*c) := le_of_eq (PrimeSpectrum.basicOpen_mul b c).symm
  obtain ⟨x, hx⟩ := (smul_bijective (M := tilde M) hU n).2 (tilde.toOpen M U m)
  obtain ⟨y, hy⟩ := (smul_bijective (M := tilde M) hV n).2 (tilde.toOpen M V m)
  change (a*c)^n • x = tilde.toOpen M U m at hx
  change (b*c)^n • y = tilde.toOpen M V m at hy
  have hx' : res (tilde M) (inf_le_left : W ≤ U) x = b^n • w := by
    apply (smul_bijective (M := tilde M) (inf_le_left.trans hU : W ≤ D (a*c)) n).1
    change (a*c)^n • res (tilde M) (inf_le_left : W ≤ U) x = (a*c)^n • (b^n • w)
    rw [← Scheme.Modules.map_smul_Spec, hx, tilde_res_toOpen, ← mul_smul, ← mul_pow]
    simpa only [mul_right_comm a c b] using hm.symm
  have hy' : res (tilde M) (inf_le_right : W ≤ V) y = a^n • w := by
    apply (smul_bijective (M := tilde M) (inf_le_right.trans hV : W ≤ D (b*c)) n).1
    change (b*c)^n • res (tilde M) (inf_le_right : W ≤ V) y = (b*c)^n • (a^n • w)
    rw [← Scheme.Modules.map_smul_Spec, hy, tilde_res_toOpen, ← mul_smul, ← mul_pow]
    simpa only [mul_comm (b*c) a, ← mul_assoc] using hm.symm
  let J : Ideal R := Ideal.span {a^n, b^n}
  have ha : a ∈ J.radical := Ideal.mem_radical_iff.mpr ⟨n, Ideal.subset_span (by simp)⟩
  have hb : b ∈ J.radical := Ideal.mem_radical_iff.mpr ⟨n, Ideal.subset_span (by simp)⟩
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp (J.radical.add_mem ha hb)
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hk
  obtain ⟨x', hx''⟩ := (smul_bijective (M := tilde M) (inf_le_right : U ≤ D c) k).2 (q • x)
  obtain ⟨y', hy''⟩ := (smul_bijective (M := tilde M) (inf_le_right : V ≤ D c) k).2 (-(p • y))
  change c^k • x' = q • x at hx''
  change c^k • y' = -(p • y) at hy''
  refine ⟨x', y', (smul_bijective (M := tilde M)
    (inf_le_left.trans inf_le_right : W ≤ D c) k).1 ?_⟩
  change c^k • (res (tilde M) (inf_le_left : W ≤ U) x' -
    res (tilde M) (inf_le_right : W ≤ V) y') = c^k • w
  rw [smul_sub, ← Scheme.Modules.map_smul_Spec, ← Scheme.Modules.map_smul_Spec, hx'', hy'']
  rw [map_neg, sub_neg_eq_add, Scheme.Modules.map_smul_Spec, Scheme.Modules.map_smul_Spec,
    hx', hy', ← mul_smul, ← mul_smul, ← add_smul, add_comm, hpq]

end Spectrum


private instance {X : Scheme.{u}} :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  preservesFiniteColimits J _ _ := by
    constructor
    intro F
    let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let T := SheafOfModules.forget X.ringCatSheaf
    let A := SheafOfModules.toSheaf X.ringCatSheaf
    have : PreservesColimitsOfShape J (S ⋙ A) := by
      change PreservesColimitsOfShape J
        (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          presheafToSheaf _ AddCommGrpCat.{u})
      infer_instance
    let t := isColimitOfPreserves S (colimit.isColimit (F ⋙ T))
    have : PreservesColimit ((F ⋙ T) ⋙ S) A :=
      preservesColimit_of_preserves_colimit_cocone t
        (isColimitOfPreserves (S ⋙ A) (colimit.isColimit (F ⋙ T)))
    let e : ((F ⋙ T) ⋙ S) ≅ F :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit)
    exact preservesColimit_of_iso_diagram A e

private lemma locally_surjective_of_epi {X : Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) [Epi f] : TopCat.Presheaf.IsLocallySurjective f.mapPresheaf := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.PreservesEpimorphisms := by infer_instance
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi (F.map f)).2 inferInstance

private lemma lift_cycle_locally {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.Exact)
    {U : X.Opens} (s : Γ(S.X₂, U)) (hs : S.g.app U s = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hV : V ≤ U), (∃ t : Γ(S.X₁, V),
      S.f.app V t = res S.X₂ hV s) ∧ x ∈ V := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : F.Additive := inferInstanceAs ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive)
  have : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  have : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let T := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hT : T.Exact := T.exact_of_f_is_kernel S.cyclesIsKernel
  obtain ⟨s', hs'⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (hT.map F) (show Mono (F.map S.iCycles) by infer_instance) s hs
  have : Epi S.toCycles := S.exact_iff_epi_toCycles.mp hS
  obtain ⟨V, hV, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff S.toCycles.mapPresheaf).mp
      (locally_surjective_of_epi S.toCycles) U s' x hx
  refine ⟨V, hV, ⟨t, ?_⟩, hxV⟩
  change S.iCycles.app U s' = s at hs'
  change S.toCycles.app V t = res S.cycles hV s' at ht
  rw [← S.toCycles_i, Hom.comp_app, ConcreteCategory.comp_apply, ht, app_res, hs']

private abbrev freeOpenPresheaf {X : Scheme.{u}} (U : X.Opens) :=
  (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)

private abbrev sheafifyModules (X : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

private def freeOpenHomEquiv {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    ((sheafifyModules X).obj (freeOpenPresheaf U) ⟶ M) ≃ Γ(M, U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (freeOpenPresheaf U) M).trans PresheafOfModules.freeYonedaEquiv

/-- Injectivity applied to the inclusion of the free module sheaves on two opens
extends sections across the inclusion. -/
private lemma restrict_surjective_of_injective {X : Scheme.{u}} (J : X.Modules) [Injective J]
    {U V : X.Opens} (h : U ≤ V) : Function.Surjective (res J h) := by
  let m : freeOpenPresheaf U ⟶ freeOpenPresheaf V :=
    (PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map (homOfLE h))
  have : Mono m := PresheafOfModules.mono_of_injective (f := m) <| by
    intro W
    change Function.Injective (Finsupp.mapDomain (fun f : W.unop ⟶ U => f ≫ homOfLE h))
    exact Finsupp.mapDomain_injective (fun _ _ _ => Subsingleton.elim _ _)
  have : Mono ((sheafifyModules X).map m) := inferInstance
  intro s
  let p := (freeOpenHomEquiv U J).symm s
  let q := Injective.factorThru p ((sheafifyModules X).map m)
  have comm : (sheafifyModules X).map m ≫ q = p := Injective.comp_factorThru _ _
  refine ⟨freeOpenHomEquiv V J q, ?_⟩
  have eq : freeOpenHomEquiv U J ((sheafifyModules X).map m ≫ q) =
      res J h (freeOpenHomEquiv V J q) := by
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    change PresheafOfModules.freeYonedaEquiv (adj.homEquiv _ _ ((sheafifyModules X).map m ≫ q)) = _
    have ha := adj.homEquiv_naturality_left m q
    rw [ha]
    let k := adj.homEquiv (freeOpenPresheaf V) J q
    let adjFree := PresheafOfModules.freeAdjunction X.ringCatSheaf.obj
    change yonedaEquiv (adjFree.homEquiv (yoneda.obj U) _ (m ≫ k)) =
      res J h (yonedaEquiv (adjFree.homEquiv (yoneda.obj V) _ k))
    rw [adjFree.homEquiv_naturality_left (yoneda.map (homOfLE h)) k]
    exact (yonedaEquiv_naturality _ _).symm
  rw [← eq, comm]
  exact (freeOpenHomEquiv U J).apply_symm_apply s

private instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).Additive where
  map_add := by intros; rfl

private instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor f) := by
  let precompose := (Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ Ab.{u}).obj f.opensFunctor.op
  have : PreservesFiniteLimits precompose := by
    constructor
    intro J _ _
    exact whiskeringLeft_preservesLimitsOfShape J f.opensFunctor.op
  have : PreservesFiniteLimits (restrictFunctor f ⋙ toPresheaf X) := by
    change PreservesFiniteLimits (toPresheaf Y ⋙
      (Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ Ab.{u}).obj f.opensFunctor.op)
    exact comp_preservesFiniteLimits (toPresheaf Y) precompose
  exact preservesFiniteLimits_of_reflects_of_preserves (restrictFunctor f) (toPresheaf X)

private lemma restrict_res_surjective_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (J : Y.Modules) [Injective J] {U V : X.Opens} (h : U ≤ V) :
    Function.Surjective (res (J.restrict f) h) :=
  restrict_surjective_of_injective J (f.image_mono h)


section Spectrum

variable {R : CommRingCat.{u}}

private lemma principal_cover (a b : R) : D (a+b) ≤ leftOpen a b ⊔ rightOpen a b := by
  intro x hx
  change (x ∈ D a ∧ x ∈ D (a+b)) ∨ (x ∈ D b ∧ x ∈ D (a+b))
  exact (le_basicOpen_sup_add a b hx).elim (fun h => Or.inl ⟨h, hx⟩)
    (fun h => Or.inr ⟨h, hx⟩)

private def splitsKernel {A B : (Spec R).Modules} (g : A ⟶ B) : Prop :=
  ∀ (a b : R) (w : Γ(A, leftOpen a b ⊓ rightOpen a b)),
    g.app _ w = 0 →
    ∃ x : Γ(A, leftOpen a b), ∃ y : Γ(A, rightOpen a b),
      g.app _ x = 0 ∧ g.app _ y = 0 ∧ res A inf_le_left x - res A inf_le_right y = w

private lemma lift_add {A B : (Spec R).Modules} {g : A ⟶ B} (hg : splitsKernel g)
    {V : (Spec R).Opens} (s : Γ(B, V)) {a b : R} (ha : D a ≤ V) (hb : D b ≤ V)
    (x : Γ(A, D a)) (y : Γ(A, D b))
    (hx : g.app _ x = res B ha s) (hy : g.app _ y = res B hb s) :
    ∃ z : Γ(A, D (a+b)), g.app _ z = res B ((le_basicOpen_sup_add a b).trans (sup_le ha hb)) s := by
  let U₁ := leftOpen a b
  let U₂ := rightOpen a b
  let W := U₁ ⊓ U₂
  let t₁ := res A (inf_le_left : U₁ ≤ D a) x
  let t₂ := res A (inf_le_left : U₂ ≤ D b) y
  let w := res A (inf_le_left : W ≤ U₁) t₁ - res A (inf_le_right : W ≤ U₂) t₂
  have hw : g.app W w = 0 := by
    dsimp only [w]
    rw [map_sub, app_res g (inf_le_left : W ≤ U₁) t₁, app_res g (inf_le_right : W ≤ U₂) t₂]
    dsimp only [t₁, t₂]
    rw [app_res g (inf_le_left : U₁ ≤ D a) x, app_res g (inf_le_left : U₂ ≤ D b) y,
      hx, hy]
    repeat rw [res_res]
    exact sub_self _
  obtain ⟨p, q, hp, hq, hpq⟩ := hg a b w hw
  have eq : res A (inf_le_left : W ≤ U₁) (t₁ - p) =
      res A (inf_le_right : W ≤ U₂) (t₂ - q) := by
    rw [map_sub, map_sub]
    apply sub_eq_sub_iff_sub_eq_sub.mpr
    exact hpq.symm
  obtain ⟨z, hz₁, hz₂⟩ := exists_gluing₂ A
    (inf_le_right : U₁ ≤ D (a+b)) (inf_le_right : U₂ ≤ D (a+b))
    (principal_cover a b) (t₁ - p) (t₂ - q) eq
  refine ⟨z, (abSheaf B).eq_of_locally_eq₂
    (homOfLE (inf_le_right : U₁ ≤ D (a+b))) (homOfLE (inf_le_right : U₂ ≤ D (a+b)))
    (principal_cover a b) _ _ ?_ ?_⟩
  · change res B (inf_le_right : U₁ ≤ D (a+b)) (g.app _ z) = _
    rw [← app_res, hz₁, map_sub, hp, sub_zero]
    change g.app U₁ t₁ = res B (inf_le_right : U₁ ≤ D (a+b)) (res B _ s)
    dsimp only [t₁]
    rw [app_res g (inf_le_left : U₁ ≤ D a) x, hx, res_res, res_res]
  · change res B (inf_le_right : U₂ ≤ D (a+b)) (g.app _ z) = _
    rw [← app_res, hz₂, map_sub, hq, sub_zero]
    change g.app U₂ t₂ = res B (inf_le_right : U₂ ≤ D (a+b)) (res B _ s)
    dsimp only [t₂]
    rw [app_res g (inf_le_left : U₂ ≤ D b) y, hy, res_res, res_res]

/-- The elements whose principal opens admit a lift of a fixed cycle form an
ideal. Local exactness puts the element defining the original open in its radical. -/
private lemma exact_sections_on_principal {S : ShortComplex (Spec R).Modules} (hS : S.Exact)
    (hSplit : splitsKernel S.f) (c : R) (s : Γ(S.X₂, D c)) (hs : S.g.app _ s = 0) :
    ∃ t : Γ(S.X₁, D c), S.f.app _ t = s := by
  classical
  let I : Ideal R :=
    { carrier := {a | ∃ ha : D a ≤ D c, ∃ t : Γ(S.X₁, D a), S.f.app _ t = res S.X₂ ha s}
      zero_mem' := by
        have h : D (0 : R) = ⊥ := PrimeSpectrum.basicOpen_zero
        refine ⟨by rw [h]; exact bot_le, 0, ?_⟩
        have hz : IsZero Γ(S.X₂, D (0 : R)) :=
          (isZero_zero Ab).of_iso (((abSheaf S.X₂).isTerminalOfEqEmpty h).uniqueUpToIso
            (isZero_zero Ab).isTerminal)
        rw [map_zero]
        have hzero := hz.eq_of_src (0 : Γ(S.X₂, D (0 : R)) ⟶ _) (𝟙 _)
        exact congr($(hzero) (res S.X₂ (h.symm ▸ bot_le) s))
      add_mem' := by
        rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
        exact ⟨(le_basicOpen_sup_add a b).trans (sup_le ha hb),
          lift_add hSplit s ha hb x y hx hy⟩
      smul_mem' := by
        rintro a b ⟨hb, t, ht⟩
        change ∃ h : D (a * b) ≤ D c, ∃ t : Γ(S.X₁, D (a*b)), S.f.app _ t = res S.X₂ h s
        let h : D (a*b) ≤ D b := PrimeSpectrum.basicOpen_mul_le_right a b
        exact ⟨h.trans hb, res S.X₁ h t, by simp [ht]⟩ }
  have hcover : D c ≤ ⨆ a : I, D (a : R) := by
    intro x hx
    obtain ⟨V, hV, ⟨t, ht⟩, hxV⟩ := lift_cycle_locally hS s hs x hx
    obtain ⟨_, ⟨a, rfl⟩, hxa, haV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.2
    have ham : a ∈ I := ⟨haV.trans hV, res S.X₁ haV t, by simp [ht]⟩
    exact Opens.mem_iSup.mpr ⟨⟨a, ham⟩, hxa⟩
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (mem_radical_of_basicOpen hcover)
  have hpow : c^(n+1) ∈ I := by
    rw [pow_succ, mul_comm]
    exact I.mul_mem_left c hn
  have heq : D (c^(n+1)) = D c := PrimeSpectrum.basicOpen_pow _ _ (Nat.succ_pos _)
  have hex : ∃ h : D (c^(n+1)) ≤ D c,
      ∃ t : Γ(S.X₁, D (c^(n+1))), S.f.app _ t = res S.X₂ h s := hpow
  rw [heq] at hex
  obtain ⟨h, t, ht⟩ := hex
  exact ⟨t, by simpa [res, show homOfLE h = 𝟙 (D c) from Subsingleton.elim _ _] using ht⟩

end Spectrum


private lemma comp_app_zero {X : Scheme.{u}} {A B C : X.Modules} {f : A ⟶ B} {g : B ⟶ C}
    (h : f ≫ g = 0) (U : X.Opens) (x : Γ(A, U)) : g.app U (f.app U x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, h, Hom.zero_app]
  rfl

section Spectrum

variable {R : CommRingCat.{u}}

private lemma splitsKernel_of_quasicoherent {M A B : (Spec R).Modules} [M.IsQuasicoherent]
    (ι : M ⟶ A) (g : A ⟶ B) [Mono ι] (h : ι ≫ g = 0)
    (hexact : (ShortComplex.mk ι g h).Exact) : splitsKernel g := by
  intro a b w hw
  let F := SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf
  have : F.Additive := inferInstanceAs ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).Additive)
  have : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf))
  have : PreservesFiniteColimits F := inferInstanceAs
    (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf))
  let W := leftOpen a b ⊓ rightOpen a b
  obtain ⟨m, hm⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (hexact.map F) (show Mono (F.map ι) by infer_instance) w hw
  change ι.app W m = w at hm
  let e := M.fromTildeΓ
  have : IsIso e := inferInstanceAs (IsIso M.fromTildeΓ)
  obtain ⟨m', hm'⟩ := (ConcreteCategory.bijective_of_isIso (e.app W)).2 m
  obtain ⟨x, y, hxy⟩ := split_tilde _ a b m'
  refine ⟨ι.app _ (e.app _ x), ι.app _ (e.app _ y), comp_app_zero h _ _,
    comp_app_zero h _ _, ?_⟩
  rw [← app_res ι inf_le_left, ← app_res ι inf_le_right, ← map_sub,
    ← app_res e inf_le_left, ← app_res e inf_le_right, ← map_sub, hxy, hm', hm]

private lemma principal_resolution_exact (M : (Spec R).Modules) [M.IsQuasicoherent]
    (C : CochainComplex (Spec R).Modules ℕ) (ι : M ⟶ C.X 0) [Mono ι]
    (hι : ι ≫ C.d 0 1 = 0) (hzero : (ShortComplex.mk _ _ hι).Exact)
    (hex : ∀ n : ℕ, (C.sc' n (n+1) (n+2)).Exact)
    (hflasque : ∀ (n : ℕ) {U V : (Spec R).Opens} (h : U ≤ V),
      Function.Surjective (res (C.X n) h)) :
    ∀ (n : ℕ) (a : R) (s : Γ(C.X (n+1), D a)),
      (C.d (n+1) (n+2)).app _ s = 0 →
      ∃ t : Γ(C.X n, D a), (C.d n (n+1)).app _ t = s := by
  intro n
  induction n with
  | zero =>
      exact exact_sections_on_principal (hex 0) (splitsKernel_of_quasicoherent ι _ hι hzero)
  | succ n ih =>
      apply exact_sections_on_principal (hex (n+1))
      change splitsKernel (C.d (n+1) (n+2))
      intro a b w hw
      let W := leftOpen a b ⊓ rightOpen a b
      have hW : ∀ z : Γ(C.X (n+1), W), (C.d (n+1) (n+2)).app W z = 0 →
          ∃ t : Γ(C.X n, W), (C.d n (n+1)).app W t = z := by
        rw [show W = D (a*b*(a+b)) from overlap_eq a b]
        exact ih _
      obtain ⟨t, ht⟩ := hW w hw
      obtain ⟨s, hs⟩ := hflasque n (inf_le_left : W ≤ leftOpen a b) t
      refine ⟨(C.d n (n+1)).app _ s, 0,
        comp_app_zero (C.d_comp_d n (n+1) (n+2)) _ _, map_zero _, ?_⟩
      rw [map_zero, sub_zero, ← app_res (C.d n (n+1)) inf_le_left, hs, ht]

end Spectrum

private lemma isZero_derived_evaluation_of_spectrum {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f ''ᵁ ⊤ = U)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((evaluation X U).rightDerived (n+1)).obj M) := by
  let I := injectiveResolution M
  let F := restrictFunctor f
  let C := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let ι : M.restrict f ⟶ C.X 0 := F.map (I.ι.f 0)
  have hι : ι ≫ C.d 0 1 = 0 := by
    change F.map (I.ι.f 0) ≫ F.map (I.cocomplex.d 0 1) = 0
    rw [← F.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero]
  have : Mono ι := by
    change Mono (F.map (I.ι.f 0))
    infer_instance
  have hzero : (ShortComplex.mk _ _ hι).Exact := I.exact₀.map F
  have hex (j : ℕ) : (C.sc' j (j+1) (j+2)).Exact := (I.exact_succ j).map F
  have hflasque (j : ℕ) {A B : (Spec R).Opens} (h : A ≤ B) :
      Function.Surjective (res (C.X j) h) :=
    restrict_res_surjective_of_injective f (I.cocomplex.X j) h
  have exactTop (s : Γ(C.X (n+1), ⊤)) (hs : (C.d (n+1) (n+2)).app _ s = 0) :
      ∃ t : Γ(C.X n, ⊤), (C.d n (n+1)).app _ t = s := by
    have H := principal_resolution_exact (M.restrict f) C ι hι hzero hex
      (fun j _ _ h => hflasque j h) n (1 : R)
    rw [show D (1 : R) = ⊤ from PrimeSpectrum.basicOpen_one] at H
    exact H s hs
  let K := ((evaluation X U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hexU : (K.sc' n (n+1) (n+2)).Exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    change ∀ (s : Γ(I.cocomplex.X (n+1), U)),
      (I.cocomplex.d (n+1) (n+2)).app U s = 0 →
        ∃ t : Γ(I.cocomplex.X n, U), (I.cocomplex.d n (n+1)).app U t = s
    rw [← hU]
    exact exactTop
  have hK : K.ExactAt (n+1) :=
    (K.exactAt_iff' n (n+1) (n+2) (by simp) (by simp only [CochainComplex.next]; rfl)).2 hexU
  exact hK.isZero_homology.of_iso (I.isoRightDerivedObj (evaluation X U) (n+1))

/-- An affine open has vanishing positive derived evaluation on quasi-coherent sheaves.
The ambient injective resolution is restricted to the open's affine spectrum. -/
theorem isZero_rightDerived_evaluation_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero (((evaluation X U).rightDerived n).obj M) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact isZero_derived_evaluation_of_spectrum hU.fromSpec U
    (hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec) M n

theorem affineAcyclicity : Specs.LinearAlgebraicGroups.Cohomology.AffineAcyclicity := by
  intro X _ M _ n hn
  exact isZero_rightDerived_evaluation_of_isAffineOpen (isAffineOpen_top X) M n hn

theorem spectrumAcyclicity : Specs.LinearAlgebraicGroups.Cohomology.SpectrumAcyclicity := by
  intro R M _ n hn
  exact isZero_rightDerived_evaluation_of_isAffineOpen (isAffineOpen_top (Spec R)) M n hn

theorem affineOpenAcyclicity : Specs.LinearAlgebraicGroups.Cohomology.AffineOpenAcyclicity := by
  intro X U hU M _ n hn
  have : IsAffine U.toScheme := hU
  exact ⟨isZero_rightDerived_evaluation_of_isAffineOpen hU M n hn,
    isZero_rightDerived_evaluation_of_isAffineOpen (isAffineOpen_top U.toScheme) (M.restrict U.ι) n hn⟩

end LinearAlgebraicGroups.Cohomology
