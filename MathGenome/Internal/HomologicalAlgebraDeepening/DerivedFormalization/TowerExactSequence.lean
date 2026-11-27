import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Cochains
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TowerExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-! The canonical maps of the short complex attached to an inverse tower. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits Opposite

open Specs.DerivedFormalization.TowerExactSequence (transition towerProduct)

universe u v w

noncomputable section

variable {R : Type u} [Ring R]

/-- The canonical map from the inverse limit to the product of the stages. -/
abbrev towerLimitInclusion (A : ℕᵒᵖ ⥤ Comp.{v} R) :=
  Specs.DerivedFormalization.TowerExactSequence.inclusionValue A

/-- The successor transition on the product of the stages. -/
abbrev towerShift (A : ℕᵒᵖ ⥤ Comp.{v} R) :=
  Specs.DerivedFormalization.TowerExactSequence.shiftValue A

/-- The identity minus the successor transition on the product. -/
abbrev towerDifference (A : ℕᵒᵖ ⥤ Comp.{v} R) :=
  Specs.DerivedFormalization.TowerExactSequence.differenceValue A

/-- The inverse limit, product, and difference map form a short complex for every tower. -/
abbrev towerShortComplex (A : ℕᵒᵖ ⥤ Comp.{v} R) : ShortComplex (Comp.{v} R) :=
  Specs.DerivedFormalization.TowerExactSequence.shortComplexValue A

@[reassoc]
lemma towerLimitInclusion_π (A : ℕᵒᵖ ⥤ Comp.{v} R) (n : ℕ) :
    towerLimitInclusion A ≫ Pi.π (fun m ↦ A.obj (op m)) n = limit.π A (op n) :=
  Pi.lift_comp_π _ _

@[reassoc]
lemma towerDifference_π (A : ℕᵒᵖ ⥤ Comp.{v} R) (n : ℕ) :
    towerDifference A ≫ Pi.π (fun m ↦ A.obj (op m)) n =
      Pi.π (fun m ↦ A.obj (op m)) n -
        Pi.π (fun m ↦ A.obj (op m)) (n + 1) ≫ transition A n := by
  simp only [Specs.DerivedFormalization.TowerExactSequence.differenceValue,
    Specs.DerivedFormalization.TowerExactSequence.shiftValue, Preadditive.sub_comp,
    Category.id_comp, Pi.map'_comp_π]

/-- The inverse limit is the kernel of the difference map for any inverse tower. -/
def towerLimitIsKernel (A : ℕᵒᵖ ⥤ Comp.{v} R) :
    IsLimit (KernelFork.ofι (towerShortComplex A).f (towerShortComplex A).zero) := by
  let p := fun n : ℕ ↦ Pi.π (fun m ↦ A.obj (op m)) n
  let cone (s : KernelFork (towerDifference A)) : Cone A :=
    { pt := s.pt
      π := NatTrans.ofOpSequence (fun n ↦ s.ι ≫ p n) (by
        intro n
        have h : s.ι ≫ towerDifference A ≫ p n = 0 := by
          rw [← Category.assoc, s.condition, zero_comp]
        rw [towerDifference_π, Preadditive.comp_sub, sub_eq_zero] at h
        change 𝟙 s.pt ≫ (s.ι ≫ p n) = (s.ι ≫ p (n + 1)) ≫ transition A n
        rw [Category.id_comp, Category.assoc]
        exact h) }
  have fac (s : KernelFork (towerDifference A)) :
      limit.lift A (cone s) ≫ towerLimitInclusion A = s.ι := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, towerLimitInclusion_π, limit.lift_π]
    rfl
  change IsLimit (KernelFork.ofι (towerLimitInclusion A) (towerShortComplex A).zero)
  refine isLimitAux _ (fun s ↦ limit.lift A (cone s)) fac ?_
  intro s m hm
  change m ≫ towerLimitInclusion A = s.ι at hm
  apply limit.hom_ext (F := A)
  intro j
  rw [limit.lift_π]
  change m ≫ limit.π A (op j.unop) = s.ι ≫ p j.unop
  rw [← towerLimitInclusion_π, ← Category.assoc, hm]

/-- A strict map of towers induces commuting squares on the limit and both products. -/
theorem towerShortComplex_naturality (R : Type u) [Ring R]
    (A B : ℕᵒᵖ ⥤ Comp.{v} R) (f : A ⟶ B) :
    let p : towerProduct A ⟶ towerProduct B :=
      CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
    limMap f ≫ towerLimitInclusion B = towerLimitInclusion A ≫ p ∧
    p ≫ towerDifference B = towerDifference A ≫ p := by
  dsimp only
  constructor
  · apply Pi.hom_ext
    intro n
    simp only [Category.assoc, towerLimitInclusion_π, limMap_π, Pi.map_π,
      towerLimitInclusion_π_assoc]
  · apply Pi.hom_ext
    intro n
    simp only [Category.assoc, towerDifference_π, Preadditive.comp_sub,
      Pi.map_π, Pi.map_π_assoc, towerDifference_π_assoc, Preadditive.sub_comp]
    rw [f.naturality]

private lemma moduleFan_projections_bijective {I : Type w} [Small.{v} I]
    {M : I → ModuleCat.{v} R} {P : ModuleCat.{v} R} (p : ∀ j, P ⟶ M j)
    (hp : IsLimit (Fan.mk P p)) :
    Function.Bijective (fun (x : P) (j : I) ↦ p j x) := by
  let U := forget (ModuleCat.{v} R)
  let F := Discrete.functor M
  let : PreservesLimit F U :=
    preservesLimit_of_preserves_limit_cone (ModuleCat.HasLimits.limitConeIsLimit F)
      (Types.Small.limitConeIsLimit (F ⋙ U))
  let h := isLimitFanMkObjOfIsLimit U M p hp
  let hc := (Types.Small.productLimitCone (fun j ↦ U.obj (M j))).isLimit
  let e := (h.conePointUniqueUpToIso hc).toEquiv.trans (equivShrink _).symm
  have he : (e : P → ∀ j, M j) = fun x j ↦ p j x := by
    funext x j
    have hj := h.conePointUniqueUpToIso_hom_comp hc ⟨j⟩
    exact congr($hj x)
  rw [← he]
  exact e.bijective

private lemma cochainProduct_projections_bijective {I : Type w} [Small.{v} I]
    (A : I → Comp.{v} R) (i : ℤ) :
    Function.Bijective (fun (x : (∏ᶜ A).X i) (j : I) ↦ (Pi.π A j).f i x) := by
  let : HasLimitsOfShape (Discrete I) (ModuleCat.{v} R) := ModuleCat.hasLimitsOfShape
  exact moduleFan_projections_bijective _ (isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i) A)

private lemma towerDifference_surjective (A : ℕᵒᵖ ⥤ Comp.{v} R)
    (hs : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i)) (i : ℤ) :
    Function.Surjective ((towerDifference A).f i) := by
  let stages := fun n : ℕ ↦ A.obj (op n)
  let p := fun n : ℕ ↦ (Pi.π stages n).f i
  have hp : Function.Bijective (fun (x : (towerProduct A).X i) n ↦ p n x) :=
    cochainProduct_projections_bijective stages i
  intro b
  choose lift hlift using fun n ↦ hs n i
  let a : ∀ n : ℕ, (stages n).X i :=
    Nat.rec (motive := fun n ↦ (stages n).X i) 0
      (fun n x ↦ lift n (x - p n b))
  obtain ⟨x, hx⟩ := hp.surjective a
  have hxn (n : ℕ) : p n x = a n := congrFun hx n
  refine ⟨x, hp.injective (funext fun n ↦ ?_)⟩
  have hcoord := HomologicalComplex.congr_hom (towerDifference_π A n) i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply] at hcoord
  change p n ((towerDifference A).f i x) = p n b
  rw [← ConcreteCategory.comp_apply, hcoord]
  change p n x - (transition A n).f i (p (n + 1) x) = p n b
  rw [hxn n, hxn (n + 1)]
  change a n - (transition A n).f i (lift n (a n - p n b)) = p n b
  rw [hlift, sub_sub_cancel]

/-- The canonical sequence is short exact for towers with degreewise-surjective transitions. -/
theorem towerShortComplex_shortExact (R : Type u) [Ring R] (A : ℕᵒᵖ ⥤ Comp.{v} R)
    (hs : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i)) :
    (towerShortComplex A).ShortExact := by
  exact ShortComplex.ShortExact.mk' ((towerShortComplex A).exact_of_f_is_kernel
    (towerLimitIsKernel A)) (mono_of_isLimit_fork (towerLimitIsKernel A))
    (HomologicalComplex.epi_of_epi_f (towerDifference A)
      (fun i ↦ (ModuleCat.epi_iff_surjective _).2 (towerDifference_surjective A hs i)))

private lemma homologyClass_eq_zero_iff (S : ShortComplex (ModuleCat.{v} R))
    (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ y : S.X₁, S.f y = S.iCycles z := by
  have h := congrArg (fun (f : S.cycles ⟶ S.opcycles) ↦ f z) S.homology_π_ι
  change S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) at h
  have hi := (ModuleCat.mono_iff_injective S.homologyι).1 inferInstance
  have hz : S.homologyπ z = 0 ↔ S.pOpcycles (S.iCycles z) = 0 := by
    have hzero : S.homologyι (0 : S.homology) = 0 := map_zero S.homologyι.hom
    rw [← h, ← hzero]
    exact hi.eq_iff.symm
  rw [hz, S.moduleCat_pOpcycles_eq_zero_iff]
  rfl

private lemma homologyπ_surjective (K : Comp.{v} R) (i : ℤ) :
    Function.Surjective (K.homologyπ i) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The cohomology comparison induced by the product projections is an isomorphism. -/
theorem cohomology_preservesProduct (R : Type u) [Ring R] (I : Type w) [Small.{v} I]
    (A : I → Comp.{v} R) (i : ℤ) : IsIso (piComparison (cohomologyFunctor R i) A) := by
  let K := ∏ᶜ A
  let p := Pi.π A
  let H := cohomologyFunctor R i
  let cmp := piComparison H A
  let prev := (ComplexShape.up ℤ).prev i
  let next := (ComplexShape.up ℤ).next i
  have coord (j : I) (x : K.homology i) :
      Pi.π (fun j ↦ H.obj (A j)) j (cmp x) = HomologicalComplex.homologyMap (p j) i x :=
    congr($(piComparison_comp_π H A j) x)
  have cycleCoord (j : I) (z : K.cycles i) :
      (A j).iCycles i (HomologicalComplex.cyclesMap (p j) i z) =
        (p j).f i (K.iCycles i z) :=
    congr($(HomologicalComplex.cyclesMap_i (p j) i) z)
  have classCoord (j : I) (z : K.cycles i) :
      HomologicalComplex.homologyMap (p j) i (K.homologyπ i z) =
        (A j).homologyπ i (HomologicalComplex.cyclesMap (p j) i z) :=
    congr($(HomologicalComplex.homologyπ_naturality (p j) i) z)
  have diffCoord (j : I) (a b : ℤ) (x : K.X a) :
      (p j).f b (K.d a b x) = (A j).d a b ((p j).f a x) :=
    congrArg (fun (f : K.X a ⟶ (A j).X b) ↦ f x) ((p j).comm a b).symm
  have hp (k : ℤ) : Function.Bijective (fun (x : K.X k) j ↦ (p j).f k x) :=
    cochainProduct_projections_bijective A k
  apply (ConcreteCategory.isIso_iff_bijective cmp).2
  constructor
  · apply (injective_iff_map_eq_zero cmp.hom).2
    intro x hx
    change cmp x = 0 at hx
    obtain ⟨z, rfl⟩ := homologyπ_surjective K i x
    have hboundary (j : I) : ∃ y : (A j).X prev,
        (A j).d prev i y = (p j).f i (K.iCycles i z) := by
      have hz := (coord j (K.homologyπ i z)).symm
      rw [hx, map_zero, classCoord] at hz
      obtain ⟨y, hy⟩ := (homologyClass_eq_zero_iff ((A j).sc i) _).1 hz
      exact ⟨y, hy.trans (cycleCoord j z)⟩
    choose y hy using hboundary
    obtain ⟨b, hb⟩ := (hp prev).surjective y
    apply (homologyClass_eq_zero_iff (K.sc i) z).2
    refine ⟨b, (hp i).injective (funext fun j ↦ ?_)⟩
    have hbj : (p j).f prev b = y j := congrFun hb j
    change (p j).f i (K.d prev i b) = (p j).f i (K.iCycles i z)
    rw [diffCoord, hbj, hy]
  · intro x
    choose z hz using fun j : I ↦ homologyπ_surjective (A j) i
      (Pi.π (fun j ↦ H.obj (A j)) j x)
    obtain ⟨y, hy⟩ := (hp i).surjective (fun j ↦ (A j).iCycles i (z j))
    have hyj (j : I) : (p j).f i y = (A j).iCycles i (z j) := congrFun hy j
    have hcycle : K.d i next y = 0 := by
      apply (hp next).injective
      funext j
      change (p j).f next (K.d i next y) = (p j).f next 0
      rw [diffCoord, hyj, map_zero, ← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
      rfl
    let S := K.sc i
    let zK : K.cycles i := S.moduleCatCyclesIso.inv ⟨y, hcycle⟩
    have hzK : K.iCycles i zK = y :=
      congr($(S.moduleCatCyclesIso_inv_iCycles) (⟨y, hcycle⟩ : S.moduleCatLeftHomologyData.K))
    refine ⟨K.homologyπ i zK, ?_⟩
    apply (moduleFan_projections_bijective _ (productIsProduct (fun j ↦ H.obj (A j)))).injective
    funext j
    change Pi.π (fun j ↦ H.obj (A j)) j (cmp (K.homologyπ i zK)) =
      Pi.π (fun j ↦ H.obj (A j)) j x
    rw [coord, classCoord, ← hz j]
    congr 1
    apply (ModuleCat.mono_iff_injective ((A j).iCycles i)).1 inferInstance
    rw [cycleCoord, hzK, hyj]

end
end DerivedFormalization
