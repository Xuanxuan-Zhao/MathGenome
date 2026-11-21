import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieLowDegreeCohomology
import Batteries.Tactic.OpenPrivate

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory P103.Specs.Ch10.Complexes
namespace AdvancedHomologicalAlgebra.CE.LowDegree
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

lemma zeroCoord_apply (f : W k g 0 →ₗ[k] M) :
    zeroCoord k g M f = f (wedge k g 0 Fin.elim0) := by
  change f ((exteriorPower.zeroEquiv k g).symm 1) = _
  congr 1
  apply (exteriorPower.zeroEquiv k g).injective
  simp [wedge, exteriorPower.zeroEquiv_ιMulti]

lemma oneCoord_apply (f : W k g 1 →ₗ[k] M) (x : g) :
    oneCoord k g M f x = f (wedge k g 1 (fun _ => x)) := by
  change f ((exteriorPower.oneEquiv k g).symm x) = _
  congr 1

variable (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
  (s : ∀ n, (δ (n+1)).comp (δ n) = 0)
  (hf : HasCochainFormula k g M δ)

include hf

lemma differential_zero (f : W k g 0 →ₗ[k] M) (x : g) :
    δ 0 f (wedge k g 1 (fun _ => x)) =
      Shared.Lie.inclusion k g x • zeroCoord k g M f := by
  rw [hf, zeroCoord_apply]
  simp [cochainActionSum, cochainBracketSum]
  congr 2

lemma differential_one (f : W k g 1 →ₗ[k] M) (x y : g) :
    δ 1 f (wedge k g 2 ![x,y]) =
      Shared.Lie.inclusion k g x • oneCoord k g M f y -
      Shared.Lie.inclusion k g y • oneCoord k g M f x -
      oneCoord k g M f ⁅x,y⁆ := by
  rw [hf]
  simp only [oneCoord_apply]
  simp [cochainActionSum, cochainBracketSum, Fin.sum_univ_two, sub_eq_add_neg]
  congr 2

lemma cycle_zero_iff (f : W k g 0 →ₗ[k] M) :
    δ 0 f = 0 ↔ zeroCoord k g M f ∈ invariants k g M := by
  constructor
  · intro h x
    have := LinearMap.congr_fun h (wedge k g 1 (fun _ => x))
    simpa only [differential_zero k g M δ hf, LinearMap.zero_apply] using this
  · intro h
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    have hx : x = fun _ => x 0 := by ext i; congr 1; exact Fin.eq_zero i
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      hx, differential_zero k g M δ hf]
    exact h (x 0)

lemma cycle_one_iff (f : W k g 1 →ₗ[k] M) :
    δ 1 f = 0 ↔ oneCoord k g M f ∈ derivations k g M := by
  constructor
  · intro h x y
    have := LinearMap.congr_fun h (wedge k g 2 ![x,y])
    rw [differential_one k g M δ hf] at this
    exact (sub_eq_zero.mp this).symm
  · intro h
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply, hx,
      differential_one k g M δ hf, h]
    simp

omit hf

lemma mem_cycles_iff (n : ℕ) (f : W k g n →ₗ[k] M) :
    f ∈ cycles (Ext.cochain k g M δ s) n ↔ δ n f = 0 := by
  unfold cycles
  rw [CochainComplex.next]
  simp only [Ext.cochain, CochainComplex.of_d, ModuleCat.hom_ofHom, LinearMap.mem_ker]
  rfl

lemma boundaries_zero : boundaries (Ext.cochain k g M δ s) 0 = ⊥ := by
  unfold boundaries
  rw [CochainComplex.prev_nat_zero]
  rw [HomologicalComplex.shape _ _ _ (by decide)]
  simp

lemma mem_boundaries_one (f : W k g 1 →ₗ[k] M) :
    f ∈ boundaries (Ext.cochain k g M δ s) 1 ↔ ∃ a, δ 0 a = f := by
  unfold boundaries
  rw [show (ComplexShape.up ℕ).prev 1 = 0 from CochainComplex.prev_nat_succ 0]
  rfl

include hf

lemma boundaries_one_iff (f : W k g 1 →ₗ[k] M) :
    f ∈ boundaries (Ext.cochain k g M δ s) 1 ↔
      ∃ m : M, ∀ x, oneCoord k g M f x = Shared.Lie.inclusion k g x • m := by
  rw [mem_boundaries_one]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨zeroCoord k g M a, ?_⟩
    intro x
    rw [oneCoord_apply, differential_zero k g M δ hf]
  · rintro ⟨m, hm⟩
    refine ⟨(zeroCoord k g M).symm m, ?_⟩
    apply (oneCoord k g M).injective
    ext x
    rw [oneCoord_apply, differential_zero k g M δ hf, LinearEquiv.apply_symm_apply]
    exact (hm x).symm

lemma zero_cycles_image :
    (cycles (Ext.cochain k g M δ s) 0).map
      ((zeroCoord k g M).restrictScalars ℤ).toLinearMap = invariants k g M := by
  ext m
  constructor
  · rintro ⟨f, h, rfl⟩
    exact (cycle_zero_iff k g M δ hf f).mp ((mem_cycles_iff k g M δ s 0 f).mp h)
  · intro h
    refine ⟨(zeroCoord k g M).symm m, ?_, by simp⟩
    apply (mem_cycles_iff k g M δ s 0 _).mpr
    apply (cycle_zero_iff k g M δ hf _).mpr
    simpa using h

lemma one_cycles_image :
    (cycles (Ext.cochain k g M δ s) 1).map
      ((oneCoord k g M).restrictScalars ℤ).toLinearMap = derivations k g M := by
  ext f
  constructor
  · rintro ⟨a, h, rfl⟩
    exact (cycle_one_iff k g M δ hf a).mp ((mem_cycles_iff k g M δ s 1 a).mp h)
  · intro h
    refine ⟨(oneCoord k g M).symm f, ?_, by simp⟩
    apply (mem_cycles_iff k g M δ s 1 _).mpr
    apply (cycle_one_iff k g M δ hf _).mpr
    simpa using h

/-- Restriction of the coordinate equivalences to the actual cocycles. -/
def zeroCyclesEquiv : cycles (Ext.cochain k g M δ s) 0 ≃ₗ[ℤ] invariants k g M :=
  ((zeroCoord k g M).restrictScalars ℤ).ofSubmodules _ _
    (zero_cycles_image k g M δ s hf)

def oneCyclesEquiv : cycles (Ext.cochain k g M δ s) 1 ≃ₗ[ℤ] derivations k g M :=
  ((oneCoord k g M).restrictScalars ℤ).ofSubmodules _ _
    (one_cycles_image k g M δ s hf)

omit hf
lemma cycleBoundaries_zero : cycleBoundaries (Ext.cochain k g M δ s) 0 = ⊥ := by
  simp only [cycleBoundaries, boundaries_zero k g M δ s, Submodule.comap_bot,
    Submodule.ker_subtype]

include hf
lemma one_boundaries_image :
    (cycleBoundaries (Ext.cochain k g M δ s) 1).map
      (oneCyclesEquiv k g M δ s hf).toLinearMap = inner k g M := by
  ext f
  constructor
  · rintro ⟨a, h, rfl⟩
    exact (boundaries_one_iff k g M δ s hf a.val).mp h
  · intro h
    refine ⟨(oneCyclesEquiv k g M δ s hf).symm f, ?_, by simp⟩
    apply (boundaries_one_iff k g M δ s hf _).mpr
    rcases h with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro x
    have he := congrArg (fun a : derivations k g M => a.val x)
      ((oneCyclesEquiv k g M δ s hf).apply_symm_apply f)
    exact he.trans (hm x)

/-- H⁰ is the invariant submodule; the equality is fixed by evaluation. -/
def zeroCohomologyEquiv : Homology (Ext.cochain k g M δ s) 0 ≃+ invariants k g M :=
  (((cycleBoundaries (Ext.cochain k g M δ s) 0).quotEquivOfEqBot
    (cycleBoundaries_zero k g M δ s)).trans (zeroCyclesEquiv k g M δ s hf)).toAddEquiv

/-- H¹ is derivations modulo inner derivations. -/
def oneCohomologyEquiv : Homology (Ext.cochain k g M δ s) 1 ≃+ outer k g M :=
  (Submodule.Quotient.equiv _ _ (oneCyclesEquiv k g M δ s hf)
    (one_boundaries_image k g M δ s hf)).toAddEquiv

lemma identifies : Identifies k g M δ s
    (zeroCohomologyEquiv k g M δ s hf) (oneCohomologyEquiv k g M δ s hf) := by
  constructor
  · intro z
    rfl
  · intro z
    exact ⟨oneCyclesEquiv k g M δ s hf z, rfl, rfl⟩

omit hf

variable (N : Type w') [AddCommGroup N] [Module k N]
  [Module (U k g) N] [IsScalarTower k (U k g) N]
variable (δN : ∀ n, (W k g n →ₗ[k] N) →ₗ[k] (W k g (n+1) →ₗ[k] N))
  (hfN : HasCochainFormula k g N δN)

include hf hfN in
lemma differential_natural (h : M →ₗ[U k g] N) (n : ℕ) (f : W k g n →ₗ[k] M) :
    δN n ((h.restrictScalars k).comp f) = (h.restrictScalars k).comp (δ n f) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  change δN n ((h.restrictScalars k).comp f) (wedge k g (n+1) x) =
    h (δ n f (wedge k g (n+1) x))
  rw [hfN, hf, map_add]
  congr 1
  · simp only [cochainActionSum, map_sum, map_zsmul, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, h.map_smul]
  · cases n with
    | zero => simp only [cochainBracketSum, map_zero]
    | succ n =>
      simp only [cochainBracketSum, map_sum, map_zsmul, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply]

lemma zeroCoord_natural (h : M →ₗ[U k g] N) (a : W k g 0 →ₗ[k] M) :
    zeroCoord k g N ((h.restrictScalars k).comp a) = h (zeroCoord k g M a) := by
  rw [zeroCoord_apply, zeroCoord_apply]
  rfl

lemma oneCoord_natural (h : M →ₗ[U k g] N) (a : W k g 1 →ₗ[k] M) :
    oneCoord k g N ((h.restrictScalars k).comp a) =
      (h.restrictScalars k).comp (oneCoord k g M a) := by
  ext x
  rw [oneCoord_apply]
  change h (a (wedge k g 1 (fun _ => x))) = h (oneCoord k g M a x)
  rw [oneCoord_apply]

end AdvancedHomologicalAlgebra.CE.LowDegree

namespace AdvancedHomologicalAlgebra.CE.LowDegree
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

theorem differentials : Specs.AdvancedHomologicalAlgebra.CE.LowDegree.differentialsExpected k g M := by
  intro δ hf
  constructor
  · intro m x
    rw [differential_zero k g M δ hf, LinearEquiv.apply_symm_apply]
  · intro f x y
    rw [differential_one k g M δ hf, LinearEquiv.apply_symm_apply]

theorem cohomology : Specs.AdvancedHomologicalAlgebra.CE.LowDegree.identificationsExpected k g M := by
  intro δ s hf
  exact ⟨zeroCohomologyEquiv k g M δ s hf, oneCohomologyEquiv k g M δ s hf,
    identifies k g M δ s hf⟩

open private pointwiseHomologyMap pointwiseHomologyMap_induces
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt

theorem naturality :
    Specs.AdvancedHomologicalAlgebra.CE.LowDegree.naturalityExpected.{u,v,w,w'} k g M := by
  intro δ s hf N _ _ _ _ δN sN hfN e₀ e₁ e₀N e₁N he heN h
  let K := Ext.cochain k g M δ s
  let L := Ext.cochain k g N δN sN
  let post (n : ℕ) : K.X n →ₗ[ℤ] L.X n :=
    (P103.HomTensorExactness.post (h.restrictScalars k)).toIntLinearMap
  have comm i j : (L.d i j).hom.comp (post i) = (post j).comp (K.d i j).hom := by
    by_cases hij : (ComplexShape.up ℕ).Rel i j
    · change i + 1 = j at hij
      subst j
      apply LinearMap.ext
      intro z
      simp only [K, L, Ext.cochain, CochainComplex.of_d, ModuleCat.hom_ofHom]
      exact differential_natural k g M δ hf N δN hfN h i z
    · rw [L.shape i j hij, K.shape i j hij]
      simp
  let H (n : ℕ) : Homology K n →ₗ[ℤ] Homology L n :=
    (pointwiseHomologyMap post comm n).toAddMonoidHom.toIntLinearMap
  have hH : Ext.InducesCohomologyMap post H := pointwiseHomologyMap_induces post comm
  refine ⟨H, hH, ?_, ?_⟩
  · intro a
    induction a using Submodule.Quotient.induction_on with
    | _ z =>
      rcases hH.2 0 z with ⟨y, hy, hHy⟩
      apply Subtype.ext
      change (e₀N (H 0 (homologyClass K 0 z))).val = h (e₀ (homologyClass K 0 z)).val
      rw [hHy, heN.1, he.1, hy]
      exact zeroCoord_natural k g M N h z.val
  · intro a
    induction a using Submodule.Quotient.induction_on with
    | _ z =>
      rcases hH.2 1 z with ⟨y, hy, hHy⟩
      rcases he.2 z with ⟨a, ha, hqa⟩
      rcases heN.2 y with ⟨b, hb, hqb⟩
      change e₁N (H 1 (homologyClass K 1 z)) = outerMap k g M N h (e₁ (homologyClass K 1 z))
      rw [hHy, hqb, hqa]
      change (inner k g N).mkQ b = (inner k g N).mkQ (derivationsMap k g M N h a)
      congr 1
      apply Subtype.ext
      rw [hb, hy]
      change oneCoord k g N ((h.restrictScalars k).comp z.val) =
        (h.restrictScalars k).comp a.val
      rw [ha]
      exact oneCoord_natural k g M N h z.val

theorem ext_comparison [Module.Free k g] :
    Specs.AdvancedHomologicalAlgebra.CE.LowDegree.extExpected k g M := by
  let D := boundaryData k g
  let C := cochainData k g M D
  obtain ⟨he, hfree⟩ := Ext.free_resolution k g D
  obtain ⟨e, heval, hq⟩ := Ext.cohomology k g D he M C
  obtain ⟨e₀, e₁, hident⟩ := cohomology k g M C.differential C.squared C.formula
  obtain ⟨q₀, hq₀⟩ := hq 0
  obtain ⟨q₁, hq₁⟩ := hq 1
  refine ⟨D.differential, D.augmented, he, C.differential, C.squared, e₀, e₁,
    D.formula, hfree, C.formula, hident, e, e₀.symm.trans q₀, e₁.symm.trans q₁, ?_, ?_, ?_⟩
  · intro n F z
    rw [heval, C.evaluate_tmul]
  · intro z
    simpa using hq₀ z
  · intro z
    simpa using hq₁ z

end AdvancedHomologicalAlgebra.CE.LowDegree
