import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.DualVermaExtensions
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.RestrictedDual
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Module.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-! Hom dimensions and splitting of extensions of Verma modules by dual Verma modules. -/

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U highestVector_value)
open Specs.RepTheorySurvey.CategoryO
  (Setup restrictedLieRingModule restrictedLieModule)
open Specs.RepTheorySurvey.CategoryO.DualVermaExtensions
open Specs.RepTheorySurvey.CategoryO.WeightBounds (support)
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO.DualVermaExtensions

open RestrictedDual (costandard dualModule dualMap dualWeights_spec costandard_mem_O dual_mem_O)
open Specs.RepTheorySurvey.CategoryO.RestrictedDual (pair pair_dualMap)
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal (inducedLieRingModule inducedLieModule)

open private envelopingHomOfLieHom surjective_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects
open private root_smul_weight direction_nonneg from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds
open private cartanMap onWeight dual_shortExact evaluation evaluation_bijective pair_evaluation
  weight_antisymm from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.RestrictedDual

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

private abbrev topVector (nu : D.Weight) : M D nu :=
  highestVector_value D.cartan D.direction (character D nu)

private theorem topVector_weight (nu : D.Weight) :
    topVector D nu ∈ weightSpace D.cartan (M D nu) nu := by
  have h : weightSpace D.cartan (M D nu) nu = ℂ ∙ topVector D nu :=
    (verma_mem_O D nu).2.2.2.2.2
  rw [h]
  exact Submodule.mem_span_singleton_self _

private theorem hom_ext_top (nu : D.Weight) {X : ModuleCat.{v} (U g)}
    {f k : M D nu →ₗ[U g] X} (h : f (topVector D nu) = k (topVector D nu)) : f = k :=
  LinearMap.ext_on (verma_mem_O D nu).2.2.1 (Set.eqOn_singleton.mpr h)

private theorem exists_verma_map (nu : D.Weight) (X : ModuleCat.{v} (U g)) (x : X)
    (hx : x ∈ weightSpace D.cartan X nu)
    (he : ∀ j : D.Simple, (ι ℂ (D.e j)) • x = 0) :
    ∃ f : M D nu →ₗ[U g] X, f (topVector D nu) = x := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  have hx' : ∀ h : D.cartan, ⁅(h : g), x⁆ = nu h • x :=
    (mem_weightSpace D.cartan X nu x).mp hx
  obtain ⟨f, hf, _⟩ := (_root_.LieAlgebrasAndRepresentations.VermaWeightsUniversal.verma_universal
    D.semisimple D.cartan D.direction D.regular nu (character D nu) (character_unique D nu).1
    D.e (fun j => ⟨(D.triple j).e_mem, (D.triple j).e_ne_zero⟩) X x hx' he).1
  let : LieRingModule g (M D nu : Type u) :=
    inducedLieRingModule D.cartan D.direction (character D nu)
  let : LieModule ℂ g (M D nu : Type u) :=
    inducedLieModule D.cartan D.direction (character D nu)
  exact ⟨envelopingHomOfLieHom (V := (M D nu : Type u)) (W := (X : Type v))
    (fun _ _ => rfl) (fun _ _ => rfl) f, hf⟩

private theorem costandard_support (nu lam : D.Weight) :
    nu ∈ support D (costandard D lam) ↔ weightLE D nu lam := by
  change nu ∈ support D (dualModule D (M D lam)) ↔ _
  rw [(dualWeights_spec D (M D lam) (verma_mem_O D lam).1.2.1).2.1]
  exact (verma_mem_O D lam).2.2.2.2.1 nu

private theorem no_raised_weight (nu lam : D.Weight)
    (h : ¬ (weightLE D nu lam ∧ nu ≠ lam)) (j : D.Simple) :
    ¬ weightLE D (D.alpha j + nu) lam := by
  intro hw
  change lam - (D.alpha j + nu) ∈ QPlus D at hw
  have hj : D.alpha j ∈ QPlus D := Submodule.subset_span ⟨j, rfl⟩
  have hsum : lam - nu ∈ QPlus D := by
    convert (QPlus D).add_mem hw hj using 1
    abel
  apply h ⟨hsum, ?_⟩
  intro heq
  subst lam
  rw [show nu - (D.alpha j + nu) = -D.alpha j by abel] at hw
  have hn := direction_nonneg D hw
  rw [map_neg] at hn
  exact (not_le_of_gt j.property.1.2) (neg_nonneg.mp hn)

private theorem raising_eq_zero (X : ModuleCat.{v} (U g)) (nu : D.Weight) (x : X)
    (hx : x ∈ weightSpace D.cartan X nu)
    (hs : ∀ j : D.Simple, D.alpha j + nu ∉ support D X)
    (j : D.Simple) : (ι ℂ (D.e j)) • x = 0 := by
  have he := root_smul_weight D X (D.alpha j) nu (D.e j) x (D.triple j).e_mem hx
  have hb : weightSpace D.cartan X (D.alpha j + nu) = ⊥ := not_ne_iff.mp (hs j)
  rw [hb] at he
  exact (Submodule.mem_bot (R := ℂ)).mp he

private theorem topVector_raising (nu : D.Weight) (j : D.Simple) :
    (ι ℂ (D.e j)) • topVector D nu = 0 :=
  raising_eq_zero D (M D nu) nu _ (topVector_weight D nu) (fun i h =>
    no_raised_weight D nu nu (fun h => h.2 rfl) i
      ((verma_mem_O D nu).2.2.2.2.1 _ |>.mp h)) j

private theorem split_of_no_raised_weight (nu lam : D.Weight)
    (h : ¬ (weightLE D nu lam ∧ nu ≠ lam)) (X : O.{u,u} D)
    (i : costandard D lam →ₗ[U g] X.obj) (p : X.obj →ₗ[U g] M D nu)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p) :
    ∃ s : M D nu →ₗ[U g] X.obj, p.comp s = LinearMap.id := by
  let := restrictedLieRingModule (costandard D lam) (g := g)
  let := restrictedLieModule (costandard D lam) (g := g)
  let := restrictedLieRingModule X.obj (g := g)
  let := restrictedLieModule X.obj (g := g)
  let := restrictedLieRingModule (M D nu) (g := g)
  let := restrictedLieModule (M D nu) (g := g)
  have hex (mu : D.Weight) :=
    WeightExactness.shortExact (cartanMap D (ModuleCat.ofHom i))
      (cartanMap D (ModuleCat.ofHom p)) X.property.2.1 hi he hp mu
  obtain ⟨x, hx⟩ := (hex nu).2.2 ⟨topVector D nu, topVector_weight D nu⟩
  have hx' : p (x : X.obj) = topVector D nu := congrArg Subtype.val hx
  -- The raised lift lies in the kernel, whose corresponding weight space vanishes.
  have hk (j : D.Simple) : (ι ℂ (D.e j)) • (x : X.obj) = 0 := by
    let y : weightSpace D.cartan X.obj (D.alpha j + nu) :=
      ⟨_, root_smul_weight D X.obj (D.alpha j) nu (D.e j) x (D.triple j).e_mem x.property⟩
    have hy : onWeight D (ModuleCat.ofHom p) _ y = 0 := by
      apply Subtype.ext
      change p ((ι ℂ (D.e j)) • (x : X.obj)) = 0
      rw [map_smul, hx', topVector_raising D]
    obtain ⟨z, hz⟩ := ((hex (D.alpha j + nu)).2.1 y).mp hy
    have hb : weightSpace D.cartan (costandard D lam) (D.alpha j + nu) = ⊥ :=
      not_ne_iff.mp (fun hn => no_raised_weight D nu lam h j ((costandard_support D _ _).mp hn))
    have hz0 : (z : costandard D lam) = 0 := by
      have hm : (z : costandard D lam) ∈ weightSpace D.cartan (costandard D lam)
          (D.alpha j + nu) := z.property
      rw [hb] at hm
      exact (Submodule.mem_bot (R := ℂ)).mp hm
    have eq : i (z : costandard D lam) = (y : X.obj) := congrArg Subtype.val hz
    rw [hz0, map_zero] at eq
    exact eq.symm
  obtain ⟨s, hs⟩ := exists_verma_map D nu X.obj x x.property hk
  refine ⟨s, hom_ext_top D nu ?_⟩
  change p (s (topVector D nu)) = _
  rw [hs]
  exact hx'

private abbrev transpose {X Y : ModuleCat.{v} (U g)} (f : X →ₗ[U g] Y) :
    dualModule D Y →ₗ[U g] dualModule D X :=
  (dualMap D (ModuleCat.ofHom f)).hom

private theorem transpose_zero {X Y : ModuleCat.{v} (U g)} :
    transpose D (0 : X →ₗ[U g] Y) = 0 := by
  apply LinearMap.ext
  intro l
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change pair D Y l (0 : Y) = 0
  exact map_zero (show Module.Dual ℂ Y from l.val)

private def doubleDualEquiv (X : ModuleCat.{v} (U g)) (hX : objects D X) :
    X ≃ₗ[U g] dualModule D (dualModule D X) :=
  LinearEquiv.ofBijective (evaluation D X hX.2.1)
    (evaluation_bijective D X hX.2.1 (weightBounds D X hX).1)

private theorem evaluation_natural {X Y : ModuleCat.{v} (U g)}
    (hX : objects D X) (hY : objects D Y) (f : X →ₗ[U g] Y) (x : X) :
    transpose D (transpose D f) (doubleDualEquiv D X hX x) =
      doubleDualEquiv D Y hY (f x) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro l
  change pair D (dualModule D Y) (transpose D (transpose D f) (evaluation D X hX.2.1 x)) l =
      pair D (dualModule D Y) (evaluation D Y hY.2.1 (f x)) l
  rw [pair_dualMap, pair_evaluation, pair_evaluation]
  rfl

private theorem transpose_ne_zero {X Y : ModuleCat.{v} (U g)}
    (hX : objects D X) (hY : objects D Y) {f : X →ₗ[U g] Y} (hf : f ≠ 0) :
    transpose D f ≠ 0 := by
  intro hz
  apply hf
  apply LinearMap.ext
  intro x
  apply (doubleDualEquiv D Y hY).injective
  rw [← evaluation_natural D hX hY, hz, transpose_zero]
  simp

private def evalTop (nu lam : D.Weight) :
    (M D nu ⟶ costandard D lam) →ₗ[ℂ] weightSpace D.cartan (costandard D lam) nu where
  toFun f := onWeight D f nu ⟨topVector D nu, topVector_weight D nu⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem evalTop_injective (nu lam : D.Weight) :
    Function.Injective (evalTop D nu lam) := by
  intro f k h
  apply ModuleCat.hom_ext
  exact hom_ext_top D nu (congrArg Subtype.val h)

private theorem le_of_nonzero_hom (nu lam : D.Weight)
    (f : M D nu →ₗ[U g] costandard D lam) (hf : f ≠ 0) : weightLE D nu lam := by
  apply (costandard_support D nu lam).mp
  intro hb
  change weightSpace D.cartan (costandard D lam) nu = ⊥ at hb
  apply hf
  apply hom_ext_top D nu
  have hm : f (topVector D nu) ∈ weightSpace D.cartan (costandard D lam) nu :=
    (evalTop D nu lam (ModuleCat.ofHom f)).property
  rw [hb] at hm
  exact (Submodule.mem_bot (R := ℂ)).mp hm

private theorem eq_of_nonzero_hom (nu lam : D.Weight)
    (f : M D nu →ₗ[U g] costandard D lam) (hf : f ≠ 0) : nu = lam := by
  -- The transpose gives the reverse weight inequality.
  have hn := transpose_ne_zero D (verma_mem_O D nu).1 (costandard_mem_O D lam) hf
  let e := doubleDualEquiv D (M D lam) (verma_mem_O D lam).1
  let k : M D lam →ₗ[U g] costandard D nu := (transpose D f).comp e.toLinearMap
  have hk : k ≠ 0 := by
    intro hz
    apply hn
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact LinearMap.congr_fun hz y
  exact weight_antisymm D (le_of_nonzero_hom D nu lam f hf) (le_of_nonzero_hom D lam nu k hk)

/-- The complex dimension of the Hom space between a Verma and a dual Verma. -/
theorem hom_dimension : HomDimensionType.{u} := by
  intro g _ _ _ D nu lam
  by_cases heq : nu = lam
  · subst lam
    let E := evalTop D nu nu
    have hs : Function.Surjective E := by
      intro x
      have hkill := raising_eq_zero D (costandard D nu) nu x x.property (fun j hj =>
        no_raised_weight D nu nu (fun h => h.2 rfl) j ((costandard_support D _ _).mp hj))
      obtain ⟨f, hf⟩ := exists_verma_map D nu (costandard D nu) x x.property hkill
      exact ⟨ModuleCat.ofHom f, Subtype.ext hf⟩
    let e := LinearEquiv.ofBijective E ⟨evalTop_injective D nu nu, hs⟩
    obtain ⟨q, _⟩ := (dualWeights_spec D (M D nu) (verma_mem_O D nu).1.2.1).2.2 nu
    let : FiniteDimensional ℂ (weightSpace D.cartan (M D nu) nu) :=
      (verma_mem_O D nu).2.2.2.1 nu
    let iso := e.trans q
    refine ⟨FiniteDimensional.of_injective iso.toLinearMap iso.injective, ?_⟩
    rw [iso.finrank_eq, Subspace.dual_finrank_eq, ite_eq_left rfl]
    exact (verma_mem_O D nu).2.2.2.2.2 ▸ finrank_span_singleton (verma_mem_O D nu).2.1
  · have hz (f : M D nu ⟶ costandard D lam) : f = 0 := by
      apply ModuleCat.hom_ext
      by_contra hn
      exact heq (eq_of_nonzero_hom D nu lam f.hom hn)
    let : Subsingleton (M D nu ⟶ costandard D lam) :=
      ⟨fun f k => (hz f).trans (hz k).symm⟩
    exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton, ite_eq_right heq]⟩

private theorem split_in_verma_universe (nu lam : D.Weight) (X : O.{u,u} D)
    (i : costandard D lam →ₗ[U g] X.obj) (p : X.obj →ₗ[U g] M D nu)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p) :
    ∃ s : M D nu →ₗ[U g] X.obj, p.comp s = LinearMap.id := by
  by_cases h : weightLE D nu lam ∧ nu ≠ lam
  · let Y : O.{u,u} D := ⟨dualModule D X.obj, dual_mem_O D X⟩
    let e := doubleDualEquiv D (M D lam) (verma_mem_O D lam).1
    let q : Y.obj →ₗ[U g] M D lam := e.symm.toLinearMap.comp (transpose D i)
    have hd := dual_shortExact D (ModuleCat.ofHom i) (ModuleCat.ofHom p)
      (costandard_mem_O D lam).2.1 X.property.2.1 (verma_mem_O D nu).1.2.1 hi he hp
    have hq : Function.Exact (transpose D p) q :=
      e.symm.postcomp_exact_iff_exact.mpr hd.2.1
    have hswap : ¬ (weightLE D lam nu ∧ lam ≠ nu) :=
      fun hh => h.2 (weight_antisymm D h.1 hh.1)
    obtain ⟨s, hs⟩ := split_of_no_raised_weight D lam nu hswap Y
      (transpose D p) q hd.1 hq (e.symm.surjective.comp hd.2.2)
    have hs' (y : M D lam) : transpose D i (s y) = e y := by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact LinearMap.congr_fun hs y
    -- Transpose the section to obtain a retraction of the original inclusion.
    let eX := doubleDualEquiv D X.obj X.property
    let r : X.obj →ₗ[U g] costandard D lam := (transpose D s).comp eX.toLinearMap
    have hr : r.comp i = LinearMap.id := by
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      change pair D (M D lam) (transpose D s (eX (i c))) y = pair D (M D lam) c y
      rw [pair_dualMap]
      change pair D (dualModule D X.obj) (evaluation D X.obj X.property.2.1 (i c)) (s y) = _
      rw [pair_evaluation]
      have eq := pair_dualMap D (ModuleCat.ofHom i) (s y) c
      change pair D (costandard D lam) (transpose D i (s y)) c =
        pair D X.obj (s y) (i c) at eq
      rw [← eq, hs']
      exact pair_evaluation D (M D lam) (verma_mem_O D lam).1.2.1 y c
    have hret : ∃ r : X.obj →ₗ[U g] costandard D lam, r.comp i = LinearMap.id := ⟨r, hr⟩
    exact ((he.split_tfae hi hp).out 2 1).mp hret
  · exact split_of_no_raised_weight D nu lam h X i p hi he hp

/-- Every short exact sequence in category O with a dual Verma kernel and Verma quotient splits. -/
theorem extension_splits : ExtensionSplittingType.{u,v} := by
  intro g _ _ _ D nu lam X i p hi he hp
  -- Finite generation lets us place the middle module in the universe of the Vermas.
  let : Module.Finite (U g) X.obj := X.property.1
  let : Small.{u} (X.obj : Type v) := Module.Finite.small (U g) (X.obj : Type v)
  let e : Shrink.{u} (X.obj : Type v) ≃ₗ[U g] X.obj :=
    Shrink.linearEquiv (U g) (X.obj : Type v)
  let Y : O.{u,u} D :=
    ⟨ModuleCat.of (U g) (Shrink.{u} (X.obj : Type v)),
      surjective_mem_O D X.property e.symm.toLinearMap e.symm.surjective⟩
  let j : costandard D lam →ₗ[U g] Y.obj := e.symm.toLinearMap.comp i
  let q : Y.obj →ₗ[U g] M D nu := p.comp e.toLinearMap
  have hjq : Function.Exact j q := (e.conj_symm_exact_iff_exact i p).mpr he
  obtain ⟨s, hs⟩ := split_in_verma_universe D nu lam Y j q
    (e.symm.injective.comp hi) hjq (hp.comp e.surjective)
  exact ⟨e.toLinearMap.comp s, by rw [← LinearMap.comp_assoc]; exact hs⟩

end RepTheorySurvey.CategoryO.DualVermaExtensions
