import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.FiniteLength
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.VermaLength
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Category.ModuleCat.Products

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Module UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO
attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.RepTheorySurvey.CategoryO
open Specs.RepTheorySurvey.CategoryO.WeightBounds
open BorelInduction hiding U

open private root_smul_weight from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

section Flag

variable (X : ModuleCat.{v} (U g))
local instance : Module (U D.borel) X := restrictedBorelAction D X
local instance : IsScalarTower ℂ (U D.borel) X := restrictedBorelTower D X

variable {X} {E : Submodule (U D.borel) X} {m : ℕ}
variable (b : Basis (Fin m) ℂ E) (η : Fin m → D.Weight)
variable (hb : ∀ j, (b j : X) ∈ weightSpace D.cartan X (η j))

private abbrev cartanInBorel : D.cartan →ₗ⁅ℂ⁆ D.borel :=
  LieSubalgebra.inclusion (show D.cartan ≤ D.borel from le_sup_left)

private abbrev positiveInBorel : D.nPlus →ₗ⁅ℂ⁆ D.borel :=
  LieSubalgebra.inclusion (show D.nPlus ≤ D.borel from le_sup_right)

private theorem borel_smul_coe (z : D.borel) (y : E) :
    ((ι ℂ z • y : E) : X) = ι ℂ (z : g) • (y : X) := by
  change inclusion D.borel (ι ℂ z) • (y : X) = _
  rw [inclusion_ι]

include hb in
private theorem cartan_basis_action (h : D.cartan) (j : Fin m) :
    ι ℂ (cartanInBorel D h) • b j = η j h • b j := by
  apply Subtype.ext
  rw [borel_smul_coe]
  exact (mem_weightSpace D.cartan X (η j) (b j)).mp (hb j) h

include hb in
private theorem cartan_coord (h : D.cartan) (k : Fin m) (y : E) :
    b.coord k (ι ℂ (cartanInBorel D h) • y) = η k h * b.coord k y := by
  let T : E →ₗ[ℂ] E := Algebra.lsmul ℂ ℂ E (ι ℂ (cartanInBorel D h))
  have hdiag : (b.coord k).comp T = η k h • b.coord k := by
    apply b.ext
    intro j
    change b.coord k (ι ℂ (cartanInBorel D h) • b j) = η k h * b.coord k (b j)
    rw [cartan_basis_action D b η hb, map_smul, smul_eq_mul]
    by_cases hkj : j = k
    · subst j
      rfl
    · simp [hkj]
  exact LinearMap.congr_fun hdiag y

include hb in
private theorem basis_coord_of_weight (y : E) {μ : D.Weight}
    (hy : (y : X) ∈ weightSpace D.cartan X μ) {k : Fin m}
    (hk : b.repr y k ≠ 0) : η k = μ := by
  ext h
  have hy' : ι ℂ (cartanInBorel D h) • y = μ h • y := by
    apply Subtype.ext
    rw [borel_smul_coe]
    exact (mem_weightSpace D.cartan X μ (y : X)).mp hy h
  have he := cartan_coord D b η hb h k y
  rw [hy', map_smul, smul_eq_mul] at he
  exact (mul_right_cancel₀ hk he).symm

private def flagSpace (s : Finset (Fin m)) : Submodule ℂ E :=
  Submodule.span ℂ (b '' (s : Set (Fin m)))

private theorem mem_flagSpace {s : Finset (Fin m)} {y : E} :
    y ∈ flagSpace D b s ↔ ∀ k, b.repr y k ≠ 0 → k ∈ s := by
  rw [flagSpace, b.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff]

private def IsUpper (s : Finset (Fin m)) : Prop :=
  ∀ j ∈ s, ∀ k, D.direction (η j) < D.direction (η k) → k ∈ s

private theorem borel_generators (z : D.borel) :
    ∃ h : D.cartan, ∃ p : D.nPlus, z = cartanInBorel D h + positiveInBorel D p := by
  have hz : (z : g) ∈ D.cartan.toSubmodule ⊔ D.nPlus.toSubmodule :=
    (cartan_borel D).1 ▸ z.property
  obtain ⟨h, hh, p, hp, heq⟩ := Submodule.mem_sup.mp hz
  exact ⟨⟨h, hh⟩, ⟨p, hp⟩, Subtype.ext heq.symm⟩

include hb in
private theorem positive_basis_action
    {s : Finset (Fin m)} {j : Fin m}
    (hs : ∀ k, D.direction (η j) < D.direction (η k) → k ∈ s)
    (p : D.nPlus) :
    (ι ℂ (positiveInBorel D p)) • b j ∈ flagSpace D b s := by
  have hspan : (p : g) ∈
      ⨆ α : {α : D.Weight // 0 < D.direction α}, 
        Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan α.val :=
    (root_parts D).1 ▸ p.property
  let A : U g →ₐ[ℂ] Module.End ℂ X := Algebra.lsmul ℂ ℂ X
  let T : g →ₗ[ℂ] X := (A.toLinearMap.comp (ι ℂ).toLinearMap).flip (b j : X)
  let I : E →ₗ[ℂ] X := E.subtype.restrictScalars ℂ
  have hle : (⨆ α : {α : D.Weight // 0 < D.direction α},
      Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan α.val) ≤
      ((flagSpace D b s).map I).comap T := by
    apply iSup_le
    intro α x hx
    have hxp : x ∈ D.nPlus := by
      change x ∈ D.nPlus.toSubmodule
      rw [(root_parts D).1]
      exact Submodule.mem_iSup_of_mem α hx
    let y : E := (ι ℂ (positiveInBorel D ⟨x, hxp⟩)) • b j
    have hy : (y : X) ∈ weightSpace D.cartan X (α.val + η j) :=
      by
        rw [show (y : X) = ι ℂ x • (b j : X) from borel_smul_coe D _ _]
        exact root_smul_weight D X α.val (η j) x (b j : X) hx (hb j)
    have hyS : y ∈ flagSpace D b s := (mem_flagSpace D b).mpr fun k hk => by
      have he := basis_coord_of_weight D b η hb y hy hk
      apply hs k
      rw [he, map_add]
      exact lt_add_of_pos_left _ α.property
    exact ⟨y, hyS, borel_smul_coe D _ _⟩
  obtain ⟨y, hy, he⟩ := hle hspan
  have hye : y = (ι ℂ (positiveInBorel D p)) • b j :=
    Subtype.ext (he.trans (borel_smul_coe D (positiveInBorel D p) (b j)).symm)
  exact hye ▸ hy

include hb in
private theorem smul_mem_flagSpace
    {s : Finset (Fin m)} (hs : IsUpper D η s) (a : U D.borel)
    (y : E) (hy : y ∈ flagSpace D b s) : a • y ∈ flagSpace D b s := by
  induction a using Shared.Lie.enveloping_induction ℂ D.borel generalizing y with
  | scalar c =>
    rw [algebraMap_smul]
    exact (flagSpace D b s).smul_mem c hy
  | generator z =>
    rw [Shared.Lie.inclusion]
    obtain ⟨h, p, rfl⟩ := borel_generators D z
    let T : E →ₗ[ℂ] E := Algebra.lsmul ℂ ℂ E (ι ℂ (cartanInBorel D h + positiveInBorel D p))
    have hle : flagSpace D b s ≤ (flagSpace D b s).comap T := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      change (ι ℂ (cartanInBorel D h + positiveInBorel D p)) • b j ∈ flagSpace D b s
      rw [map_add, add_smul]
      rw [cartan_basis_action D b η hb]
      exact (flagSpace D b s).add_mem ((flagSpace D b s).smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩))
        (positive_basis_action D b η hb (hs j hj) p)
    exact hle hy
  | add a a' ha ha' =>
    rw [add_smul]
    exact (flagSpace D b s).add_mem (ha y hy) (ha' y hy)
  | mul a a' ha ha' =>
    rw [mul_smul]
    exact ha _ (ha' y hy)

include hb in
private def flagSubmodule (s : Finset (Fin m)) (hs : IsUpper D η s) : Submodule (U D.borel) E :=
  { flagSpace D b s with
    smul_mem' := fun a _ hy => smul_mem_flagSpace D b η hb hs a _ hy }

include hb in
/-- The coordinate of a lowest remaining basis vector is a Borel-module map
onto its one-dimensional weight character. -/
private def flagProjection {s : Finset (Fin m)} (hs : IsUpper D η s) {i : Fin m}
    (hmin : ∀ j ∈ s, D.direction (η i) ≤ D.direction (η j)) :
    letI := weightModule_value D.cartan D.direction (character D (η i))
    flagSubmodule D b η hb s hs →ₗ[U D.borel] ℂ := by
  letI := weightModule_value D.cartan D.direction (character D (η i))
  let χ := character D (η i)
  change flagSubmodule D b η hb s hs →ₗ[U D.borel] ℂ
  let c := b.coord i
  have hpos (p : D.nPlus) :
      ∀ y ∈ flagSpace D b s, c (ι ℂ (positiveInBorel D p) • y) = 0 := by
    let T : E →ₗ[ℂ] E := Algebra.lsmul ℂ ℂ E (ι ℂ (positiveInBorel D p))
    suffices hle : flagSpace D b s ≤ (c.comp T).ker from fun _ hy => hle hy
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    have hp : ι ℂ (positiveInBorel D p) • b j ∈ flagSpace D b (s.erase i) :=
      positive_basis_action D b η hb (fun k hk =>
        Finset.mem_erase.mpr ⟨fun e => hk.not_ge (e ▸ hmin j hj), hs j hj k hk⟩) p
    change b.repr (ι ℂ (positiveInBorel D p) • b j) i = 0
    by_contra hi
    exact Finset.notMem_erase i s ((mem_flagSpace D b).mp hp i hi)
  have hχ : IsWeightCharacter D.cartan D.direction (η i) χ := (character_unique D (η i)).1
  have equivariant (a : U D.borel) (y : flagSubmodule D b η hb s hs) :
      c ((a • y : flagSubmodule D b η hb s hs) : E) = χ a * c y := by
    induction a using Shared.Lie.enveloping_induction ℂ D.borel generalizing y with
    | scalar r =>
      change c ((algebraMap ℂ (U D.borel) r) • (y : E)) = χ (algebraMap ℂ (U D.borel) r) * c y
      rw [algebraMap_smul, map_smul, AlgHom.commutes, Algebra.algebraMap_self_apply, smul_eq_mul]
    | generator z =>
      rw [Shared.Lie.inclusion]
      obtain ⟨h, p, rfl⟩ := borel_generators D z
      change c (ι ℂ (cartanInBorel D h + positiveInBorel D p) • (y : E)) =
        χ (ι ℂ (cartanInBorel D h + positiveInBorel D p)) * c y
      rw [map_add (ι ℂ), add_smul, map_add c, map_add χ,
        cartan_coord D b η hb, hpos p y y.property,
        hχ.1 h, hχ.2 p, add_zero, add_zero]
    | add a a' ha ha' =>
      rw [add_smul, Submodule.coe_add, map_add c, ha, ha', map_add χ, add_mul]
    | mul a a' ha ha' =>
      rw [mul_smul, ha, ha', map_mul χ, mul_assoc]
  exact
    { toFun := fun y => c y
      map_add' := fun y z => c.map_add (y : E) (z : E)
      map_smul' := equivariant }

private theorem finiteLength_of_exact {R : Type*} [Ring R] {V W Z : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (f : V →ₗ[R] W) (q : W →ₗ[R] Z)
    (h : Function.Exact f q) (hV : IsFiniteLength R V) (hZ : IsFiniteLength R Z) :
    IsFiniteLength R W := by
  obtain ⟨hVn, hVa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hV
  obtain ⟨hZn, hZa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hZ
  have hker := (LinearMap.exact_iff.mp h).symm
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_range_eq_ker f q hker, isArtinian_of_range_eq_ker f q hker⟩

include hb in
private theorem flag_induction_finiteLength (s : Finset (Fin m)) (hs : IsUpper D η s) :
    IsFiniteLength (U g) (Induced (inclusion D.borel) (flagSubmodule D b η hb s hs)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases h : s.Nonempty
    · obtain ⟨i, hi, hmin⟩ := s.exists_min_image (D.direction ∘ η) h
      have ht : IsUpper D η (s.erase i) := fun j hj k hk =>
        Finset.mem_erase.mpr ⟨fun e => hk.not_ge (e ▸ hmin j (Finset.mem_of_mem_erase hj)),
          hs j (Finset.mem_of_mem_erase hj) k hk⟩
      let S := flagSubmodule D b η hb s hs
      let T := flagSubmodule D b η hb (s.erase i) ht
      have hTS : T ≤ S := Submodule.span_mono (Set.image_mono (Finset.erase_subset i s))
      let f : T →ₗ[U D.borel] S := Submodule.inclusion hTS
      let := weightModule_value D.cartan D.direction (character D (η i))
      let : IsScalarTower ℂ (U D.borel) ℂ := IsScalarTower.of_algebraMap_smul
        (fun r z => by
          change character D (η i) (algebraMap ℂ (U D.borel) r) * z = r * z
          rw [AlgHom.commutes, Algebra.algebraMap_self_apply])
      let q : S →ₗ[U D.borel] ℂ := flagProjection D b η hb hs hmin
      have hq : Function.Surjective q := by
        let y : S := ⟨b i, Submodule.subset_span ⟨i, hi, rfl⟩⟩
        have he : q y = 1 := by change b.coord i (b i) = 1; simp
        intro c
        refine ⟨c • y, ?_⟩
        rw [q.map_smul_of_tower, he, smul_eq_mul, mul_one]
      have he : Function.Exact f q := by
        intro y
        change b.repr (y : E) i = 0 ↔ y ∈ Set.range f
        constructor
        · intro hy
          have hyT : (y : E) ∈ T := (mem_flagSpace D b).mpr fun k hk =>
            Finset.mem_erase.mpr ⟨fun e => hk (e.symm ▸ hy),
              (mem_flagSpace D b).mp y.property k hk⟩
          exact ⟨⟨y, hyT⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          by_contra hn
          exact Finset.notMem_erase i s ((mem_flagSpace D b).mp y.property i hn)
      obtain ⟨_, hex, _⟩ := exactInduction D.nMinus D.borel T
        (cartan_borel D).2.2 f q (mapInduced (inclusion D.borel) f) (mapInduced (inclusion D.borel) q)
        (mapInduced_tensor _ f) (mapInduced_tensor _ q) (Submodule.inclusion_injective hTS) he hq
      obtain ⟨F, _⟩ := finiteVerma D.cartan D.direction (character D (η i))
      exact finiteLength_of_exact _ _ hex (ih (s.erase i) (Finset.erase_ssubset hi) ht)
        (F.symm.isFiniteLength (verma_finite_length D (η i)))
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst s
      let S := flagSubmodule D b η hb ∅ hs
      have hS : S = ⊥ := by
        ext y
        change y ∈ flagSpace D b ∅ ↔ y ∈ (⊥ : Submodule (U D.borel) E)
        simp [flagSpace]
      rw [show flagSubmodule D b η hb ∅ hs = ⊥ from hS]
      exact .of_subsingleton

include hb in
private theorem induced_finiteLength : IsFiniteLength (U g) (Induced (inclusion D.borel) E) := by
  let hs : IsUpper D η Finset.univ := fun _ _ _ _ => Finset.mem_univ _
  let S := flagSubmodule D b η hb Finset.univ hs
  have hS : S = ⊤ := by
    ext y
    change y ∈ flagSpace D b Finset.univ ↔ y ∈ (⊤ : Submodule (U D.borel) E)
    simp [mem_flagSpace]
  have hlen := flag_induction_finiteLength D b η hb Finset.univ hs
  apply hlen.of_surjective (f := mapInduced (inclusion D.borel) S.subtype)
  have hsub : Surjective S.subtype := fun y => ⟨⟨y, hS ▸ Submodule.mem_top⟩, rfl⟩
  intro z
  obtain ⟨z, rfl⟩ := (balance (inclusion D.borel) E).mkQ_surjective z
  induction z using TensorProduct.inductionOn with
  | tmul a y =>
    obtain ⟨y, rfl⟩ := hsub y
    exact ⟨induceTensor (inclusion D.borel) a y, mapInduced_tensor _ _ _ _⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

end Flag

theorem categoryO_finiteLength : CategoryOFiniteLengthType.{u, v} := by
  intro g _ _ _ D X
  obtain ⟨_, _, _, E, _, _, _, _, ⟨m, b, η, hb⟩, q, hq, _⟩ :=
    generatingBorelModule D X.obj X.property
  exact (induced_finiteLength D b η hb).of_surjective hq

section Abelian

open private submodule_mem_O surjective_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects

instance objects_closedUnderSubobjects : (objects.{u, v} D).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    have hf := (ModuleCat.mono_iff_injective f).mp inferInstance
    let S := f.hom.range
    have : IsNoetherian (U g) Y :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D ⟨Y, hY⟩)).1
    have hS := submodule_mem_O D Y hY S (IsNoetherian.noetherian S)
    let e : X ≃ₗ[U g] S := LinearEquiv.ofInjective f.hom hf
    exact surjective_mem_O D hS e.symm.toLinearMap e.symm.surjective

instance objects_closedUnderQuotients : (objects.{u, v} D).IsClosedUnderQuotients where
  prop_of_epi f _ hX := surjective_mem_O D hX f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

private theorem product_mem_O {J : Type} [Finite J] (X : J → ModuleCat.{v} (U g))
    (hX : ∀ j, objects D (X j)) :
    objects D (ModuleCat.of (U g) (∀ j, X j)) := by
  classical
  let := Fintype.ofFinite J
  let Y := ModuleCat.of (U g) (∀ j, X j)
  let W := weightSpace D.cartan Y
  have (j : J) : Module.Finite (U g) (X j) := (hX j).1
  refine ⟨inferInstanceAs (Module.Finite (U g) (∀ j, X j)), ?_, ?_⟩
  · let := restrictedLieRingModule Y (g := g)
    let := restrictedLieModule Y (g := g)
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact WeightExactness.weightSpaces_independent (H := D.cartan) (X := Y)
    · let ins (j : J) : X j →ₗ[ℂ] Y := LinearMap.single ℂ (fun j => X j) j
      have hw (j : J) (μ : D.Weight) :
          (weightSpace D.cartan (X j) μ).map (ins j) ≤ W μ := by
        rintro _ ⟨x, hx, rfl⟩
        apply (mem_weightSpace D.cartan Y μ (ins j x)).mpr
        intro h
        funext k
        change (ι ℂ (h : g)) • Pi.single (M := fun j => ↥(X j)) j x k =
          μ h • Pi.single (M := fun j => ↥(X j)) j x k
        by_cases he : k = j
        · subst k
          simpa only [Pi.single_eq_same] using (mem_weightSpace D.cartan (X j) μ x).mp hx h
        · simp only [Pi.single_eq_of_ne he, smul_zero]
      have hins (j : J) : LinearMap.range (ins j) ≤ ⨆ μ, W μ := by
        rw [← Submodule.map_top, ← (hX j).2.1.submodule_iSup_eq_top, Submodule.map_iSup]
        exact iSup_mono (hw j)
      apply top_unique
      intro y _
      have hsum : (∑ j, ins j (y j)) = y :=
        LinearMap.sum_single_apply (φ := fun j => X j) y
      rw [← hsum]
      exact Submodule.sum_mem _ (fun j _ => hins j ⟨y j, rfl⟩)
  · intro y
    let P := orbit D.nPlus Y y
    let Q (j : J) := orbit D.nPlus (X j) (y j)
    have (j : J) : FiniteDimensional ℂ (Q j) := (hX j).2.2 (y j)
    let i (j : J) : P →ₗ[ℂ] Q j :=
      (LinearMap.proj j : Y →ₗ[ℂ] X j).restrict (p := P) (q := Q j) (by
        intro z hz
        obtain ⟨a, ha⟩ := (mem_orbit D.nPlus Y y z).mp hz
        exact (mem_orbit D.nPlus (X j) (y j) (z j)).mpr ⟨a, congrFun ha j⟩)
    apply FiniteDimensional.of_injective (LinearMap.pi i)
    intro z z' h
    apply Subtype.ext
    funext j
    exact congrArg (fun f : ∀ j, Q j => (f j : X j)) h

private instance objects_closedUnderFiniteProducts : (objects.{u, v} D).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro Y ⟨p⟩
    let X : J → ModuleCat.{v} (U g) := fun j => p.diag.obj ⟨j⟩
    let e : p.diag ≅ Discrete.functor X := Discrete.natIsoFunctor
    have hlim := (IsLimit.postcomposeHomEquiv e p.cone).symm p.isLimit
    let i := IsLimit.conePointUniqueUpToIso (ModuleCat.productConeIsLimit X) hlim
    exact (objects D).prop_of_iso i (product_mem_O D X fun j => p.prop_diag_obj ⟨j⟩)⟩

private instance objects_containsZero : (objects.{u, v} D).ContainsZero where
  exists_zero := by
    let X : PEmpty → ModuleCat.{v} (U g) := PEmpty.elim
    exact ⟨_, ModuleCat.isZero_of_subsingleton _, product_mem_O D X (fun j => nomatch j)⟩

/-- The category inherits its abelian structure from left enveloping modules. -/
noncomputable instance categoryOAbelian : Abelian (O.{u, v} D) :=
  inferInstanceAs (Abelian (objects.{u, v} D).FullSubcategory)

theorem categoryO_abelian : CategoryOAbelianType.{u, v} := by
  intro g _ _ _ D
  refine ⟨⟨categoryOAbelian D, rfl⟩, fun {X Y} f => ?_⟩
  exact ⟨⟨(objects D).createsKernels f⟩, ⟨(objects D).createsCokernels f⟩⟩

end Abelian

theorem categoryO_theorem : CategoryOTheoremType.{u, v} :=
  ⟨weightBounds, categoryO_abelian, categoryO_finiteLength,
    simpleQuotient_in_O, simpleQuotient_equiv_iff, simpleClassification⟩

end RepTheorySurvey.CategoryO
