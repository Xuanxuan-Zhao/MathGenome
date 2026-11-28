import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SingularCochainSheaves
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology Filter
open TopCat.Presheaf
open P202Specs.SingularChains P202Specs.CohomologyPairs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

namespace RepTheorySurvey.Geometric.SingularCochainSheaves

open Analytic Analytic.SingularCochains

abbrev ordinaryPresheafComplex : Expected.PresheafComplexType.{u} := presheafComplex
abbrev ordinarySheafComplex : Expected.SheafComplexType.{u} := sheafComplex
abbrev augmentedCochainPresheafComplex : Expected.PresheafComplexType.{u} :=
  augmentedPresheafComplex
abbrev augmentedCochainSheafComplex : Expected.SheafComplexType.{u} :=
  augmentedSheafComplex

private abbrev presheaf (X : TopCat.{u}) (q : ℕ) := (presheafComplex X).X (q : ℤ)
private abbrev sheaf (X : TopCat.{u}) (q : ℕ) := (sheafComplex X).X (q : ℤ)

private def simplexInclusion {X : TopCat.{u}} {U V : Opens X} {q : ℕ}
    (s : SimplexIn U q) (h : ∀ t, (s t).val ∈ V) : SimplexIn V q :=
  ⟨fun t => ⟨(s t).val, h t⟩,
    (continuous_subtype_val.comp s.continuous).subtype_mk _⟩

abbrev cochainCoordinates : Expected.CoordinatesType.{u} := @coordinates
abbrev sheafificationUnit : Expected.ComplexUnitType.{u} := complexUnit
abbrev cochainToSections : Expected.SectionMapType.{u} := @sectionMap
abbrev rationalAugmentation : Expected.AugmentationType.{u} :=
  Analytic.SingularCochains.augmentation

theorem coordinates_restrict {X : TopCat.{u}} {V U : Opens X} (q : ℕ)
    (i : V ⟶ U) (c : (presheaf X q).obj (op U)) (s : SimplexIn V q) :
    coordinates V q ((presheaf X q).map i.op c) s = coordinates U q c (includeSimplex i s) := by
  let f := (Opens.toTopCat X).map i
  let a := (ordinaryNonnegativeIso ℚ ℚ (TopCat.of V) q).inv
  let b := (ordinaryNonnegativeIso ℚ ℚ (TopCat.of U) q).inv
  let t := (simplexEquiv (TopCat.of V) q).symm s
  let t' : Simplex (TopCat.of U) q := (TopCat.toSSet.map f).app (op (SimplexCategory.mk q)) t
  have ht' : (simplexEquiv (TopCat.of U) q).symm (includeSimplex i s) = t' := by
    apply (simplexEquiv (TopCat.of U) q).injective
    rw [Equiv.apply_symm_apply]
    symm
    calc
      _ = f.hom.comp (simplexEquiv (TopCat.of V) q t) :=
        P202.SingularChains.simplexEquiv_postcomp f q t
      _ = includeSimplex i s := by
        dsimp only [t, includeSimplex]
        rw [Equiv.apply_symm_apply]
  have natural :
      a ≫ ((ordinaryFunctor ℚ ℚ).map f).f (q : ℤ) =
        (chainMap ℚ ℚ f).f q ≫ b := by
    change _ ≫ (HomologicalComplex.extendMap (chainMap ℚ ℚ f) (degreeEmbedding 0)).f (q : ℤ) = _
    rw [HomologicalComplex.extendMap_f _ _ (i := q)
      (show (degreeEmbedding 0).f q = (q : ℤ) by simp [degreeEmbedding])]
    change a ≫ (ordinaryNonnegativeIso ℚ ℚ (TopCat.of V) q).hom ≫
      (chainMap ℚ ℚ f).f q ≫ b = _
    rw [show a = (ordinaryNonnegativeIso ℚ ℚ (TopCat.of V) q).inv from rfl,
      Iso.inv_hom_id_assoc]
  let c' : (ordinaryComplex ℚ ℚ (TopCat.of U)).X (q : ℤ) →ₗ[ℚ] Values.{u} := c
  change c' (((ordinaryFunctor ℚ ℚ).map f).f (q : ℤ) (a (Finsupp.single t 1))) = _
  rw [show coordinates U q c (includeSimplex i s) = c' (b (Finsupp.single t' 1)) by
    change c' (b (Finsupp.single _ 1)) = _
    rw [ht']
    rfl]
  have h := congrArg (fun m => m (Finsupp.single t (1 : ℚ))) natural
  change ((ordinaryFunctor ℚ ℚ).map f).f (q : ℤ) (a (Finsupp.single t 1)) =
    b ((chainMap ℚ ℚ f).f q (Finsupp.single t 1)) at h
  rw [h]
  congr 2
  exact P202.SingularChains.chainMap_single ℚ ℚ f q t 1

private theorem cochains_restrict_surjective {X : TopCat.{u}} {V U : Opens X} (q : ℕ)
    (i : V ⟶ U) : Function.Surjective ((presheaf X q).map i.op) := by
  classical
  intro c
  let values (s : SimplexIn U q) : Values.{u} :=
    if h : ∀ t, (s t).val ∈ V then coordinates V q c (simplexInclusion s h) else 0
  refine ⟨(coordinates U q).symm values, (coordinates V q).injective ?_⟩
  funext s
  rw [coordinates_restrict, LinearEquiv.apply_symm_apply]
  have h : ∀ t, ((includeSimplex i s) t).val ∈ V := fun t => (s t).property
  rw [show values (includeSimplex i s) = coordinates V q c
      (simplexInclusion (includeSimplex i s) h) by exact dite_eq_left h]
  congr 1

private theorem unit_locally_surjective (X : TopCat.{u}) (q : ℕ) :
    TopCat.Presheaf.IsLocallySurjective (unit X (q : ℤ)) := by
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2
  intro x
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Coeff.{u} (presheaf X q)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

private theorem agree_near_point {X : TopCat.{u}} (q : ℕ) {O V : Opens X}
    {x : X} (hx : x ∈ O) (hx' : x ∈ V)
    (a : (presheaf X q).obj (op O)) (b : (presheaf X q).obj (op V))
    (h : (sheaf X q).presheaf.germ O x hx ((unit X (q : ℤ)).app (op O) a) =
      (sheaf X q).presheaf.germ V x hx' ((unit X (q : ℤ)).app (op V) b)) :
    ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ O) (j : W ⟶ V),
      (presheaf X q).map i.op a = (presheaf X q).map j.op b := by
  apply TopCat.Presheaf.germ_eq (X := X) (presheaf X q) x hx hx' a b
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Coeff.{u} (presheaf X q)
  apply (ModuleCat.mono_iff_injective ((TopCat.Presheaf.stalkFunctor Coeff.{u} x).map
    (unit X (q : ℤ)))).mp inferInstance
  simpa only [TopCat.Presheaf.stalkFunctor_map_germ_apply] using h

private theorem patchCochain {X : TopCat.{u}} [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] (U : Opens X) (q : ℕ)
    (s : (sheaf X q).obj.obj (op U)) :
    ∃ c : (presheaf X q).obj (op U), (unit X (q : ℤ)).app (op U) c = s := by
  classical
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have localRep := (TopCat.Presheaf.isLocallySurjective_iff (unit X (q : ℤ))).mp
    (unit_locally_surjective X q) U s
  have hRep (x : U) : ∃ (V : Opens X) (hVU : V ≤ U) (c : (presheaf X q).obj (op V)),
      x.val ∈ V ∧ (unit X (q : ℤ)).app (op V) c =
        (sheaf X q).obj.map (homOfLE hVU).op s := by
    obtain ⟨V, hVU, ⟨c, hc⟩, hx⟩ := localRep x.val x.property
    exact ⟨V, hVU, c, hx, hc⟩
  choose V hVU c hxV hc using hRep
  let v (x : U) : Set U := Subtype.val ⁻¹' (V x : Set X)
  have hvOpen (x : U) : IsOpen (v x) := (V x).isOpen.preimage continuous_subtype_val
  have small (x : U) : ∃ B : Set U, (x ∈ B ∧ IsOpen B) ∧ closure B ⊆ v x :=
    (hasBasis_opens_closure x).mem_iff.mp ((hvOpen x).mem_nhds (hxV x))
  choose B hB hBv using small
  obtain ⟨W, hWo, hWcover, hWfinite, hWB⟩ := precise_refinement B
    (fun x => (hB x).2) (Set.iUnion_eq_univ_iff.mpr fun x => ⟨x, (hB x).1⟩)
  have hWV (i : U) : closure (W i) ⊆ v i := (closure_mono (hWB i)).trans (hBv i)
  let smallSimplex (t : SimplexIn U q) (i : U) : Prop := ∀ z, t z ∈ W i
  let value (t : SimplexIn U q) : Values.{u} :=
    if h : ∃ i, smallSimplex t i then
      coordinates (V h.choose) q (c h.choose)
        (simplexInclusion t (fun z => hWV h.choose (subset_closure (h.choose_spec z))))
    else 0
  let global := (coordinates U q).symm value
  refine ⟨global, TopCat.Presheaf.section_ext (sheaf X q) U _ _ (fun x hx => ?_)⟩
  let y : U := ⟨x, hx⟩
  obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hWcover y
  have hjV : x ∈ V j := hWV j (subset_closure hj)
  have hGerm (i : U) (hi : x ∈ V i) :
      (sheaf X q).presheaf.germ (V i) x hi ((unit X (q : ℤ)).app (op (V i)) (c i)) =
        (sheaf X q).presheaf.germ U x hx s := by
    rw [hc i]
    exact TopCat.Presheaf.germ_res_apply (sheaf X q).presheaf (homOfLE (hVU i)) x hi s
  let I : Set U := {i | y ∈ closure (W i)}
  have hI : I.Finite := hWfinite.closure.point_finite y
  have hAgree (i : I) :
      ∃ (A : Opens X) (_ : x ∈ A) (li : A ⟶ V i.val) (lj : A ⟶ V j),
        (presheaf X q).map li.op (c i.val) = (presheaf X q).map lj.op (c j) := by
    have hiV : x ∈ V i.val := hWV i.val i.property
    exact agree_near_point q hiV hjV (c i.val) (c j) ((hGerm i.val hiV).trans (hGerm j hjV).symm)
  choose A hxA li lj hA using hAgree
  have hEach (i : I) : Subtype.val ⁻¹' (A i : Set X) ∈ 𝓝 y :=
    ((A i).isOpen.preimage continuous_subtype_val).mem_nhds (hxA i)
  have hAll : (⋂ i : I, Subtype.val ⁻¹' (A i : Set X)) ∈ 𝓝 y := by
    letI : Finite I := hI
    exact Filter.iInter_mem.mpr hEach
  have hAvoid := hWfinite.closure.iInter_compl_mem_nhds (fun _ => isClosed_closure) y
  obtain ⟨N, ⟨hyN, hNo⟩, hN⟩ := (nhds_basis_opens y).mem_iff.mp
    (inter_mem (inter_mem ((hWo j).mem_nhds hj) hAvoid) hAll)
  let H : Opens X := U.isOpenEmbedding.functor.obj (⟨N, hNo⟩ : Opens (TopCat.of U))
  have hxH : x ∈ H := ⟨y, hyN, rfl⟩
  have hHU : H ≤ U := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  let iHU : H ⟶ U := homOfLE hHU
  have hNof (z : H) : iHU z ∈ N := by
    obtain ⟨w, hw, he⟩ := z.property
    have eq : iHU z = w := Subtype.ext he.symm
    exact eq ▸ hw
  have hHVj : H ≤ V j := fun z hz => hWV j (subset_closure (hN (hNof ⟨z, hz⟩)).1.1)
  let iHVj : H ⟶ V j := homOfLE hHVj
  have hlocal :
      (presheaf X q).map iHU.op global = (presheaf X q).map iHVj.op (c j) := by
    apply (coordinates H q).injective
    funext t
    rw [coordinates_restrict, coordinates_restrict]
    have ht (z : _) : (includeSimplex iHU t) z ∈ N := hNof (t z)
    have hsmall : ∃ i, smallSimplex (includeSimplex iHU t) i :=
      ⟨j, fun z => (hN (ht z)).1.1⟩
    let i := hsmall.choose
    have hi : i ∈ I := by
      by_contra hi
      let z : Convexity.StdSimplex ℝ (Fin (q + 1)) := Classical.choice inferInstance
      have hz := (hN (ht z)).1.2
      have hbad := Set.mem_iInter₂.mp hz i hi
      exact hbad (subset_closure (hsmall.choose_spec z))
    let k : I := ⟨i, hi⟩
    have hk : H ≤ A k := fun z hz => Set.mem_iInter.mp (hN (hNof ⟨z, hz⟩)).2 k
    let ik : H ⟶ A k := homOfLE hk
    have hcompare := congrArg (fun a => coordinates (A k) q a (includeSimplex ik t)) (hA k)
    rw [coordinates_restrict, coordinates_restrict] at hcompare
    rw [show coordinates U q global = value from (coordinates U q).apply_symm_apply value]
    unfold value
    rw [dite_eq_left hsmall]
    change coordinates (V i) q (c i) _ = coordinates (V j) q (c j) _
    convert hcompare using 2 <;> apply ContinuousMap.ext <;> intro z <;> rfl
  have hunit := congrArg (fun c => (unit X (q : ℤ)).app (op H) c) hlocal
  have nat (O : Opens X) (f : H ⟶ O) (a : (presheaf X q).obj (op O)) :
      (unit X (q : ℤ)).app (op H) ((presheaf X q).map f.op a) =
        (sheaf X q).obj.map f.op ((unit X (q : ℤ)).app (op O) a) :=
    congrArg (fun m => m a) ((unit X (q : ℤ)).naturality f.op)
  rw [nat U iHU, nat (V j) iHVj, hc j] at hunit
  apply Eq.trans (TopCat.Presheaf.germ_res_apply (sheaf X q).presheaf iHU x hxH _).symm
  rw [hunit]
  rw [← TopCat.Presheaf.germ_res_apply (sheaf X q).presheaf (homOfLE (hVU j)) x hjV s]
  exact TopCat.Presheaf.germ_res_apply (sheaf X q).presheaf iHVj x hxH _

theorem sectionSurjective : Expected.SectionSurjectivity.{u} := by
  intro X _ _ _ U q
  exact patchCochain U q

theorem flabby : Expected.Flabbiness.{u} := by
  intro X _ _ _ q
  constructor
  intro U V i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨a, rfl⟩ := sectionSurjective X V.unop q s
  obtain ⟨b, hb⟩ := cochains_restrict_surjective q i.unop a
  use (unit X (q : ℤ)).app U b
  exact (congrArg (fun m => m b) ((unit X (q : ℤ)).naturality i)).symm.trans
    (congrArg (fun c => (unit X (q : ℤ)).app V c) hb)

private theorem dualExact (S : ShortComplex Coeff.{u}) (hS : S.Exact) :
    (S.op.map (dualFunctor ℚ Values.{u})).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  let a' : S.X₂ →ₗ[ℚ] Values.{u} := a
  change a'.comp S.f.hom = 0 at ha
  have hker : LinearMap.ker S.g.hom ≤ LinearMap.ker a' := by
    intro x hx
    obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff.mp hS) x hx
    change a' x = 0
    rw [← hy]
    exact LinearMap.congr_fun ha y
  let b := ((LinearMap.ker S.g.hom).liftQ a' hker).comp
    S.g.hom.quotKerEquivRange.symm.toLinearMap
  obtain ⟨c, hc⟩ := b.exists_extend
  refine ⟨c, ?_⟩
  change c.comp S.g.hom = a'
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun hc
    ⟨S.g.hom x, LinearMap.mem_range_self S.g.hom x⟩
  change c (S.g.hom x) =
    (LinearMap.ker S.g.hom).liftQ a' hker
      (S.g.hom.quotKerEquivRange.symm ⟨S.g.hom x, _⟩) at he
  rw [LinearMap.quotKerEquivRange_symm_apply_image] at he
  exact he

private theorem exact_augmented_on_contractible (X : TopCat.{u}) (U : Opens X)
    (hU : Nonempty U) (hC : ContractibleSpace U) (i : ℤ) :
    (((augmentedPresheafComplex X).sc' (i - 1) i (i + 1)).map
      ((evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op U))).Exact := by
  let K := reducedComplex ℚ ℚ (TopCat.of U)
  have hK : K.ExactAt i := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (P202.PrismHomotopy.contractible ℚ ℚ (TopCat.of U) i)
  have h' : (K.sc' (i + 1) i (i - 1)).Exact := by
    exact (HomologicalComplex.exactAt_iff' K _ _ _
      (ComplexShape.prev_eq' _ (show i + 1 = i + 1 from rfl))
      (ComplexShape.next_eq' _ (show i - 1 + 1 = i by omega))).mp hK
  exact dualExact _ h'

private abbrev presheafStalk {X : TopCat.{u}} (x : X) :
    ((Opens X)ᵒᵖ ⥤ Coeff.{u}) ⥤ Coeff.{u} :=
  TopCat.Presheaf.stalkFunctor Coeff.{u} x

private instance {X : TopCat.{u}} (x : X) : (presheafStalk x).PreservesZeroMorphisms :=
  inferInstanceAs ((TopCat.Presheaf.stalkFunctor Coeff.{u} x).PreservesZeroMorphisms)

private theorem stalk_exact_of_basis {X : TopCat.{u}} {S : ShortComplex ((Opens X)ᵒᵖ ⥤ Coeff.{u})}
    (x : X) (basis : ∀ U : Opens X, x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧
      (S.map ((evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op V))).Exact) :
    (S.map (presheafStalk x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  obtain ⟨U, hxU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := X) S.X₂ a
  change (TopCat.Presheaf.stalkFunctor Coeff.{u} x).map S.g (TopCat.Presheaf.germ (X := X) S.X₂ U x hxU b) = 0 at ha
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  have he : TopCat.Presheaf.germ (X := X) S.X₃ U x hxU (S.g.app (op U) b) = TopCat.Presheaf.germ (X := X) S.X₃ U x hxU 0 := by
    simpa only [map_zero] using ha
  obtain ⟨W, hxW, j, _, hz⟩ := TopCat.Presheaf.germ_eq (X := X) S.X₃ x hxU hxU _ _ he
  obtain ⟨V, hxV, hVW, hV⟩ := basis W hxW
  let k : V ⟶ W := homOfLE hVW
  let b' := S.X₂.map (k ≫ j).op b
  have hz' : S.g.app (op V) b' = 0 := by
    change S.g.app (op V) (S.X₂.map (k ≫ j).op b) = _
    have hn := congrArg (fun f => f b) (S.g.naturality (k ≫ j).op)
    change S.g.app (op V) (S.X₂.map (k ≫ j).op b) =
      S.X₃.map (k ≫ j).op (S.g.app (op U) b) at hn
    rw [hn, op_comp, Functor.map_comp_apply, hz, map_zero, map_zero]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp hV b' hz'
  change S.f.app (op V) c = b' at hc
  refine ⟨TopCat.Presheaf.germ (X := X) S.X₁ V x hxV c, ?_⟩
  change (TopCat.Presheaf.stalkFunctor Coeff.{u} x).map S.f (TopCat.Presheaf.germ (X := X) S.X₁ V x hxV c) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hc]
  exact TopCat.Presheaf.germ_res_apply S.X₂ (k ≫ j) x hxV b

private theorem sheafify_exact_of_basis {X : TopCat.{u}}
    (S : ShortComplex ((Opens X)ᵒᵖ ⥤ Coeff.{u}))
    (basis : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧
      (S.map ((evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op V))).Exact) :
    (S.map (presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u})).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let st := TopCat.Presheaf.stalkFunctor Coeff.{u} x
  let e (P : X.Presheaf Coeff.{u}) :
      st.obj P ≅ st.obj (sheafify (Opens.grothendieckTopology X) P) :=
    letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Coeff.{u} P
    asIso (st.map (toSheafify (Opens.grothendieckTopology X) P))
  have natural {P Q : X.Presheaf Coeff.{u}} (f : P ⟶ Q) :
      (e P).hom ≫ st.map (sheafifyMap (Opens.grothendieckTopology X) f) =
        st.map f ≫ (e Q).hom := by
    change st.map _ ≫ st.map _ = st.map _ ≫ st.map _
    rw [← Functor.map_comp, ← Functor.map_comp, toSheafify_naturality]
  exact ShortComplex.exact_of_iso
    (ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃) (natural S.f) (natural S.g))
    (stalk_exact_of_basis x (basis x))

theorem augmentedExact : Expected.AugmentedExactness.{u} := by
  intro X hX i
  apply (HomologicalComplex.exactAt_iff' _ (i := i - 1) (j := i) (k := i + 1) ?_ ?_).mpr
  · change (((augmentedPresheafComplex X).sc' (i - 1) i (i + 1)).map
      (presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u})).Exact
    apply sheafify_exact_of_basis
    intro x U hx
    obtain ⟨V, hxV, hVU, hC⟩ := hX x U hx
    exact ⟨V, hxV, hVU, exact_augmented_on_contractible X V ⟨⟨x, hxV⟩⟩ hC i⟩
  · exact ComplexShape.prev_eq' _ (show i - 1 + 1 = i by omega)
  · exact ComplexShape.next_eq' _ (show i + 1 = i + 1 from rfl)

theorem nonnegativeSupport : Expected.NonnegativeSupport.{u} := by
  intro X
  apply (CochainComplex.isStrictlyGE_iff _ _).mpr
  intro i hi
  let P := (presheafComplex X).X i
  have hP : IsZero P := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply NatTrans.ext
    funext U
    let K := ordinaryComplex ℚ ℚ (TopCat.of U.unop)
    have hK : IsZero (K.X i) := P202.SingularChains.ordinary_negative_chains ℚ ℚ _ i hi
    exact ((dualFunctor ℚ Values.{u}).map_isZero hK.op).eq_of_src _ _
  exact (presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}).map_isZero hP

open private augmentationAtZero dualCoefficientIso from
  MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SingularCochainSheaves

private lemma ordinaryDegree_naturality {Y Z : TopCat.{u}} (f : Y ⟶ Z) (n : ℕ) :
    ((ordinaryFunctor ℚ ℚ).map f).f (n : ℤ) ≫ (ordinaryNonnegativeIso ℚ ℚ Z n).hom =
      (ordinaryNonnegativeIso ℚ ℚ Y n).hom ≫ (chainMap ℚ ℚ f).f n := by
  change (HomologicalComplex.extendMap (chainMap ℚ ℚ f) (degreeEmbedding 0)).f (n : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (i := n)
    (show (degreeEmbedding 0).f n = (n : ℤ) by simp [degreeEmbedding])]
  change ((ordinaryNonnegativeIso ℚ ℚ Y n).hom ≫ (chainMap ℚ ℚ f).f n ≫
    (ordinaryNonnegativeIso ℚ ℚ Z n).inv) ≫ (ordinaryNonnegativeIso ℚ ℚ Z n).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma reducedDegree_naturality {Y Z : TopCat.{u}} (f : Y ⟶ Z) (n : ℕ) :
    ((reducedFunctor ℚ ℚ).map f).f (n : ℤ) ≫ (reducedNonnegativeIso ℚ ℚ Z n).hom =
      (reducedNonnegativeIso ℚ ℚ Y n).hom ≫ (chainMap ℚ ℚ f).f n := by
  change (HomologicalComplex.extendMap (augmentedShiftedMap ℚ ℚ f) (degreeEmbedding (-1))).f
    (n : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (i := n + 1)
    (show (degreeEmbedding (-1)).f (n + 1) = (n : ℤ) by simp [degreeEmbedding])]
  change ((reducedNonnegativeIso ℚ ℚ Y n).hom ≫ (chainMap ℚ ℚ f).f n ≫
    (reducedNonnegativeIso ℚ ℚ Z n).inv) ≫ (reducedNonnegativeIso ℚ ℚ Z n).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma reducedAugmentation_naturality {Y Z : TopCat.{u}} (f : Y ⟶ Z) :
    ((reducedFunctor ℚ ℚ).map f).f (-1) ≫ (reducedAugmentationIso ℚ ℚ Z).hom =
      (reducedAugmentationIso ℚ ℚ Y).hom := by
  change (HomologicalComplex.extendMap (augmentedShiftedMap ℚ ℚ f) (degreeEmbedding (-1))).f
    (-1) ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (i := 0)
    (show (degreeEmbedding (-1)).f 0 = -1 from rfl)]
  change ((reducedAugmentationIso ℚ ℚ Y).hom ≫ 𝟙 _ ≫
    (reducedAugmentationIso ℚ ℚ Z).inv) ≫ (reducedAugmentationIso ℚ ℚ Z).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def chainDegreeIso (Y : TopCat.{u}) (n : ℕ) :
    (reducedComplex ℚ ℚ Y).X (n : ℤ) ≅ (ordinaryComplex ℚ ℚ Y).X (n : ℤ) :=
  reducedNonnegativeIso ℚ ℚ Y n ≪≫ (ordinaryNonnegativeIso ℚ ℚ Y n).symm

private lemma chainDegreeIso_naturality {Y Z : TopCat.{u}} (f : Y ⟶ Z) (n : ℕ) :
    ((reducedFunctor ℚ ℚ).map f).f (n : ℤ) ≫ (chainDegreeIso Z n).hom =
      (chainDegreeIso Y n).hom ≫ ((ordinaryFunctor ℚ ℚ).map f).f (n : ℤ) := by
  apply (cancel_mono (ordinaryNonnegativeIso ℚ ℚ Z n).hom).mp
  simp only [chainDegreeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ordinaryDegree_naturality, Iso.inv_hom_id_assoc]
  exact reducedDegree_naturality f n

private def cochainDegreeIso (X : TopCat.{u}) (n : ℕ) :
    (presheafComplex X).X (n : ℤ) ≅ (augmentedPresheafComplex X).X (n : ℤ) :=
  NatIso.ofComponents (fun U =>
    (dualFunctor ℚ Values.{u}).mapIso (chainDegreeIso ((Opens.toTopCat X).obj U.unop) n).op)
    (by
      intro U V f
      let D := dualFunctor ℚ Values.{u}
      let g := (Opens.toTopCat X).map f.unop
      change D.map (((ordinaryFunctor ℚ ℚ).map g).f (n : ℤ)).op ≫
        D.map (chainDegreeIso ((Opens.toTopCat X).obj V.unop) n).hom.op =
          D.map (chainDegreeIso ((Opens.toTopCat X).obj U.unop) n).hom.op ≫
            D.map (((reducedFunctor ℚ ℚ).map g).f (n : ℤ)).op
      rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp, chainDegreeIso_naturality])

private def cochainAugmentationIso (X : TopCat.{u}) :
    (Functor.const ((Opens X)ᵒᵖ)).obj (ModuleCat.of ℚ Values.{u}) ≅
      (augmentedPresheafComplex X).X (-1) :=
  NatIso.ofComponents (fun U => dualCoefficientIso ≪≫ (dualFunctor ℚ Values.{u}).mapIso
    (reducedAugmentationIso ℚ ℚ ((Opens.toTopCat X).obj U.unop)).op) (by
      intro U V f
      let D := dualFunctor ℚ Values.{u}
      let g := (Opens.toTopCat X).map f.unop
      change 𝟙 _ ≫ (dualCoefficientIso.hom ≫
        D.map (reducedAugmentationIso ℚ ℚ ((Opens.toTopCat X).obj V.unop)).hom.op) =
          (dualCoefficientIso.hom ≫
            D.map (reducedAugmentationIso ℚ ℚ ((Opens.toTopCat X).obj U.unop)).hom.op) ≫
              D.map (((reducedFunctor ℚ ℚ).map g).f (-1)).op
      rw [Category.id_comp, Category.assoc, ← D.map_comp, ← op_comp,
        reducedAugmentation_naturality])

private lemma chainDegreeIso_d (Y : TopCat.{u}) (n : ℕ) :
    (reducedComplex ℚ ℚ Y).d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (chainDegreeIso Y n).hom =
      (chainDegreeIso Y (n + 1)).hom ≫ (ordinaryComplex ℚ ℚ Y).d ((n + 1 : ℕ) : ℤ) (n : ℤ) := by
  apply (cancel_epi (reducedNonnegativeIso ℚ ℚ Y (n + 1)).inv).mp
  apply (cancel_mono (ordinaryNonnegativeIso ℚ ℚ Y n).hom).mp
  simp only [chainDegreeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [P202.SingularChains.reduced_boundary, P202.SingularChains.ordinary_boundary]

private lemma cochainDegreeIso_d (X : TopCat.{u}) (n : ℕ) :
    (cochainDegreeIso X n).hom ≫ (augmentedPresheafComplex X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      (presheafComplex X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ (cochainDegreeIso X (n + 1)).hom := by
  apply NatTrans.ext
  funext U
  let D := dualFunctor ℚ Values.{u}
  let Y := (Opens.toTopCat X).obj U.unop
  change D.map (chainDegreeIso Y n).hom.op ≫
    D.map ((reducedComplex ℚ ℚ Y).d ((n + 1 : ℕ) : ℤ) (n : ℤ)).op =
      D.map ((ordinaryComplex ℚ ℚ Y).d ((n + 1 : ℕ) : ℤ) (n : ℤ)).op ≫
        D.map (chainDegreeIso Y (n + 1)).hom.op
  rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp, chainDegreeIso_d]

private lemma chainDegreeIso_augmentation (Y : TopCat.{u}) :
    (reducedComplex ℚ ℚ Y).d 0 (-1) ≫ (reducedAugmentationIso ℚ ℚ Y).hom =
      (chainDegreeIso Y 0).hom ≫ augmentationAtZero Y := by
  apply (cancel_epi (reducedNonnegativeIso ℚ ℚ Y 0).inv).mp
  simp only [chainDegreeIso, augmentationAtZero, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact P202.SingularChains.reduced_augmentation ℚ ℚ Y

private lemma cochainAugmentationIso_d (X : TopCat.{u}) :
    (cochainAugmentationIso X).hom ≫ (augmentedPresheafComplex X).d (-1) 0 =
      presheafAugmentation X ≫ (cochainDegreeIso X 0).hom := by
  apply NatTrans.ext
  funext U
  let D := dualFunctor ℚ Values.{u}
  let Y := (Opens.toTopCat X).obj U.unop
  change (dualCoefficientIso.hom ≫ D.map (reducedAugmentationIso ℚ ℚ Y).hom.op) ≫
    D.map ((reducedComplex ℚ ℚ Y).d 0 (-1)).op =
      (dualCoefficientIso.hom ≫ D.map (augmentationAtZero Y).op) ≫
        D.map (chainDegreeIso Y 0).hom.op
  rw [Category.assoc, Category.assoc, ← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp,
    chainDegreeIso_augmentation]

private abbrev sheafification (X : TopCat.{u}) :=
  presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}

private def sheafDegreeIso (X : TopCat.{u}) (n : ℕ) :
    (sheafComplex X).X (n : ℤ) ≅ (augmentedSheafComplex X).X (n : ℤ) :=
  (sheafification X).mapIso (cochainDegreeIso X n)

private def sheafAugmentationIso (X : TopCat.{u}) :
    rational X ≅ (augmentedSheafComplex X).X (-1) :=
  (sheafification X).mapIso (cochainAugmentationIso X)

private lemma sheafDegreeIso_d (X : TopCat.{u}) (n : ℕ) :
    (sheafDegreeIso X n).hom ≫ (augmentedSheafComplex X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      (sheafComplex X).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ (sheafDegreeIso X (n + 1)).hom := by
  change (sheafification X).map _ ≫ (sheafification X).map _ =
    (sheafification X).map _ ≫ (sheafification X).map _
  rw [← Functor.map_comp, ← Functor.map_comp, cochainDegreeIso_d]

private lemma sheafAugmentationIso_d (X : TopCat.{u}) :
    (sheafAugmentationIso X).hom ≫ (augmentedSheafComplex X).d (-1) 0 =
      augmentationArrow X ≫ (sheafDegreeIso X 0).hom := by
  change (sheafification X).map _ ≫ (sheafification X).map _ =
    (sheafification X).map _ ≫ (sheafification X).map _
  rw [← Functor.map_comp, ← Functor.map_comp, cochainAugmentationIso_d]

private lemma exactAugmentedTriple (X : TopCat.{u}) (hX : HasContractibleOpenBasis X)
    (i j k : ℤ) (h₁ : i + 1 = j) (h₂ : j + 1 = k) :
    ((augmentedSheafComplex X).sc' i j k).Exact :=
  (HomologicalComplex.exactAt_iff' _ _ _ _ (ComplexShape.prev_eq' _ h₁)
    (ComplexShape.next_eq' _ h₂)).mp (augmentedExact X hX j)

private lemma augmented_d_before_augmentation (X : TopCat.{u}) :
    (augmentedSheafComplex X).d (-2) (-1) = 0 := by
  change (sheafification X).map ((augmentedPresheafComplex X).d (-2) (-1)) = 0
  rw [← Functor.map_zero (F := sheafification X)]
  congr 1
  apply NatTrans.ext
  funext U
  let Y := TopCat.of U.unop
  have hZ : IsZero ((reducedComplex ℚ ℚ Y).X (-2)) :=
    (P202.SingularChains.reduced_below_minus_one ℚ ℚ Y (-2) (by decide)).1
  exact ((dualFunctor ℚ Values.{u}).map_isZero hZ.op).eq_of_src _ _

private lemma mono_augmentationArrow (X : TopCat.{u}) (hX : HasContractibleOpenBasis X) :
    Mono (augmentationArrow X) := by
  haveI : Mono ((augmentedSheafComplex X).d (-1) 0) :=
    ((HomologicalComplex.sc' (augmentedSheafComplex X) (-2) (-1) 0).exact_iff_mono
      (augmented_d_before_augmentation X)).mp (exactAugmentedTriple X hX (-2) (-1) 0 rfl rfl)
  haveI : Mono (augmentationArrow X ≫ (sheafDegreeIso X 0).hom) := by
    rw [← sheafAugmentationIso_d]
    infer_instance
  exact mono_of_mono _ (sheafDegreeIso X 0).hom

private lemma exact_ordinary_succ (X : TopCat.{u}) (hX : HasContractibleOpenBasis X) (n : ℕ) :
    (sheafComplex X).ExactAt ((n + 1 : ℕ) : ℤ) := by
  let i := (n : ℤ)
  let j := ((n + 1 : ℕ) : ℤ)
  let k := ((n + 1 + 1 : ℕ) : ℤ)
  have h₁ : i + 1 = j := Int.natCast_succ n |>.symm
  have h₂ : j + 1 = k := Int.natCast_succ (n + 1) |>.symm
  apply (HomologicalComplex.exactAt_iff' _ i j k (ComplexShape.prev_eq' _ h₁)
    (ComplexShape.next_eq' _ h₂)).mpr
  let e : (sheafComplex X).sc' i j k ≅ (augmentedSheafComplex X).sc' i j k :=
    ShortComplex.isoMk (sheafDegreeIso X n) (sheafDegreeIso X (n + 1))
      (sheafDegreeIso X (n + 1 + 1)) (sheafDegreeIso_d X n) (sheafDegreeIso_d X (n + 1))
  exact ShortComplex.exact_of_iso e.symm (exactAugmentedTriple X hX i j k h₁ h₂)

private lemma quasiIsoAt_augmentation_zero (X : TopCat.{u}) (hX : HasContractibleOpenBasis X) :
    QuasiIsoAt (augmentation X) 0 := by
  let K := (CochainComplex.singleFunctor (Sheaves X) 0).obj (rational X)
  let m : K.sc' (-1) 0 1 ⟶ (sheafComplex X).sc' (-1) 0 1 :=
    (HomologicalComplex.shortComplexFunctor' (Sheaves X) (.up ℤ) (-1) 0 1).map
      (augmentation X)
  apply (quasiIsoAt_iff' (augmentation X) (-1) 0 1
    (ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl))
    (ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl))).mpr
  have fzero : (K.sc' (-1) 0 1).f = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (rational X) (-1) 0
  have gzero : (K.sc' (-1) 0 1).g = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (rational X) 0 1
  letI := nonnegativeSupport X
  have ho : ((sheafComplex X).sc' (-1) 0 1).f = 0 :=
    ((sheafComplex X).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_src _ _
  apply (ShortComplex.quasiIso_iff_of_zeros m fzero gzero ho).mpr
  let e₀ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) (rational X)
  have hm : m.τ₂ = e₀.hom ≫ augmentationArrow X := by
    change (augmentation X).f 0 = _
    unfold Analytic.SingularCochains.augmentation
    exact HomologicalComplex.mkHomFromSingle_f (augmentationArrow X) _
  constructor
  · let S := ShortComplex.mk m.τ₂ ((sheafComplex X).sc' (-1) 0 1).g
      (by rw [m.comm₂₃, gzero, zero_comp])
    let e : S ≅ (augmentedSheafComplex X).sc' (-1) 0 1 :=
      ShortComplex.isoMk (e₀ ≪≫ sheafAugmentationIso X) (sheafDegreeIso X 0)
        (sheafDegreeIso X 1) (by
          change (e₀.hom ≫ (sheafAugmentationIso X).hom) ≫
            (augmentedSheafComplex X).d (-1) 0 = m.τ₂ ≫ (sheafDegreeIso X 0).hom
          rw [Category.assoc, sheafAugmentationIso_d, hm, Category.assoc])
        (sheafDegreeIso_d X 0)
    exact ShortComplex.exact_of_iso e.symm (exactAugmentedTriple X hX (-1) 0 1 rfl rfl)
  · rw [hm]
    haveI := mono_augmentationArrow X hX
    infer_instance

theorem resolution : Expected.Resolution.{u} := by
  intro X hX
  rw [quasiIso_iff]
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · apply (quasiIsoAt_iff_exactAt _ i
      (HomologicalComplex.exactAt_single_obj _ _ _ _ hi.ne)).mpr
    letI := nonnegativeSupport X
    exact HomologicalComplex.ExactAt.of_isZero ((sheafComplex X).isZero_of_isStrictlyGE 0 i hi)
  · exact quasiIsoAt_augmentation_zero X hX
  · apply (quasiIsoAt_iff_exactAt _ i
      (HomologicalComplex.exactAt_single_obj _ _ _ _ hi.ne')).mpr
    let n := (i - 1).toNat
    have hn : ((n + 1 : ℕ) : ℤ) = i := by
      simp only [Int.natCast_succ, n]
      omega
    rw [← hn]
    exact exact_ordinary_succ X hX n

private theorem skyscraper_flasque {X : TopCat.{u}} (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] (A : Coeff.{u}) :
    TopCat.Sheaf.IsFlasque (skyscraperSheaf x A) := by
  constructor
  intro U V i
  by_cases hx : x ∈ V.unop
  · have hU : x ∈ U.unop := i.unop.le hx
    change Epi ((skyscraperPresheaf x A).map i)
    rw [skyscraperPresheaf_map, dite_eq_left hx]
    infer_instance
  · have hterm := isTerminalSkyscraperSheafObjObjOfNotMem (A := A) (U := V) hx
    have hz := (IsZero.iff_id_eq_zero _).mpr (hterm.hom_ext (𝟙 _) 0)
    exact hz.epi _

private theorem product_flasque {X : TopCat.{u}} {ι : Type u} (G : ι → Sheaves X)
    (hG : ∀ i, TopCat.Sheaf.IsFlasque (G i)) :
    TopCat.Sheaf.IsFlasque (∏ᶜ G) := by
  classical
  constructor
  intro U V f
  apply (ModuleCat.epi_iff_surjective _).mpr
  let ev (U : (Opens X)ᵒᵖ) := sectionsOn U.unop
  letI (U : (Opens X)ᵒᵖ) : PreservesLimits (ev U) := by
    change PreservesLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) Coeff.{u} ⋙
        (evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op U.unop))
    exact comp_preservesLimits _ _
  have hlim (U : (Opens X)ᵒᵖ) :=
    isLimitOfHasProductOfPreservesLimit (ev U) G
  intro t
  let t' (i : ι) := (ev V).map (Pi.π G i) t
  have lift (i : ι) : ∃ s : (ev U).obj (G i), (G i).obj.map f s = t' i :=
    (ModuleCat.epi_iff_surjective _).mp ((hG i).epi f) (t' i)
  choose s hs using lift
  let A := ModuleCat.of ℚ Values.{u}
  let a : Fan (fun i => (ev U).obj (G i)) :=
    Fan.mk A (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (s i) ∘ₗ
      (ULift.moduleEquiv : Values.{u} ≃ₗ[ℚ] ℚ).toLinearMap))
  let el : A := ULift.up 1
  let p := (hlim U).lift a
  refine ⟨p el, ?_⟩
  let elementMap (z : (ev V).obj (∏ᶜ G)) : A ⟶ (ev V).obj (∏ᶜ G) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z ∘ₗ
      (ULift.moduleEquiv : Values.{u} ≃ₗ[ℚ] ℚ).toLinearMap)
  have he (z : (ev V).obj (∏ᶜ G)) : elementMap z el = z := by
    change (1 : ℚ) • z = z
    simp
  have eq : elementMap ((∏ᶜ G).obj.map f (p el)) = elementMap t := by
    apply (hlim V).hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (ev V).map (Pi.π G i.as) (r.down • (∏ᶜ G).obj.map f (p el)) =
      (ev V).map (Pi.π G i.as) (r.down • t)
    simp only [map_smul]
    congr 1
    have n := congrArg (fun m => m (p el)) ((Pi.π G i.as).hom.naturality f)
    change (ev V).map (Pi.π G i.as) ((∏ᶜ G).obj.map f (p el)) =
      (G i.as).obj.map f ((ev U).map (Pi.π G i.as) (p el)) at n
    rw [n]
    have h := congrArg (fun m => m el) ((hlim U).fac a i)
    change (ev U).map (Pi.π G i.as) (p el) = a.π.app i el at h
    rw [h]
    change (G i.as).obj.map f ((1 : ℚ) • s i.as) = t' i.as
    rw [one_smul, hs]
  exact (he _).symm.trans ((congrArg (fun m => m el) eq).trans (he _))

private theorem injective_flasque {X : TopCat.{u}} (F : Sheaves X) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  classical
  let G (x : X) := skyscraperSheaf x ((stalk x).obj F)
  let a (x : X) : F ⟶ G x := (stalkSkyscraperSheafAdjunction x).unit.app F
  let j : F ⟶ ∏ᶜ G := Pi.lift a
  haveI hj : Mono j := by
    apply (TopCat.Sheaf.forget Coeff.{u} X).mono_of_mono_map
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro U
    apply (ModuleCat.mono_iff_injective _).mpr
    intro s t h
    apply TopCat.Presheaf.section_ext F U.unop s t
    intro x hx
    have fac : j ≫ Pi.π G x = a x := Pi.lift_comp_π _ _
    have eq := congrArg (fun z => (Pi.π G x).hom.app U z) h
    change ((j ≫ Pi.π G x).hom.app U) s = ((j ≫ Pi.π G x).hom.app U) t at eq
    rw [fac] at eq
    have hp : (a x).hom.app U = F.presheaf.germ U.unop x hx ≫
        eqToHom (ite_eq_left hx).symm := by
      change (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x (𝟙 (F.presheaf.stalk x))).app U = _
      rw [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, dite_eq_left hx, Category.id_comp]
    rw [hp] at eq
    exact (ModuleCat.mono_iff_injective (eqToHom (ite_eq_left hx).symm)).mp inferInstance eq
  let r := Injective.factorThru (𝟙 F) j
  have hr : j ≫ r = 𝟙 F := Injective.comp_factorThru _ _
  haveI : TopCat.Sheaf.IsFlasque (∏ᶜ G) := product_flasque G (fun x => skyscraper_flasque x _)
  constructor
  intro U V f
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro t
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective ((∏ᶜ G).obj.map f)).mp inferInstance
    (j.hom.app V t)
  refine ⟨r.hom.app U b, ?_⟩
  have hn := congrArg (fun m => m b) (r.hom.naturality f)
  change r.hom.app V ((∏ᶜ G).obj.map f b) = F.obj.map f (r.hom.app U b) at hn
  rw [← hn, hb]
  exact congrArg (fun m => m.hom.app V t) hr

private abbrev forgetCoefficients := forget₂ Coeff.{u} AddCommGrpCat.{u}

private abbrev forgetSheaf (X : TopCat.{u}) : Sheaves X ⥤ X.Sheaf AddCommGrpCat.{u} :=
  sheafCompose (Opens.grothendieckTopology X) forgetCoefficients.{u}

private instance (X : TopCat.{u}) : (forgetSheaf X).Additive where
  map_add := by intros; rfl

private def forgetStalkIso {X : TopCat.{u}} (x : X) :
    forgetSheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ≅ stalk x ⋙ forgetCoefficients.{u} :=
  Functor.isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) Coeff.{u} ⋙
    (Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ Coeff.{u}).obj
      (OpenNhds.inclusion x).op) (preservesColimitNatIso forgetCoefficients).symm

private theorem forgetShortExact {X : TopCat.{u}} (S : ShortComplex (Sheaves X))
    (h : S.ShortExact) : (S.map (forgetSheaf X)).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    have hx : (S.map (stalk x ⋙ forgetCoefficients.{u})).Exact :=
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S |>.mp h.exact x).map forgetCoefficients
    exact ShortComplex.exact_of_iso (S.mapNatIso (forgetStalkIso x).symm) hx
  · apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro U
    haveI := h.mono_f
    haveI : Mono (S.f.hom.app U) := (NatTrans.mono_iff_mono_app _).mp
      (CategoryTheory.presheaf_mono_of_mono _ _ _) U
    exact (AddCommGrpCat.mono_iff_injective _).mpr
      ((ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (S.f.hom.app U)))
  · apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    have hlocal := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp
      ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr h.epi_g)
    exact hlocal

private theorem forgetFlasque {X : TopCat.{u}} {F : Sheaves X}
    (h : TopCat.Sheaf.IsFlasque F) : TopCat.Sheaf.IsFlasque ((forgetSheaf X).obj F) := by
  constructor
  intro U V f
  exact (AddCommGrpCat.epi_iff_surjective _).mpr ((ModuleCat.epi_iff_surjective _).mp (h.epi f))

private theorem flasqueOfForget {X : TopCat.{u}} {F : Sheaves X}
    (h : TopCat.Sheaf.IsFlasque ((forgetSheaf X).obj F)) : TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V f
  exact (ModuleCat.epi_iff_surjective _).mpr ((AddCommGrpCat.epi_iff_surjective _).mp (h.epi f))

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open AdvancedHomologicalAlgebra

theorem flasqueAcyclic : Expected.FlasqueAcyclicity.{u} := by
  intro X M hM U n
  letI := HasDerivedCategory.standard Coeff.{u}
  let F := sectionsOn U
  let T := rightSystem F
  have hT : IsCohomological T := UniversalDeltaFunctors.rightDelta _ _ F
  have vanish (I : Sheaves X) [Injective I] (k : ℕ) :
      IsZero ((T.value (k + 1)).obj I) :=
    ClassicalDerivedValues.rightInjectiveVanishing _ _ F I k
  suffices h : ∀ N : Sheaves X, TopCat.Sheaf.IsFlasque N →
      IsZero ((T.value (n + 1)).obj N) from h M hM
  induction n with
  | zero =>
    intro N hN
    let S := UniversalDeltaFunctors.injectiveSequence N
    have hS := UniversalDeltaFunctors.injectiveSequence_shortExact N
    letI : Epi (T.δ hS 0) := UniversalDeltaFunctors.dimensionShift_epi T hT vanish N 0
    letI : TopCat.Sheaf.IsFlasque (S.map (forgetSheaf X)).X₁ := forgetFlasque hN
    have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) (forgetShortExact S hS)
    letI : Epi (F.map S.g) := (ModuleCat.epi_iff_surjective _).mpr
      ((AddCommGrpCat.epi_iff_surjective _).mp he)
    letI := ClassicalDerivedValues.rightZero _ _ F
    letI : Epi ((T.value 0).map S.g) := by
      change Epi ((rightValue F 0).map S.g)
      exact epi_of_epi_fac ((rightDegreeZeroUnit F).naturality S.g).symm
    exact IsZero.of_epi_eq_zero (T.δ hS 0)
      (zero_of_epi_comp ((T.value 0).map S.g) (hT.exact₃ hS 0).zero)
  | succ n ih =>
    intro N hN
    let S := UniversalDeltaFunctors.injectiveSequence N
    have hS := UniversalDeltaFunctors.injectiveSequence_shortExact N
    letI : TopCat.Sheaf.IsFlasque (S.map (forgetSheaf X)).X₁ := forgetFlasque hN
    letI : TopCat.Sheaf.IsFlasque (S.map (forgetSheaf X)).X₂ :=
      forgetFlasque (injective_flasque _)
    have hQ : TopCat.Sheaf.IsFlasque S.X₃ :=
      flasqueOfForget (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (forgetShortExact S hS))
    letI : Epi (T.δ hS (n + 1)) :=
      UniversalDeltaFunctors.dimensionShift_epi T hT vanish N (n + 1)
    exact IsZero.of_epi (T.δ hS (n + 1)) (ih S.X₃ hQ)

end RepTheorySurvey.Geometric.SingularCochainSheaves
