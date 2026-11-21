import MathGenome.Internal.Specs.D07.Ch15.RadicalsImplySolvableNormalRadicalGroup
import MathGenome.Internal.D07.Ch15.RadicalComposita
import MathGenome.Internal.D07.Ch15.RootsUnity
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

noncomputable section
universe u v
namespace D07.Ch15.RadicalsImplySolvableNormalRadicalGroup
open Polynomial IntermediateField Specs.D07.Ch15.RadicalDefinition
open Specs.D07.Ch15.RadicalsImplySolvableNormalRadicalGroup

/-- Compare finite radical towers to the library's radical-closed subfield. -/
theorem tower_in_solvableByRad : TowerInSolvableByRad.{u,v} := by
  intro K Ω _ _ _ _ N hN
  apply RadicalComposita.radical_extension_induction
    (P := fun E => E ≤ solvableByRad K Ω) bot_le ?_ hN
  intro E F _ ih hstep
  obtain ⟨a, n, hn, hp, rfl⟩ := hstep
  apply adjoin_le_iff.mpr
  rintro x (hx | rfl)
  · exact ih hx
  · exact solvableByRad.rad_mem hn.ne' (ih hp)

/-- For a finite normal extension, a basis supplies finitely many minimal
polynomials whose splitting field is the whole extension. Their solvable
Galois groups therefore suffice. No primitive-element theorem is used. -/
theorem isSolvable_aut_of_minpoly (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [h : Normal K L]
    (hmin : ∀ x : L, Group.IsSolvable (minpoly K x).Gal) :
    Group.IsSolvable (L ≃ₐ[K] L) := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  let p : K[X] := ∏ i, minpoly K (b i)
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero (h.isIntegral _)
  have hs : IsSplittingField K L p := by
    refine ⟨?_, ?_⟩
    · exact Polynomial.map_prod (algebraMap K L) _ _ ▸
        Splits.prod fun i _ => h.splits (b i)
    · apply Subalgebra.toSubmodule.injective
      rw [Algebra.top_toSubmodule, eq_top_iff, ← b.span_eq, Submodule.span_le,
        Set.range_subset_iff]
      intro i
      apply Algebra.subset_adjoin
      apply (Multiset.mem_toFinset.mpr ?_)
      apply (mem_roots (Polynomial.map_ne_zero hp0)).mpr
      rw [IsRoot.def, eval_map_algebraMap, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (b i))
  let := hs
  have hp : Group.IsSolvable p.Gal := by
    exact Finset.prod_induction _ (fun q : K[X] => Group.IsSolvable q.Gal)
      (fun q r hq hr => gal_mul_isSolvable hq hr) gal_one_isSolvable
      (fun i _ => hmin (b i))
  change Group.IsSolvable (p.SplittingField ≃ₐ[K] p.SplittingField) at hp
  let := hp
  let e := (IsSplittingField.algEquiv L p).autCongr
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem normal_radical_group : NormalRadicalGroup.{u,v} := by
  intro K Ω _ _ _ _ N hN hnormal
  let := hnormal
  let := RadicalComposita.radical_extension_finite K Ω N hN
  refine ⟨inferInstance, isSolvable_aut_of_minpoly K N fun x => ?_⟩
  have hx : (x : Ω) ∈ solvableByRad K Ω := tower_in_solvableByRad K Ω N hN x.2
  have hgal := isSolvable_gal_minpoly hx
  change Group.IsSolvable (minpoly K (N.val x)).Gal at hgal
  rwa [minpoly.algHom_eq N.val N.val.injective x] at hgal

/-- A root-containing radical step is normal even when the binomial is
inseparable. The ratio homomorphism does not use a separable degree formula. -/
theorem normal_cyclic_step : NormalCyclicStep.{u,v} := by
  intro M Ω _ _ _ _ a n hn ha hroots
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, hb⟩ := mem_bot.mp ha
  let L := adjoin M {a}
  let α : L := ⟨a, mem_adjoin_simple_self M a⟩
  have hα : α ^ n = algebraMap M L b := Subtype.ext hb.symm
  let p := minpoly M a
  have hp0 : p ≠ 0 := minpoly.ne_zero ((inferInstance : Normal M Ω).isIntegral a)
  have hpn : p ∣ X ^ n - C b := minpoly.dvd M a (by
    simp only [map_sub, aeval_X_pow, aeval_C, hb, sub_self])
  have root_mem : ∀ x ∈ p.rootSet Ω, x ∈ L := by
    intro x hx
    have hxpow : x ^ n = algebraMap M Ω b := by
      have hx' := aeval_eq_zero_of_dvd_aeval_eq_zero hpn ((mem_rootSet_of_ne hp0).mp hx)
      simpa only [map_sub, aeval_X_pow, aeval_C, sub_eq_zero] using hx' 
    by_cases ha0 : a = 0
    · have : x = 0 := (pow_eq_zero_iff hn.ne').mp (hxpow.trans (hb.trans (by simp [ha0, hn.ne'])))
      simp [this]
    · have hr : (x / a) ^ n = 1 := by
        rw [div_pow, hxpow, hb, div_self (pow_ne_zero _ ha0)]
      have hx' := L.mul_mem ((show (⊥ : IntermediateField M Ω) ≤ L from bot_le) (hroots _ hr)) (mem_adjoin_simple_self M a)
      simpa only [div_mul_cancel₀ _ ha0] using hx'
  have hs : IsSplittingField M L p := IntermediateField.isSplittingField_iff.mpr ⟨
    IntermediateField.splits_of_splits ((inferInstance : Normal M Ω).splits a) root_mem, ?_⟩
  · have hnormal : Normal M L := @Normal.of_isSplittingField M _ _ _ _ p hs
    refine ⟨hnormal, ?_⟩
    have extα {σ τ : L ≃ₐ[M] L} (h : σ α = τ α) : σ = τ := by
      apply AlgEquiv.coe_toAlgHom_injective
      apply adjoin_algHom_ext M
      rintro x (rfl : x = a)
      exact h
    by_cases ha0 : a = 0
    · have : Subsingleton (L ≃ₐ[M] L) := ⟨fun σ τ => extα (by
        have hzero : α = 0 := Subtype.ext ha0
        simp only [hzero, map_zero])⟩
      infer_instance
    have hα0 : α ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have hratio (σ : L ≃ₐ[M] L) : (σ α / α) ^ n = 1 := by
      rw [div_pow, ← map_pow, hα, σ.commutes]
      exact div_self (hα ▸ pow_ne_zero n hα0)
    have hbase (σ : L ≃ₐ[M] L) : ∃ c : M, algebraMap M L c = σ α / α := by
      obtain ⟨c, hc⟩ := mem_bot.mp (hroots ((σ α / α : L) : Ω) (by
        exact_mod_cast hratio σ))
      exact ⟨c, Subtype.ext hc⟩
    let χ : (L ≃ₐ[M] L) →* rootsOfUnity n L :=
      { toFun := fun σ => rootsOfUnity.mkOfPowEq (σ α / α) (hratio σ)
        map_one' := by
          apply Subtype.ext
          apply Units.ext
          simp only [rootsOfUnity.val_mkOfPowEq_coe, AlgEquiv.one_apply,
            OneMemClass.coe_one, Units.val_one, div_self hα0]
        map_mul' := by
          intro σ τ
          apply Subtype.ext
          apply Units.ext
          change (σ (τ α) / α) = (σ α / α) * (τ α / α)
          obtain ⟨c, hc⟩ := hbase τ
          have ht : τ α = algebraMap M L c * α := by
            rw [hc, div_mul_cancel₀ _ hα0]
          rw [ht, map_mul, σ.commutes, hc]
          field_simp }
    exact isCyclic_of_injective χ (by
      intro σ τ heq
      apply extα
      have h := congrArg (fun x : rootsOfUnity n L => ((x : Lˣ) : L)) heq
      change σ α / α = τ α / α at h
      exact (div_left_inj' hα0).mp h)
  · apply le_antisymm
    · apply adjoin_le_iff.mpr
      rintro x (rfl : x = a)
      apply subset_adjoin M
      exact (mem_rootSet_of_ne hp0).mpr (minpoly.aeval M x)
    · exact adjoin_le_iff.mpr root_mem

theorem lcm_root_adjunction : LcmRootAdjunction.{u,v} := by
  intro K Ω _ _ _ _ _ r n hn
  classical
  let q := ringExpChar K
  let d : Fin r → ℕ := fun i => ordCompl[q] (n i)
  let m := Finset.univ.lcm d
  have hdpos (i) : 0 < d i := Nat.ordCompl_pos q (hn i).ne'
  have hdcast (i) : (d i : K) ≠ 0 := by
    rcases expChar_is_prime_or_one K q with hprime | hq
    · let : CharP K q := (expChar_prime_iff K hprime).mp inferInstance
      exact (CharP.cast_eq_zero_iff K q (d i)).not.mpr
        (Nat.not_dvd_ordCompl hprime (hn i).ne')
    · have : ExpChar K 1 := hq ▸ (inferInstance : ExpChar K q)
      have : CharZero K := charZero_of_expChar_one' K
      dsimp only [d]
      rw [hq, Nat.ordCompl_of_not_prime _ _ Nat.not_prime_one]
      exact_mod_cast (hn i).ne'
  have hmcast : (m : K) ≠ 0 := by
    intro hm
    obtain ⟨k, hk⟩ := Finset.lcm_dvd_prod Finset.univ d
    have hp : ((∏ i, d i : ℕ) : K) = 0 := by
      rw [hk, Nat.cast_mul, hm, zero_mul]
    rw [Nat.cast_prod] at hp
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hdcast i)) hp
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun hm => hmcast (by simp [hm]))
  obtain ⟨ζ, hζ⟩ := RootsUnity.primitive_root_exists K Ω m hmpos hmcast
  refine ⟨hmpos, hmcast, ζ, hζ, ?_⟩
  let C := adjoin K {ζ}
  have hC : C = Specs.D07.Ch15.RootsUnity.RootField K Ω m :=
    (RootsUnity.generated_by_primitive_root K Ω m hmpos ζ hζ).symm
  obtain ⟨hfin, hgalois, hcomm⟩ :=
    RootsUnity.root_field_finite_galois_abelian K Ω m hmpos hmcast
  rw [← hC] at hfin hgalois hcomm
  let := hgalois
  refine ⟨hfin, inferInstance, hcomm, ?_⟩
  intro i z hz
  let : ExpChar Ω q := expChar_of_injective_algebraMap (algebraMap K Ω).injective q
  have hz' : z ^ d i = 1 := by
    apply iterateFrobenius_inj Ω q ((n i).factorization q)
    change (z ^ d i) ^ (q ^ (n i).factorization q) = 1 ^ (q ^ (n i).factorization q)
    rw [← pow_mul, Nat.mul_comm (d i), Nat.ordProj_mul_ordCompl_eq_self, hz, one_pow]
  have hzm : z ^ m = 1 := by
    obtain ⟨k, hk⟩ := Finset.dvd_lcm (s := Finset.univ) (f := d) (Finset.mem_univ i)
    change z ^ Finset.univ.lcm d = 1
    rw [hk, pow_mul, hz', one_pow]
  let : NeZero m := ⟨hmpos.ne'⟩
  obtain ⟨k, _, hk⟩ := hζ.eq_pow_of_pow_eq_one hzm
  rw [← hk]
  exact pow_mem (mem_adjoin_simple_self K ζ) k

theorem cyclic_fixing_factor : CyclicFixingFactor.{u,v} := by
  intro M E _ _ _ L hnormal hcyclic
  let := hnormal
  let := hcyclic
  let f : (E ≃ₐ[M] E) →* (L ≃ₐ[M] L) := AlgEquiv.restrictNormalHom L
  have hk : f.ker = L.fixingSubgroup := L.restrictNormalHom_ker
  have h : L.fixingSubgroup.Normal := hk ▸ f.normal_ker
  refine ⟨h, ?_⟩
  letI := h
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  exact isCyclic_of_injective e.toMonoidHom e.injective

/-- The explicit subnormal inclusion needed between two consecutive fixing
subgroups. The larger extension need not be separable. -/
theorem nested_fixing_factor (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (E F : IntermediateField K L)
    (hEF : E ≤ F) (hnormal : Normal E (extendScalars hEF))
    (hcyclic : IsCyclic ((extendScalars hEF) ≃ₐ[E] (extendScalars hEF))) :
    ∃ h : (F.fixingSubgroup.subgroupOf E.fixingSubgroup).Normal,
      letI := h
      IsCyclic (E.fixingSubgroup ⧸ F.fixingSubgroup.subgroupOf E.fixingSubgroup) := by
  let F' := extendScalars hEF
  let := hnormal
  let := hcyclic
  let f : E.fixingSubgroup →* (F' ≃ₐ[E] F') :=
    (AlgEquiv.restrictNormalHom F').comp E.fixingSubgroupEquiv.toMonoidHom
  have hk : f.ker = F.fixingSubgroup.subgroupOf E.fixingSubgroup := by
    ext σ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h' := congrArg (fun τ : F' ≃ₐ[E] F' => (τ ⟨x, hx⟩ : L)) h
      simpa [f, AlgEquiv.restrictNormalHom_apply,
        coe_fixingSubgroupEquiv_apply] using h'
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      simpa [f, AlgEquiv.restrictNormalHom_apply,
        coe_fixingSubgroupEquiv_apply] using h (x : L) x.2
  have h : (F.fixingSubgroup.subgroupOf E.fixingSubgroup).Normal := hk ▸ f.normal_ker
  refine ⟨h, ?_⟩
  letI := h
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  exact isCyclic_of_injective e.toMonoidHom e.injective

/-- Base change of a specified radical adjunction. All n-th roots of unity in
the normal ambient field are assumed to belong to the new base. -/
theorem normal_cyclic_step_between (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]
    (E F : IntermediateField K Ω) (a : Ω) (n : ℕ) (hn : 0 < n)
    (ha : a ^ n ∈ E) (hgen : F = adjoin K ((E : Set Ω) ∪ {a}))
    (hroots : ∀ z : Ω, z ^ n = 1 → z ∈ E) (hEF : E ≤ F) :
    Normal E (extendScalars hEF) ∧
      IsCyclic ((extendScalars hEF) ≃ₐ[E] (extendScalars hEF)) := by
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  have heq : extendScalars hEF = adjoin E {a} := by
    apply restrictScalars_injective K
    rw [extendScalars_restrictScalars, restrictScalars_adjoin]
    exact hgen
  rw [heq]
  exact normal_cyclic_step E Ω a n hn
    (mem_bot.mpr ⟨⟨a ^ n, ha⟩, rfl⟩)
    (fun z hz => mem_bot.mpr ⟨⟨z, hroots z hz⟩, rfl⟩)

/-- The initial roots-of-unity quotient only needs commutativity. -/
theorem abelian_fixing_factor (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    [Normal K E] (hcomm : ∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) :
    ∃ h : E.fixingSubgroup.Normal, letI := h
      ∀ σ τ : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup, σ * τ = τ * σ := by
  let f : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  have hk : f.ker = E.fixingSubgroup := E.restrictNormalHom_ker
  have h : E.fixingSubgroup.Normal := hk ▸ f.normal_ker
  refine ⟨h, ?_⟩
  letI := h
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  intro σ τ
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (hcomm _ _)

/-- The complete base change and fixing-subgroup construction for a given
radical presentation. The normal ambient compositum may be inseparable. -/
theorem tower_refinement : TowerRefinement.{u,v} := by
  intro K Ω _ _ _ _ _ r T a n hT0 hstep hN
  classical
  have hT : radicalTowerValue K Ω r T := ⟨hT0, fun i =>
    ⟨a i, n i, (hstep i).1, (hstep i).2.1, (hstep i).2.2⟩⟩
  have hmono := RadicalDefinition.radical_tower_monotone K Ω r T hT
  obtain ⟨_, _, ζ, hζ, hCfin, hCnormal, hCcomm, hroots⟩ :=
    lcm_root_adjunction K Ω r n (fun i => (hstep i).1)
  refine ⟨ζ, hζ, ?_⟩
  let C := adjoin K {ζ}
  let N' := C ⊔ T (Fin.last r)
  let F : Fin (r + 1) → IntermediateField K N' :=
    fun i => (C ⊔ T i).comap N'.val
  have : FiniteDimensional K (T (Fin.last r)) :=
    RadicalComposita.radical_extension_finite K Ω _ ⟨r, T, hT, rfl⟩
  have : FiniteDimensional K C := hCfin
  have : Normal K C := hCnormal
  have : Normal K (T (Fin.last r)) := hN
  have : Normal K N' := inferInstanceAs (Normal K ↥(C ⊔ T (Fin.last r) : IntermediateField K Ω))
  have hFmono : Monotone F := by
    intro i j hij x hx
    exact (sup_le_sup le_rfl (hmono hij)) hx
  have hU (i) : C ⊔ T i ≤ N' := sup_le_sup_left (hmono (Fin.le_last i)) C
  have hmap (i) : (F i).map N'.val = C ⊔ T i :=
    map_comap_eq_self (by simpa only [fieldRange_val] using hU i)
  have hFlast : F (Fin.last r) = ⊤ := by
    ext x
    exact iff_of_true x.2 trivial
  refine ⟨inferInstance, inferInstance, hFmono, ?_, ?_, ?_⟩
  · change (F (Fin.last r)).fixingSubgroup = ⊥
    rw [hFlast, fixingSubgroup_top]
  · have hmap0 : (F 0).map N'.val = C := by
      simpa only [hT0, sup_bot_eq] using hmap 0
    let e : F 0 ≃ₐ[K] C := (equivMap (F 0) N'.val).trans (equivOfEq hmap0)
    have : Normal K (F 0) := Normal.of_algEquiv e.symm
    apply abelian_fixing_factor K N' (F 0)
    intro σ τ
    apply e.autCongr.injective
    simpa only [map_mul] using hCcomm (e.autCongr σ) (e.autCongr τ)
  · intro i
    let E := F i.castSucc
    let B := F i.succ
    have hi : E ≤ B := hFmono (Fin.castSucc_le_succ i)
    have hai : a i ∈ T i.succ := (hstep i).2.2 ▸
      subset_adjoin K _ (Or.inr rfl)
    let b : N' := ⟨a i, (show T (Fin.last r) ≤ N' from le_sup_right) ((hmono (Fin.le_last i.succ)) hai)⟩
    have hb : b ^ n i ∈ E :=
      (show T i.castSucc ≤ C ⊔ T i.castSucc from le_sup_right) (hstep i).2.1
    have hgen : B = adjoin K ((E : Set N') ∪ {b}) := by
      have hm : (adjoin K ((E : Set N') ∪ {b})).map N'.val = C ⊔ T i.succ := by
        rw [adjoin_map, Set.image_union, Set.image_singleton, ← coe_map, hmap i.castSucc]
        change adjoin K (((C ⊔ T i.castSucc : IntermediateField K Ω) : Set Ω) ∪ {a i}) = C ⊔ T i.succ
        rw [(hstep i).2.2, adjoin_union, adjoin_self, adjoin_union, adjoin_self, sup_assoc]
      simpa only [comap_map] using (congrArg (fun H => H.comap N'.val) hm).symm
    have hr (z : N') (hz : z ^ n i = 1) : z ∈ E := by
      apply (show C ≤ C ⊔ T i.castSucc from le_sup_left)
      apply hroots i (z : Ω)
      exact_mod_cast hz
    obtain ⟨hnormal, hcyclic⟩ := normal_cyclic_step_between K N' E B b (n i)
      (hstep i).1 hb hgen hr hi
    refine ⟨hi, hnormal, hcyclic, ?_⟩
    exact nested_fixing_factor K N' E B hi hnormal hcyclic

end D07.Ch15.RadicalsImplySolvableNormalRadicalGroup
