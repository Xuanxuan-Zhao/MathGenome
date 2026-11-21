import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularChains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial
universe u v w

namespace P202.Homology.CellularComparison
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularComparison

variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

def lowerIso (m : ℕ) : (skeletalPair X m).sub ≅ skeletalSpace X m :=
  TopCat.isoOfHomeo (lowerHomeomorph X m)

@[simp] lemma lowerIso_hom (m : ℕ) : (lowerIso X m).hom = lowerMap X m := rfl

instance lowerMap_isIso (m : ℕ) : IsIso (lowerMap X m) :=
  inferInstanceAs (IsIso (lowerIso X m).hom)

def skeletalShortExact (m : ℕ) :
    (sequence (ordinaryFunctor R M) (skeletalPair X m)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.ordinary_short_exact R M (skeletalPair X m))

theorem skeletalVanishing :
    ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
      (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
      (m n : ℕ), m ≤ n → IsZero (homology R M (skeletalSpace X m) (n : ℤ)) := by
  intro X _ _ R _ M _ _ m
  induction m with
  | zero =>
    intro n _
    letI := P202.Homology.skeletalSpace_zero_isEmpty X
    exact P202.SingularDegreeZero.emptyOrdinary R M (skeletalSpace X 0) n
  | succ m ih =>
    intro n hn
    have hz := ((homologyFunctor R M (n : ℤ)).mapIso (lowerIso X m)).isZero_iff.mpr
      (ih n (by omega))
    exact ((skeletalShortExact X R M m).homology_exact₂ (n : ℤ)).isZero_of_both_isZero hz
      (P202.Homology.cellularRelativeVanishing X R M m n (by omega))

@[simp] lemma skeletonInclusion_comp {a b c : ℕ} (h : a ≤ b) (k : b ≤ c) :
    skeletonInclusion X h ≫ skeletonInclusion X k = skeletonInclusion X (h.trans k) := rfl

@[simp] lemma skeletonInclusion_toSpace {a b : ℕ} (h : a ≤ b) :
    skeletonInclusion X h ≫ skeletonToSpace X b = skeletonToSpace X a := rfl

@[simp] lemma skeletonInclusion_refl (a : ℕ) :
    skeletonInclusion X (le_refl a) = 𝟙 (skeletalSpace X a) := rfl

lemma lowerMap_step (m : ℕ) :
    lowerMap X m ≫ skeletonInclusion X (Nat.le_succ m) = (skeletalPair X m).inclusion := rfl

/-- Attaching cells in dimensions greater than n+1 preserves degree-n homology. -/
lemma step_isIso (n m : ℕ) (h : n + 2 ≤ m) :
    IsIso ((homologyFunctor R M (n : ℤ)).map
      (skeletonInclusion X (Nat.le_succ m))) := by
  let S := skeletalShortExact X R M m
  have hz₁ := P202.Homology.cellularRelativeVanishing X R M m (n+1) (by omega)
  have hz₀ := P202.Homology.cellularRelativeVanishing X R M m n (by omega)
  haveI hmono : Mono (homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X m)) (n : ℤ)) := (S.homology_exact₁ ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)).mono_g
    (hz₁.eq_zero_of_src _)
  haveI hepi : Epi (homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X m)) (n : ℤ)) := (S.homology_exact₂ (n : ℤ)).epi_f (hz₀.eq_zero_of_tgt _)
  haveI : IsIso (homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X m)) (n : ℤ)) :=
    isIso_of_mono_of_epi _
  have hh : (homologyFunctor R M (n : ℤ)).map (lowerMap X m) ≫
      (homologyFunctor R M (n : ℤ)).map (skeletonInclusion X (Nat.le_succ m)) =
      homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X m)) (n : ℤ) := by
    rw [← Functor.map_comp, lowerMap_step]
    rfl
  haveI : IsIso ((homologyFunctor R M (n : ℤ)).map (lowerMap X m) ≫
      (homologyFunctor R M (n : ℤ)).map (skeletonInclusion X (Nat.le_succ m))) := by
    rw [hh]; infer_instance
  exact IsIso.of_isIso_comp_left ((homologyFunctor R M (n : ℤ)).map (lowerMap X m)) _

lemma skeletonInclusion_isIso (n a b : ℕ) (ha : n+2 ≤ a) (hab : a ≤ b) :
    IsIso ((homologyFunctor R M (n : ℤ)).map (skeletonInclusion X hab)) := by
  induction b, hab using Nat.le_induction with
  | base => simp only [skeletonInclusion_refl, Functor.map_id]; infer_instance
  | succ b hab ih =>
    haveI := ih
    haveI := step_isIso X R M n b (ha.trans hab)
    rw [← skeletonInclusion_comp X hab (Nat.le_succ b), Functor.map_comp]
    infer_instance

/-- Finiteness is total finiteness of the cell set, not local finiteness. -/
lemma finiteSubcomplex_bounded (A : Subcomplex X) (hA : A.IsFinite) :
    ∃ m, A.carrier ⊆ skeletonLT X m := by
  classical
  let F := hA.toFinset
  refine ⟨F.sup (fun d => d.1) + 1, ?_⟩
  intro x hx
  simp only [Subcomplex.carrier, Set.mem_iUnion] at hx
  obtain ⟨n, c, hxc⟩ := hx
  have hc : (⟨n, c.val⟩ : Σ n, Cell X n) ∈ F := hA.mem_toFinset.mpr c.property
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
    ⟨Nat.lt_succ_of_le (Finset.le_sup (f := fun d => d.1) hc),
      Set.mem_iUnion.mpr ⟨c.val, hxc⟩⟩⟩

theorem finiteChainSupport :
    ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
      (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
      (n : ℕ) (c : Chains M (TopCat.of X) n),
      ∃ m, ∃ b : Chains M (skeletalSpace X m) n,
        (chainMap R M (skeletonToSpace X m)).f n b = c := by
  intro X _ _ R _ M _ _ n c
  classical
  let K : Set X := ⋃ s : c.support, Set.range (simplexEquiv (TopCat.of X) n s.val)
  have hK : IsCompact K := isCompact_iUnion (fun s =>
    isCompact_range (simplexEquiv (TopCat.of X) n s.val).continuous)
  obtain ⟨A, hA, hKA⟩ := P202.Topology.compactContainedInFiniteSubcomplex K hK
  obtain ⟨m, hm⟩ := finiteSubcomplex_bounded X A hA
  let P : Pair.{w} := ⟨TopCat.of X, skeletonLT X m⟩
  have hs : ∀ s, s ∉ Set.range ((TopCat.toSSet.map P.inclusion).app
      (Opposite.op ⦋n⦌)) → c s = 0 := by
    intro s hs
    by_contra hcs
    apply hs
    apply (P202.RelativeSingularChains.simplex_image P n s).mpr
    intro x
    exact hm (hKA (Set.mem_iUnion.mpr ⟨⟨s, Finsupp.mem_support_iff.mpr hcs⟩, ⟨x, rfl⟩⟩))
  obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff _
    (P202.RelativeSingularChains.simplex_injective P n) c).mpr hs
  exact ⟨m, b, hb⟩

lemma ordinaryMap_degree {Y Z : TopCat.{w}} (f : Y ⟶ Z) (n : ℕ) :
    ((ordinaryFunctor R M).map f).f (n : ℤ) ≫ (ordinaryNonnegativeIso R M Z n).hom =
      (ordinaryNonnegativeIso R M Y n).hom ≫ (chainMap R M f).f n := by
  change (HomologicalComplex.extendMap (chainMap R M f) (degreeEmbedding 0)).f _ ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by
    change (0 : ℤ) + n = n; omega)]
  simp [ordinaryNonnegativeIso]

lemma ordinaryChainSupport (n : ℤ) (c : (ordinaryComplex R M (TopCat.of X)).X n) :
    ∃ m, ∃ b : (ordinaryComplex R M (skeletalSpace X m)).X n,
      ((ordinaryFunctor R M).map (skeletonToSpace X m)).f n b = c := by
  by_cases hn : n < 0
  · refine ⟨0, 0, ?_⟩
    letI : Subsingleton ((ordinaryComplex R M (TopCat.of X)).X n) := ModuleCat.subsingleton_of_isZero
      (P202.SingularChains.ordinary_negative_chains R M (TopCat.of X) n hn)
    exact @Subsingleton.elim ((ordinaryComplex R M (TopCat.of X)).X n) inferInstance _ _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    obtain ⟨m, b, hb⟩ := finiteChainSupport X R M k ((ordinaryNonnegativeIso R M _ k).hom c)
    refine ⟨m, (ordinaryNonnegativeIso R M _ k).inv b, ?_⟩
    apply (ModuleCat.mono_iff_injective (ordinaryNonnegativeIso R M _ k).hom).mp inferInstance
    have he := congrArg (fun f => f ((ordinaryNonnegativeIso R M (skeletalSpace X m) k).inv b))
      (ordinaryMap_degree R M (skeletonToSpace X m) k)
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply] at he
    have heq : (ordinaryNonnegativeIso R M (skeletalSpace X m) k).hom
        ((ordinaryNonnegativeIso R M (skeletalSpace X m) k).inv b) = b :=
      congrArg (fun f : (complex R M (skeletalSpace X m)).X k ⟶ _ => f b)
        (ordinaryNonnegativeIso R M (skeletalSpace X m) k).inv_hom_id
    exact he.trans ((congrArg (fun b => (chainMap R M (skeletonToSpace X m)).f k b) heq).trans hb)

instance ordinarySkeletonToSpace_mono (m : ℕ) :
    Mono ((ordinaryFunctor R M).map (skeletonToSpace X m)) :=
  inferInstanceAs (Mono (inclusion (ordinaryFunctor R M)
    (⟨TopCat.of X, skeletonLT X m⟩ : Pair.{w})))

section ConcreteCycles
variable {R : Type u} [CommRing R]
variable {ι : Type*} {c : ComplexShape ι}
variable (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι)

lemma boundary_of_class_zero (z : K.cycles i) (hz : K.homologyπ i z = 0) :
    ∃ b : K.X (c.prev i), K.d (c.prev i) i b = K.iCycles i z := by
  let S := K.sc i
  have he : (ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp he z hz
  refine ⟨b, ?_⟩
  have hi := congrArg S.iCycles hb
  simp only [← ModuleCat.comp_apply, ShortComplex.toCycles_i] at hi
  change K.d (c.prev i) i b = K.iCycles i z at hi
  exact hi

lemma class_of_boundary (b : K.X (c.prev i)) (z : K.cycles i)
    (hz : K.iCycles i z = K.d (c.prev i) i b) : K.homologyπ i z = 0 := by
  let S := K.sc i
  have he : z = S.toCycles b := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    simp only [← ModuleCat.comp_apply, ShortComplex.toCycles_i]
    exact hz
  rw [he]
  exact congrArg (fun f => f b) S.toCycles_comp_homologyπ

lemma lift_cycle_of_chain {L : HomologicalComplex (ModuleCat.{v} R) c}
    (f : K ⟶ L) [Mono (f.f (c.next i))]
    (z : L.cycles i) (b : K.X i) (hb : f.f i b = L.iCycles i z) :
    ∃ y : K.cycles i, K.iCycles i y = b ∧ cyclesMap f i y = z := by
  have hb0 : K.d i (c.next i) b = 0 := by
    apply (ModuleCat.mono_iff_injective (f.f (c.next i))).mp inferInstance
    rw [map_zero]
    have hf := congrArg (fun a => a b) (f.comm i (c.next i))
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hb] at hf
    have hz := congrArg (fun a => a z) (L.iCycles_d i (c.next i))
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hf.symm.trans hz
  let y := (K.sc i).cyclesMk b hb0
  have hy : K.iCycles i y = b := (K.sc i).i_cyclesMk b hb0
  refine ⟨y, hy, ?_⟩
  apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
  have hf := congrArg (fun a => a y) (cyclesMap_i f i)
  simp only [ModuleCat.comp_apply, hy] at hf
  exact hf.trans hb

end ConcreteCycles

lemma ordinaryInclusion_toSpace {a b : ℕ} (h : a ≤ b) :
    (ordinaryFunctor R M).map (skeletonInclusion X h) ≫
      (ordinaryFunctor R M).map (skeletonToSpace X b) =
      (ordinaryFunctor R M).map (skeletonToSpace X a) := by
  rw [← Functor.map_comp, skeletonInclusion_toSpace]

lemma homologyInclusion_toSpace (n : ℤ) {a b : ℕ} (h : a ≤ b) :
    (homologyFunctor R M n).map (skeletonInclusion X h) ≫
      (homologyFunctor R M n).map (skeletonToSpace X b) =
      (homologyFunctor R M n).map (skeletonToSpace X a) := by
  rw [← Functor.map_comp, skeletonInclusion_toSpace]

lemma cycleSupport (n : ℤ) (z : (ordinaryComplex R M (TopCat.of X)).cycles n) :
    ∃ m, ∃ y : (ordinaryComplex R M (skeletalSpace X m)).cycles n,
      cyclesMap ((ordinaryFunctor R M).map (skeletonToSpace X m)) n y = z := by
  obtain ⟨m, b, hb⟩ := ordinaryChainSupport X R M n
    ((ordinaryComplex R M (TopCat.of X)).iCycles n z)
  obtain ⟨y, _, hy⟩ := lift_cycle_of_chain (ordinaryComplex R M (skeletalSpace X m)) n
    ((ordinaryFunctor R M).map (skeletonToSpace X m)) z b hb
  exact ⟨m, y, hy⟩

lemma homologySupport (n : ℤ) (a : homology R M (TopCat.of X) n) :
    ∃ m, ∃ b : homology R M (skeletalSpace X m) n,
      (homologyFunctor R M n).map (skeletonToSpace X m) b = a := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryComplex R M (TopCat.of X)).homologyπ n)).mp inferInstance a
  obtain ⟨m, y, hy⟩ := cycleSupport X R M n z
  refine ⟨m, (ordinaryComplex R M (skeletalSpace X m)).homologyπ n y, ?_⟩
  have he := congrArg (fun f => f y)
    (homologyπ_naturality ((ordinaryFunctor R M).map (skeletonToSpace X m)) n)
  simp only [ModuleCat.comp_apply] at he
  exact he.trans ((congrArg ((ordinaryComplex R M (TopCat.of X)).homologyπ n) hy).trans hz)

lemma skeletonToSpace_surjective (n m : ℕ) (hm : n+2 ≤ m) :
    Function.Surjective ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X m)) := by
  intro a
  obtain ⟨k, b, hb⟩ := homologySupport X R M (n : ℤ) a
  let j := max k m
  let q := (homologyFunctor R M (n : ℤ)).map
    (skeletonInclusion X (show m ≤ j from le_max_right _ _))
  haveI : IsIso q := skeletonInclusion_isIso X R M n m j hm (le_max_right _ _)
  let u := (homologyFunctor R M (n : ℤ)).map
    (skeletonInclusion X (show k ≤ j from le_max_left _ _)) b
  refine ⟨inv q u, ?_⟩
  have heq : q (inv q u) = u := congrArg (fun f => f u) (IsIso.inv_hom_id q)
  have he := congrArg (fun f => f (inv q u))
    (homologyInclusion_toSpace X R M (n : ℤ) (show m ≤ j from le_max_right _ _))
  have hk := congrArg (fun f => f b)
    (homologyInclusion_toSpace X R M (n : ℤ) (show k ≤ j from le_max_left _ _))
  change (homologyFunctor R M (n : ℤ)).map (skeletonToSpace X j) (q (inv q u)) = _ at he
  exact he.symm.trans ((congrArg
    ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X j)) heq).trans (hk.trans hb))

lemma skeletonToSpace_injective (n m : ℕ) (hm : n+2 ≤ m) :
    Function.Injective ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X m)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  let K := ordinaryComplex R M (skeletalSpace X m)
  let L := ordinaryComplex R M (TopCat.of X)
  let f := (ordinaryFunctor R M).map (skeletonToSpace X m)
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance a
  have hz0 : L.homologyπ (n : ℤ) (cyclesMap f (n : ℤ) z) = 0 := by
    have he := congrArg (fun g => g z) (homologyπ_naturality f (n : ℤ))
    simp only [ModuleCat.comp_apply] at he
    exact he.symm.trans ((congrArg (homologyMap f (n : ℤ)) hz).trans ha)
  obtain ⟨b, hb⟩ := boundary_of_class_zero L (n : ℤ) (cyclesMap f (n : ℤ) z) hz0
  obtain ⟨k, b', hb'⟩ := ordinaryChainSupport X R M
    ((ComplexShape.down ℤ).prev (n : ℤ)) b
  let j := max k m
  let g := (ordinaryFunctor R M).map
    (skeletonInclusion X (show m ≤ j from le_max_right _ _))
  let t := (ordinaryFunctor R M).map
    (skeletonInclusion X (show k ≤ j from le_max_left _ _))
  let r := (ordinaryFunctor R M).map (skeletonToSpace X j)
  have hgr : g ≫ r = f := ordinaryInclusion_toSpace X R M (le_max_right _ _)
  have htr : t ≫ r = (ordinaryFunctor R M).map (skeletonToSpace X k) :=
    ordinaryInclusion_toSpace X R M (le_max_left _ _)
  have hbound : (ordinaryComplex R M (skeletalSpace X j)).iCycles (n : ℤ)
      (cyclesMap g (n : ℤ) z) =
      (ordinaryComplex R M (skeletalSpace X j)).d
        ((ComplexShape.down ℤ).prev (n : ℤ)) (n : ℤ)
        (t.f ((ComplexShape.down ℤ).prev (n : ℤ)) b') := by
    apply (ModuleCat.mono_iff_injective (r.f (n : ℤ))).mp inferInstance
    have hi := congrArg (fun v => v z) (cyclesMap_i g (n : ℤ))
    have hfi := congrArg (fun v => v z) (cyclesMap_i f (n : ℤ))
    have hg := congrArg (fun v => v.f (n : ℤ) (K.iCycles (n : ℤ) z)) hgr
    have ht := congrArg (fun v => v.f ((ComplexShape.down ℤ).prev (n : ℤ)) b') htr
    have hd := congrArg (fun v => v (t.f ((ComplexShape.down ℤ).prev (n : ℤ)) b'))
      (r.comm ((ComplexShape.down ℤ).prev (n : ℤ)) (n : ℤ))
    simp only [ModuleCat.comp_apply, HomologicalComplex.comp_f] at hi hfi hg ht hd
    exact (congrArg (r.f (n : ℤ)) hi).trans (hg.trans (hfi.symm.trans
      (hb.symm.trans ((congrArg (L.d ((ComplexShape.down ℤ).prev (n : ℤ)) (n : ℤ))
        (ht.trans hb')).symm.trans hd))))
  have hc := class_of_boundary (ordinaryComplex R M (skeletalSpace X j)) (n : ℤ)
    (t.f ((ComplexShape.down ℤ).prev (n : ℤ)) b') (cyclesMap g (n : ℤ) z) hbound
  have hn := congrArg (fun v => v z) (homologyπ_naturality g (n : ℤ))
  simp only [ModuleCat.comp_apply] at hn
  haveI : IsIso (homologyMap g (n : ℤ)) :=
    skeletonInclusion_isIso X R M n m j hm (le_max_right _ _)
  apply (ModuleCat.mono_iff_injective (homologyMap g (n : ℤ))).mp inferInstance
  rw [map_zero]
  exact (congrArg (homologyMap g (n : ℤ)) hz.symm).trans (hn.trans hc)

theorem skeletalStabilization :
    ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
      (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
      (n m : ℕ), n + 2 ≤ m →
      IsIso ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X m)) := by
  intro X _ _ R _ M _ _ n m hm
  haveI : Mono ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X m)) :=
    (ModuleCat.mono_iff_injective _).mpr (skeletonToSpace_injective X R M n m hm)
  haveI : Epi ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X m)) :=
    (ModuleCat.epi_iff_surjective _).mpr (skeletonToSpace_surjective X R M n m hm)
  exact isIso_of_mono_of_epi _

/-- Absolute skeletal classes inject into cellular chains. -/
abbrev skeletalProjection (n : ℕ) :=
  homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)

abbrev skeletalBoundary (n : ℕ) :=
  pairConnecting R M (skeletalPair X (n+1)) n ≫
    (homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1))

abbrev skeletalAdvance (n : ℕ) :=
  (homologyFunctor R M (n : ℤ)).map (skeletonInclusion X (Nat.le_succ (n+1)))

instance skeletalProjection_mono (n : ℕ) : Mono (skeletalProjection X R M n) := by
  have hz := ((homologyFunctor R M (n : ℤ)).mapIso (lowerIso X n)).isZero_iff.mpr
    (skeletalVanishing X R M n n le_rfl)
  exact ((skeletalShortExact X R M n).homology_exact₂ (n : ℤ)).mono_g (hz.eq_zero_of_src _)

lemma skeletalBoundary_projection (n : ℕ) :
    skeletalBoundary X R M n ≫ skeletalProjection X R M n = differential X R M n := rfl

lemma skeletalBoundary_advance (n : ℕ) :
    skeletalBoundary X R M n ≫ skeletalAdvance X R M n = 0 := by
  dsimp only [skeletalBoundary, skeletalAdvance]
  rw [Category.assoc, ← Functor.map_comp, lowerMap_step]
  rw [pairConnecting_eq R M _ _ (P202.RelativeSingularChains.ordinary_short_exact R M _)]
  exact (skeletalShortExact X R M (n+1)).δ_comp _ _ _

instance skeletalAdvance_epi (n : ℕ) : Epi (skeletalAdvance X R M n) := by
  have hz := P202.Homology.cellularRelativeVanishing X R M (n+1) n (by omega)
  haveI : Epi (homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X (n+1))) (n : ℤ)) :=
    ((skeletalShortExact X R M (n+1)).homology_exact₂ (n : ℤ)).epi_f (hz.eq_zero_of_tgt _)
  have he : (homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1)) ≫
      skeletalAdvance X R M n =
      homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X (n+1))) (n : ℤ) := by
    rw [← Functor.map_comp, lowerMap_step]; rfl
  haveI : Epi ((homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1)) ≫
      skeletalAdvance X R M n) := by rw [he]; infer_instance
  exact epi_of_epi ((homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1))) _

lemma skeletalBoundary_advance_exact (n : ℕ) :
    (ShortComplex.mk (skeletalBoundary X R M n) (skeletalAdvance X R M n)
      (skeletalBoundary_advance X R M n)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro a ha
  let q := (homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1))
  have hq : q (inv q a) = a := congrArg (fun f => f a) (IsIso.inv_hom_id q)
  have hi : homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X (n+1))) (n : ℤ)
      (inv q a) = 0 := by
    have he : q ≫ skeletalAdvance X R M n =
        homologyMap (inclusion (ordinaryFunctor R M) (skeletalPair X (n+1))) (n : ℤ) := by
      rw [← Functor.map_comp, lowerMap_step]; rfl
    exact (congrArg (fun f => f (inv q a)) he).symm.trans
      ((congrArg (skeletalAdvance X R M n) hq).trans ha)
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((skeletalShortExact X R M (n+1)).homology_exact₁ ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp))
    (inv q a) hi
  refine ⟨b, ?_⟩
  have he : pairConnecting R M (skeletalPair X (n+1)) n b = inv q a := by
    rw [pairConnecting_eq R M _ _ (P202.RelativeSingularChains.ordinary_short_exact R M _)]
    exact hb
  exact (congrArg q he).trans hq

/-- A window with explicit incoming degree, avoiding any choice of `prev`. -/
abbrev cellularWindow (n : ℕ) :=
  (cellularComplex X R M).sc' (n+1) n ((ComplexShape.down ℕ).next n)

lemma projection_window_zero (n : ℕ) :
    skeletalProjection X R M n ≫ (cellularWindow X R M n).g = 0 := by
  cases n with
  | zero =>
    change skeletalProjection X R M 0 ≫ (cellularComplex X R M).d 0 _ = 0
    rw [(cellularComplex X R M).shape 0 _ (by simp), comp_zero]
  | succ n =>
    change skeletalProjection X R M (n+1) ≫ (cellularComplex X R M).d (n+1)
      ((ComplexShape.down ℕ).next (n+1)) = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n+1) n by simp)]
    simp only [cellularComplex, ChainComplex.of_d]
    change skeletalProjection X R M (n+1) ≫ differential X R M n = 0
    dsimp only [differential, skeletalProjection]
    rw [← Category.assoc, ← Category.assoc, projection_pairConnecting]
    simp

lemma projection_window_exact (n : ℕ) :
    (ShortComplex.mk (skeletalProjection X R M n) (cellularWindow X R M n).g
      (projection_window_zero X R M n)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro a ha
  cases n with
  | zero =>
    haveI := P202.Homology.zeroSkeleton_projection_isIso X R M
    exact (ModuleCat.epi_iff_surjective (skeletalProjection X R M 0)).mp inferInstance a
  | succ n =>
    have hh : differential X R M n a = 0 := by
      change (cellularComplex X R M).d (n+1) ((ComplexShape.down ℕ).next (n+1)) a = 0 at ha
      rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n+1) n by simp)] at ha
      simpa only [cellularComplex, ChainComplex.of_d] using ha
    have hc : pairConnecting R M (skeletalPair X (n+1)) n a = 0 := by
      have h := (ModuleCat.mono_iff_injective (skeletalProjection X R M n)).mp inferInstance
        (hh.trans (map_zero _).symm)
      exact (ModuleCat.mono_iff_injective
        ((homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1)))).mp inferInstance
          (h.trans (map_zero _).symm)
    rw [pairConnecting_eq R M _ _ (P202.RelativeSingularChains.ordinary_short_exact R M _)] at hc
    exact (ShortComplex.moduleCat_exact_iff _).mp
      ((skeletalShortExact X R M (n+1)).homology_exact₃ ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)) a hc

private def cokernel_isColimit_congr
    {A B H : ModuleCat.{v} R} {f g : A ⟶ B} (h : f = g) (π : B ⟶ H)
    (wf : f ≫ π = 0) (wg : g ≫ π = 0)
    (hg : IsColimit (CokernelCofork.ofπ π wg)) :
    IsColimit (CokernelCofork.ofπ π wf) := by
  subst g
  exact hg

def windowKernel (n : ℕ) : IsLimit (KernelFork.ofι (skeletalProjection X R M n)
    (projection_window_zero X R M n)) :=
  (projection_window_exact X R M n).fIsKernel

lemma windowKernel_lift (n : ℕ) :
    (windowKernel X R M n).lift
      (KernelFork.ofι (cellularWindow X R M n).f (cellularWindow X R M n).zero) =
      skeletalBoundary X R M n := by
  apply (cancel_mono (skeletalProjection X R M n)).mp
  have hfac := (windowKernel X R M n).fac
    (KernelFork.ofι (cellularWindow X R M n).f (cellularWindow X R M n).zero)
      WalkingParallelPair.zero
  change (windowKernel X R M n).lift
      (KernelFork.ofι (cellularWindow X R M n).f (cellularWindow X R M n).zero) ≫
      skeletalProjection X R M n = (cellularWindow X R M n).f at hfac
  refine hfac.trans ?_
  change (cellularComplex X R M).d (n+1) n = differential X R M n
  simp only [cellularComplex, ChainComplex.of_d]

/-- The two skeletal exact sequences are respectively the kernel and cokernel
in the homology data for this SAME cellular differential. Explicit fields
keep the objects and maps transparent independently of the exactness proofs. -/
def windowData (n : ℕ) : (cellularWindow X R M n).LeftHomologyData where
  K := homology R M (skeletalSpace X (n+1)) (n : ℤ)
  H := homology R M (skeletalSpace X (n+2)) (n : ℤ)
  i := skeletalProjection X R M n
  π := skeletalAdvance X R M n
  wi := projection_window_zero X R M n
  hi := windowKernel X R M n
  wπ := by
    rw [windowKernel_lift]
    exact skeletalBoundary_advance X R M n
  hπ := cokernel_isColimit_congr R (windowKernel_lift X R M n) _ _
    (skeletalBoundary_advance X R M n)
    (skeletalBoundary_advance_exact X R M n).gIsCokernel

def windowChange (n : ℕ) : (cellularComplex X R M).sc n ≅ cellularWindow X R M n :=
  (cellularComplex X R M).isoSc' (n+1) n ((ComplexShape.down ℕ).next n)
    ((ComplexShape.down ℕ).prev_eq'
      (show (ComplexShape.down ℕ).Rel (n+1) n by simp)) rfl

/-- The canonical isomorphism at the (n+1)-skeleton, before passage to X. -/
def finiteStageComparison (n : ℕ) :
    (cellularComplex X R M).homology n ≅ homology R M (skeletalSpace X (n+2)) (n : ℤ) :=
  ShortComplex.homologyMapIso (windowChange X R M n) ≪≫ (windowData X R M n).homologyIso

section Natural
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  [CWStructure X] [CWStructure Y]

lemma projection_natural (f : CellularMap X Y) (n : ℕ) :
    skeletalProjection X R M n ≫ cellularDegreeMap R M f n =
      (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+1)) ≫ skeletalProjection Y R M n := by
  change homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) _ ≫
      homologyMap (relativeMap (ordinaryFunctor R M) (f.onPair n)) _ =
    homologyMap ((ordinaryFunctor R M).map (f.onSkeleton (n+1))) _ ≫
      homologyMap (projection (ordinaryFunctor R M) (skeletalPair Y n)) _
  rw [← homologyMap_comp, ← homologyMap_comp, projection_map]
  rfl

lemma advance_natural (f : CellularMap X Y) (n : ℕ) :
    skeletalAdvance X R M n ≫ (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+2)) =
      (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+1)) ≫ skeletalAdvance Y R M n := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

def windowMapData (f : CellularMap X Y)
    (F : cellularComplex X R M ⟶ cellularComplex Y R M)
    (hF : ∀ n, F.f n = cellularDegreeMap R M f n) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' _ _ (n+1) n ((ComplexShape.down ℕ).next n)).map F)
      (windowData X R M n) (windowData Y R M n) where
  φK := (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+1))
  φH := (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+2))
  commi := by
    change _ = skeletalProjection X R M n ≫ F.f n
    rw [hF]
    exact (projection_natural R M f n).symm
  commf' := by
    apply (cancel_mono (windowData Y R M n).i).mp
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    change (windowData X R M n).f' ≫
      (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+1)) ≫ skeletalProjection Y R M n = _
    rw [← projection_natural R M f n, ← hF n, ← Category.assoc]
    change ((windowData X R M n).f' ≫ (windowData X R M n).i) ≫ F.f n = _
    rw [ShortComplex.LeftHomologyData.f'_i]
    exact (F.comm (n+1) n).symm
  commπ := advance_natural R M f n

lemma finiteStageComparison_natural (f : CellularMap X Y)
    (F : cellularComplex X R M ⟶ cellularComplex Y R M)
    (hF : ∀ n, F.f n = cellularDegreeMap R M f n) (n : ℕ) :
    homologyMap F n ≫ (finiteStageComparison Y R M n).hom =
      (finiteStageComparison X R M n).hom ≫
        (homologyFunctor R M (n : ℤ)).map (f.onSkeleton (n+2)) := by
  let φ := (shortComplexFunctor' _ _ (n+1) n ((ComplexShape.down ℕ).next n)).map F
  have hn := (natIsoSc' (ModuleCat.{max v w} R) (ComplexShape.down ℕ)
    (n+1) n ((ComplexShape.down ℕ).next n)
    ((ComplexShape.down ℕ).prev_eq' (by simp)) rfl).hom.naturality F
  have hh := congrArg (fun g => ShortComplex.homologyMap g) hn
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at hh
  change homologyMap F n ≫ ShortComplex.homologyMap (windowChange Y R M n).hom =
    ShortComplex.homologyMap (windowChange X R M n).hom ≫ ShortComplex.homologyMap φ at hh
  dsimp only [finiteStageComparison, Iso.trans_hom, ShortComplex.homologyMapIso_hom]
  rw [← Category.assoc, hh, Category.assoc, (windowMapData R M f F hF n).homologyMap_comm]
  rfl

end Natural

lemma windowChange_middle (n : ℕ) : (windowChange X R M n).hom.τ₂ =
    𝟙 ((cellularComplex X R M).X n) := rfl

lemma windowChange_cycles_i (n : ℕ) :
    ShortComplex.cyclesMap (windowChange X R M n).hom ≫ (cellularWindow X R M n).iCycles =
      (cellularComplex X R M).iCycles n := by
  have h := ShortComplex.cyclesMap_i (windowChange X R M n).hom
  change _ = (cellularComplex X R M).iCycles n ≫ (windowChange X R M n).hom.τ₂ at h
  exact h.trans ((congrArg (fun f => (cellularComplex X R M).iCycles n ≫ f)
    (windowChange_middle X R M n)).trans (Category.comp_id _))

lemma windowData_cycles_i (n : ℕ) :
    (windowData X R M n).cyclesIso.hom ≫ skeletalProjection X R M n =
      (cellularWindow X R M n).iCycles :=
  (windowData X R M n).cyclesIso_hom_comp_i

lemma window_cycle_coordinate (n : ℕ)
    (z : (cellularComplex X R M).cycles n)
    (a : homology R M (skeletalSpace X (n+1)) (n : ℤ))
    (ha : (cellularComplex X R M).iCycles n z = skeletalProjection X R M n a) :
    (windowData X R M n).cyclesIso.hom
      (ShortComplex.cyclesMap (windowChange X R M n).hom z) = a := by
  apply (ModuleCat.mono_iff_injective (skeletalProjection X R M n)).mp inferInstance
  have h : ShortComplex.cyclesMap (windowChange X R M n).hom ≫
      (windowData X R M n).cyclesIso.hom ≫ skeletalProjection X R M n =
      (cellularComplex X R M).iCycles n := by
    exact (congrArg (fun f => ShortComplex.cyclesMap (windowChange X R M n).hom ≫ f)
      (windowData_cycles_i X R M n)).trans (windowChange_cycles_i X R M n)
  exact (congrArg (fun f => f z) h).trans ha

lemma finiteStageComparison_cycle_formula (n : ℕ)
    (z : (cellularComplex X R M).cycles n) :
    (finiteStageComparison X R M n).hom ((cellularComplex X R M).homologyπ n z) =
      skeletalAdvance X R M n ((windowData X R M n).cyclesIso.hom
        (ShortComplex.cyclesMap (windowChange X R M n).hom z)) := by
  have hn := congrArg (fun f => f z)
    (ShortComplex.homologyπ_naturality (windowChange X R M n).hom)
  have hh := congrArg (fun f => f (ShortComplex.cyclesMap (windowChange X R M n).hom z))
    (windowData X R M n).homologyπ_comp_homologyIso_hom
  simp only [ModuleCat.comp_apply] at hn hh
  change (windowData X R M n).homologyIso.hom
    (ShortComplex.homologyMap (windowChange X R M n).hom
      ((cellularComplex X R M).homologyπ n z)) = _
  exact (congrArg (windowData X R M n).homologyIso.hom hn).trans hh

lemma finiteStageComparison_on_cycles (n : ℕ)
    (z : (cellularComplex X R M).cycles n)
    (a : homology R M (skeletalSpace X (n+1)) (n : ℤ))
    (ha : (cellularComplex X R M).iCycles n z = skeletalProjection X R M n a) :
    (finiteStageComparison X R M n).hom ((cellularComplex X R M).homologyπ n z) =
      skeletalAdvance X R M n a :=
  (finiteStageComparison_cycle_formula X R M n z).trans
    (congrArg (skeletalAdvance X R M n) (window_cycle_coordinate X R M n z a ha))

/-- The comparison is formed from the skeletal pair sequences and inclusion in X. -/
def comparisonIso (n : ℕ) :
    (cellularComplex X R M).homology n ≅ homology R M (TopCat.of X) (n : ℤ) := by
  haveI := skeletalStabilization X R M n (n+2) le_rfl
  exact finiteStageComparison X R M n ≪≫
    asIso ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X (n+2)))

lemma comparisonIso_natural {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (f : CellularMap X Y)
    (F : cellularComplex X R M ⟶ cellularComplex Y R M)
    (hF : ∀ n, F.f n = cellularDegreeMap R M f n) (n : ℕ) :
    homologyMap F n ≫ (comparisonIso Y R M n).hom =
      (comparisonIso X R M n).hom ≫
        (homologyFunctor R M (n : ℤ)).map (TopCat.ofHom f.map) := by
  dsimp only [comparisonIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, finiteStageComparison_natural R M f F hF n]
  simp only [Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

lemma comparisonIso_on_cycles (n : ℕ)
    (z : (cellularComplex X R M).cycles n)
    (a : homology R M (skeletalSpace X (n+1)) (n : ℤ))
    (ha : (cellularComplex X R M).iCycles n z = skeletalProjection X R M n a) :
    (comparisonIso X R M n).hom ((cellularComplex X R M).homologyπ n z) =
      (homologyFunctor R M (n : ℤ)).map (skeletonToSpace X (n+1)) a := by
  change (homologyFunctor R M (n : ℤ)).map (skeletonToSpace X (n+2))
    ((finiteStageComparison X R M n).hom ((cellularComplex X R M).homologyπ n z)) = _
  exact (congrArg ((homologyFunctor R M (n : ℤ)).map (skeletonToSpace X (n+2)))
    (finiteStageComparison_on_cycles X R M n z a ha)).trans
      (congrArg (fun f => f a) (homologyInclusion_toSpace X R M (n : ℤ) (Nat.le_succ (n+1))))

theorem comparison : Expected.comparison.{u,v,w} := by
  intro R _ M _ _
  refine ⟨fun X _ _ n => comparisonIso X R M n, ?_, ?_⟩
  · intro X Y _ _ _ _ f F hF n
    exact comparisonIso_natural R M f F hF n
  · intro X _ _ n z a ha
    exact comparisonIso_on_cycles X R M n z a ha

end P202.Homology.CellularComparison
