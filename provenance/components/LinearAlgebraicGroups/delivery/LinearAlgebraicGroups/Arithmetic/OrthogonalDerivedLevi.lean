import Specs.LinearAlgebraicGroups.Arithmetic.OrthogonalDerivedLevi
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
import LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import LinearAlgebraicGroups.Arithmetic.LabelledSplitRankOneProduct
import LinearAlgebraicGroups.Arithmetic.OrthogonalLeviFactorDisplacement
import LinearAlgebraicGroups.Arithmetic.DerivedProjectionDescent
import LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open WithConv

universe u

set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.OrthogonalDerivedLevi

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive IsTorus)
open Pinning (AttachedDatum SplitBorelPair)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup FactorsThrough commutatorMap)
open SimpleRoots (evaluate)
open StandardParabolicLevi (HasFace)
open CocharacterDynamics (LimitDecomposition)

open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private normalSubgroup_of_iso from LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private comp_commutatorMap from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private face_values evaluate_root from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private subgroupIso from LinearAlgebraicGroups.Reductive.CentralDerived
open private splitTorus_baseChange from LinearAlgebraicGroups.Classification.CentralIsogenies

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- A cocharacter on the empty face is regular. Its Levi is therefore the
specified split maximal torus, so the compared Levi is a torus over the
ground field. -/
private theorem torus_of_empty_face [IsGalois F K] {P : SplitBorelPair F}
    (D : AttachedDatum P) {G : AffineAlgebraicGroup F} {c : Cocharacter G.val}
    (M : LimitDecomposition c) {d : Cocharacter P.T.group}
    (M₀ : LimitDecomposition (d ≫ P.T.inclusion))
    (b : (groupBaseChange F K).obj M₀.centralizer.group ≅
      (groupBaseChange F K).obj M.centralizer.group)
    (hd : letI := D.comm; HasFace D.base ∅ d) :
    IsTorus M.centralizer.group := by
  letI := D.comm
  have hreg : BorelsAndChambers.IsRegular P.T d := by
    intro i hi
    have hz := (face_values D.datum.rootDatum D.base ∅ (evaluate D.datum d)
      (by simp) (fun j hj => by rw [evaluate_root]; exact hd.2 j hj) i).1
    rw [evaluate_root] at hz
    have he := hz.mp hi
    simp only [Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at he
    exact D.datum.rootDatum.ne_zero i he
  obtain ⟨h, -⟩ := RootData.BorelsAndChambers.regularCocharacterBorel
    P.G P.reductive P.T P.split P.maximal d hreg M₀
  obtain ⟨e, -⟩ := subgroupIso h.1 h.2
  obtain ⟨n, ⟨s⟩⟩ := splitTorus_baseChange K P.split
  exact ⟨K, inferInstance, inferInstance, inferInstance, n,
    ⟨b.symm ≪≫ (groupBaseChange F K).mapIso e ≪≫ s⟩⟩


/-- Commutator factorization is invariant under an ambient isomorphism. -/
private theorem transported_commutator_factors {k : Type u} [Field k]
    {G H : GroupScheme k} (e : G ≅ H) {S : ClosedSubgroup G}
    (h : FactorsThrough S (commutatorMap (𝟙 G) (𝟙 G))) :
    FactorsThrough (transportSubgroup e S) (commutatorMap (𝟙 H) (𝟙 H)) := by
  obtain ⟨w, hw⟩ := h
  change G.X ⊗ G.X ⟶ S.group.X at w
  let x : H.X ⊗ H.X ⟶ G.X := fst H.X H.X ≫ e.inv.hom.hom
  let y : H.X ⊗ H.X ⟶ G.X := snd H.X H.X ≫ e.inv.hom.hom
  refine ⟨lift x y ≫ w, ?_⟩
  have hw' : w ≫ S.inclusion.hom.hom = commutatorMap (𝟙 G) (𝟙 G) := hw
  change (lift x y ≫ w) ≫ (S.inclusion.hom.hom ≫ e.hom.hom.hom) = _
  rw [← Category.assoc (lift x y ≫ w), Category.assoc (lift x y) w, hw', comp_commutatorMap]
  have hG : (𝟙 G : G ⟶ G).hom.hom = 𝟙 G.X := rfl
  have hH : (𝟙 H : H ⟶ H).hom.hom = 𝟙 H.X := rfl
  have he₀ : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X :=
    ((Grp.forget (SchemeOver k)).mapIso e).inv_hom_id
  have he (v : H.X ⊗ H.X ⟶ H.X) :
      (v ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = v := by
    rw [Category.assoc, he₀, Category.comp_id]
  simp only [hG, hH, MonObj.mul_comp, GrpObj.inv_comp, commutatorElement_def,
    Category.comp_id, x, y, he, commutatorMap]

/-- Transporting the smallest normal subgroup through an isomorphism preserves
the defining commutator property. -/
private theorem transported_derived {k : Type u} [Field k] {G H : GroupScheme k}
    (e : G ≅ H) {S : ClosedSubgroup G} (h : IsDerivedSubgroup S) :
    IsDerivedSubgroup (transportSubgroup e S) := by
  refine ⟨normalSubgroup_of_iso e.symm (Iso.refl _) (by simp [transportSubgroup]) h.1,
    transported_commutator_factors e h.2.1, ?_⟩
  intro N hN hw
  let N' := transportSubgroup e.symm N
  obtain ⟨f, hf⟩ := h.2.2 N'
    (normalSubgroup_of_iso e (Iso.refl _) (by simp [N', transportSubgroup]) hN)
    (transported_commutator_factors e.symm hw)
  change S.group ⟶ N.group at f
  refine ⟨f, ?_⟩
  change f ≫ N.inclusion ≫ e.inv = S.inclusion at hf
  change f ≫ N.inclusion = S.inclusion ≫ e.hom
  calc
    f ≫ N.inclusion = (f ≫ N.inclusion ≫ e.inv) ≫ e.hom := by
      rw [Category.assoc f (N.inclusion ≫ e.inv), Category.assoc N.inclusion,
        e.inv_hom_id, Category.comp_id]
    _ = S.inclusion ≫ e.hom := by rw [hf]

open Specs.Unipotent (closedSubgroupAlgebraicGroup)

/-- The isomorphism of the extended Levis induces the isomorphism of their
actual extended derived subgroups, with the expected inclusion square. -/
private theorem compared_derived {L₀ L : AffineAlgebraicGroup F}
    (h₀ : IsReductive L₀) (h : IsReductive L)
    (b : (groupBaseChange F K).obj L₀.val ≅ (groupBaseChange F K).obj L.val)
    {H₀ : ClosedSubgroup L₀.val} (hs₀ : IsDerivedSubgroup H₀)
    {H : ClosedSubgroup L.val} (hs : IsDerivedSubgroup H) :
    ∃ e : (groupBaseChange F K).obj H₀.group ≅ (groupBaseChange F K).obj H.group,
      e.hom ≫ (groupBaseChange F K).map H.inclusion =
        (groupBaseChange F K).map H₀.inclusion ≫ b.hom := by
  obtain ⟨hH₀, hd₀, -⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange
    K L₀ H₀ hs₀ h₀.1 h₀.2.1
  obtain ⟨hH, hd, -⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange
    K L H hs h.1 h.2.1
  exact LinearAlgebraicGroups.SchemeDerivedGroup.normalClosure_unique
    (transported_derived b hd₀) hd


section RootLattices

open RootPairing

/-- Off-diagonal Cartan entries vanish on this face. Reflecting a root in a
selected simple root changes exactly its coefficient in that direction. The
sign condition on the simple coefficients forces every face root to lie in
one rank-one component. -/
private theorem root_of_orthogonal_face {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (Q : RootPairing Idx ℤ X Y) [Q.IsReduced] (b : Q.Base) {J : Set Idx}
    (hJ : J ⊆ b.support) (hpair : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Q.pairing i j = 0)
    {α : Idx} (hα : Q.root α ∈ Submodule.span ℤ (Q.root '' J)) :
    ∃ j ∈ J, α = j ∨ α = Q.reflectionPerm j j := by
  classical
  obtain ⟨a, ha, hroot⟩ := (Finsupp.mem_span_image_iff_linearCombination ℤ).mp hα
  have hsupport : (a : Idx → ℤ).support ⊆ b.support := fun j hj =>
    hJ (ha (Finsupp.mem_support_iff.mpr hj))
  have hsum : (∑ j ∈ b.support, a j • Q.root j) = Q.root α :=
    (Finsupp.linearCombination_apply_of_mem_supported ℤ
      ((Finsupp.mem_supported ℤ a).mpr (fun _ hj => hJ (ha hj)))).symm.trans hroot
  have hnonempty : ∃ j ∈ J, a j ≠ 0 := by
    by_contra! hz
    apply Q.ne_zero α
    rw [← hsum]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ J
    · rw [hz j hj, zero_smul]
    · rw [show a j = 0 from Finsupp.notMem_support_iff.mp fun h => hj (ha h), zero_smul]
  obtain ⟨i, hi, hai⟩ := hnonempty
  have hsum_root : (∑ j ∈ b.support, a j • Q.root j) ∈ Set.range Q.root := ⟨α, hsum.symm⟩
  have ha_sign := b.pos_or_neg_of_sum_smul_root_mem a hsum_root hsupport
  let a' : Idx → ℤ := fun j => if j = i then -a j else a j
  have hsupport' : a'.support ⊆ b.support := by
    intro j hj
    apply hsupport
    intro h
    apply hj
    simp [a', show a j = 0 from h]
  have hreflect :
      Q.root (Q.reflectionPerm i α) = ∑ j ∈ b.support, a' j • Q.root j := by
    rw [root_reflectionPerm, ← hsum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_zsmul]
    by_cases hji : j = i
    · subst j
      simp [a', reflection_apply_self, neg_smul, smul_neg]
    · by_cases hjJ : j ∈ J
      · rw [reflection_apply_root, hpair j hjJ i hi hji, zero_smul, sub_zero]
        simp [a', hji]
      · have hz : a j = 0 := Finsupp.notMem_support_iff.mp fun h => hjJ (ha h)
        simp [a', hji, hz]
  have ha'_sign := b.pos_or_neg_of_sum_smul_root_mem a'
    ⟨Q.reflectionPerm i α, hreflect⟩ hsupport'
  have hvanish (j : Idx) (hj : j ≠ i) : a j = 0 := by
    have hi' : a' i = -a i := by simp [a']
    have hj' : a' j = a j := ite_eq_right hj
    rcases ha_sign with h₁ | h₁ <;> rcases ha'_sign with h₂ | h₂
    · have h : 0 ≤ a i := h₁.le i
      have h' : 0 ≤ a' i := h₂.le i
      rw [hi'] at h'
      omega
    · have h : 0 ≤ a j := h₁.le j
      have h' : a' j ≤ 0 := h₂.le j
      rw [hj'] at h'
      omega
    · have h : a j ≤ 0 := h₁.le j
      have h' : 0 ≤ a' j := h₂.le j
      rw [hj'] at h'
      omega
    · have h : a i ≤ 0 := h₁.le i
      have h' : a' i ≤ 0 := h₂.le i
      rw [hi'] at h'
      omega
  have he : Q.root α = a i • Q.root i := by
    rw [← hsum, Finset.sum_eq_single i]
    · intro j _ hji
      rw [hvanish j hji, zero_smul]
    · exact fun h => (h (hJ hi)).elim
  have hdep : ¬ LinearIndependent ℤ ![Q.root α, Q.root i] := by
    rw [LinearIndependent.pair_iff]
    intro h
    have hc := h 1 (-a i) (by rw [he]; simp [neg_smul])
    exact one_ne_zero hc.1
  refine ⟨i, hi, (IsReduced.eq_or_eq_neg (P := Q) α i hdep).imp (fun h => Q.root.injective h) ?_⟩
  intro h
  apply Q.root.injective
  rwa [root_reflectionPerm, reflection_apply_self]

/-- The sum of the selected coroots evaluates to two on each selected
positive root. In particular it gives a regular cocharacter of the
orthogonal subsystem. -/
private theorem pairing_coroot_sum {Idx X Y I : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Fintype I]
    (Q : RootPairing Idx ℤ X Y) (r : I → Idx)
    (horth : ∀ i j, i ≠ j → Q.pairing (r i) (r j) = 0) (i : I) :
    Q.toLinearMap (Q.root (r i)) (∑ j, Q.coroot (r j)) = 2 := by
  classical
  rw [map_sum]
  simp only [root_coroot_eq_pairing]
  rw [Finset.sum_eq_single i]
  · exact Q.pairing_same _
  · intro j _ hji
    exact horth i j hji.symm
  · simp

/-- The sublattice spanned by selected vectors in an integral basis is
saturated. A positive integral multiple detects the same coefficient support. -/
private theorem mem_basis_span_of_nsmul_mem {Idx Y : Type*} [AddCommGroup Y]
    (basis : Module.Basis Idx ℤ Y) (J : Set Idx) {n : ℕ} (hn : 0 < n) {y : Y}
    (hy : n • y ∈ Submodule.span ℤ (basis '' J)) :
    y ∈ Submodule.span ℤ (basis '' J) := by
  rw [basis.mem_span_image] at hy ⊢
  intro i hi
  apply hy
  change i ∈ (basis.repr y).support at hi
  change i ∈ (basis.repr (n • y)).support
  rw [Finsupp.mem_support_iff] at hi ⊢
  rw [map_nsmul, Finsupp.nsmul_apply, nsmul_eq_mul]
  exact mul_ne_zero (by exact_mod_cast hn.ne') hi

open Specs.GeometricRadicals (IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)

/-- For the actual torus of the simply connected split reference group the
selected simple coroots span a saturated sublattice. -/
private theorem saturated_face_coroot_span {P : SplitBorelPair F} (D : AttachedDatum P)
    (hg : IsSemisimple P.G) (hsc : GeometricallySimplyConnected P.G)
    (J : Set (Root P.T)) (hJ : letI := D.comm; J ⊆ D.base.support) :
    letI := D.comm
    ∀ (y : Additive (Cocharacter P.T.group)) (n : ℕ), 0 < n →
      n • y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' J) →
      y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' J) := by
  letI := D.comm
  let Q := D.datum.rootDatum
  let v : D.base.support → Additive (Cocharacter P.T.group) := fun i => Q.coroot i
  have hv : Set.range v = Q.coroot '' (D.base.support : Set (Root P.T)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have ht : Submodule.span ℤ (Set.range v) = ⊤ := calc
    _ = Submodule.span ℤ (Q.coroot '' (D.base.support : Set (Root P.T))) :=
      congrArg (Submodule.span ℤ) hv
    _ = Submodule.span ℤ (Set.range Q.coroot) := D.base.span_int_coroot_support
    _ = ⊤ := (Classification.SimplyConnectedLattice.latticeCriterion
      P.G hg P.T P.split P.maximal D.datum).mp hsc
  let basis : Module.Basis D.base.support ℤ (Additive (Cocharacter P.T.group)) :=
    Module.Basis.mk D.base.linearIndepOn_coroot ht.ge
  have hval (i : D.base.support) : basis i = Q.coroot i := Module.Basis.mk_apply _ _ i
  let Js := (Subtype.val : D.base.support → Root P.T) ⁻¹' J
  have hspan : Q.coroot '' J = basis '' Js := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hJ hi⟩, hi, hval _⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.val, hi, (hval i).symm⟩
  intro y n hn hy
  change n • y ∈ Submodule.span ℤ (Q.coroot '' J) at hy
  change y ∈ Submodule.span ℤ (Q.coroot '' J)
  rw [hspan] at hy ⊢
  exact mem_basis_span_of_nsmul_mem basis Js hn hy

end RootLattices

section SplitLevi

open Specs.StandardParabolicLevi (IsCommonKernelTorus leviRoots)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.BorelProper (IsParabolic)
open Specs.CharacterPairing (absoluteRoots)

open private attachedBase_regular
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private common_kernel_for_face face_common_kernel_centralizer face_levi_roots
  face_parabolic
  from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private torus_subgroupOf_centralizer
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private maximal_torus_in_intermediate_group
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private restrictSubgroup
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_commutative from LinearAlgebraicGroups.Reductive.GeneralLinearStructure

/-- Describe the actual centralizer of the given cocharacter, using the
attached datum and the fixed ambient torus. -/
private theorem split_face_levi {P : SplitBorelPair F} (D : AttachedDatum P)
    (J : Set (Root P.T)) {d : Cocharacter P.T.group}
    (M : LimitDecomposition (d ≫ P.T.inclusion))
    (hd : letI := D.comm; HasFace D.base J d) :
    letI := D.comm
    IsParabolic P.G M.parabolic ∧ IsSubgroupOf P.B M.parabolic ∧
    IsReductive (closedSubgroupAlgebraicGroup M.centralizer) ∧
    ∃ (S : ClosedSubgroup P.T.group) (T : ClosedSubgroup M.centralizer.group)
      (e : P.T.group ≅ T.group), IsCommonKernelTorus J S ∧
      IsCentralizer (subgroupOfSubgroup P.T S) M.centralizer ∧
      e.hom ≫ T.inclusion ≫ M.centralizer.inclusion = P.T.inclusion ∧
      RankOneFlag.IsGeometricallyMaximal T ∧
      absoluteRoots T = (fun α : Root P.T => e.inv ≫ α.val) '' leviRoots D.datum J := by
  letI := D.comm
  obtain ⟨c, _, hc, hb⟩ := attachedBase_regular D
  obtain ⟨S, hS, z, hz⟩ := common_kernel_for_face P.split hd
  obtain ⟨hp, hBP⟩ := face_parabolic P.reductive P.split P.maximal P.borel P.containsTorus hc hb hd M
  obtain ⟨hC, hR⟩ := face_common_kernel_centralizer P.reductive P.split P.maximal hc hb hd S hS z hz M
  obtain ⟨j, hj⟩ := torus_subgroupOf_centralizer P.split d M
  let T := restrictSubgroup P.T M.centralizer j hj
  let e : P.T.group ≅ T.group := Iso.refl _
  have he : e.hom ≫ T.inclusion ≫ M.centralizer.inclusion = P.T.inclusion := by
    change 𝟙 P.T.group ≫ j ≫ M.centralizer.inclusion = P.T.inclusion
    rw [Category.id_comp, hj]
  refine ⟨hp, hBP, hR, S, T, e, hS, hC, he, maximal_torus_in_intermediate_group hj P.maximal, ?_⟩
  exact face_levi_roots P.split hc hb hd M T e he


end SplitLevi

section CentralizerPullback

open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

/-- Centralization of a cocharacter is preserved and detected by a closed
immersion, on every test scheme. -/
private theorem centralizes_comp_closed {G H : GroupScheme F}
    (f : H ⟶ G) (hf : IsClosedImmersion f.hom.hom.left) (c : Cocharacter H)
    {Y : SchemeOver F} (y : Y ⟶ H.X) :
    Centralizes c y ↔ Centralizes (c ≫ f) (y ≫ f.hom.hom) := by
  letI := mono_over f.hom.hom hf
  rw [centralizes_iff, centralizes_iff]
  constructor
  · intro h U g z
    let m := IsMonHom.monoidHom f.hom.hom U
    have e := (h U g z).map m
    change Commute ((g ≫ y) ≫ f.hom.hom) ((z ≫ c.hom.hom) ≫ f.hom.hom) at e
    simpa only [Category.assoc, Grp.comp_hom_hom] using e
  · intro h U g z
    let m := IsMonHom.monoidHom f.hom.hom U
    apply Commute.of_map (f := m)
      (fun x y he => (cancel_mono f.hom.hom).mp he)
    change Commute ((g ≫ y) ≫ f.hom.hom) ((z ≫ c.hom.hom) ≫ f.hom.hom)
    simpa only [Category.assoc, Grp.comp_hom_hom] using h U g z

/-- The scheme centralizer inside a closed subgroup is the pullback of the
ambient centralizer of the same cocharacter. -/
private theorem limit_centralizer_pullback {G H : GroupScheme F} (f : H ⟶ G)
    (hf : IsClosedImmersion f.hom.hom.left) (c : Cocharacter H)
    (D : LimitDecomposition c) (E : LimitDecomposition (c ≫ f)) :
    ∃ i : D.centralizer.group ⟶ E.centralizer.group,
      IsPullback i D.centralizer.inclusion E.centralizer.inclusion f := by
  let C := D.centralizer
  let C' := E.centralizer
  let U := Grp.forget (SchemeOver F)
  haveI : Mono C.inclusion.hom.hom := mono_over _ C.isClosedImmersion
  haveI : Mono C'.inclusion.hom.hom := mono_over _ C'.isClosedImmersion
  haveI : Mono C.inclusion := U.mono_of_mono_map (inferInstanceAs (Mono C.inclusion.hom.hom))
  haveI : Mono C'.inclusion := U.mono_of_mono_map (inferInstanceAs (Mono C'.inclusion.hom.hom))
  have hc : Centralizes c C.inclusion.hom.hom :=
    (D.centralizer_points _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨q, hq⟩ := (E.centralizer_points _ (C.inclusion ≫ f).hom.hom).mp
    ((centralizes_comp_closed f hf c C.inclusion.hom.hom).mp hc)
  obtain ⟨i, hi⟩ := factor_group_through_subgroup C' (C.inclusion ≫ f) q hq
  refine ⟨i, IsPullback.of_isLimit' ⟨hi⟩ ?_⟩
  have hex (s : PullbackCone C'.inclusion f) :
      ∃ j : s.pt ⟶ C.group, j ≫ C.inclusion = s.snd := by
    have hs : s.fst.hom.hom ≫ C'.inclusion.hom.hom = s.snd.hom.hom ≫ f.hom.hom :=
      U.congr_map s.condition
    have h : Centralizes (c ≫ f) (s.snd.hom.hom ≫ f.hom.hom) :=
      (E.centralizer_points _ _).mpr ⟨s.fst.hom.hom, hs⟩
    obtain ⟨w, hw⟩ := (D.centralizer_points _ _).mp
      ((centralizes_comp_closed f hf c s.snd.hom.hom).mpr h)
    exact factor_group_through_subgroup C s.snd w hw
  classical
  choose l hl using hex
  refine PullbackCone.IsLimit.mk _ l ?_ (fun s => hl s) ?_
  · intro s
    apply (cancel_mono C'.inclusion).mp
    change (l s ≫ i) ≫ C'.inclusion = s.fst ≫ C'.inclusion
    rw [Category.assoc, hi, ← Category.assoc, hl, s.condition]
  · intro s m _ hm
    exact (cancel_mono C.inclusion).mp (hm.trans (hl s).symm)

end CentralizerPullback

section DerivedTorus

open Specs.GeometricRadicals (IsSplitTorus IsSemisimple)
open Specs.RankOneFlag (SameSubgroup)
open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private cocharacter_factors_through_centralizer from LinearAlgebraicGroups.Relative.LeviConjugacy
set_option backward.isDefEq.respectTransparency false
open Specs.SchemeDerivedGroup (IsSubgroupOf IsCommutative)
open Specs.StandardParabolicLevi (IsCommonKernelTorus leviRoots)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.RootGroups (rankOneWord)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private centralizer_le rootPoint_comp_vanishing
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private character_restricts_trivially from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private lattice_torus_of_split cocharacter_ext_units
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private rankOneWord_comp from LinearAlgebraicGroups.RootData.RootGroups
open private contractingKilled postMul postInv
  from LinearAlgebraicGroups.Reductive.CentralDerived
open private liftToSchemeKernel from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private baseChange_closed from LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private connectedOfGeometricallyConnected from LinearAlgebraicGroups.Reductive.CentralDerived

/-- The normalized coroot word maps to the identity in the Levi's torus
quotient, since each contracting root coordinate does. -/
private theorem coroot_killed_by_levi_quotient {P : SplitBorelPair F}
    (D : AttachedDatum P) (J : Set (Root P.T))
    (S : ClosedSubgroup P.T.group) (hS : IsCommonKernelTorus J S)
    (L : ClosedSubgroup P.G.val) (hL : IsCentralizer (subgroupOfSubgroup P.T S) L)
    (t : P.T.group ⟶ L.group) (ht : t ≫ L.inclusion = P.T.inclusion)
    (Q : AffineAlgebraicGroup F) (q : L.group ⟶ Q.val) (hQ : IsTorus Q.val) :
    letI := D.comm
    ∀ α ∈ leviRoots D.datum J, ((D.datum.rootDatum.coroot α).toMul ≫ t) ≫ q = 0 := by
  letI := D.comm
  letI := torus_commutative Q hQ
  have hcomm : IsCommutative Q.val := fun _ _ _ => mul_comm _ _
  intro α hα
  obtain ⟨C, _, _, _, U, V, _, _, _, _, A, pos, neg, _, _, _, _, w, hw⟩ :=
    D.datum.attached α
  obtain ⟨j, hj⟩ := C.kernelTorus_largest.2.2 S (lattice_torus_of_split hS.1)
    (character_restricts_trivially (D := D.datum) hS hα)
  have hsub : IsSubgroupOf (subgroupOfSubgroup P.T S)
      (subgroupOfSubgroup P.T C.kernelTorus) :=
    ⟨j, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.T.inclusion) hj)⟩
  obtain ⟨v, hv⟩ := centralizer_le hsub C.centralizes hL
  let x := pos.root.hom ≫ U.contracting.inclusion ≫ v
  let y := neg.root.hom ≫ V.contracting.inclusion ≫ v
  have hx : x ≫ q = 0 := by
    dsimp only [x]
    rw [Category.assoc, Category.assoc, contractingKilled
      (G := closedSubgroupAlgebraicGroup C.subgroup) (v ≫ q) hcomm U, comp_zero]
  have hy : y ≫ q = 0 := by
    dsimp only [y]
    rw [Category.assoc, Category.assoc, contractingKilled
      (G := closedSubgroupAlgebraicGroup C.subgroup) (v ≫ q) hcomm V, comp_zero]
  have hp (R : TestAlgebra F) (b : Rˣ) :
      cocharacterPoint w.coroot R b ≫ t.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹ := by
    letI := mono_over L.inclusion.hom.hom L.isClosedImmersion
    apply (cancel_mono L.inclusion.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, ht, w.coroot_word, postMul, postInv,
      ← rankOneWord_comp, ← rankOneWord_comp]
    simp only [x, y, Category.assoc, hv]
  rw [← hw]
  apply cocharacter_ext_units
  intro R b
  have hword (s : Rˣ) : rankOneWord x y R s ≫ q.hom.hom = 1 := by
    rw [rankOneWord, postMul, postMul, rootPoint_comp_vanishing hx,
      rootPoint_comp_vanishing hy, mul_one, mul_one]
  change ((cocharacterPoint w.coroot R b ≫ t.hom.hom) ≫ q.hom.hom) =
    unitPoint R b ≫ (1 : _ ⟶ Q.val.X)
  rw [hp, postMul, postInv, hword, hword, inv_one, mul_one, MonObj.comp_one]

open private pushCocharacters from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.CharacterDescent (StandardLattice)
open private splitPresentation latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private torsionFree_of_diagonal_torus from LinearAlgebraicGroups.RootData.RankOneFlag
open private latticeEquivOfBasis from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private splitBaseChange from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private torus_of_iso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private subgroupOf_of_sections from LinearAlgebraicGroups.Reductive.SubtorusCentralizer

/-- A smooth connected closed subgroup of a split torus is split.
Smoothness and connectedness eliminate torsion in its character group. -/
private theorem split_of_smooth_connected_closed_in_torus {S T : GroupScheme F}
    (i : S ⟶ T) (hi : IsClosedImmersion i.hom.hom.left) (hT : IsSplitTorus T)
    (hs : Smooth S.X.hom) (hc : ConnectedSpace S.X.left) : IsSplitTorus S := by
  obtain ⟨n, ⟨e⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} n
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates n).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  let U := Grp.forget (SchemeOver F) ⋙ Over.forget (Spec (CommRingCat.of F))
  haveI : IsIso e.inv.hom.hom.left := U.map_isIso e.inv
  letI := hi
  have hj : IsClosedImmersion (i ≫ e.inv).hom.hom.left :=
    IsClosedImmersion.comp _ _
  obtain ⟨N, ⟨d, _⟩, _⟩ :=
    (LinearAlgebraicGroups.DiagonalizableGroups.diagonalClosedSubgroups F M S (i ≫ e.inv)).mp hj
  let B := groupAlgebra F (M ⧸ N)
  letI : Group.FG (M ⧸ N) := Group.fg_of_surjective
    (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hB : Specs.CharacterDescent.IsMultiplicativeType B :=
    ⟨F, inferInstance, inferInstance, inferInstance,
      splitBaseChange (K := F) B ⟨⟨CommGrpCat.of (M ⧸ N), inferInstance⟩, ⟨Iso.refl _⟩⟩⟩
  let v := U.mapIso d.symm
  have hs' : Smooth (specGroup B).X.hom := by
    rw [← d.inv.hom.hom.w]
    letI := hs
    change Smooth (v.hom ≫ S.X.hom)
    infer_instance
  have hc' : ConnectedSpace (specGroup B).X.left := by
    exact v.hom.homeomorph.connectedSpace_iff.mpr hc
  have hTor := (LinearAlgebraicGroups.GeometricRadicals.torusCoordinateComparison B).mpr
    ((LinearAlgebraicGroups.SmoothnessAndIsogenies.smoothConnectedMultiplicativeType B).mpr
      ⟨hB, hs', hc'⟩)
  letI := torsionFree_of_diagonal_torus (M ⧸ N) hTor
  letI : Module.Finite ℤ (Additive (M ⧸ N)) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive (M ⧸ N))
  obtain ⟨s⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := F) m
  exact ⟨m, ⟨d ≪≫ (hopfSpec (CommRingCat.of F)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv F F (latticeEquivOfBasis b).symm)).op
      ≪≫ s⟩⟩

/-- A torus centralizes each morphism into it. -/
private theorem centralizes_through_commutative {G H V : GroupScheme F} (p : V ⟶ H)
    (i : H ⟶ G) (hH : IsCommutative H) :
    Centralizes (p ≫ i) i.hom.hom := by
  apply (centralizes_iff _ _).mpr
  intro Y g x
  have h : Commute g (x ≫ p.hom.hom) := hH Y _ _
  have h' := h.map (IsMonHom.monoidHom i.hom.hom Y)
  change Commute (g ≫ i.hom.hom) ((x ≫ p.hom.hom) ≫ i.hom.hom) at h'
  simpa only [Category.assoc, Grp.comp_hom_hom] using h' 

open private torus_commutative from LinearAlgebraicGroups.Reductive.GeneralLinearStructure in
/-- A split torus representing a cocharacter centralizer is geometrically maximal
if it contains that cocharacter. -/
private theorem maximal_of_cocharacter_centralizer {H : GroupScheme F}
    (c : Cocharacter H) (D : LimitDecomposition c)
    (hs : IsSplitTorus D.centralizer.group) : IsGeometricallyMaximal D.centralizer := by
  obtain ⟨w, hw⟩ := cocharacter_factors_through_centralizer D
  let Ω := AlgebraicClosure F
  let B := groupBaseChange F Ω
  obtain ⟨hm, hcentral⟩ := centralizerSchemeBaseChange F Ω c D.centralizer D.centralizer_points
  have hTs := lattice_torus_of_split (splitTorus_baseChange Ω hs)
  refine ⟨hm, hTs, ?_⟩
  intro T hT hST
  obtain ⟨j, hj⟩ := hST
  change B.obj D.centralizer.group ⟶ T.group at j
  change j ≫ T.inclusion = B.map D.centralizer.inclusion at hj
  have hfactor : B.map c = (B.map w ≫ j) ≫ T.inclusion := by
    calc
      B.map c = B.map (w ≫ D.centralizer.inclusion) := congrArg B.map hw.symm
      _ = B.map w ≫ B.map D.centralizer.inclusion := B.map_comp _ _
      _ = (B.map w ≫ j) ≫ T.inclusion :=
        (congrArg (B.map w ≫ ·) hj.symm).trans (Category.assoc _ _ _).symm
  apply subgroupOf_of_sections
  apply (hcentral _ _).mp
  change Centralizes (B.map c) T.inclusion.hom.hom
  rw [hfactor]
  exact centralizes_through_commutative (B.map w ≫ j) T.inclusion
    (torus_commutative hT)

/-- The derived-group intersection with a split maximal torus is a split
maximal torus when a regular cocharacter of the Levi factors through it. -/
private theorem derived_torus_of_regular {L : AffineAlgebraicGroup F} (hL : IsReductive L)
    (H : ClosedSubgroup L.val) (hH : IsDerivedSubgroup H) (T : ClosedSubgroup L.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (y : Cocharacter T.group) (hy : BorelsAndChambers.IsRegular T y)
    (c : Cocharacter H.group) (hc : c ≫ H.inclusion = y ≫ T.inclusion) :
    ∃ (S : ClosedSubgroup H.group) (p : S.group ⟶ T.group),
      IsPullback p S.inclusion T.inclusion H.inclusion ∧
      IsSplitTorus S.group ∧ IsGeometricallyMaximal S := by
  let A := closedSubgroupAlgebraicGroup (G := L) H
  have hA := reductive_of_semisimple A (Reductive.CentralDerived.derivedSemisimple L hL H hH)
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition A c
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition L (c ≫ H.inclusion)
  have he : SameSubgroup E.centralizer T := by
    revert E
    rw [hc]
    intro E
    exact (RootData.BorelsAndChambers.regularCocharacterBorel L hL T hs hm y hy E).1
  obtain ⟨e, he⟩ := subgroupIso he.1 he.2
  obtain ⟨p, hp⟩ := limit_centralizer_pullback H.inclusion H.isClosedImmersion c D E
  have hp' : IsPullback (p ≫ e.hom) D.centralizer.inclusion T.inclusion H.inclusion :=
    hp.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp]) 
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simpa only [Iso.refl_hom, Category.comp_id] using he.symm)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  have hpc : IsClosedImmersion (p ≫ e.hom).hom.hom.left :=
    MorphismProperty.of_isPullback
      ((hp'.map (Grp.forget _ ⋙ Over.forget _)).flip) H.isClosedImmersion
  letI : Smooth A.val.X.hom := hA.1
  letI : ConnectedSpace A.val.X.left := connectedOfGeometricallyConnected A hA.2.1
  have hSmooth := (CocharacterDynamics.limitSubgroupsSmooth A c D).2.2
  letI := (CocharacterDynamics.geometricallyConnectedLimitSubgroups A c D).2.2
  have hConn : ConnectedSpace D.centralizer.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.centralizer.group.X.hom
  have hSplit := split_of_smooth_connected_closed_in_torus (p ≫ e.hom) hpc hs hSmooth hConn
  exact ⟨D.centralizer, p ≫ e.hom, hp', hSplit, maximal_of_cocharacter_centralizer c D hSplit⟩


open Specs.QuasiSplitOrbitDerivedRoots (SplitFace)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private splitBorelPair semisimple_iff_corootFullRank
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private face_preimage_borel from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots

set_option maxHeartbeats 800000 in
/-- The cocharacter image of the derived maximal torus is exactly the integral
span of the selected simple coroots. -/
private theorem face_coroot_lattice {P : SplitBorelPair F} (D : AttachedDatum P)
    (J : Set (Root P.T)) (S : SplitFace D J)
    (hss : IsSemisimple P.G) (hsc : GeometricallySimplyConnected P.G)
    (hroots : letI := D.comm; ∀ α ∈ leviRoots D.datum J,
      ∃ β ∈ J, α = β ∨ α = D.datum.rootDatum.reflectionPerm β β) :
    letI := D.comm
    ∀ y : Additive (Cocharacter P.T.group),
      (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' J) := by
  letI := D.comm
  have hS := Reductive.CentralDerived.derivedSemisimple (closedSubgroupAlgebraicGroup S.levi)
    S.reductive S.derived S.isDerived
  let Q := splitBorelPair S.group (reductive_of_semisimple S.group hS)
    S.torus S.torusSplit S.torusMaximal
  let E := Classification.Pinning.attachedDatum Q
  letI := E.comm
  letI : IsCommMonObj S.torus.group.X := E.comm
  letI := E.datum.freeCocharacters
  letI := E.datum.finiteCocharacters
  let f := pushCocharacters S.toAmbientTorus
  let C := corootLattice E
  let M := Submodule.span ℤ (D.datum.rootDatum.coroot '' J)
  have hM : M ≤ f.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    have hα' : α ∈ leviRoots D.datum J := Submodule.subset_span ⟨α, hα, rfl⟩
    obtain ⟨c, hc⟩ := QuasiSplitOrbitDerivedRoots.faceCorootFactors D J S α hα'
    exact ⟨Additive.ofMul c, Additive.toMul.injective hc⟩
  have hC : C ≤ M.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, rfl⟩
    obtain ⟨α, hα, ha⟩ := QuasiSplitOrbitDerivedRoots.faceRootRestrictionSurjective D J S β.property
    change S.toAmbientTorus ≫ α.val = β.val at ha
    have hb : S.toAmbientTorus ≫ α.val ∈ CharacterPairing.absoluteRoots S.torus :=
      ha.symm ▸ β.property
    have ha' : β = ⟨S.toAmbientTorus ≫ α.val, hb⟩ :=
      Subtype.ext ha.symm
    have hf : f (E.datum.rootDatum.coroot β) = D.datum.rootDatum.coroot α := by
      apply Additive.toMul.injective
      rw [ha']
      exact QuasiSplitOrbitDerivedRoots.faceAttachedCoroots D J S α hα _ _ (E.datum.attached _)
    change f (E.datum.rootDatum.coroot β) ∈ M
    rw [hf]
    obtain ⟨j, hj, h | h⟩ := hroots α hα
    · subst α
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    · rw [h, RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]
      exact M.neg_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
  letI : Finite (Additive (Cocharacter Q.T.group) ⧸ C) :=
    (Submodule.finiteQuotient_iff C).mpr ((semisimple_iff_corootFullRank Q E).mp hS)
  intro y
  constructor
  · rintro ⟨c, hc⟩
    let x : Additive (Cocharacter Q.T.group) := Additive.ofMul c
    let n := addOrderOf (C.mkQ x)
    have hn : 0 < n := addOrderOf_pos _
    have hnx : n • x ∈ C := by
      apply (Submodule.Quotient.mk_eq_zero C).mp
      change C.mkQ (n • x) = 0
      rw [map_nsmul, addOrderOf_nsmul_eq_zero]
    have hxy : f x = y := Additive.toMul.injective hc
    have hm : n • y ∈ M := by
      have h := hC hnx
      change f (n • x) ∈ M at h
      rwa [map_nsmul, hxy] at h
    exact saturated_face_coroot_span D hss hsc J S.simple y n hn hm
  · intro hy
    obtain ⟨c, hc⟩ := hM hy
    exact ⟨c.toMul, congrArg Additive.toMul hc⟩


end DerivedTorus

section DerivedBorel

open Specs.GeometricRadicals (IsSplitTorus IsMaximalTorus IsSemisimple)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsQuasiSplit subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.StandardParabolicLevi (IsCommonKernelTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private subgroupPreimage subgroupPreimage_pullback borel_of_compared_subgroups
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private extendSubgroup extend_subgroupOf borel_of_same lattice_torus_of_split
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroup_of_intersection conjugate_le_of_normal
  from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private inclusion_mono subgroupOfSubgroup_le
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private extendedBorel from LinearAlgebraicGroups.Descent.BorelInnerAlignment
open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter
open private connectedOfGeometricallyConnected from LinearAlgebraicGroups.Reductive.CentralDerived
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private subgroupOf_of_sections from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private conjugationIso conjugation conjugation_apply
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private borelUnderIso from LinearAlgebraicGroups.Relative.ParabolicIntersection
open private torus_commutative from LinearAlgebraicGroups.Reductive.GeneralLinearStructure

set_option backward.isDefEq.respectTransparency false

private theorem maximal_of_self_centralizer {G : GroupScheme F} {T : ClosedSubgroup G}
    (ht : IsTorus T.group) (hc : IsCentralizer T T) : IsMaximalTorus T := by
  refine ⟨ht, ?_⟩
  intro S hs hTS
  obtain ⟨i, hi⟩ := hTS
  apply subgroupOf_of_sections
  apply (hc _ _).mp
  rw [← hi]
  exact centralizes_through_commutative i S.inclusion (torus_commutative hs)

private theorem extended_maximal_torus {Ω : Type u} [Field Ω] [Algebra F Ω]
    (G : AffineAlgebraicGroup F) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (ht : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T) :
    IsMaximalTorus (extendSubgroup Ω T) := by
  have hC := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T
    (lattice_torus_of_split ht) hm
  obtain ⟨_, hC'⟩ := centralizerSchemeBaseChange F Ω T.inclusion T hC
  exact maximal_of_self_centralizer (lattice_torus_of_split (splitTorus_baseChange Ω ht)) hC'

/-- The intersection with the reference Borel is a Borel in the split Levi. -/
private theorem reference_levi_borel {Ω : Type u} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (P : SplitBorelPair F) (S : ClosedSubgroup P.T.group) (hs : IsSplitTorus S.group)
    (L : ClosedSubgroup P.G.val) (hc : IsCentralizer (subgroupOfSubgroup P.T S) L) :
    IsBorel (subgroupPreimage (extendSubgroup Ω L).inclusion (extendSubgroup Ω P.B)) := by
  let G' := baseChangedAlgebraicGroup Ω P.G
  let T' := extendSubgroup Ω P.T
  let S' := extendSubgroup Ω (subgroupOfSubgroup P.T S)
  let C := extendSubgroup Ω L
  let B := extendSubgroup Ω P.B
  let W := subgroupPreimage C.inclusion B
  let hpb := subgroupPreimage_pullback C.inclusion B
  have hG := (Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := Ω) P.G P.reductive.1 P.reductive.2.1).mpr P.reductive
  have hSm : IsSubgroupOf S' T' := extend_subgroupOf ⟨S.inclusion, rfl⟩
  obtain ⟨_, hC⟩ := centralizerSchemeBaseChange F Ω (subgroupOfSubgroup P.T S).inclusion L hc
  obtain ⟨A, hA, hAb⟩ := Reductive.SubtorusCentralizer.centralizerBorel
    G' hG.1 (connectedOfGeometricallyConnected G' hG.2.1) T' S'
    (extended_maximal_torus P.G P.reductive P.T P.split P.maximal)
    (lattice_torus_of_split (splitTorus_baseChange Ω hs)) hSm C hC B
    (extendedBorel P.G P.reductive P.B P.borel Ω) (extend_subgroupOf P.containsTorus)
  have hAW : IsSubgroupOf A W := by
    obtain ⟨f, hf⟩ := (subgroup_of_intersection (H := subgroupOfSubgroup C A) hA).mp
      ⟨𝟙 _, Category.id_comp _⟩ B (by simp)
    exact ⟨hpb.lift f A.inclusion hf, hpb.lift_snd _ _ _⟩
  have hWA : IsSubgroupOf W A := by
    apply (subgroupOfSubgroup_le C W A).mp
    apply (subgroup_of_intersection hA).mpr
    intro Y hY
    have h : Y = C ∨ Y = B := by simpa using hY
    rcases h with rfl | rfl
    · exact ⟨W.inclusion, rfl⟩
    · exact ⟨pullback.fst B.inclusion C.inclusion, hpb.w⟩
  exact borel_of_same (H := closedSubgroupAlgebraicGroup (G := G') C) hAb ⟨hAW, hWA⟩

/-- An ambient conjugation restricts to an isomorphism on a closed normal
subgroup, with both inclusions retained. -/
private theorem conjugation_on_normal {G : GroupScheme F} (D : ClosedSubgroup G)
    (hD : IsNormalSubgroup D.inclusion) (g : 𝟙_ (SchemeOver F) ⟶ G.X) :
    ∃ e : D.group ≅ D.group,
      e.hom ≫ D.inclusion = D.inclusion ≫ (conjugationIso g).hom := by
  obtain ⟨f, hf⟩ := conjugate_le_of_normal hD g
  obtain ⟨j, hj⟩ := conjugate_le_of_normal hD g⁻¹
  change f ≫ D.inclusion = D.inclusion ≫ (conjugationIso g).hom at hf
  change j ≫ D.inclusion = D.inclusion ≫ (conjugationIso g).inv at hj
  letI := inclusion_mono D
  refine ⟨⟨f, j, ?_, ?_⟩, hf⟩
  · apply (cancel_mono D.inclusion).mp
    rw [Category.assoc, hj, ← Category.assoc f, hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono D.inclusion).mp
    rw [Category.assoc, hf, ← Category.assoc j, hj, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

private theorem borel_preimage_congr [IsAlgClosed F] {L L' H H' : AffineAlgebraicGroup F}
    (i : H.val ⟶ L.val) (i' : H'.val ⟶ L'.val)
    (e : L.val ≅ L'.val) (d : H.val ≅ H'.val)
    (hi : d.hom ≫ i' = i ≫ e.hom)
    (B : ClosedSubgroup L.val) (B' : ClosedSubgroup L'.val)
    (b : B.group ≅ B'.group) (hb : b.hom ≫ B'.inclusion = B.inclusion ≫ e.hom)
    {C : ClosedSubgroup H.val} (w : C.group ⟶ B.group)
    (hpb : IsPullback w C.inclusion B.inclusion i) (hC : IsBorel C) :
    IsBorel (subgroupPreimage i' B') := by
  have h := hpb.of_iso (Iso.refl _) b d e
    (fst' := w ≫ b.hom) (snd' := C.inclusion ≫ d.hom)
    (by rw [Iso.refl_hom, Category.id_comp]) (by rw [Iso.refl_hom, Category.id_comp])
    hb.symm hi.symm
  let h' := subgroupPreimage_pullback i' B'
  let s := h.isoIsPullback _ _ h'
  exact (borel_of_compared_subgroups d s (h.isoIsPullback_hom_snd _ _ h')).mp hC

private theorem borel_intersection_of_compared_reference [IsAlgClosed F]
    {L₀ L H₀ : AffineAlgebraicGroup F} (hL : IsReductive L)
    (H : ClosedSubgroup L.val) (hH : IsNormalSubgroup H.inclusion)
    (i : H₀.val ⟶ L₀.val) (e : L₀.val ≅ L.val) (d : H₀.val ≅ H.group)
    (hi : d.hom ≫ H.inclusion = i ≫ e.hom)
    (B₀ : ClosedSubgroup L₀.val) (hB₀ : IsBorel B₀)
    (B : ClosedSubgroup L.val) (hB : IsBorel B)
    {C : ClosedSubgroup H₀.val} (w : C.group ⟶ B₀.group)
    (hpb : IsPullback w C.inclusion B₀.inclusion i) (hC : IsBorel C) :
    IsBorel (subgroupPreimage H.inclusion B) := by
  let B₁ := transportSubgroup e B₀
  obtain ⟨g, b, hb⟩ := GeometricBorelConjugacy.borelsConjugate L hL.1
    (connectedOfGeometricallyConnected L hL.2.1) B₁ B (borelUnderIso e hB₀) hB
  obtain ⟨d', hd'⟩ := conjugation_on_normal H hH g
  let E := e ≪≫ conjugationIso g
  let D := d ≪≫ d'
  have hD : D.hom ≫ H.inclusion = i ≫ E.hom := by
    change (d.hom ≫ d'.hom) ≫ H.inclusion = i ≫ e.hom ≫ (conjugationIso g).hom
    rw [Category.assoc, hd', ← Category.assoc d.hom, hi, Category.assoc]
  have hB₂ : b.hom ≫ B.inclusion = B₀.inclusion ≫ E.hom := by
    apply Grp.hom_ext
    change (b.hom ≫ B.inclusion).hom.hom =
      B₁.inclusion.hom.hom ≫ (conjugation g).hom.hom
    rw [conjugation_apply]
    exact hb
  exact borel_preimage_congr (H' := closedSubgroupAlgebraicGroup (G := L) H)
    i H.inclusion E D hD B₀ B b hB₂ w hpb hC

/-- Transport a comparison over the finite splitting field to an algebraically
closed field containing both it and the given extension. -/
private noncomputable def comparisonOverClosure {E Ω : Type u}
    [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [Algebra K Ω] [IsScalarTower F K Ω] {X Y : GroupScheme F}
    (a : (groupBaseChange F K).obj X ≅ (groupBaseChange F K).obj Y) :
    (groupBaseChange F Ω).obj X ≅ (groupBaseChange F E ⋙ groupBaseChange E Ω).obj Y :=
  (groupBaseChangeTowerIso (k := F) (K := K) (L := Ω)).symm.app X ≪≫
    (groupBaseChange K Ω).mapIso a ≪≫
    (groupBaseChangeTowerIso (k := F) (K := K) (L := Ω)).app Y ≪≫
    (groupBaseChangeTowerIso (k := F) (K := E) (L := Ω)).symm.app Y

set_option maxHeartbeats 1200000 in
private theorem comparisonOverClosure_square {E Ω : Type u}
    [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [Algebra K Ω] [IsScalarTower F K Ω] {X Y A B : GroupScheme F}
    (a : (groupBaseChange F K).obj X ≅ (groupBaseChange F K).obj Y)
    (b : (groupBaseChange F K).obj A ≅ (groupBaseChange F K).obj B)
    (i : A ⟶ X) (j : B ⟶ Y)
    (h : b.hom ≫ (groupBaseChange F K).map j = (groupBaseChange F K).map i ≫ a.hom) :
    (comparisonOverClosure (E := E) (Ω := Ω) b).hom ≫
      (groupBaseChange F E ⋙ groupBaseChange E Ω).map j =
        (groupBaseChange F Ω).map i ≫ (comparisonOverClosure (E := E) (Ω := Ω) a).hom := by
  let J := groupBaseChange K Ω
  let aK := groupBaseChangeTowerIso (k := F) (K := K) (L := Ω)
  let aE := groupBaseChangeTowerIso (k := F) (K := E) (L := Ω)
  have he := J.congr_map h
  rw [J.map_comp, J.map_comp] at he
  change ((aK.inv.app A ≫ J.map b.hom) ≫ aK.hom.app B) ≫ aE.inv.app B ≫
      (groupBaseChange F E ⋙ groupBaseChange E Ω).map j =
    (groupBaseChange F Ω).map i ≫ ((aK.inv.app X ≫ J.map a.hom) ≫ aK.hom.app Y) ≫ aE.inv.app Y
  simp only [Category.assoc]
  rw [← aE.inv.naturality j, ← aK.hom.naturality_assoc j]
  change aK.inv.app A ≫ J.map b.hom ≫ J.map ((groupBaseChange F K).map j) ≫
      aK.hom.app Y ≫ aE.inv.app Y =
    (groupBaseChange F Ω).map i ≫ aK.inv.app X ≫ J.map a.hom ≫ aK.hom.app Y ≫ aE.inv.app Y
  rw [← Category.assoc (J.map b.hom), he, Category.assoc]
  exact (aK.inv.naturality_assoc i _).symm

set_option maxHeartbeats 1600000 in
/-- Quasi-splitness passes to the scalar-extended derived subgroup. The
intersection with the given Borel is compared to the reference intersection
over an algebraic closure of the extension. -/
private theorem derived_quasiSplit_of_comparison [FiniteDimensional F K]
    {P : SplitBorelPair F} (S : ClosedSubgroup P.T.group) (hS : IsSplitTorus S.group)
    {L₀ : ClosedSubgroup P.G.val} (hC : IsCentralizer (subgroupOfSubgroup P.T S) L₀)
    (hL₀ : IsReductive (closedSubgroupAlgebraicGroup L₀))
    (H₀ : ClosedSubgroup L₀.group) (hH₀ : IsDerivedSubgroup H₀)
    (hb₀ : IsKBorel (subgroupPreimage (H₀.inclusion ≫ L₀.inclusion) P.B))
    (L : AffineAlgebraicGroup F) (hL : IsReductive L) (H : ClosedSubgroup L.val) (hH : IsDerivedSubgroup H)
    (b : (groupBaseChange F K).obj L₀.group ≅ (groupBaseChange F K).obj L.val)
    (d : (groupBaseChange F K).obj H₀.group ≅ (groupBaseChange F K).obj H.group)
    (hd : d.hom ≫ (groupBaseChange F K).map H.inclusion =
      (groupBaseChange F K).map H₀.inclusion ≫ b.hom)
    (E : Type u) [Field E] [Algebra F E]
    (hLE : IsQuasiSplit (baseChangedAlgebraicGroup E L)) :
    IsQuasiSplit (baseChangedAlgebraicGroup E (closedSubgroupAlgebraicGroup H)) := by
  let A := baseChangedAlgebraicGroup E L
  let Ω := AlgebraicClosure E
  let φ : K →ₐ[F] Ω := IsAlgClosed.lift
  letI : Algebra K Ω := φ.toRingHom.toAlgebra
  letI : IsScalarTower F K Ω := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  obtain ⟨hDE, hDer, _⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange E L H hH hL.1 hL.2.1
  let D := Specs.GeometricRadicals.baseChangedSubgroup E H hDE
  have hDr := reductive_of_semisimple (closedSubgroupAlgebraicGroup (G := A) D)
    (Reductive.CentralDerived.derivedSemisimple A hLE.1 D hDer)
  refine ⟨hDr, ?_⟩
  obtain ⟨B, hb⟩ := hLE.2
  let V := subgroupPreimage D.inclusion B
  let W := extendSubgroup Ω V
  refine ⟨V, W.isClosedImmersion, ?_⟩
  change IsBorel W
  let C := baseChangedAlgebraicGroup Ω A
  have hCr := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := Ω)
    A hLE.1.1 hLE.1.2.1).mpr hLE.1
  let D' := extendSubgroup Ω D
  obtain ⟨_, hD', _⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange Ω A D hDer hLE.1.1 hLE.1.2.1
  let T := extendSubgroup Ω L₀
  let B₀ := subgroupPreimage T.inclusion (extendSubgroup Ω P.B)
  have hB₀ := reference_levi_borel (Ω := Ω) P S hS L₀ hC
  let V₀ := subgroupPreimage (H₀.inclusion ≫ L₀.inclusion) P.B
  let W₀ := extendSubgroup Ω V₀
  let G₀ := baseChangedAlgebraicGroup Ω (closedSubgroupAlgebraicGroup (G := P.G) L₀)
  let H₀' := baseChangedAlgebraicGroup Ω (closedSubgroupAlgebraicGroup
    (G := closedSubgroupAlgebraicGroup L₀) H₀)
  have hH₀r := reductive_of_semisimple (closedSubgroupAlgebraicGroup
    (G := closedSubgroupAlgebraicGroup L₀) H₀)
    (Reductive.CentralDerived.derivedSemisimple _ hL₀ H₀ hH₀)
  have hW₀ : IsBorel W₀ := extendedBorel _ hH₀r V₀ hb₀ Ω
  let g := (groupBaseChange F Ω).map H₀.inclusion
  have hpb₀ : IsPullback
      ((groupBaseChange F Ω).map (pullback.fst P.B.inclusion (H₀.inclusion ≫ L₀.inclusion)))
      W₀.inclusion (extendSubgroup Ω P.B).inclusion (g ≫ T.inclusion) := by
    let D₀ := groupBaseChange F Ω
    have hpb := LinearAlgebraicGroups.baseChangeSubgroupPullback F Ω
      (subgroupPreimage_pullback (H₀.inclusion ≫ L₀.inclusion) P.B)
    change IsPullback _ _ _ (D₀.map (H₀.inclusion ≫ L₀.inclusion)) at hpb
    rw [D₀.map_comp] at hpb
    exact hpb
  let hpB₀ := subgroupPreimage_pullback T.inclusion (extendSubgroup Ω P.B)
  let hw₀ := hpb₀.of_right' hpB₀
  let eL := comparisonOverClosure (E := E) (Ω := Ω) b
  let eH := comparisonOverClosure (E := E) (Ω := Ω) d
  have hs : eH.hom ≫ D'.inclusion = g ≫ eL.hom :=
    comparisonOverClosure_square b d H₀.inclusion H.inclusion hd
  let B' := extendSubgroup Ω B
  have hpV : IsPullback ((groupBaseChange E Ω).map (pullback.fst B.inclusion D.inclusion))
      W.inclusion B'.inclusion D'.inclusion :=
    LinearAlgebraicGroups.baseChangeSubgroupPullback E Ω (subgroupPreimage_pullback D.inclusion B)
  have hI := borel_intersection_of_compared_reference
    (L₀ := G₀) (L := C) (H₀ := H₀') hCr D' hD'.1 g eL eH hs
    B₀ hB₀ B' (extendedBorel A hLE.1 B hb Ω) _ hw₀ hW₀
  let hpI := subgroupPreimage_pullback D'.inclusion B'
  let i := hpI.isoIsPullback _ _ hpV
  let A' := closedSubgroupAlgebraicGroup (G := C) D'
  exact (borel_of_compared_subgroups (G := A') (H := A') (B := subgroupPreimage D'.inclusion B')
    (C := W) (Iso.refl D'.group) i
    ((hpI.isoIsPullback_hom_snd _ _ hpV).trans (Category.comp_id _).symm)).mp hI

end DerivedBorel


section LabelledRoots

open Specs.BorelsAndChambers (subgroupRoots positiveRoots)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Pinning (IsSimple)
open Specs.StandardParabolicLevi (leviRoots)
open Specs.QuasiSplitOrbitDerivedRoots (SplitFace)
open private attachedBase_regular face_root_pairing restrictFaceCharacters
  face_character_span_injective face_preimage_borel subgroupPreimage subgroupPreimage_pullback
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private pairing_pushforward reductive_of_semisimple
  from LinearAlgebraicGroups.Classification.CentralIsogenies

set_option backward.isDefEq.respectTransparency false

private noncomputable def derivedBorelPair {P : SplitBorelPair F} {D : AttachedDatum P}
    {J : Set (Root P.T)} (S : SplitFace D J)
    (hB : IsKBorel (subgroupPreimage S.inclusion P.B))
    (hTB : IsSubgroupOf S.torus (subgroupPreimage S.inclusion P.B)) : SplitBorelPair F where
  G := S.group
  reductive := reductive_of_semisimple S.group
    (Reductive.CentralDerived.derivedSemisimple _ S.reductive S.derived S.isDerived)
  T := S.torus
  split := S.torusSplit
  maximal := S.torusMaximal
  B := subgroupPreimage S.inclusion P.B
  borel := hB
  containsTorus := hTB

set_option maxHeartbeats 1000000 in
/-- The positive roots of the derived reference Levi are the marked restrictions.
They are all simple, and their Cartan pairings are those of the marked roots. -/
private theorem labelled_derived_roots {P : SplitBorelPair F} (D : AttachedDatum P) {I : Type u}
    (r : I ↪ Root P.T) (S : SplitFace D (Set.range r))
    (hSpan : letI := D.comm; ∀ y : Additive (Cocharacter P.T.group),
      (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' Set.range r))
    (hroots : letI := D.comm; ∀ α ∈ leviRoots D.datum (Set.range r),
      ∃ i, α = r i ∨ α = D.datum.rootDatum.reflectionPerm (r i) (r i))
    (hB : IsKBorel (subgroupPreimage S.inclusion P.B))
    (hTB : IsSubgroupOf S.torus (subgroupPreimage S.inclusion P.B))
    (E : AttachedDatum (derivedBorelPair S hB hTB)) :
    letI := D.comm
    letI := E.comm
    ∃ e : I ≃ E.base.support,
      (∀ i, (e i).val.val = S.toAmbientTorus ≫ (r i).val) ∧
      ∀ i j, E.datum.rootDatum.pairing (e i).val (e j).val =
        D.datum.rootDatum.pairing (r i) (r j) := by
  letI := D.comm
  letI := E.comm
  let P' := derivedBorelPair S hB hTB
  let J := Set.range r
  have hr (i : I) : r i ∈ leviRoots D.datum J := Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩
  let f (i : I) : Root P'.T :=
    ⟨_, (QuasiSplitOrbitDerivedRoots.faceRootRestrictions D J S (r i) (hr i)).1⟩
  have hsimple (i : I) : IsSimple P (r i) := (D.simple_iff _).mp (S.simple ⟨i, rfl⟩)
  have hs (α : Root P.T) (hα : α ∈ leviRoots D.datum J) (β : Root P'.T)
      (hβ : β.val = S.toAmbientTorus ≫ α.val) :
      β ∈ subgroupRoots P'.T P'.B ↔ α ∈ subgroupRoots P.T P.B := by
    have h := (QuasiSplitOrbitDerivedRoots.faceRootRestrictions D J S α hα).1
    have he : β = ⟨S.toAmbientTorus ≫ α.val, h⟩ := Subtype.ext hβ
    rw [he]
    exact QuasiSplitOrbitDerivedRoots.faceBorelRoots D J S P.B P'.B
      (pullback.fst P.B.inclusion S.inclusion) (subgroupPreimage_pullback S.inclusion P.B) α hα h
  have hf (i : I) : f i ∈ subgroupRoots P'.T P'.B :=
    (hs (r i) (hr i) (f i) rfl).mpr (hsimple i).1
  have hneg (i : I) :
      D.datum.rootDatum.reflectionPerm (r i) (r i) ∉ subgroupRoots P.T P.B := by
    obtain ⟨c, _, hc, _⟩ := attachedBase_regular D
    have h := (hsimple i).1
    rw [← hc] at h ⊢
    change 0 < CharacterPairing.pairing P.T.group (r i).val c at h
    change ¬ 0 < CharacterPairing.pairing P.T.group
      (D.datum.rootDatum.reflectionPerm (r i) (r i)).val c
    rw [← evaluate_root D.datum c] at h ⊢
    rw [D.datum.rootDatum.root_reflectionPerm, D.datum.rootDatum.reflection_apply_self, map_neg]
    exact not_lt.mpr (neg_nonpos.mpr h.le)
  have hsur (β : Root P'.T) (hβ : β ∈ subgroupRoots P'.T P'.B) : ∃ i, f i = β := by
    obtain ⟨α, hα, he⟩ := QuasiSplitOrbitDerivedRoots.faceRootRestrictionSurjective D J S β.property
    have h := (hs α hα β he.symm).mp hβ
    rcases hroots α hα with ⟨i, hi | hi⟩
    · exact ⟨i, Subtype.ext ((congrArg (fun a : Root P.T => S.toAmbientTorus ≫ a.val) hi).symm.trans he)⟩
    · exact (hneg i (hi ▸ h)).elim
  have hfi : Function.Injective f := by
    intro i j h
    apply r.injective
    exact QuasiSplitOrbitDerivedRoots.faceRootRestrictionInjective D J S (hr i) (hr j)
      (congrArg Subtype.val h)
  have hsf (i : I) : IsSimple P' (f i) := by
    refine ⟨hf i, ?_⟩
    intro β hβ δ hδ hEq
    obtain ⟨j, rfl⟩ := hsur β hβ
    obtain ⟨l, rfl⟩ := hsur δ hδ
    have he : D.datum.rootDatum.root (r i) =
        D.datum.rootDatum.root (r j) + D.datum.rootDatum.root (r l) := by
      apply face_character_span_injective S hSpan (hr i)
        (Submodule.add_mem _ (hr j) (hr l))
      rw [map_add, D.datum.root_eq, D.datum.root_eq, D.datum.root_eq]
      change Additive.ofMul (f i).val = Additive.ofMul ((f j).val * (f l).val)
      exact congrArg Additive.ofMul hEq
    apply (hsimple i).2 _ (hsimple j).1 _ (hsimple l).1
    rw [D.datum.root_eq, D.datum.root_eq, D.datum.root_eq] at he
    exact congrArg Additive.toMul he
  let a (i : I) : E.base.support := ⟨f i, (E.simple_iff _).mpr (hsf i)⟩
  let e := Equiv.ofBijective a ⟨fun _ _ hh => hfi (congrArg Subtype.val hh), by
    intro x
    obtain ⟨i, hi⟩ := hsur x.val ((E.simple_iff _).mp x.property).1
    exact ⟨i, Subtype.ext hi⟩⟩
  refine ⟨e, fun _ => rfl, ?_⟩
  intro i j
  change E.datum.rootDatum.pairing (f i) (f j) = D.datum.rootDatum.pairing (r i) (r j)
  let b := (E.datum.rootDatum.coroot (f j)).toMul
  have hb : b ≫ S.toAmbientTorus = (D.datum.rootDatum.coroot (r j)).toMul :=
    QuasiSplitOrbitDerivedRoots.faceAttachedCoroots D J S (r j) (hr j) (f j).property b
      (E.datum.attached (f j))
  change E.datum.rootDatum.toLinearMap (E.datum.rootDatum.root (f i))
    (E.datum.rootDatum.coroot (f j)) = _
  rw [E.datum.root_eq]
  change E.datum.rootDatum.toLinearMap (Additive.ofMul (f i).val) (Additive.ofMul b) = _
  rw [E.datum.pairing_eq]
  exact (face_root_pairing S (r i) (r j) b hb).symm

end LabelledRoots

section CoordinateDescent

open _root_.LinearAlgebraicGroups.Descent
open Specs.QuasiSplitInducedWeilProduct (IsCoordinateProduct ProductDescent)
open private actionRingHom from LinearAlgebraicGroups.Descent.AffineGroups

variable {I : Type u} [MulAction Gal(K/F) I]

/-- Each coordinate inclusion of a product is injective. Evaluate its product
on the factor itself, using the counits for all remaining coordinates. -/
private theorem projection_injective {A : HopfAlgebraCategory K} {B : I → HopfAlgebraCategory K}
    {p : ∀ i, B i ⟶ A} (hp : IsCoordinateProduct p) (i : I) :
    Function.Injective (p i).hom := by
  classical
  let x (j : I) : B j →ₐ[K] B i :=
    if h : j = i then h ▸ AlgHom.id K (B j)
    else (Algebra.ofId K (B i)).comp (Bialgebra.counitAlgHom K (B j))
  obtain ⟨f, hf⟩ := (hp (CommAlgCat.of K (B i))).surjective x
  have hi : f.comp (p i).hom.toAlgHom = AlgHom.id K (B i) := by
    simpa [x] using congrFun hf i
  intro y z he
  have hy := DFunLike.congr_fun hi y
  have hz := DFunLike.congr_fun hi z
  exact hy.symm.trans ((congrArg f he).trans hz)

/-- Stability of the coordinate subalgebras gives the semilinear transport on
the factors, with the forward permutation on the coordinate inclusions. -/
private noncomputable def coordinateTransport {A : HopfAlgebraCategory K}
    (D : HopfDescentDatum F A) {B : I → HopfAlgebraCategory K}
    (p : ∀ i, B i ⟶ A) {i j : I}
    (hi : Function.Injective (p i).hom) (hj : Function.Injective (p j).hom)
    (σ : Gal(K/F))
    (h : D.action.act σ '' Set.range (p i).hom = Set.range (p j).hom) :
    { e : B i ≃+* B j //
      ∀ x, (p j).hom (e x) = D.action.act σ ((p i).hom x) } := by
  classical
  let f := (actionRingHom D σ).comp (p i).hom.toAlgHom.toRingHom
  have hmem (x : B i) : ∃ y : B j, (p j).hom y = f x := by
    change f x ∈ Set.range (p j).hom
    rw [← h]
    exact ⟨_, ⟨x, rfl⟩, rfl⟩
  let g : B i → B j := fun x => (hmem x).choose
  have hg (x : B i) : (p j).hom (g x) = f x := (hmem x).choose_spec
  let q : B i →+* B j :=
    { toFun := g
      map_one' := hj (by simp only [hg, map_one])
      map_mul' := fun x y => hj (by simp only [hg, map_mul])
      map_zero' := hj (by simp only [hg, map_zero])
      map_add' := fun x y => hj (by simp only [hg, map_add]) }
  have hq : Function.Bijective q := by
    refine ⟨fun x y he => hi ((D.action.act σ).injective ?_), ?_⟩
    · change f x = f y
      rw [← hg, ← hg]
      exact congrArg (p j).hom he
    · intro z
      have hz : (p j).hom z ∈ D.action.act σ '' Set.range (p i).hom :=
        h.symm ▸ ⟨z, rfl⟩
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hz
      exact ⟨x, hj ((hg x).trans hx)⟩
  exact ⟨RingEquiv.ofBijective q hq, hg⟩

open private standard from LinearAlgebraicGroups.Descent.Forms

/-- On the canonical scalar extension of the coordinate algebra the descent
comparison is the identity. The only additional data required from the
geometry are the product projections and stability of their images. -/
private noncomputable def productDescentOfStableProjections
    (A : HopfAlgebraCategory F) (B : I → HopfAlgebraCategory K)
    (hB : ∀ i, Algebra.FiniteType K (B i))
    (p : ∀ i, B i ⟶ extendedHopf K A) (hp : IsCoordinateProduct p)
    (hperm : ∀ σ i j, σ • i = j →
      (SemilinearAction.scalarExtension (K := K) A).act σ '' Set.range (p i).hom =
        Set.range (p j).hom) :
    ProductDescent (F := F) (K := K) (I := I) := by
  let D := standard K A
  let e (σ : Gal(K/F)) (i j : I) (h : σ • i = j) :=
    coordinateTransport D p (projection_injective hp i) (projection_injective hp j)
      σ (hperm σ i j h)
  refine
    { total := extendedHopf K A
      factor := B
      finiteType := hB
      projection := p
      product := hp
      datum := D
      transport := fun σ i j h => (e σ i j h).val
      transportProjection := fun σ i j h => (e σ i j h).property
      transportScalar := ?_
      descent := ⟨A, Iso.refl _, by intros; rfl⟩ }
  intro σ i j h r
  apply projection_injective hp j
  rw [(e σ i j h).property]
  change D.action.act σ ((p i).hom.toAlgHom (algebraMap K (B i) r)) =
    (p j).hom.toAlgHom (algebraMap K (B j) (σ r))
  rw [(p i).hom.toAlgHom.commutes, (p j).hom.toAlgHom.commutes]
  change D.action.act σ (algebraMap K (extendedHopf K A) r) =
    algebraMap K (extendedHopf K A) (σ r)
  rw [Algebra.algebraMap_eq_smul_one, D.action.map_smul, D.map_one,
    Algebra.algebraMap_eq_smul_one]

open private productPointsEquiv
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct

/-- Scheme product projections are coordinate product projections on every
test algebra. -/
private theorem coordinateProduct_of_fan [Finite I]
    {A : HopfAlgebraCategory K} {B : I → HopfAlgebraCategory K}
    (p : ∀ i, B i ⟶ A)
    (h : IsLimit (Fan.mk (specGroup A) (fun i => specGroupMap (p i)))) :
    IsCoordinateProduct p := by
  obtain ⟨e, _, he⟩ := LinearAlgebraicGroups.hopfSpecPoints K
  intro R
  let φ (C : HopfAlgebraCategory K) : (C →ₐ[K] R) ≃
      ((groupPointsFunctor K).obj (specGroup C)).obj R :=
    (WithConv.equiv _).symm.trans ((e C).app R).groupIsoToMulEquiv.toEquiv
  let ψ := productPointsEquiv _ h R
  let χ := (φ A).trans (ψ.toEquiv.trans (Equiv.piCongrRight fun i => (φ (B i)).symm))
  have hχ (x : A →ₐ[K] R) : χ x = fun i => x.comp (p i).hom.toAlgHom := by
    funext i
    apply (φ (B i)).injective
    change φ (B i) ((φ (B i)).symm
        (((groupPointsFunctor K).map (specGroupMap (p i))).app R (φ A x))) =
      φ (B i) (x.comp (p i).hom.toAlgHom)
    rw [Equiv.apply_symm_apply]
    exact (he (p i) R (toConv x)).symm
  exact (show (fun (x : A →ₐ[K] R) i => x.comp (p i).hom.toAlgHom) = χ from
    funext fun x => (hχ x).symm) ▸ χ.bijective

open private extendedGroupIso extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem scalarExtensionComparison :
    Forms.IsScalarExtensionComparison (extendedGroupIso (k := F) K) :=
  extendedSpecIso_hom_fst K

/-- The terminal group represents the empty product on every test algebra. -/
private theorem emptyCoordinateProduct [IsEmpty I]
    {A : HopfAlgebraCategory K} {B : I → HopfAlgebraCategory K} (p : ∀ i, B i ⟶ A)
    (e : specGroup A ≅ Grp.trivial (SchemeOver K)) : IsCoordinateProduct p := by
  intro R
  let T : IsTerminal (specGroup A).X :=
    (isTerminalTensorUnit (C := SchemeOver K)).ofIso ((Grp.forget _).mapIso e).symm
  refine ⟨?_, ?_⟩
  · intro f g _
    let eR := Spec.mapMulEquiv (R := K) (S := A) (T := R)
    have h : eR (toConv f) = eR (toConv g) := T.hom_ext _ _
    exact congrArg ofConv (eR.injective h)
  · intro f
    refine ⟨(Algebra.ofId K R).comp (Bialgebra.counitAlgHom K A), ?_⟩
    funext i
    exact isEmptyElim i

end CoordinateDescent

section EmptyFace

open Specs.GeometricRadicals (GeometricGroup identitySubgroup)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.SchemeDerivedGroup (IsCommutative DerivedSeries)
open Specs.Unipotent (baseChangedAlgebraicGroup)

open private identity_smoothConnectedNormal from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private baseChange_trivial_iso from LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private reductive_geometricGroup connected_of_geometricallyConnected
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private baseChange_closed from LinearAlgebraicGroups.RootData.RankOneFlag
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private pairing_pushforward from LinearAlgebraicGroups.Classification.CentralIsogenies
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private torus_commutative from LinearAlgebraicGroups.Reductive.GeneralLinearStructure

private theorem identity_isDerived {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsCommutative G.val) : IsDerivedSubgroup (identitySubgroup G) := by
  refine ⟨(identity_smoothConnectedNormal G).2.2, ⟨toUnit _, ?_⟩, ?_⟩
  · change (1 : G.val.X ⊗ G.val.X ⟶ G.val.X) = commutatorMap (𝟙 G.val) (𝟙 G.val)
    let x : G.val.X ⊗ G.val.X ⟶ G.val.X := fst _ _
    let y : G.val.X ⊗ G.val.X ⟶ G.val.X := snd _ _
    change 1 = x * y * x⁻¹ * y⁻¹
    rw [hG _ x y, mul_assoc y, mul_inv_cancel, mul_one, mul_inv_cancel]
  · intro N _ _
    refine ⟨0, ?_⟩
    exact (Grp.isZero_trivial (SchemeOver k)).eq_of_src _ _

/-- If the derived group has trivial underlying group scheme, its whole
scalar extension is a Borel. Reductivity follows by base change of the
derived subgroup under the given reductivity premise. -/
private theorem quasiSplit_of_trivial_derived
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    (L : AffineAlgebraicGroup k) (hL : IsReductive L)
    {H : ClosedSubgroup L.val} (hH : IsDerivedSubgroup H)
    (t : H.group ≅ Grp.trivial (SchemeOver k))
    (hLE : IsReductive (baseChangedAlgebraicGroup E L)) :
    IsQuasiSplit (baseChangedAlgebraicGroup E (closedSubgroupAlgebraicGroup H)) := by
  let C := baseChangedAlgebraicGroup E (closedSubgroupAlgebraicGroup H)
  obtain ⟨hi, hd, -⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange E L H hH hL.1 hL.2.1
  let D : ClosedSubgroup (baseChangedAlgebraicGroup E L).val :=
    ⟨_, (groupBaseChange k E).map H.inclusion, hi⟩
  have hC : IsReductive C :=
    reductive_of_semisimple _ (Reductive.CentralDerived.derivedSemisimple
      (baseChangedAlgebraicGroup E L) hLE D hd)
  let e : C.val ≅ Grp.trivial (SchemeOver E) :=
    (groupBaseChange k E).mapIso t ≪≫ baseChange_trivial_iso E
  let Eg := AlgebraicClosure E
  let B : ClosedSubgroup C.val := ⟨C.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 _))⟩
  have hb : IsClosedImmersion ((groupBaseChange E Eg).map B.inclusion).hom.hom.left :=
    baseChange_closed B.inclusion B.isClosedImmersion
  let e' : (GeometricGroup C).val ≅ Grp.trivial (SchemeOver Eg) :=
    (groupBaseChange E Eg).mapIso e ≪≫ baseChange_trivial_iso Eg
  have hgeom := reductive_geometricGroup C hC
  refine ⟨hC, B, hb, ⟨hgeom.1, connected_of_geometricallyConnected hgeom.2.1,
    ⟨0, _, DerivedSeries.zero, ⟨e'⟩⟩⟩, ?_⟩
  intro N _ _
  refine ⟨N.inclusion, ?_⟩
  change N.inclusion ≫ (groupBaseChange E Eg).map (𝟙 C.val) = _
  rw [(groupBaseChange E Eg).map_id C.val, Category.comp_id]

open _root_.LinearAlgebraicGroups.Descent.Forms (IsScalarExtensionComparison)
open Specs.QuasiSplitInducedWeilProduct (ProductDescent)

/-- All conclusions for the empty face use the identity subgroup and
its canonical coordinate descent. -/
private theorem empty_face_descent [IsGalois F K] {I : Type u} [MulAction Gal(K/F) I]
    [IsEmpty I] (L : AffineAlgebraicGroup F) (hL : IsReductive L) (hT : IsTorus L.val) :
    ∃ (H : ClosedSubgroup L.val) (X : ProductDescent (F := F) (K := K) (I := I))
      (_j : specGroup X.descent.coordinate ≅ H.group)
      (t : ∀ A : HopfAlgebraCategory F,
        specGroup (extendedHopf K A) ≅ (groupBaseChange F K).obj (specGroup A)),
      IsDerivedSubgroup H ∧ IsScalarExtensionComparison t ∧
      (∀ (E : Type u) [Field E] [Algebra F E],
        IsQuasiSplit (baseChangedAlgebraicGroup E L) →
          IsQuasiSplit (baseChangedAlgebraicGroup E (closedSubgroupAlgebraicGroup H))) := by
  let H := identitySubgroup L
  have hH : IsDerivedSubgroup H := identity_isDerived L (torus_commutative hT)
  obtain ⟨A, _, ⟨j⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup H)
  let t := extendedGroupIso (k := F) K
  let B : I → HopfAlgebraCategory K := isEmptyElim
  let p : ∀ i, B i ⟶ extendedHopf K A := isEmptyElim
  let e : specGroup (extendedHopf K A) ≅ Grp.trivial (SchemeOver K) :=
    t A ≪≫ (groupBaseChange F K).mapIso j ≪≫ baseChange_trivial_iso K
  let X := productDescentOfStableProjections A B isEmptyElim p (emptyCoordinateProduct p e)
    (fun _ => isEmptyElim)
  refine ⟨H, X, j, t, hH, scalarExtensionComparison, ?_⟩
  intro E _ _ hLE
  exact quasiSplit_of_trivial_derived L hL hH (Iso.refl _) hLE.1


open Specs.QuasiSplitOrbitDerivedRoots (SplitFace)
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private pushCocharacters face_preimage_borel
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private liftToSchemeKernel from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private baseChangeMapIsPullback from LinearAlgebraicGroups.Flag.HomogeneousQuotient

open Specs.Arithmetic.OrthogonalLeviFactorDisplacement (IsUpperRootProjection)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.RelativeFormComparison (fieldTest IsInduced transportedAut)
open Specs.AutomorphismSequence (relativePoints)
open Specs.StandardGroups (specialLinearPoints)
open Specs.QuasiSplitInnerForms (outerHom)
open Descent.Forms (spectrumIso)

private theorem upper_root_projection {U V : GroupScheme F} {S : AffineAlgebraicGroup F}
    (s : SpecialMatrixPoints S 2) (e : V ≅ U) (f : V ⟶ S.val)
    (hf : IsClosedImmersion f.hom.hom.left)
    (hs : ∀ R : TestAlgebra F,
      Set.range (fun x : Points V.X R => (s.hom.app R (x ≫ f.hom.hom)).val) =
        Set.range (fun a : R => (1 + Matrix.single ⟨0⟩ ⟨1⟩ a :
          Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R))) :
    IsUpperRootProjection s (e.inv ≫ f) := by
  intro R
  let e' : V.X ≅ U.X := (Grp.forget (SchemeOver F)).mapIso e
  let g (x : Points V.X R) := s.hom.app R (x ≫ f.hom.hom)
  let a₁ (t : R) := Matrix.SpecialLinearGroup.transvection
    (show (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ by decide) t
  have he (x : Points U.X R) :
      s.hom.app R (((groupPointsFunctor F).map (e.inv ≫ f)).app R x) =
        g (x ≫ e'.inv) := by
    change s.hom.app R (x ≫ (e.inv ≫ f).hom.hom) =
      s.hom.app R ((x ≫ e.inv.hom.hom) ≫ f.hom.hom)
    rw [Grp.comp_hom_hom, Category.assoc]
  refine ⟨?_, ?_⟩
  · haveI : Mono f.hom.hom := Over.mono_of_mono_left _
    intro x y h
    apply (cancel_mono e'.inv).mp
    apply (cancel_mono f.hom.hom).mp
    apply ((s.app R).groupIsoToMulEquiv).injective
    exact (he x).symm.trans ((congrArg (s.hom.app R) h).trans (he y))
  · change Set.range (fun x : Points U.X R =>
        s.hom.app R (((groupPointsFunctor F).map (e.inv ≫ f)).app R x)) = Set.range a₁
    simp only [he]
    apply Set.ext
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      have hm : (g (x ≫ e'.inv)).val ∈ Set.range (fun t => (a₁ t).val) :=
        hs R ▸ ⟨x ≫ e'.inv, rfl⟩
      obtain ⟨t, ht⟩ := hm
      exact ⟨t, Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      have hm : (a₁ t).val ∈ Set.range (fun x : Points V.X R => (g x).val) :=
        (hs R).symm ▸ ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hm
      refine ⟨x ≫ e'.hom, ?_⟩
      change g ((x ≫ e'.hom) ≫ e'.inv) = a₁ t
      rw [Category.assoc, e'.hom_inv_id, Category.comp_id]
      exact Subtype.ext hx

/-- The matrix comparison of a split factor after extending scalars. -/
private noncomputable def baseChangeSpecialLinearPoints {S : AffineAlgebraicGroup F}
    (s : SpecialMatrixPoints S 2) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj S.val) ≅
      specialLinearPoints K (ULift.{u} (Fin 2)) :=
  NatIso.ofComponents (fun R => ((baseChangePointGroupEquiv K S.val R).trans
    (s.app ((restrictTestAlgebra F K).obj R)).groupIsoToMulEquiv).toGrpIso) (by
      intro R T f
      apply GrpCat.ext
      intro x
      change Points ((baseChange F K).obj S.val.X) R at x
      change s.hom.app ((restrictTestAlgebra F K).obj T)
        (baseChangePoint F K S.val.X T (mapPoints f x)) =
        Matrix.SpecialLinearGroup.map f.hom.toRingHom
          (s.hom.app ((restrictTestAlgebra F K).obj R) (baseChangePoint F K S.val.X R x))
      rw [baseChangePointsNaturality]
      exact congrArg (fun g => g (baseChangePoint F K S.val.X R x))
        (s.hom.naturality ((restrictTestAlgebra F K).map f)))

private theorem baseChange_zero {U V : GroupScheme F} :
    (groupBaseChange F K).map (0 : U ⟶ V) = 0 := by
  let Z := Grp.trivial (SchemeOver F)
  have hz : (0 : U ⟶ V) = (0 : U ⟶ Z) ≫ (0 : Z ⟶ V) := by simp
  rw [hz, Functor.map_comp]
  have hZ : IsZero ((groupBaseChange F K).obj Z) :=
    (Grp.isZero_trivial (SchemeOver K)).of_iso (baseChange_trivial_iso K)
  rw [hZ.eq_of_tgt ((groupBaseChange F K).map (0 : U ⟶ Z)) 0, zero_comp]

set_option maxHeartbeats 2500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The assigned comparison. The empty face is resolved by the actual
identity subgroup of the Levi. -/
theorem derivedFactors : Specs.Arithmetic.OrthogonalDerivedLevi.DerivedFactors.{u} := by
  classical
  intro F K I _ _ _ _ _ _ _ A P D l Q seq hss hsc G c M hL d M₀ a p b iK hi hp hb r hr hd horth haction
  by_cases hI : IsEmpty I
  · letI := hI
    letI := D.comm
    have hface : (Set.range r : Set (Root P.pair.T)) = ∅ := by
      ext α
      constructor
      · rintro ⟨i, _⟩
        exact isEmptyElim i
      · intro h
        exact False.elim h
    have hd' : HasFace D.base (∅ : Set (Root P.pair.T)) d :=
      hface ▸ hd
    have htorus := torus_of_empty_face D M M₀ b hd'
    obtain ⟨H, X, j, t, hH, ht, hq⟩ :=
      empty_face_descent (K := K) (I := I) (closedSubgroupAlgebraicGroup M.centralizer) hL htorus
    exact ⟨H, X, j, t, hH, ht, isEmptyElim, fun _ => htorus, hq, isEmptyElim⟩
  · letI := D.comm
    let J : Set (Root P.pair.T) := Set.range r
    obtain ⟨hP₀, hB₀, hr₀, S, T, eT, hS, hcentral, heT, hmax, hroots⟩ :=
      split_face_levi D J M₀ hd
    obtain ⟨H₀, hH₀⟩ := LinearAlgebraicGroups.SchemeDerivedGroup.derivedSubgroupExists
      (closedSubgroupAlgebraicGroup M₀.centralizer)
    obtain ⟨H, hH⟩ := LinearAlgebraicGroups.SchemeDerivedGroup.derivedSubgroupExists
      (closedSubgroupAlgebraicGroup M.centralizer)
    change ClosedSubgroup M₀.centralizer.group at H₀
    change ClosedSubgroup M.centralizer.group at H
    obtain ⟨eH, heH⟩ := compared_derived hr₀ hL b hH₀ hH
    have hderivedSquare :
        eH.hom ≫ (groupBaseChange F K).map (H.inclusion ≫ M.centralizer.inclusion) =
          (groupBaseChange F K).map (H₀.inclusion ≫ M₀.centralizer.inclusion) ≫ a.hom := by
      let B := groupBaseChange F K
      change eH.hom ≫ B.map (H.inclusion ≫ M.centralizer.inclusion) =
        B.map (H₀.inclusion ≫ M₀.centralizer.inclusion) ≫ a.hom
      change eH.hom ≫ B.map H.inclusion = B.map H₀.inclusion ≫ b.hom at heH
      change B.map M₀.centralizer.inclusion ≫ a.hom = b.hom ≫ B.map M.centralizer.inclusion at hb
      calc
        _ = (eH.hom ≫ B.map H.inclusion) ≫ B.map M.centralizer.inclusion := by
          rw [B.map_comp, Category.assoc]
        _ = B.map H₀.inclusion ≫ (b.hom ≫ B.map M.centralizer.inclusion) := by
          exact (congrArg (· ≫ B.map M.centralizer.inclusion) heH).trans (Category.assoc _ _ _)
        _ = _ := by rw [← hb, B.map_comp, Category.assoc]
    have hfaceRoots (α : Root P.pair.T) (hα : α ∈ StandardParabolicLevi.leviRoots D.datum J) :
        ∃ i, α = r i ∨ α = D.datum.rootDatum.reflectionPerm (r i) (r i) := by
      letI := D.datum.reduced
      obtain ⟨j, ⟨i, rfl⟩, hj⟩ := root_of_orthogonal_face D.datum.rootDatum D.base hr
        (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h; exact horth i j (fun h' => h (congrArg r h'))) hα
      exact ⟨i, hj⟩
    letI := Fintype.ofFinite I
    let y : Additive (Cocharacter P.pair.T.group) := ∑ i, D.datum.rootDatum.coroot (r i)
    have hyRegular : BorelsAndChambers.IsRegular T (y.toMul ≫ eT.hom) := by
      intro β
      have hβm : β.val ∈ (fun α : Root P.pair.T => eT.inv ≫ α.val) ''
          StandardParabolicLevi.leviRoots D.datum J := by
        rw [← hroots]
        exact β.property
      obtain ⟨α, hα, hβ⟩ := hβm
      change CharacterPairing.pairing T.group β.val (y.toMul ≫ eT.hom) ≠ 0
      rw [← hβ, pairing_pushforward]
      have hχ : CentralIsogenies.characterPullback eT.hom (eT.inv ≫ α.val) = α.val :=
        eT.hom_inv_id_assoc α.val
      rw [hχ, ← D.datum.pairing_eq, ← D.datum.root_eq]
      change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root α) y ≠ 0
      rcases hfaceRoots α hα with ⟨i, h | h⟩
      · rw [h]
        exact (pairing_coroot_sum D.datum.rootDatum r horth i).trans_ne (by decide : (2 : ℤ) ≠ 0)
      · let j : Root P.pair.T := r i
        have hneg : D.datum.rootDatum.root (D.datum.rootDatum.reflectionPerm j j) =
            -D.datum.rootDatum.root j :=
          (RootPairing.root_reflectionPerm D.datum.rootDatum j j).trans
            (RootPairing.reflection_apply_self D.datum.rootDatum j)
        have hpos := pairing_coroot_sum D.datum.rootDatum r horth i
        change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root j) y = 2 at hpos
        rw [h]
        change D.datum.rootDatum.toLinearMap
          (D.datum.rootDatum.root (D.datum.rootDatum.reflectionPerm j j)) y ≠ 0
        rw [hneg, map_neg, LinearMap.neg_apply, hpos]
        decide
    let L₀ := closedSubgroupAlgebraicGroup M₀.centralizer
    obtain ⟨Q₀, q, hq, _, hQ₀⟩ := Reductive.CentralDerived.derivedTorusQuotient L₀ hr₀ H₀ hH₀
    change M₀.centralizer.group ⟶ Q₀.val at q
    letI : IsCommMonObj Q₀.val.X := torus_commutative Q₀ hQ₀
    let t := eT.hom ≫ T.inclusion
    have ht : t ≫ M₀.centralizer.inclusion = P.pair.T.inclusion := heT
    have hkill (i : I) : ((D.datum.rootDatum.coroot (r i)).toMul ≫ t) ≫ q = 0 :=
      coroot_killed_by_levi_quotient D J S hS M₀.centralizer hcentral t ht Q₀ q hQ₀ _
        (Submodule.subset_span ⟨r i, ⟨i, rfl⟩, rfl⟩)
    have hyKill : (y.toMul ≫ t) ≫ q = 0 := by
      let f := pushCocharacters (t ≫ q)
      have hn (i : I) : f (D.datum.rootDatum.coroot (r i)) = 0 := by
        apply Additive.toMul.injective
        change (D.datum.rootDatum.coroot (r i)).toMul ≫ (t ≫ q) = 0
        exact (Category.assoc _ _ _).symm.trans (hkill i)
      have hh : f y = 0 := by
        change f (∑ i, D.datum.rootDatum.coroot (r i)) = 0
        rw [map_sum, Finset.sum_eq_zero (fun i _ => hn i)]
      exact (Category.assoc _ _ _).trans (congrArg Additive.toMul hh)
    obtain ⟨v, hv⟩ := liftToSchemeKernel hq (y.toMul ≫ t) hyKill
    obtain ⟨T₀, vT, hpb, hsplit, hmax₀⟩ := derived_torus_of_regular hr₀ H₀ hH₀ T
      (by obtain ⟨n, ⟨e⟩⟩ := P.pair.split; exact ⟨n, ⟨eT.symm ≪≫ e⟩⟩)
      hmax (y.toMul ≫ eT.hom) hyRegular v (hv.trans (Category.assoc _ _ _).symm)
    letI := inclusion_mono M₀.centralizer
    have htPullback : IsPullback eT.inv T.inclusion P.pair.T.inclusion M₀.centralizer.inclusion :=
      IsPullback.of_horiz_isIso_mono ⟨
        (congrArg (eT.inv ≫ ·) heT.symm).trans (eT.inv_hom_id_assoc _)⟩
    let face : SplitFace D J :=
      ⟨hr, S, hS, M₀.centralizer, hcentral, hr₀, T, eT, heT, hmax, hroots,
        H₀, hH₀, T₀, vT ≫ eT.inv, hpb.paste_horiz htPullback, hsplit, hmax₀⟩
    have hSpan := face_coroot_lattice D J face hss hsc (by
      intro α hα
      obtain ⟨i, hi⟩ := hfaceRoots α hα
      exact ⟨r i, ⟨i, rfl⟩, hi⟩)
    have hSimplyConnected := QuasiSplitOrbitDerivedRoots.splitDerivedSimplyConnected D J face hSpan
    obtain ⟨hB, hTB⟩ := face_preimage_borel face hSpan P.pair.B P.pair.borel P.pair.containsTorus
    have hQuasiSplit := derived_quasiSplit_of_comparison S hS.1 hcentral hr₀ H₀ hH₀ hB
      (closedSubgroupAlgebraicGroup M.centralizer) hL H hH b eH heH
    let P' := derivedBorelPair face hB hTB
    let D' := Classification.Pinning.attachedDatum P'
    obtain ⟨labels, hlabels, hCartan⟩ := labelled_derived_roots D r face hSpan hfaceRoots hB hTB D'
    letI : Nonempty I := not_isEmpty_iff.mp hI
    have hRoot (i : I) :
        ∃ V : ClosedSubgroup P'.G.val, RootGroups.IsRootSubgroup P'.T V (labels i).val.val ∧
          ∃ e : V.group ≅ (P.roots (r i)).val.group,
            e.hom ≫ (P.roots (r i)).val.inclusion = V.inclusion ≫ face.inclusion := by
      rw [hlabels i]
      exact (QuasiSplitOrbitDerivedRoots.faceRootRestrictions D J face (r i)
        (Submodule.subset_span ⟨r i, ⟨i, rfl⟩, rfl⟩)).2
          (P.roots (r i)).val (P.roots (r i)).property
    choose V hV eV heV using hRoot
    have hs' : IsSemisimple P'.G :=
      Reductive.CentralDerived.derivedSemisimple L₀ hr₀ H₀ hH₀
    obtain ⟨S₂, s, π, ⟨hπ⟩, hproj⟩ := LabelledSplitRankOneProduct.splitRankOneProduct
      F I P' D' hs' hSimplyConnected labels
      (fun i j hij => (hCartan j i).trans (horth j i (Ne.symm hij))) V hV
    let uᵣ (i : I) : (P.roots (r i)).val.group ⟶ H₀.group := (eV i).inv ≫ (V i).inclusion
    have hu (i : I) : uᵣ i ≫ H₀.inclusion ≫ M₀.centralizer.inclusion =
        (P.roots (r i)).val.inclusion := by
      change ((eV i).inv ≫ (V i).inclusion) ≫ face.inclusion = _
      rw [Category.assoc, ← heV i, Iso.inv_hom_id_assoc]
    have hOff (i j : I) (h : j ≠ i) : uᵣ i ≫ π j = 0 := by
      change ((eV i).inv ≫ (V i).inclusion) ≫ π j = 0
      rw [Category.assoc, (hproj i).1 j h, comp_zero]
    have hUpper (i : I) : IsUpperRootProjection s (uᵣ i ≫ π i) := by
      rw [show uᵣ i ≫ π i = (eV i).inv ≫ ((V i).inclusion ≫ π i) from Category.assoc ..]
      exact upper_root_projection s (eV i) _ (hproj i).2.1 (hproj i).2.2
    let B := groupBaseChange F K
    let L := closedSubgroupAlgebraicGroup M.centralizer
    obtain ⟨pR, hpR, _⟩ := (DerivedProjectionDescent.comparisonUniqueness F K _ _).1 p
    obtain ⟨bR, hbR, _⟩ := (DerivedProjectionDescent.comparisonUniqueness F K _ _).1 b
    obtain ⟨eR, heR, _⟩ := (DerivedProjectionDescent.comparisonUniqueness F K _ _).1 eH
    have liftDisplacement {V W : GroupScheme F}
        (rV : relativePoints V (fieldTest F K) ≅ relativePoints W (fieldTest F K))
        (σ : Gal(K/F)) :
        ∃ δ : B.obj V ≅ B.obj V, IsInduced F K δ (transportedAut F K rV σ).asIso := by
      obtain ⟨δ, hδ, _⟩ := (DerivedProjectionDescent.comparisonUniqueness F K V V).2
        (transportedAut F K rV σ).asIso
      exact ⟨δ, hδ⟩
    choose δG hδG using liftDisplacement iK
    choose δP hδP using liftDisplacement pR
    choose δL hδL using liftDisplacement bR
    choose δH hδH using liftDisplacement eR
    have hperm (σ : Gal(K/F)) (i : I) : ∃ v : B.obj S₂.val ≅ B.obj S₂.val,
        (δH σ).hom ≫ B.map (π (σ • i)) = B.map (π i) ≫ v.hom := by
      have hpσ := DerivedProjectionDescent.displacementSquare F K M₀.parabolic.inclusion
        M.parabolic.inclusion p a hp pR iK hpR hi σ (δP σ) (δG σ) (hδP σ) (hδG σ)
      have hbσ := DerivedProjectionDescent.displacementSquare F K M₀.centralizer.inclusion
        M.centralizer.inclusion b a hb bR iK hbR hi σ (δL σ) (δG σ) (hδL σ) (hδG σ)
      have hhσ := DerivedProjectionDescent.displacementSquare F K H₀.inclusion
        H.inclusion eH b heH.symm eR bR heR hbR σ (δH σ) (δL σ) (hδH σ) (hδL σ)
      let τ : I ≃ I :=
        ⟨(σ • ·), (σ⁻¹ • ·), inv_smul_smul σ, smul_inv_smul σ⟩
      exact OrthogonalLeviFactorDisplacement.factorDisplacement F K I P D seq r hr d M₀
        hd hP₀ hr₀ H₀ hH₀ (δG σ) (transportedAut F K iK σ) (hδG σ)
          (δP σ) (δL σ) (δH σ) hpσ hbσ hhσ τ (haction σ) S₂ s π ⟨hπ⟩ uᵣ hu hOff hUpper i
    obtain ⟨X, j, t, ht, θ, hθ⟩ := DerivedProjectionDescent.coordinatePermutationDescent
      F K I P'.G (closedSubgroupAlgebraicGroup (G := L) H) S₂ π hπ eH eR heR δH hδH hperm
    refine ⟨H, X, j, t, hH, ht, fun i => ⟨(groupPointsFunctor K).mapIso (θ i) ≪≫
      baseChangeSpecialLinearPoints s⟩, fun h => (hI h).elim, hQuasiSplit, ?_⟩
    intro comparison i
    let f := B.map (uᵣ i) ≫ eH.hom
    have hf (k : I) : f ≫ comparison.hom ≫ specGroupMap (X.projection k) ≫ (θ k).hom =
        B.map (uᵣ i ≫ π k) := by
      change (B.map (uᵣ i) ≫ eH.hom) ≫ comparison.hom ≫ specGroupMap (X.projection k) ≫
        (θ k).hom = _
      rw [Category.assoc, hθ k, Iso.hom_inv_id_assoc]
      exact (B.map_comp (uᵣ i) (π k)).symm
    refine ⟨f, ?_, ?_, ?_⟩
    · change (B.map (uᵣ i) ≫ eH.hom) ≫ B.map (H.inclusion ≫ M.centralizer.inclusion) = _
      rw [Category.assoc, hderivedSquare, ← Category.assoc, ← B.map_comp, hu i]
    · intro k hk
      apply (cancel_mono (θ k).hom).mp
      calc
        (f ≫ comparison.hom ≫ specGroupMap (X.projection k)) ≫ (θ k).hom =
            B.map (uᵣ i ≫ π k) := by simpa only [Category.assoc] using hf k
        _ = 0 ≫ (θ k).hom := by rw [hOff i k hk, baseChange_zero, zero_comp]
    · have hclosed : IsClosedImmersion (uᵣ i ≫ π i).hom.hom.left := by
        change IsClosedImmersion (((eV i).inv ≫ (V i).inclusion) ≫ π i).hom.hom.left
        rw [Category.assoc, Grp.comp_hom_hom, Over.comp_left]
        let forget := Grp.forget (SchemeOver F) ⋙ Over.forget _
        letI : IsIso (eV i).inv.hom.hom.left := forget.map_isIso (eV i).inv
        exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mpr
          (hproj i).2.1
      have hclosedK : IsClosedImmersion (B.map (uᵣ i ≫ π i)).hom.hom.left :=
        MorphismProperty.of_isPullback (baseChangeMapIsPullback K (uᵣ i ≫ π i).hom.hom).flip hclosed
      let g := f ≫ comparison.hom ≫ specGroupMap (X.projection i)
      have hg : (g ≫ (θ i).hom) = B.map (uᵣ i ≫ π i) := by
        simpa only [g, Category.assoc] using hf i
      have hclosedComp : IsClosedImmersion (g.hom.hom.left ≫ (θ i).hom.hom.hom.left) := by
        rw [← Over.comp_left, ← Grp.comp_hom_hom, hg]
        exact hclosedK
      let forget := Grp.forget (SchemeOver K) ⋙ Over.forget _
      letI : IsIso (θ i).hom.hom.hom.left := forget.map_isIso (θ i).hom
      exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp hclosedComp

end EmptyFace

end LinearAlgebraicGroups.Arithmetic.OrthogonalDerivedLevi
