import Specs.LinearAlgebraicGroups.Descent.FiniteFieldFlags
import Specs.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import LinearAlgebraicGroups.Descent.SmoothLang
import LinearAlgebraicGroups.Descent.AffineGroups
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Tactic.Group

import LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra HopfAlgebra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace LinearAlgebraicGroups.Descent.FiniteFieldFlags

universe u

open _root_.LinearAlgebraicGroups.Specs
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsTorus IsSplitTorus
  baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel ConjugatesSubgroups)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000


variable {k : Type u} [Field k]

private theorem geometric_smooth (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) :
    Smooth (GeometricGroup G).val.X.hom := by
  let := hs
  exact inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k (AlgebraicClosure k))))

private theorem geometric_connected [Fintype k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    ConnectedSpace (GeometricGroup G).val.X.left := by
  let := hs
  let := hc
  let := G.property.2.2
  exact smoothGroupGeometricConnectedness k G.val

/-- A subspace preserved by a coefficient automorphism is spanned by vectors fixed
by that automorphism. Every finitely supported vector can be reduced using a fixed
vector supported on the same finite set. -/
private theorem span_fixed_coefficients {K index : Type*} [Field K] (σ : K ≃+* K)
    (J : Submodule K (index →₀ K))
    (hJ : ∀ x ∈ J, Finsupp.mapRange σ (map_zero σ) x ∈ J) :
    Submodule.span K {x | x ∈ J ∧ Finsupp.mapRange σ (map_zero σ) x = x} = J := by
  classical
  let F : (index →₀ K) → (index →₀ K) := Finsupp.mapRange σ (map_zero σ)
  let S := Submodule.span K {x | x ∈ J ∧ F x = x}
  have hF (x : index →₀ K) (i : index) : F x i = σ (x i) := rfl
  change S = J
  apply le_antisymm (Submodule.span_le.mpr fun x hx => hx.1)
  intro x
  suffices h : ∀ n (v : index →₀ K), v.support.card ≤ n → v ∈ J → v ∈ S from
    h x.support.card x le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv hvJ
    by_cases hzero : v = 0
    · exact hzero ▸ S.zero_mem
    obtain ⟨i, hi⟩ : v.support.Nonempty := Finsupp.support_nonempty_iff.mpr hzero
    have hvi := Finsupp.mem_support_iff.mp hi
    let eligible (m : ℕ) :=
      ∃ w ∈ J, w.support ⊆ v.support ∧ w i = 1 ∧ w.support.card = m
    have hex : ∃ m, eligible m := by
      refine ⟨_, (v i)⁻¹ • v, J.smul_mem _ hvJ, Finsupp.support_smul, ?_, rfl⟩
      simp [Finsupp.smul_apply, hvi]
    obtain ⟨w, hwJ, hwv, hwi, hwm⟩ := Nat.find_spec hex
    have hwFJ : F w ∈ J := hJ w hwJ
    have hsupport (a : index →₀ K) (ha : a.support ⊆ w.support)
        (j : index) (hj : j ∈ w.support) (haj : a j = 0) :
        a.support.card < w.support.card := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨ha, fun he =>
        Finsupp.mem_support_iff.mp (he.symm ▸ hj) haj⟩
    have hwF : F w = w := by
      by_contra hne
      have hne' : F w - w ≠ 0 := sub_ne_zero.mpr hne
      obtain ⟨j, hj⟩ : (F w - w).support.Nonempty := Finsupp.support_nonempty_iff.mpr hne'
      have hdj := Finsupp.mem_support_iff.mp hj
      have hjw : j ∈ w.support := by
        apply Finsupp.mem_support_iff.mpr
        intro hz
        apply hdj
        simp [Finsupp.sub_apply, hF, hz]
      let a := w - (w j / (F w - w) j) • (F w - w)
      have haJ : a ∈ J := J.sub_mem hwJ (J.smul_mem _ (J.sub_mem hwFJ hwJ))
      have haw : a.support ⊆ w.support := by
        intro t ht
        apply Finsupp.mem_support_iff.mpr
        intro hz
        exact Finsupp.mem_support_iff.mp ht (by simp [a, Finsupp.sub_apply, hF, hz])
      have hai : a i = 1 := by simp [a, Finsupp.sub_apply, hF, hwi]
      have haj : a j = 0 := by
        simp only [a, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        change w j - w j / (F w - w) j * (F w - w) j = 0
        rw [div_mul_cancel₀ _ hdj, sub_self]
      have hmin := Nat.find_min' hex ⟨a, haJ, haw.trans hwv, hai, rfl⟩
      exact (not_lt_of_ge hmin) (hwm ▸ hsupport a haw j hjw haj)
    have hwS : w ∈ S := Submodule.subset_span ⟨hwJ, hwF⟩
    let z := v - v i • w
    have hzJ : z ∈ J := J.sub_mem hvJ (J.smul_mem _ hwJ)
    have hzle : z.support ⊆ v.support := by
      intro j hj
      apply Finsupp.mem_support_iff.mpr
      intro hz
      have hwj : w j = 0 := by
        by_contra hn
        exact (Finsupp.mem_support_iff.mp (hwv (Finsupp.mem_support_iff.mpr hn))) hz
      exact Finsupp.mem_support_iff.mp hj (by simp [z, Finsupp.sub_apply, hz, hwj])
    have hzi : z i = 0 := by simp [z, Finsupp.sub_apply, hwi]
    have hzlt : z.support.card < n := by
      apply lt_of_lt_of_le (Finset.card_lt_card ?_) hv
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hzle, fun he =>
        Finsupp.mem_support_iff.mp (he.symm ▸ hi) hzi⟩
    have hzS := ih _ hzlt z le_rfl hzJ
    simpa [z] using S.add_mem hzS (S.smul_mem (v i) hwS)

section IdealDescent

variable {K A : Type u} [Field K] [Algebra k K] [CommRing A] [Algebra k A]

private theorem extend_contract_of_stable (σ : K ≃ₐ[k] K)
    (hfixed : ∀ r : K, σ r = r → r ∈ Set.range (algebraMap k K))
    (J : Ideal (K ⊗[k] A))
    (hJ : ∀ x ∈ J, Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A) x ∈ J) :
    (J.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)).map
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) = J := by
  classical
  let index := Module.Free.ChooseBasisIndex k A
  let b : Module.Basis index k A := Module.Free.chooseBasis k A
  let B := b.baseChange K
  let i : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let I := (J.comap i).map i
  let J' : Submodule K (index →₀ K) := (J.restrictScalars K).map B.repr.toLinearMap
  let act := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)
  have hrepr (x : K ⊗[k] A) :
      B.repr (act x) = Finsupp.mapRange σ (map_zero σ) (B.repr x) := by
    have htmul (r : K) (a : A) :
        B.repr (r ⊗ₜ[k] a) = r • (b.repr a).mapRange (algebraMap k K) (map_zero _) := by
      ext j
      simp only [B, Module.Basis.baseChange_repr_tmul, Finsupp.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul, Algebra.smul_def]
      exact mul_comm _ _
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      ext j
      simp [act, htmul, map_mul, AlgEquiv.commutes]
    | add x y hx hy =>
      ext j
      have hxj := DFunLike.congr_fun hx j
      have hyj := DFunLike.congr_fun hy j
      simp only [Finsupp.mapRange_apply] at hxj hyj
      simp only [map_add, Finsupp.add_apply, Finsupp.mapRange_apply, hxj, hyj]
  have hJ' (v : index →₀ K) (hv : v ∈ J') : Finsupp.mapRange σ (map_zero σ) v ∈ J' := by
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨act x, hJ x hx, hrepr x⟩
  have hfixed' (v : index →₀ K) (hv : Finsupp.mapRange σ (map_zero σ) v = v) :
      ∃ a : A, B.repr (i a) = v := by
    have hr (j : index) : ∃ r : k, algebraMap k K r = v j :=
      hfixed _ (congrArg (fun f : index →₀ K ↦ f j) hv)
    choose r hr using hr
    let a := ∑ j ∈ v.support, r j • b j
    refine ⟨a, ?_⟩
    change B.repr ((1 : K) ⊗ₜ[k] a) = v
    ext j
    rw [Module.Basis.baseChange_repr_tmul]
    simp only [a, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    by_cases hj : j ∈ v.support
    · simp [hj, Algebra.smul_def, hr]
    · simp [hj, Finsupp.notMem_support_iff.mp hj]
  change I = J
  apply le_antisymm (Ideal.map_comap_le)
  intro x hx
  have hmember : B.repr x ∈ J' := ⟨x, hx, rfl⟩
  rw [← span_fixed_coefficients σ.toRingEquiv J' hJ'] at hmember
  have hle : Submodule.span K {v | v ∈ J' ∧ Finsupp.mapRange σ (map_zero σ) v = v} ≤
      (I.restrictScalars K).comap B.repr.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨a, ha⟩ := hfixed' v hv.2
    obtain ⟨y, hy, hyv⟩ := hv.1
    have hai : i a = y := B.repr.injective (ha.trans hyv.symm)
    change B.repr.symm v ∈ I
    rw [← ha, LinearEquiv.symm_apply_apply]
    exact Ideal.mem_map_of_mem i (show i a ∈ J from hai ▸ hy)
  have h := hle hmember
  simpa using h


open private comparison_counit_base tensorAlong tensorAlong_tmul
  tensorAlong_injective from LinearAlgebraicGroups.Descent.AffineGroups

private theorem hopfIdeal_of_extension (A : HopfAlgebraCategory k) (I : Ideal A)
    (hI : (extendedIdeal K I).IsHopfIdeal K) :
    I.IsHopfIdeal k := by
  let B := A ⧸ I
  let E := K ⊗[k] B
  let j : B →ₐ[k] E := Algebra.TensorProduct.includeRight
  let q : A →ₐ[k] B := Ideal.Quotient.mkₐ k I
  let Q : (K ⊗[k] A) →ₐ[K] E := Algebra.TensorProduct.map (AlgHom.id K K) q
  have hQt (a : A) : Q (1 ⊗ₜ[k] a) = j (q a) := rfl
  let J := extendedIdeal K I
  have hJ : ∀ a ∈ I, (1 ⊗ₜ[k] a : K ⊗[k] A) ∈ J := fun a ha ↦
    Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) ha
  have hQ : J ≤ RingHom.ker Q := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change Q (1 ⊗ₜ[k] a) = 0
    rw [hQt, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let m := Ideal.Quotient.liftₐ J Q (fun _ hx ↦ hQ hx)
  have hm (x : K ⊗[k] A) : m (Ideal.Quotient.mk J x) = Q x := rfl
  have hj : Function.Injective j :=
    Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective
  have hT : Function.Injective (tensorAlong (K := K) j j) := by
    have he : j.toLinearMap.liftBaseChange K = LinearMap.id := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro r x
      change r • ((1 : K) ⊗ₜ[k] x) = r ⊗ₜ[k] x
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact tensorAlong_injective j j (he ▸ Function.injective_id) (he ▸ Function.injective_id)
  refine {toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_}
  · intro a ha
    apply (algebraMap k K).injective
    rw [map_zero, ← comparison_counit_base]
    exact hI.toIsCoideal.counit_eq_zero (hJ a ha)
  · intro a ha
    apply hT
    rw [map_zero]
    have hco : TensorProduct.map m.toLinearMap m.toLinearMap
        (TensorProduct.map (Ideal.Quotient.mkₐ K J).toLinearMap
          (Ideal.Quotient.mkₐ K J).toLinearMap (comul (R := K) (1 ⊗ₜ[k] a))) = 0 := by
      rw [show TensorProduct.map (Ideal.Quotient.mkₐ K J).toLinearMap
          (Ideal.Quotient.mkₐ K J).toLinearMap (comul (R := K) (1 ⊗ₜ[k] a)) = 0
          from hI.toIsCoideal.map_mkQ_comul_eq_zero (hJ a ha), map_zero]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp] at hco
    have hlin : m.toLinearMap.comp (Ideal.Quotient.mkₐ K J).toLinearMap = Q.toLinearMap :=
      LinearMap.ext hm
    rw [hlin] at hco
    have hc : TensorProduct.map Q.toLinearMap Q.toLinearMap
        (comul (R := K) (1 ⊗ₜ[k] a)) =
        tensorAlong (K := K) j j (TensorProduct.map q.toLinearMap q.toLinearMap
          (comul (R := k) a)) := by
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      generalize comul (R := k) a = z
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          TensorProduct.map_tmul, AlgHom.toLinearMap_apply, tensorAlong_tmul, hQt]
      | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]
    exact hc.symm.trans hco
  · intro a ha
    have h := hI.antipode_mem (hJ a ha)
    change (1 ⊗ₜ[k] antipode k a : K ⊗[k] A) ∈ J at h
    have h' : Q (1 ⊗ₜ[k] antipode k a) = 0 := hQ h
    rw [hQt] at h' 
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hj (h'.trans (map_zero j).symm))


end IdealDescent

section Conjugation

private abbrev Section (G : GroupScheme k) := (𝟙_ (SchemeOver k)) ⟶ G.X

private def conjugation {G : GroupScheme k} (g : Section G) : G.X ⟶ G.X :=
  let c := toUnit G.X ≫ g
  c * 𝟙 G.X * c⁻¹

private theorem comp_conjugation {G : GroupScheme k} (g : Section G)
    {X : SchemeOver k} (x : X ⟶ G.X) :
    x ≫ conjugation g = (toUnit X ≫ g) * x * (toUnit X ≫ g)⁻¹ := by
  have h : x ≫ toUnit G.X = toUnit X := (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  simp only [conjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, h, Category.comp_id]

private instance conjugation_isMonHom {G : GroupScheme k} (g : Section G) :
    IsMonHom (conjugation g) where
  one_hom := by
    change (1 : (𝟙_ (SchemeOver k)) ⟶ G.X) ≫ conjugation g = 1
    rw [comp_conjugation, mul_one, mul_inv_cancel]
  mul_hom := by
    rw [comp_conjugation, MonObj.mul_eq_mul]
    simp only [MonObj.comp_mul, tensorHom_fst, tensorHom_snd, comp_conjugation]
    group

private def conjugationIso {G : GroupScheme k} (g : Section G) : G ≅ G :=
  Grp.mkIso'
    { hom := conjugation g
      inv := conjugation g⁻¹
      hom_inv_id := by
        rw [comp_conjugation]
        simp only [conjugation, GrpObj.comp_inv, inv_inv]
        group
      inv_hom_id := by
        rw [comp_conjugation]
        simp only [conjugation, GrpObj.comp_inv, inv_inv]
        group }

private theorem conjugates_iff_iso {G : GroupScheme k} (g : Section G)
    (H N : ClosedSubgroup G) :
    ConjugatesSubgroups g H N ↔
      ∃ e : H.group ≅ N.group, e.hom ≫ N.inclusion = H.inclusion ≫ (conjugationIso g).hom := by
  unfold ConjugatesSubgroups
  apply exists_congr
  intro e
  change ((e.hom ≫ N.inclusion).hom.hom =
    (toUnit H.group.X ≫ g) * H.inclusion.hom.hom * (toUnit H.group.X ≫ g)⁻¹) ↔ _
  rw [← comp_conjugation g H.inclusion.hom.hom]
  change ((e.hom ≫ N.inclusion).hom.hom =
    (H.inclusion ≫ (conjugationIso g).hom).hom.hom) ↔ _
  exact ⟨Grp.hom_ext _ _, fun h ↦ congrArg (fun a ↦ a.hom.hom) h⟩

end Conjugation

section Tori

open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem isTorus_of_iso {G H : GroupScheme k} (e : G ≅ H) (h : IsTorus H) :
    IsTorus G := by
  obtain ⟨E, _, _, _, r, ⟨i⟩⟩ := h
  exact ⟨E, inferInstance, inferInstance, inferInstance, r,
    ⟨(groupBaseChange k E).mapIso e ≪≫ i⟩⟩

private theorem torusHopf_split [IsAlgClosed k] (A : HopfAlgebraCategory k)
    (h : Specs.CharacterDescent.IsTorus A) :
    ∃ r : ℕ, Nonempty (groupAlgebra k (Specs.CharacterDescent.StandardLattice.{u} r) ≅ A) := by
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := h
  let embedding : E →ₐ[k] k := IsSepClosed.lift
  let : Algebra E k := embedding.toRingHom.toAlgebra
  let : IsScalarTower k E k := IsScalarTower.of_algebraMap_eq' embedding.comp_algebraMap.symm
  refine ⟨r, ⟨(CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange E k _)).symm ≪≫
    (CharacterDescent.extendedHopfFunctor k).mapIso e ≪≫
    CharacterDescent.extendedHopfTower k A ≪≫ ?_⟩⟩
  exact CommHopfAlgCat.isoMk (Bialgebra.TensorProduct.lid k A)

private theorem isSplitTorus_of_torus [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (h : IsTorus G.val) : IsSplitTorus G.val := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  have hA := (CharacterDescent.torusOnSchemes A).mpr (isTorus_of_iso e h)
  obtain ⟨r, ⟨d⟩⟩ := torusHopf_split A hA
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨e.symm ≪≫ (hopfSpec (CommRingCat.of k)).mapIso d.op ≪≫ i⟩⟩

private theorem isTorus_of_split {G : GroupScheme k} (h : IsSplitTorus G) :
    IsTorus G := by
  refine ⟨k, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := h
  have hb : fieldSpecMap k k = 𝟙 _ := Spec.map_id _
  let P (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) := Over.pullback b
  let c : baseChange k k ≅ 𝟭 _ := eqToIso (congrArg P hb) ≪≫ Over.pullbackId
  let d : groupBaseChange k k ≅ 𝟭 _ := Functor.mapGrpNatIso c ≪≫ Functor.mapGrpIdIso
  exact ⟨r, ⟨d.app G ≪≫ e⟩⟩

private theorem splitTorus_baseChange (K : Type u) [Field K] [Algebra k K] (r : ℕ) :
    Nonempty ((groupBaseChange k K).obj (StandardGroups.multiplicativePowerGroup k
      (ULift.{u} (Fin r))).val ≅
      (StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin r))).val) := by
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := k) r
  obtain ⟨j⟩ := CharacterDescent.standardSplitTorus (k := K) r
  let a := groupAlgebra k (Specs.CharacterDescent.StandardLattice.{u} r)
  exact ⟨(groupBaseChange k K).mapIso i.symm ≪≫ (extendedGroupIso K a).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso
      (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k K _)).op.symm ≪≫ j⟩

private theorem splitTorus_integral (r : ℕ) :
    IsIntegral (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val.X.left := by
  let I := ULift.{u} (Fin r)
  let f : (I → ℤ) →ₙ+ Lex (I → ℤ) := (AddMonoidHom.id _).toAddHom
  let : UniqueSums (I → ℤ) := .of_injective_addHom f (fun _ _ h ↦ h) inferInstance
  have : IsDomain (StandardGroups.LaurentPowerCoordinates k I) :=
    inferInstanceAs (IsDomain (AddMonoidAlgebra k (I → ℤ)))
  exact (affine_isIntegral_iff _).mpr this

open private isIso_of_schemeIso definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq
  from LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem trivial_isSplitTorus : IsSplitTorus (Grp.trivial (SchemeOver k)) := by
  let M := Specs.CharacterDescent.StandardLattice.{u} 0
  let A := CommHopfAlgCat.of k k
  let f : specGroup A ⟶ Grp.trivial (SchemeOver k) := default
  have hf : f.hom.hom.left = (specGroup A).X.hom := by
    have h := f.hom.hom.w
    change f.hom.hom.left ≫ 𝟙 _ = (specGroup A).X.hom at h
    rwa [Category.comp_id] at h
  have hA : (specGroup A).X.hom = 𝟙 _ := Spec.map_id _
  have : IsIso f.hom.hom.left := by rw [hf, hA]; infer_instance
  have : IsIso f := isIso_of_schemeIso f
  let e : groupAlgebra k M ≅ A := CommHopfAlgCat.isoMk (MonoidAlgebra.bialgEquivOfSubsingleton M)
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := k) 0
  exact ⟨0, ⟨(asIso f).symm ≪≫ (hopfSpec (CommRingCat.of k)).mapIso e.op ≪≫ i⟩⟩

private theorem maximalTorus_exists [IsAlgClosed k] (G : AffineAlgebraicGroup k) :
    ∃ T : ClosedSubgroup G.val, IsMaximalTorus T := by
  classical
  have := G.property.1
  have := G.property.2.1
  have hGn : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  have : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    hGn.component_noetherian ⟨⊤, isAffineOpen_top G.val.X.left⟩
  have hprime (H : ClosedSubgroup G.val) (hH : IsTorus H.group) :
      (definingIdeal H).IsPrime := by
    obtain ⟨r, ⟨e⟩⟩ := isSplitTorus_of_torus (closedSubgroupAlgebraicGroup H) hH
    let e' := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
    have := splitTorus_integral (k := k) r
    have : Nonempty H.group.X.left :=
      ⟨η[H.group.X].left (IsLocalRing.closedPoint k)⟩
    let e'' : H.group.X.left ≅
        (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val.X.left := e'
    have : IsIntegral H.group.X.left := isIntegral_of_isOpenImmersion e''.hom
    exact RingHom.ker_isPrime _
  let score (H : ClosedSubgroup G.val) := (definingIdeal H).height.toNat
  let eligible (n : ℕ) := ∃ H : ClosedSubgroup G.val, IsTorus H.group ∧ score H = n
  have hex : ∃ n, eligible n := by
    refine ⟨_, Specs.GeometricRadicals.identitySubgroup G, ?_, rfl⟩
    exact isTorus_of_split trivial_isSplitTorus
  obtain ⟨T, hT, hscore⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  rintro S hS ⟨f, hf⟩
  have hle := definingIdeal_le f hf
  have he : definingIdeal T = definingIdeal S := by
    by_contra hn
    have := hprime T hT
    have := hprime S hS
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime
      (lt_of_le_of_ne hle (Ne.symm hn))
    have hlt' : score S < score T := by
      have eqS := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal S))
      have eqT := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal T))
      exact ENat.natCast_lt_natCast.mp (eqS.symm ▸ eqT.symm ▸ hlt)
    exact (not_lt_of_ge (hscore ▸ Nat.find_min' hex ⟨S, hS, rfl⟩)) hlt'
  have : IsIso f := factor_iso_of_definingIdeal_eq f hf he
  exact ⟨inv f, by rw [← hf, IsIso.inv_hom_id_assoc]⟩

end Tori

section Twisting

variable {K : Type u} [Field K] [Algebra k K]
private abbrev scalarIso (σ : K ≃ₐ[k] K) :
    Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of K) :=
  Scheme.Spec.mapIso (σ.toRingEquiv.toCommRingCatIso).op

private theorem scalarIso_hom_comp (σ : K ≃ₐ[k] K) :
    (scalarIso σ).hom ≫ fieldSpecMap k K = fieldSpecMap k K := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ fieldSpecMap k K = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact σ.commutes a

private theorem scalarIso_inv_comp (σ : K ≃ₐ[k] K) :
    (scalarIso σ).inv ≫ fieldSpecMap k K = fieldSpecMap k K := scalarIso_hom_comp σ.symm

private abbrev twist (σ : K ≃ₐ[k] K) : SchemeOver K ⥤ SchemeOver K :=
  Over.map (scalarIso σ).hom

private instance (σ : K ≃ₐ[k] K) : (twist σ).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

private abbrev twistGroups (σ : K ≃ₐ[k] K) : GroupScheme K ⥤ GroupScheme K :=
  (twist σ).mapGrp

private def twistBaseChangeIso (σ : K ≃ₐ[k] K) :
    baseChange k K ⋙ twist σ ≅ baseChange k K :=
  NatIso.ofComponents (fun X =>
    let f := X.hom
    let b := fieldSpecMap k K
    let s := scalarIso σ
    let l := pullback.fst f b
    let r := pullback.snd f b
    let hs : l ≫ f = (r ≫ s.hom) ≫ b := by
      rw [Category.assoc, scalarIso_hom_comp, pullback.condition]
    let ht : l ≫ f = (r ≫ s.inv) ≫ b := by
      rw [Category.assoc, scalarIso_inv_comp, pullback.condition]
    { hom := Over.homMk (pullback.lift l (r ≫ s.hom) hs) (pullback.lift_snd _ _ _)
      inv := Over.homMk (pullback.lift l (r ≫ s.inv) ht) (by
        change pullback.lift l (r ≫ s.inv) ht ≫ r ≫ s.hom = r
        rw [← Category.assoc, pullback.lift_snd, Category.assoc,
          Iso.inv_hom_id, Category.comp_id])
      hom_inv_id := by
        apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · change (pullback.lift l (r ≫ s.hom) hs ≫ pullback.lift l (r ≫ s.inv) ht) ≫ l =
            𝟙 _ ≫ l
          rw [Category.assoc, show pullback.lift l (r ≫ s.inv) ht ≫ l = l from
            pullback.lift_fst _ _ _, pullback.lift_fst, Category.id_comp]
        · change (pullback.lift l (r ≫ s.hom) hs ≫ pullback.lift l (r ≫ s.inv) ht) ≫ r =
            𝟙 _ ≫ r
          rw [Category.assoc, show pullback.lift l (r ≫ s.inv) ht ≫ r = r ≫ s.inv from
            pullback.lift_snd _ _ _, ← Category.assoc, pullback.lift_snd, Category.assoc,
            Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · change (pullback.lift l (r ≫ s.inv) ht ≫ pullback.lift l (r ≫ s.hom) hs) ≫ l =
            𝟙 _ ≫ l
          rw [Category.assoc, show pullback.lift l (r ≫ s.hom) hs ≫ l = l from
            pullback.lift_fst _ _ _, pullback.lift_fst, Category.id_comp]
        · change (pullback.lift l (r ≫ s.inv) ht ≫ pullback.lift l (r ≫ s.hom) hs) ≫ r =
            𝟙 _ ≫ r
          rw [Category.assoc, show pullback.lift l (r ≫ s.hom) hs ≫ r = r ≫ s.hom from
            pullback.lift_snd _ _ _, ← Category.assoc, pullback.lift_snd, Category.assoc,
            Iso.inv_hom_id, Category.comp_id, Category.id_comp] }) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [Over.pullback]
    · simp [Over.pullback])

private def twistGroupBaseChangeIso (σ : K ≃ₐ[k] K) :
    groupBaseChange k K ⋙ twistGroups σ ≅ groupBaseChange k K :=
  Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso (twistBaseChangeIso σ)

end Twisting


section SubgroupDescent

variable {K : Type u} [Field K] [Algebra k K]

open private extendedSpecIso extendedSpecIso_hom_fst extendedGroupIso extendedSpecIso_natural
  specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private def coefficientMap (σ : K ≃ₐ[k] K) (A : HopfAlgebraCategory k) :
    (K ⊗[k] A) →ₐ[k] (K ⊗[k] A) :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)

private theorem coefficientMap_spec (σ : K ≃ₐ[k] K) (A : HopfAlgebraCategory k) :
    (extendedSpecIso K A).hom.left ≫
      ((twistGroupBaseChangeIso σ).app (specGroup A)).hom.hom.hom.left =
    Spec.map (CommRingCat.ofHom (coefficientMap σ A).toRingHom) ≫
      (extendedSpecIso K A).hom.left := by
  let X := (specGroup A).X
  let g := (extendedSpecIso K A).hom.left
  let s := (scalarIso σ).hom
  let c := Spec.map (CommRingCat.ofHom (coefficientMap σ A).toRingHom)
  change g ≫ pullback.lift (pullback.fst X.hom (fieldSpecMap k K))
    (pullback.snd X.hom (fieldSpecMap k K) ≫ s) _ = c ≫ g
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, extendedSpecIso_hom_fst]
    rw [← Spec.map_comp]
    congr 1
    ext a
    change (1 : K) ⊗ₜ[k] a = coefficientMap σ A ((1 : K) ⊗ₜ[k] a)
    simp [coefficientMap]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Category.assoc c]
    have h : g ≫ pullback.snd X.hom (fieldSpecMap k K) =
        Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) :=
      (extendedSpecIso K A).hom.w
    rw [h]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

private theorem quotient_baseChange_iso (A : HopfAlgebraCategory k) (I : Ideal A)
    (J : Ideal (extendedHopf K A)) [I.IsHopfIdeal k] [J.IsHopfIdeal K]
    (h : extendedIdeal K I = J) :
    ∃ r : extendedHopf K (hopfQuotient A I) ≅ hopfQuotient (extendedHopf K A) J,
      extendedHopfMap K (hopfQuotientMap A I) =
        hopfQuotientMap (extendedHopf K A) J ≫ r.inv := by
  subst J
  obtain ⟨c, hc⟩ := extendedHopfQuotient k K A I
  exact ⟨c.symm, hc.symm⟩

private theorem descend_stable_subgroup (σ : K ≃ₐ[k] K)
    (hfixed : ∀ x : K, σ x = x → x ∈ Set.range (algebraMap k K))
    (G : AffineAlgebraicGroup k) (H : ClosedSubgroup ((groupBaseChange k K).obj G.val))
    (d : (twistGroups σ).obj H.group ≅ H.group)
    (hd : d.hom ≫ H.inclusion =
      (twistGroups σ).map H.inclusion ≫ ((twistGroupBaseChangeIso σ).app G.val).hom) :
    ∃ (N : ClosedSubgroup G.val)
      (e : (groupBaseChange k K).obj N.group ≅ H.group),
      e.hom ≫ H.inclusion = (groupBaseChange k K).map N.inclusion := by
  obtain ⟨A, _, ⟨a⟩⟩ := groupPresentation G
  let E := extendedGroupIso K A ≪≫ (groupBaseChange k K).mapIso a
  let j := H.inclusion ≫ E.inv
  let S := (Grp.forget (SchemeOver K)) ⋙ Over.forget _
  have hj : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion (S.map H.inclusion ≫ (S.mapIso E).inv)
    have : IsClosedImmersion (S.map H.inclusion) := H.isClosedImmersion
    exact IsClosedImmersion.comp _ _
  obtain ⟨J, ⟨hJ, b, hb⟩, _⟩ := (closedSubgroupClassification K (extendedHopf K A)
    H.group j).mp hj
  let := hJ
  let q := specGroupMap (hopfQuotientMap (extendedHopf K A) J)
  change b.hom ≫ q = H.inclusion ≫ E.inv at hb
  have hb' : b.hom ≫ q ≫ E.hom = H.inclusion := by
    rw [← Category.assoc, hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let Y := ((groupBaseChange k K).obj G.val).X.left
  let D : Y ⟶ Y := ((twistGroupBaseChangeIso σ).app G.val).hom.hom.hom.left
  let e := E.hom.hom.hom.left
  let C := Spec.map (CommRingCat.ofHom (coefficientMap σ A).toRingHom)
  have he : e ≫ D = C ≫ e := by
    have hn := (twistGroupBaseChangeIso σ).hom.naturality a.hom
    have hn' := congrArg (fun f ↦ f.hom.hom.left) hn
    change ((groupBaseChange k K).map a.hom).hom.hom.left ≫ D =
      ((twistGroupBaseChangeIso σ).app (specGroup A)).hom.hom.hom.left ≫
      ((groupBaseChange k K).map a.hom).hom.hom.left at hn'
    let m : ((groupBaseChange k K).obj (specGroup A)).X.left ⟶ Y :=
      ((groupBaseChange k K).map a.hom).hom.hom.left
    let D₀ : ((groupBaseChange k K).obj (specGroup A)).X.left ⟶
        ((groupBaseChange k K).obj (specGroup A)).X.left :=
      ((twistGroupBaseChangeIso σ).app (specGroup A)).hom.hom.hom.left
    let g := (extendedSpecIso K A).hom.left
    have h₀ : g ≫ D₀ = C ≫ g := coefficientMap_spec σ A
    change m ≫ D = D₀ ≫ m at hn'
    change (g ≫ m) ≫ D = C ≫ g ≫ m
    rw [Category.assoc, hn', ← Category.assoc g, h₀, Category.assoc]
  let d' : H.group.X.left ⟶ H.group.X.left := d.hom.hom.hom.left
  let b' := b.hom.hom.hom.left
  let bInv := b.inv.hom.hom.left
  let i := H.inclusion.hom.hom.left
  let q' := q.hom.hom.left
  have hd' : d' ≫ i = i ≫ D := congrArg (fun f ↦ f.hom.hom.left) hd
  have hbi : b' ≫ q' ≫ e = i := congrArg (fun f ↦ f.hom.hom.left) hb'
  have hq : q' ≫ C = (bInv ≫ d' ≫ b') ≫ q' := by
    let e' := ((Grp.forget (SchemeOver K)) ⋙ Over.forget _).mapIso E
    apply (cancel_mono e'.hom).mp
    change (q' ≫ C) ≫ e = ((bInv ≫ d' ≫ b') ≫ q') ≫ e
    have hcancel : bInv ≫ b' = 𝟙 _ :=
      (((Grp.forget (SchemeOver K)) ⋙ Over.forget _).mapIso b).inv_hom_id
    have hprior : bInv ≫ i = q' ≫ e := by
      rw [← hbi, ← Category.assoc, hcancel, Category.id_comp]
    calc
      (q' ≫ C) ≫ e = (q' ≫ e) ≫ D := by rw [Category.assoc, ← he, Category.assoc]
      _ = bInv ≫ (i ≫ D) := by rw [← hprior, Category.assoc]
      _ = bInv ≫ d' ≫ i := by rw [← hd']
      _ = (bInv ≫ d' ≫ b') ≫ q' ≫ e := by rw [← hbi]; simp only [Category.assoc]
  let f := Spec.preimage (bInv ≫ d' ≫ b')
  let qR := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let cR := CommRingCat.ofHom (coefficientMap σ A).toRingHom
  have hf : cR ≫ qR = qR ≫ f := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    change q' ≫ C = Spec.map f ≫ q'
    rw [Spec.map_preimage]
    exact hq
  have hStable : ∀ x ∈ J, coefficientMap σ A x ∈ J := by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx' := ConcreteCategory.congr_hom hf x
    change Ideal.Quotient.mk J (coefficientMap σ A x) = f (Ideal.Quotient.mk J x) at hx'
    rw [hx', Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let I := J.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
  have hIJ : extendedIdeal K I = J := extend_contract_of_stable σ hfixed J hStable
  let hI := hopfIdeal_of_extension (K := K) A I (hIJ.symm ▸ hJ)
  let N : ClosedSubgroup G.val :=
    ⟨specGroup (hopfQuotient A I), specGroupMap (hopfQuotientMap A I) ≫ a.hom, by
      let Sk := (Grp.forget (SchemeOver k)) ⋙ Over.forget _
      change IsClosedImmersion (Sk.map (specGroupMap (hopfQuotientMap A I)) ≫ (Sk.mapIso a).hom)
      have : IsClosedImmersion (Sk.map (specGroupMap (hopfQuotientMap A I))) :=
        (hopfMapClosedImmersion k (hopfQuotientMap A I)).mpr Ideal.Quotient.mk_surjective
      exact IsClosedImmersion.comp _ _⟩
  obtain ⟨r, hr⟩ := quotient_baseChange_iso A I J hIJ
  let er := (hopfSpec (CommRingCat.of K)).mapIso r.op
  let eI := extendedGroupIso K (hopfQuotient A I)
  have hdQ : er.inv ≫ q = specGroupMap (extendedHopfMap K (hopfQuotientMap A I)) := by
    rw [hr, specGroupMap_comp]
    rfl
  have hnat : specGroupMap (extendedHopfMap K (hopfQuotientMap A I)) ≫
      (extendedGroupIso K A).hom =
      eI.hom ≫ (groupBaseChange k K).map (specGroupMap (hopfQuotientMap A I)) := by
    apply Grp.hom_ext
    exact extendedSpecIso_natural K (hopfQuotientMap A I)
  refine ⟨N, eI.symm ≪≫ er.symm ≪≫ b.symm, ?_⟩
  change (eI.inv ≫ er.inv ≫ b.inv) ≫ H.inclusion =
    (groupBaseChange k K).map (specGroupMap (hopfQuotientMap A I) ≫ a.hom)
  let extq := specGroupMap (extendedHopfMap K (hopfQuotientMap A I))
  calc
    _ = eI.inv ≫ er.inv ≫ q ≫ E.hom := by
      rw [← hb']; simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = eI.inv ≫ extq ≫ E.hom := by
      change er.inv ≫ q = extq at hdQ
      rw [← hdQ, Category.assoc]
    _ = eI.inv ≫ (extq ≫ (extendedGroupIso K A).hom) ≫ (groupBaseChange k K).map a.hom := by
      simp only [E, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    _ = _ := by
      change extq ≫ (extendedGroupIso K A).hom =
        eI.hom ≫ (groupBaseChange k K).map (specGroupMap (hopfQuotientMap A I)) at hnat
      rw [hnat, Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SubgroupDescent

section SubgroupTransport

private abbrev schemeOfGroup (k : Type u) [Field k] : GroupScheme k ⥤ Scheme :=
  Grp.forget (SchemeOver k) ⋙ Over.forget _

private theorem closedImmersion_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) :
    IsClosedImmersion (f ≫ e.hom) ↔ IsClosedImmersion f := by
  constructor
  · intro h
    have := IsClosedImmersion.comp (f ≫ e.hom) e.inv
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  · intro h
    exact IsClosedImmersion.comp f e.hom

private def imageSubgroup (F : GroupScheme k ⥤ GroupScheme k)
    (hF : ∀ {X Y} (f : X ⟶ Y),
      IsClosedImmersion (F.map f).hom.hom.left ↔ IsClosedImmersion f.hom.hom.left)
    {G G' : GroupScheme k} (e : F.obj G ≅ G') (H : ClosedSubgroup G) : ClosedSubgroup G' :=
  ⟨F.obj H.group, F.map H.inclusion ≫ e.hom, by
    change IsClosedImmersion ((schemeOfGroup k).map (F.map H.inclusion) ≫
      ((schemeOfGroup k).mapIso e).hom)
    exact (closedImmersion_comp_iso _ _).mpr ((hF H.inclusion).mpr H.isClosedImmersion)⟩

/-- An equivalence preserving the closed immersions and the subgroup property
preserves maximality among closed subgroups of an affine algebraic group. -/
private theorem maximal_image (F : GroupScheme k ⥤ GroupScheme k) [F.IsEquivalence]
    (hF : ∀ {X Y} (f : X ⟶ Y),
      IsClosedImmersion (F.map f).hom.hom.left ↔ IsClosedImmersion f.hom.hom.left)
    {G G' : AffineAlgebraicGroup k} (e : F.obj G.val ≅ G'.val)
    (P : GroupScheme k → Prop)
    (hIso : ∀ (X : AffineAlgebraicGroup k) {Y : GroupScheme k}, (X.val ≅ Y) → P X.val → P Y)
    (hP : ∀ H : AffineAlgebraicGroup k, P (F.obj H.val) ↔ P H.val)
    (H : ClosedSubgroup G.val) (hH : P H.group)
    (hMax : ∀ N : ClosedSubgroup G.val, P N.group → IsSubgroupOf H N → IsSubgroupOf N H) :
    let H' := imageSubgroup F hF e H
    P H'.group ∧ ∀ N : ClosedSubgroup G'.val, P N.group → IsSubgroupOf H' N → IsSubgroupOf N H' := by
  dsimp
  refine ⟨(hP (closedSubgroupAlgebraicGroup H)).mpr hH, ?_⟩
  intro N hN h
  obtain ⟨j, hj⟩ := h
  let M := F.asEquivalence.inverse.obj N.group
  let d : F.obj M ≅ N.group := F.asEquivalence.counitIso.app N.group
  let f : M ⟶ G.val := F.preimage (d.hom ≫ N.inclusion ≫ e.inv)
  have hf : F.map f = d.hom ≫ N.inclusion ≫ e.inv := F.map_preimage _
  have hfc : IsClosedImmersion f.hom.hom.left := by
    apply (hF f).mp
    rw [hf]
    let S := schemeOfGroup k
    change IsClosedImmersion ((S.mapIso d).hom ≫ S.map N.inclusion ≫ (S.mapIso e).inv)
    have hc : IsClosedImmersion (S.map N.inclusion) := N.isClosedImmersion
    exact IsClosedImmersion.comp _ _
  let L : ClosedSubgroup G.val := ⟨M, f, hfc⟩
  let a : H.group ⟶ M := F.preimage (j ≫ d.inv)
  have ha : F.map a = j ≫ d.inv := F.map_preimage _
  change F.obj H.group ⟶ N.group at j
  change j ≫ N.inclusion = F.map H.inclusion ≫ e.hom at hj
  have haf : a ≫ L.inclusion = H.inclusion := by
    apply F.map_injective
    change F.map (a ≫ f) = F.map H.inclusion
    rw [F.map_comp, ha, hf, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hj]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hL : P L.group := (hP (closedSubgroupAlgebraicGroup L)).mp (hIso (closedSubgroupAlgebraicGroup N) d.symm hN)
  obtain ⟨b, hb⟩ := hMax L hL ⟨a, haf⟩
  change M ⟶ H.group at b
  change b ≫ H.inclusion = f at hb
  refine ⟨d.inv ≫ F.map b, ?_⟩
  change (d.inv ≫ F.map b) ≫ F.map H.inclusion ≫ e.hom = _
  rw [Category.assoc, ← Category.assoc (F.map b), ← F.map_comp, hb]
  rw [hf, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem maximal_of_subgroup_iso {G : AffineAlgebraicGroup k}
    (P : GroupScheme k → Prop)
    (hIso : ∀ (X : AffineAlgebraicGroup k) {Y : GroupScheme k}, (X.val ≅ Y) → P X.val → P Y)
    {H N : ClosedSubgroup G.val} (d : H.group ≅ N.group) (hd : d.hom ≫ N.inclusion = H.inclusion)
    (hH : P H.group)
    (hMax : ∀ S : ClosedSubgroup G.val, P S.group → IsSubgroupOf H S → IsSubgroupOf S H) :
    P N.group ∧ ∀ S : ClosedSubgroup G.val, P S.group → IsSubgroupOf N S → IsSubgroupOf S N := by
  refine ⟨hIso (closedSubgroupAlgebraicGroup H) d hH, ?_⟩
  rintro S hS ⟨i, hi⟩
  have hi' : (d.hom ≫ i) ≫ S.inclusion = H.inclusion := by
    rw [Category.assoc, hi, hd]
  obtain ⟨j, hj⟩ := hMax S hS ⟨d.hom ≫ i, hi'⟩
  exact ⟨j ≫ d.hom, by rw [Category.assoc, hd, hj]⟩

end SubgroupTransport

section TransportOfProperties

private abbrev SmoothConnectedSolvable (G : GroupScheme k) : Prop :=
  Smooth G.X.hom ∧ ConnectedSpace G.X.left ∧ Specs.SchemeDerivedGroup.IsSolvable G

private abbrev IsMaximalFor {G : GroupScheme k} (P : GroupScheme k → Prop)
    (H : ClosedSubgroup G) : Prop :=
  P H.group ∧ ∀ N : ClosedSubgroup G, P N.group → IsSubgroupOf H N → IsSubgroupOf N H

open private rationalMap solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem smoothConnectedSolvable_iso [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    {H : GroupScheme k} (e : G.val ≅ H) (h : SmoothConnectedSolvable G.val) :
    SmoothConnectedSolvable H := by
  let d := (schemeOfGroup k).mapIso e
  have he : d.hom ≫ H.X.hom = G.val.X.hom := Over.w e.hom.hom.hom
  let _ : IsAffine ((schemeOfGroup k).obj G.val) := G.property.1
  let A : AffineAlgebraicGroup k := ⟨H, IsAffine.of_isIso d.inv,
    (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType d.hom _).mp
      (he.symm ▸ G.property.2.1),
    (MorphismProperty.cancel_left_of_respectsIso @QuasiCompact d.hom _).mp
      (he.symm ▸ G.property.2.2)⟩
  have hs : Smooth H.X.hom :=
    (MorphismProperty.cancel_left_of_respectsIso @Smooth d.hom _).mp (he.symm ▸ h.1)
  have hc : ConnectedSpace H.X.left := d.hom.homeomorph.connectedSpace_iff.mp h.2.1
  let := (solvable_iff_sections G h.1 h.2.1).mp h.2.2
  have hsurj : Function.Surjective (rationalMap e.hom) := by
    intro p
    refine ⟨p ≫ e.inv.hom.hom, ?_⟩
    change (p ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = p
    have hi := ((Grp.forget (SchemeOver k)).mapIso e).inv_hom_id
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ at hi
    rw [Category.assoc, hi, Category.comp_id]
  exact ⟨hs, hc, (solvable_iff_sections A hs hc).mpr (Group.isSolvable_of_surjective hsurj)⟩

end TransportOfProperties

section TwistedSubgroups

variable {K : Type u} [Field K] [Algebra k K]

open private sectionsMap solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals

private instance (σ : K ≃ₐ[k] K) : (twistGroups σ).IsEquivalence := by
  let F := twist σ
  change F.mapGrp.IsEquivalence
  let _ : F.IsEquivalence := inferInstanceAs ((Over.map (scalarIso σ).hom).IsEquivalence)
  refine ⟨inferInstance, inferInstance, ⟨fun G ↦ ?_⟩⟩
  exact (Functor.essImage_mapGrp (F := F)).mpr (Functor.EssSurj.mem_essImage F G.X)

private theorem twist_closedImmersion (σ : K ≃ₐ[k] K)
    {G H : GroupScheme K} (f : G ⟶ H) :
    IsClosedImmersion ((twistGroups σ).map f).hom.hom.left ↔
      IsClosedImmersion f.hom.hom.left := Iff.rfl

private def twistedAlgebraicGroup (σ : K ≃ₐ[k] K) (G : AffineAlgebraicGroup K) :
    AffineAlgebraicGroup K :=
  ⟨(twistGroups σ).obj G.val, G.property.1,
    (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFiniteType _ (scalarIso σ).hom).mpr
      G.property.2.1,
    (MorphismProperty.cancel_right_of_respectsIso @QuasiCompact _ (scalarIso σ).hom).mpr
      G.property.2.2⟩

open scoped CategoryTheory.Obj in
/-- A monoidal equivalence induces an isomorphism on groups of sections after
identifying the image of the group with its chosen model. -/
private def sectionsOfFunctor (F : SchemeOver K ⥤ SchemeOver K)
    [F.Monoidal] [F.Full] [F.Faithful]
    {G H : GroupScheme K} (e : F.mapGrp.obj G ≅ H) : Section G ≃* Section H := by
  let a := Functor.Monoidal.εIso F
  let d : F.obj G.X ≅ H.X := (Grp.forget (SchemeOver K)).mapIso e
  let _ : IsMonHom d.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  let f : Section G →* Section H :=
    { toFun := fun g ↦ a.hom ≫ F.map g ≫ d.hom
      map_one' := by rw [Functor.map_one, MonObj.one_comp, MonObj.comp_one]
      map_mul' := by
        intro g h
        rw [Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul] }
  refine MulEquiv.ofBijective f ?_
  constructor
  · intro g h hgh
    apply F.map_injective
    apply (cancel_mono d.hom).mp
    exact (cancel_epi a.hom).mp hgh
  · intro g
    obtain ⟨h, hh⟩ := F.map_surjective (a.inv ≫ g ≫ d.inv)
    refine ⟨h, ?_⟩
    change a.hom ≫ F.map h ≫ d.hom = g
    simp only [hh, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem smoothConnectedSolvable_twist_iff [IsAlgClosed K] (σ : K ≃ₐ[k] K)
    (G : AffineAlgebraicGroup K) :
    SmoothConnectedSolvable ((twistGroups σ).obj G.val) ↔ SmoothConnectedSolvable G.val := by
  let H := twistedAlgebraicGroup σ G
  have hs : Smooth H.val.X.hom ↔ Smooth G.val.X.hom :=
    MorphismProperty.cancel_right_of_respectsIso @Smooth _ (scalarIso σ).hom
  let e : Section G.val ≃* Section H.val :=
    sectionsOfFunctor (twist σ) (G := G.val) (Iso.refl _)
  constructor
  · intro h
    let _ : Group.IsSolvable (Section H.val) := (solvable_iff_sections H h.1 h.2.1).mp h.2.2
    exact ⟨hs.mp h.1, h.2.1, (solvable_iff_sections G (hs.mp h.1) h.2.1).mpr
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)⟩
  · intro h
    let _ : Group.IsSolvable (Section G.val) := (solvable_iff_sections G h.1 h.2.1).mp h.2.2
    exact ⟨hs.mpr h.1, h.2.1, (solvable_iff_sections H (hs.mpr h.1) h.2.1).mpr
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)⟩

private theorem isTorus_twist_iff [IsAlgClosed K] (σ : K ≃ₐ[k] K) (G : AffineAlgebraicGroup K) :
    IsTorus ((twistGroups σ).obj G.val) ↔ IsTorus G.val := by
  have standard (r : ℕ) :
      Nonempty ((twistGroups σ).obj (StandardGroups.multiplicativePowerGroup K
        (ULift.{u} (Fin r))).val ≅
        (StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin r))).val) := by
    obtain ⟨e⟩ := splitTorus_baseChange (k := k) K r
    exact ⟨(twistGroups σ).mapIso e.symm ≪≫
      (twistGroupBaseChangeIso σ).app _ ≪≫ e⟩
  constructor
  · intro h
    obtain ⟨r, ⟨i⟩⟩ := isSplitTorus_of_torus (twistedAlgebraicGroup σ G) h
    obtain ⟨j⟩ := standard r
    exact isTorus_of_split ⟨r, ⟨(twistGroups σ).preimageIso (i ≪≫ j.symm)⟩⟩
  · intro h
    obtain ⟨r, ⟨i⟩⟩ := isSplitTorus_of_torus G h
    obtain ⟨j⟩ := standard r
    exact isTorus_of_split ⟨r, ⟨(twistGroups σ).mapIso i ≪≫ j⟩⟩

private def twistedSections (σ : K ≃ₐ[k] K) (G : GroupScheme k) :
    Section ((groupBaseChange k K).obj G) ≃* Section ((groupBaseChange k K).obj G) :=
  sectionsOfFunctor (twist σ) ((twistGroupBaseChangeIso σ).app G)

open scoped CategoryTheory.Obj in
private theorem twist_conjugation (σ : K ≃ₐ[k] K) (G : GroupScheme k)
    (g : Section ((groupBaseChange k K).obj G)) :
    (twistGroups σ).map (conjugationIso g).hom ≫ ((twistGroupBaseChangeIso σ).app G).hom =
      ((twistGroupBaseChangeIso σ).app G).hom ≫ (conjugationIso (twistedSections σ G g)).hom := by
  apply Grp.hom_ext
  let X := ((groupBaseChange k K).obj G).X
  let F := twist σ
  let e := (twistGroupBaseChangeIso σ).app G
  let d : F.obj X ⟶ X := e.hom.hom.hom
  let c := toUnit X ≫ g
  have hc : F.map c ≫ d = toUnit (F.obj X) ≫ twistedSections σ G g := by
    change F.map (toUnit X ≫ g) ≫ d =
      toUnit (F.obj X) ≫ (Functor.Monoidal.εIso F).hom ≫ F.map g ≫ d
    rw [F.map_comp, ← Functor.Monoidal.toUnit_ε F X]
    simp only [Category.assoc, Functor.Monoidal.εIso_hom]
  let m : (X ⟶ X) →* (F.obj X ⟶ X) :=
    (sectionsMap e.hom (F.obj X)).comp (F.homMonoidHom (X := X) (M := X))
  have hm (x : X ⟶ X) : m x = F.map x ≫ d := rfl
  change m (c * 𝟙 X * c⁻¹) = d ≫ conjugation (twistedSections σ G g)
  rw [map_mul, map_mul, map_inv, hm c, hc, hm (𝟙 X), F.map_id, Category.id_comp,
    comp_conjugation (twistedSections σ G g) d]

private theorem conjugation_mul {K : Type u} [Field K] {G : GroupScheme K} (g h : Section G) :
    (conjugationIso h).hom ≫ (conjugationIso g).hom = (conjugationIso (g * h)).hom := by
  apply Grp.hom_ext
  change conjugation h ≫ conjugation g = conjugation (g * h)
  rw [comp_conjugation]
  simp only [conjugation, MonObj.comp_mul, mul_inv_rev]
  group

end TwistedSubgroups

section FiniteFieldFrobenius

private def precompSections {K : Type u} [Field K] {X Y : SchemeOver K} (i : X ≅ Y)
    (G : GroupScheme K) : (Y ⟶ G.X) ≃* (X ⟶ G.X) where
  toFun g := i.hom ≫ g
  invFun g := i.inv ≫ g
  left_inv g := by simp
  right_inv g := by simp
  map_mul' _ _ := MonObj.comp_mul _ _ _

private def testUnitIso (K : Type u) [Field K] :
    (testSpec K).obj (op (CommAlgCat.of K K)) ≅ 𝟙_ (SchemeOver K) := by
  let S := Spec (CommRingCat.of K)
  let A : SchemeOver K := (testSpec K).obj (op (CommAlgCat.of K K))
  let B : SchemeOver K := 𝟙_ (SchemeOver K)
  let i : A.left ≅ B.left := Iso.refl S
  have hA : A.hom = 𝟙 S := Spec.map_id (CommRingCat.of K)
  refine Over.isoMk (f := A) (g := B) i ?_
  change 𝟙 S ≫ 𝟙 S = A.hom
  rw [hA, Category.id_comp]

open private testAlgebraIso frobeniusOnPoints_left pow_card_eq_self_iff
  from LinearAlgebraicGroups.Descent.SmoothLang

private def geometricSectionsEquiv (K : Type u) [Field K] [Algebra k K]
    (G : GroupScheme k) :
    Section ((groupBaseChange k K).obj G) ≃* Points G.X (CommAlgCat.of k K) :=
  let R := CommAlgCat.of K K
  let i := testAlgebraIso ((restrictTestAlgebra k K).obj R) (CommAlgCat.of k K)
    (RingEquiv.refl K) (fun _ ↦ rfl)
  (precompSections (testUnitIso K) _).trans
    ((baseChangePointGroupEquiv K G R).trans (precompSections ((testSpec k).mapIso i.op) G))

private theorem geometricSectionsEquiv_left {K : Type u} [Field K] [Algebra k K]
    (G : GroupScheme k) (g : Section ((groupBaseChange k K).obj G)) :
    (geometricSectionsEquiv K G g).left = g.left ≫ pullback.fst G.X.hom (fieldSpecMap k K) := by
  change Spec.map (𝟙 (CommRingCat.of K)) ≫
    (𝟙 (Spec (CommRingCat.of K)) ≫ g.left) ≫ _ = _
  rw [Spec.map_id, Category.id_comp, Category.id_comp]

private abbrev inverseFrobenius [Fintype k] :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)).symm

private theorem inverseFrobenius_fixed [Fintype k] (x : AlgebraicClosure k)
    (hx : inverseFrobenius x = x) : x ∈ Set.range (algebraMap k (AlgebraicClosure k)) := by
  apply (pow_card_eq_self_iff x).mp
  have h := congrArg (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) hx
  simpa only [inverseFrobenius, AlgEquiv.apply_symm_apply,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using h.symm

private theorem frobenius_on_geometricSections [Fintype k] (G : GroupScheme k)
    (g : Section ((groupBaseChange k (AlgebraicClosure k)).obj G)) :
    geometricSectionsEquiv (AlgebraicClosure k) G (twistedSections inverseFrobenius G g) =
      frobeniusOnPoints _ (geometricSectionsEquiv (AlgebraicClosure k) G g) := by
  let K := AlgebraicClosure k
  let σ := inverseFrobenius (k := k)
  let a := (Functor.Monoidal.εIso (twist σ)).hom
  have ha : a.left = (scalarIso σ).inv := by
    apply (cancel_mono (scalarIso σ).hom).mp
    have hw := Over.w a
    change a.left ≫ (𝟙 _ ≫ (scalarIso σ).hom) = 𝟙 _ at hw
    rw [Category.id_comp] at hw
    exact hw.trans (scalarIso σ).inv_hom_id.symm
  let p := pullback.fst G.X.hom (fieldSpecMap k K)
  let d := ((twistGroupBaseChangeIso σ).app G).hom.hom.hom.left
  have hd : d ≫ p = p := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  rw [geometricSectionsEquiv_left, frobeniusOnPoints_left, geometricSectionsEquiv_left]
  change (a.left ≫ g.left ≫ d) ≫ p = (scalarIso σ).inv ≫ g.left ≫ p
  simp only [Category.assoc, hd, ha]

private theorem lang_on_geometricSections [Fintype k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Function.Surjective (fun g : Section ((groupBaseChange k (AlgebraicClosure k)).obj G.val) ↦
      twistedSections inverseFrobenius G.val g * g⁻¹) := by
  let := hs
  let := hc
  let := G.property.2.2
  let e := geometricSectionsEquiv (AlgebraicClosure k) G.val
  intro g
  obtain ⟨b, hb⟩ := smoothLangSurjectivity k G.val (e g)
  refine ⟨e.symm b, e.injective ?_⟩
  rw [map_mul, map_inv]
  change geometricSectionsEquiv _ _ (twistedSections inverseFrobenius G.val (e.symm b)) *
    (e (e.symm b))⁻¹ = e g
  rw [frobenius_on_geometricSections]
  simpa only [e, MulEquiv.apply_symm_apply, langOnGeometricPoints] using hb

end FiniteFieldFrobenius

section FiniteFieldDescent

private theorem rational_maximal_subgroup [Fintype k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (P : GroupScheme (AlgebraicClosure k) → Prop)
    (hIso : ∀ (X : AffineAlgebraicGroup (AlgebraicClosure k))
      {Y : GroupScheme (AlgebraicClosure k)}, (X.val ≅ Y) → P X.val → P Y)
    (hP : ∀ X : AffineAlgebraicGroup (AlgebraicClosure k),
      P ((twistGroups (inverseFrobenius (k := k))).obj X.val) ↔ P X.val)
    (hConj : ∀ H N : ClosedSubgroup (GeometricGroup G).val,
      IsMaximalFor P H → IsMaximalFor P N →
        ∃ g : Section ((groupBaseChange k (AlgebraicClosure k)).obj G.val),
          ConjugatesSubgroups g H N)
    (H : ClosedSubgroup (GeometricGroup G).val) (hH : IsMaximalFor P H) :
    ∃ (N : ClosedSubgroup G.val) (h : IsClosedImmersion
      ((groupBaseChange k (AlgebraicClosure k)).map N.inclusion).hom.hom.left),
      IsMaximalFor P (baseChangedSubgroup (AlgebraicClosure k) N h) := by
  let σ := inverseFrobenius (k := k)
  let D := (twistGroupBaseChangeIso σ).app G.val
  let H' := imageSubgroup (twistGroups σ) (twist_closedImmersion σ) D H
  have hH' : IsMaximalFor P H' :=
    maximal_image (G := GeometricGroup G) (G' := GeometricGroup G)
      (twistGroups σ) (twist_closedImmersion σ) D P hIso hP H hH.1 hH.2
  obtain ⟨h, hh⟩ := hConj H H' hH hH'
  obtain ⟨a, ha⟩ := (conjugates_iff_iso h H H').mp hh
  obtain ⟨b, hb⟩ := lang_on_geometricSections G hs hc h
  let g := b⁻¹
  have hg : twistedSections σ G.val g * h = g := by
    change twistedSections σ G.val b⁻¹ * h = b⁻¹
    change twistedSections σ G.val b * b⁻¹ = h at hb
    rw [map_inv, ← hb, inv_mul_cancel_left]
  let S := imageSubgroup (𝟭 (GroupScheme (AlgebraicClosure k))) (fun _ ↦ Iff.rfl)
    (conjugationIso g) H
  have hS : IsMaximalFor P S :=
    maximal_image (G := GeometricGroup G) (G' := GeometricGroup G)
      (𝟭 (GroupScheme (AlgebraicClosure k))) (fun _ ↦ Iff.rfl) (conjugationIso g) P hIso
      (fun _ ↦ Iff.rfl) H hH.1 hH.2
  have hStable : a.inv ≫ S.inclusion = (twistGroups σ).map S.inclusion ≫ D.hom := by
    change a.inv ≫ H.inclusion ≫ (conjugationIso g).hom =
      (twistGroups σ).map (H.inclusion ≫ (conjugationIso g).hom) ≫ D.hom
    rw [Functor.map_comp, Category.assoc, twist_conjugation σ G.val g]
    change a.inv ≫ H.inclusion ≫ (conjugationIso g).hom =
      H'.inclusion ≫ (conjugationIso (twistedSections σ G.val g)).hom
    rw [← Iso.inv_hom_id_assoc a H'.inclusion, Category.assoc a.inv, ha]
    simp only [Category.assoc]
    rw [conjugation_mul, hg]
  obtain ⟨N, e, he⟩ := descend_stable_subgroup σ inverseFrobenius_fixed G S a.symm hStable
  let f := (groupBaseChange k (AlgebraicClosure k)).map N.inclusion
  change e.hom ≫ S.inclusion = f at he
  let U := schemeOfGroup (AlgebraicClosure k)
  have hf : IsClosedImmersion f.hom.hom.left := by
    change IsClosedImmersion (U.map f)
    have hi : IsClosedImmersion (U.map S.inclusion) := S.isClosedImmersion
    rw [← he, Functor.map_comp]
    exact IsClosedImmersion.comp (U.mapIso e).hom (U.map S.inclusion)
  refine ⟨N, hf, maximal_of_subgroup_iso (G := GeometricGroup G) P hIso e.symm ?_ hS.1 hS.2⟩
  change e.inv ≫ f = S.inclusion
  rw [← he, Iso.inv_hom_id_assoc]

end FiniteFieldDescent

open Specs.FiniteFieldFlags (RationalBorelExists GeometricallyMaximalTorusExists ReductiveQuasiSplit)
open Specs.GeometricBorelConjugacy (BorelExists BorelsConjugate ClosedFlagOrbitExists
  ClosedFlagStabilizerIsBorel TorusContainedInBorel)
open Specs.MaximalToriConjugate (BorelMaximalTorusIff BorelPairsConjugate ToriConjugate
  NormalizerTransitiveOnBorels)

/-- Rational Borel existence from the geometric conjugacy results and Lang's theorem. -/
theorem rationalBorelExists_conditional
    (borelExists : BorelExists.{u}) (borelsConjugate : BorelsConjugate.{u})
    (_closedFlagOrbitExists : ClosedFlagOrbitExists.{u})
    (_closedFlagStabilizerIsBorel : ClosedFlagStabilizerIsBorel.{u})
    (_torusContainedInBorel : TorusContainedInBorel.{u})
    (_borelMaximalTorusIff : BorelMaximalTorusIff.{u})
    (_borelPairsConjugate : BorelPairsConjugate.{u}) (_toriConjugate : ToriConjugate.{u})
    (_normalizerTransitiveOnBorels : NormalizerTransitiveOnBorels.{u}) :
    RationalBorelExists.{u} := by
  intro k _ _ G hs hc
  have hs' := geometric_smooth G hs
  have hc' := geometric_connected G hs hc
  obtain ⟨B, hB⟩ := borelExists (GeometricGroup G) hs' hc'
  obtain ⟨N, hN, hNB⟩ := rational_maximal_subgroup G hs hc SmoothConnectedSolvable
    smoothConnectedSolvable_iso (smoothConnectedSolvable_twist_iff inverseFrobenius)
    (borelsConjugate (GeometricGroup G) hs' hc') B hB
  exact ⟨N, hN, hNB⟩

/-- Geometrically maximal torus existence from geometric conjugacy and Lang's theorem. -/
theorem geometricallyMaximalTorusExists_conditional
    (_borelExists : BorelExists.{u}) (_borelsConjugate : BorelsConjugate.{u})
    (_closedFlagOrbitExists : ClosedFlagOrbitExists.{u})
    (_closedFlagStabilizerIsBorel : ClosedFlagStabilizerIsBorel.{u})
    (_torusContainedInBorel : TorusContainedInBorel.{u})
    (_borelMaximalTorusIff : BorelMaximalTorusIff.{u})
    (_borelPairsConjugate : BorelPairsConjugate.{u}) (toriConjugate : ToriConjugate.{u})
    (_normalizerTransitiveOnBorels : NormalizerTransitiveOnBorels.{u}) :
    GeometricallyMaximalTorusExists.{u} := by
  intro k _ _ G hs hc
  have hs' := geometric_smooth G hs
  have hc' := geometric_connected G hs hc
  obtain ⟨T, hT⟩ := maximalTorus_exists (GeometricGroup G)
  obtain ⟨N, hN, hNT⟩ := rational_maximal_subgroup G hs hc IsTorus
    (fun X {Y} (e : X.val ≅ Y) h ↦ isTorus_of_iso e.symm h)
    (isTorus_twist_iff inverseFrobenius)
    (toriConjugate (GeometricGroup G) hs' hc') T hT
  have hsplit := isSplitTorus_of_torus
    (closedSubgroupAlgebraicGroup (G := GeometricGroup G)
      (baseChangedSubgroup (AlgebraicClosure k) N hN)) hNT.1
  exact ⟨N, ⟨AlgebraicClosure k, inferInstance, inferInstance, inferInstance, hsplit⟩, hN, hNT⟩

/-- The Borel produced by the finite-field argument gives quasi-splitness. -/
theorem reductiveQuasiSplit_conditional
    (borelExists : BorelExists.{u}) (borelsConjugate : BorelsConjugate.{u})
    (closedFlagOrbitExists : ClosedFlagOrbitExists.{u})
    (closedFlagStabilizerIsBorel : ClosedFlagStabilizerIsBorel.{u})
    (torusContainedInBorel : TorusContainedInBorel.{u})
    (borelMaximalTorusIff : BorelMaximalTorusIff.{u})
    (borelPairsConjugate : BorelPairsConjugate.{u}) (toriConjugate : ToriConjugate.{u})
    (normalizerTransitiveOnBorels : NormalizerTransitiveOnBorels.{u}) :
    ReductiveQuasiSplit.{u} := by
  intro k _ _ G hG
  let := hG.2.1
  have hc : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  exact ⟨hG, rationalBorelExists_conditional borelExists borelsConjugate closedFlagOrbitExists
    closedFlagStabilizerIsBorel torusContainedInBorel borelMaximalTorusIff borelPairsConjugate
    toriConjugate normalizerTransitiveOnBorels G hG.1 hc⟩

end

end LinearAlgebraicGroups.Descent.FiniteFieldFlags

universe v8_closure_91c3ef7f9c266ac6_u0
theorem _root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«geometricallyMaximalTorusExists» : _root_.«LinearAlgebraicGroups».«Specs».«FiniteFieldFlags».«GeometricallyMaximalTorusExists».{v8_closure_91c3ef7f9c266ac6_u0} :=
  @_root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«geometricallyMaximalTorusExists_conditional».{v8_closure_91c3ef7f9c266ac6_u0} (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelMaximalTorusIff».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelPairsConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«maximalToriConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«normalizerTransitiveOnBorels».{v8_closure_91c3ef7f9c266ac6_u0})
theorem _root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«rationalBorelExists» : _root_.«LinearAlgebraicGroups».«Specs».«FiniteFieldFlags».«RationalBorelExists».{v8_closure_91c3ef7f9c266ac6_u0} :=
  @_root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«rationalBorelExists_conditional».{v8_closure_91c3ef7f9c266ac6_u0} (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelMaximalTorusIff».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelPairsConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«maximalToriConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«normalizerTransitiveOnBorels».{v8_closure_91c3ef7f9c266ac6_u0})
theorem _root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«reductiveQuasiSplit» : _root_.«LinearAlgebraicGroups».«Specs».«FiniteFieldFlags».«ReductiveQuasiSplit».{v8_closure_91c3ef7f9c266ac6_u0} :=
  @_root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«reductiveQuasiSplit_conditional».{v8_closure_91c3ef7f9c266ac6_u0} (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelMaximalTorusIff».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelPairsConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«maximalToriConjugate».{v8_closure_91c3ef7f9c266ac6_u0}) (@_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«normalizerTransitiveOnBorels».{v8_closure_91c3ef7f9c266ac6_u0})
