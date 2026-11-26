import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitLeviMatrixComparison
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Arithmetic.SplitLeviMatrixComparison

open _root_.LinearAlgebraicGroups.Specs
open Specs.SplitLeviMatrixComparison
open Specs.GeometricRadicals (IsSplitReductive)
open Pinning (SplitBorelPair AttachedDatum BasedRootDatum BasedIso)
open Specs.SimplyConnectedLattice (corootLatticeOf GeometricallySimplyConnected)
open GeneralLinearStructure (SpecialMatrixPoints)
open LinearAlgebraicGroups.OuterTypeAModels (basedDatumComparison)
open private specialMatrixModel matrixDatum_typeA from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
open private alignPairs pinAlignedPairs forgetClassification_reverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private fibreTowerIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section

private theorem basedIsoOfGroupIso {k : Type u} [Field k] (P Q : SplitBorelPair k)
    (D : AttachedDatum P) (E : AttachedDatum Q) (f : P.G.val ≅ Q.G.val) :
    Nonempty (BasedIso D.toBased E.toBased) := by
  obtain ⟨g, t, b, ht, hb⟩ := alignPairs P Q f
  obtain ⟨P', Q', hP, hQ, ⟨j⟩⟩ :=
    pinAlignedPairs P Q (Classification.Pinning.standardAdditiveLine k) g t ht b hb
  subst P
  subst Q
  exact ⟨Classification.Pinning.inducedBasedIso j D E⟩

/-- The integral model realizes the same based datum in both field fibres. -/
private theorem basedIsoOfScalarExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
    (P : SplitBorelPair k) (Q : SplitBorelPair K) (D : AttachedDatum P) (E : AttachedDatum Q)
    (f : (groupBaseChange k K).obj P.G.val ≅ Q.G.val) :
    Nonempty (BasedIso D.toBased E.toBased) := by
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨_, L, e, _, _, _, _, _, _⟩ := M.fieldFibre k
  obtain ⟨_, L', e', _, _, _, _, _, _⟩ := M.fieldFibre K
  obtain ⟨a⟩ := forgetClassification_reverse L.pinned.pair P L.attached D
    (L.datumIso.val.symm _ _)
  let b : L'.pinned.pair.G.val ≅ Q.G.val :=
    e'.symm ≪≫ (fibreTowerIso k K).app M.group ≪≫
      (groupBaseChange k K).mapIso (e ≪≫ a) ≪≫ f
  obtain ⟨c⟩ := basedIsoOfGroupIso L'.pinned.pair Q L'.attached E b
  refine ⟨⟨c.val.comp L'.datumIso.val, ?_⟩⟩
  change (fun x => c.val.indexEquiv (L'.datumIso.val.indexEquiv x)) ''
      (D.toBased.base.support : Set D.toBased.I) = _
  calc
    _ = c.val.indexEquiv '' (L'.datumIso.val.indexEquiv '' (D.toBased.base.support : Set D.toBased.I)) :=
      (Set.image_image _ _ _).symm
    _ = _ := (congrArg (Set.image c.val.indexEquiv) L'.datumIso.property).trans c.property

private theorem corootBasis {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (hP : GeometricRadicals.IsSemisimple P.G) (hSC : GeometricallySimplyConnected P.G) :
    ∃ b : Module.Basis D.toBased.base.support ℤ D.toBased.Y,
      ∀ i, b i = D.toBased.datum.coroot i := by
  letI := D.comm
  have h : corootLatticeOf D.datum = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.G hP P.T P.split P.maximal
      D.datum).mp hSC
  have hs : Set.range (fun i : D.toBased.base.support => D.toBased.datum.coroot i) =
      D.toBased.datum.coroot '' (D.toBased.base.support : Set D.toBased.I) :=
    (Set.image_eq_range _ _).symm
  have hb : Submodule.span ℤ (Set.range fun i : D.toBased.base.support =>
      D.toBased.datum.coroot i) = ⊤ := by
    rw [hs, D.toBased.base.span_int_coroot_support]
    exact h
  exact ⟨Module.Basis.mk D.toBased.base.linearIndepOn_coroot hb.ge, Module.Basis.mk_apply _ _⟩

private theorem matrixPair (k : Type u) [Field k] (r : ℕ) :
    ∃ (P : SplitBorelPair k) (D : AttachedDatum P),
      Nonempty (SpecialMatrixPoints P.G (r + 1)) ∧
      GeometricRadicals.IsSemisimple P.G ∧
      Specs.OuterTypeAModels.HasSimplyConnectedTypeA r D.toBased := by
  obtain ⟨S, ⟨s⟩⟩ := specialMatrixModel k (r + 1)
  obtain ⟨_, _, _, B, D, hD, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k r S s
  exact ⟨B.pair, D, ⟨s⟩, RootData.SpecialLinearDatum.semisimple k r S s, matrixDatum_typeA hD⟩

private theorem splitOfPair {k : Type u} [Field k] (P : SplitBorelPair k) :
    IsSplitReductive P.G :=
  ⟨P.reductive, P.T, P.split, P.maximal⟩

set_option maxHeartbeats 800000 in
theorem singleChain : SingleChain.{u} := by
  intro F _ R hR P hP hSC f D e hCartan
  let classification := Classification.PinnedEquivalence.pinnedEquivalence.2 F
  obtain ⟨P₀, h₀⟩ := classification.1 R hR
  subst R
  let D₀ := Classification.Pinning.attachedDatum P₀
  obtain ⟨a⟩ := basedIsoOfScalarExtension P₀ P D₀ D f.symm
  obtain ⟨b, hb⟩ := corootBasis D hP hSC
  obtain ⟨Q, E, hs, _, v, c, hc, hQ⟩ := matrixPair F 5
  let j := e.symm.trans v
  have h (i l : D.toBased.base.support) :
      D.toBased.datum.pairing i l = E.toBased.datum.pairing (j i) (j l) := by
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective l
    simpa [j, chainCartan] using (hCartan i l).trans (hQ i l).symm
  obtain ⟨d, _⟩ := basedDatumComparison D.toBased E.toBased b c hb hc j h
  exact ⟨Q.G, splitOfPair Q, hs, forgetClassification_reverse P₀ Q D₀ E (d.val.comp a.val)⟩

section Product

open Module
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open private SplitPairProduct SplitPairProduct.pair existsSplitPairProduct productSimpleEquiv
  simpleRootSupport cocharacterProduct productRoot_pairingLeft productRoot_pairingRight
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
open private productRootEquiv productCharacterEquiv productCharacterEquiv_root_left
  productCharacterEquiv_root_right tensorProductIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private rootFullRank_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem rootPairing_eq {k : Type u} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (i : Root P.T) (y : D.toBased.Y) :
    D.toBased.datum.toLinearMap (D.toBased.datum.root i) y =
      pairing P.T.group i.val (Additive.toMul y) := by
  letI := D.comm
  change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i)
    (Additive.ofMul (Additive.toMul y)) = _
  rw [D.datum.root_eq, D.datum.pairing_eq]

private theorem eq_of_root_evaluations (D : BasedRootDatum.{u})
    (hD : Finite (D.X ⧸ Submodule.span ℤ (Set.range D.datum.root)))
    (x y : D.Y) (h : ∀ i, D.datum.toLinearMap (D.datum.root i) x =
        D.datum.toLinearMap (D.datum.root i) y) : x = y := by
  let L := Submodule.span ℤ (Set.range D.datum.root)
  letI : Finite (D.X ⧸ L.toAddSubgroup) := hD
  let f := D.datum.flip.toLinearMap x
  let g := D.datum.flip.toLinearMap y
  have hs : L ≤ LinearMap.ker (f - g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (h i))
  apply D.datum.flip.toPerfPair.injective
  ext a
  change f a = g a
  have hn : (L.toAddSubgroup.index : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr AddSubgroup.index_ne_zero_of_finite
  have ha := LinearMap.mem_ker.mp (hs (AddSubgroup.nsmul_index_mem L.toAddSubgroup a))
  simp only [LinearMap.sub_apply, map_nsmul, nsmul_eq_mul] at ha
  exact sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_left hn)

set_option maxHeartbeats 1800000 in
private theorem productCoroots {k : Type u} [Field k] {P Q : SplitBorelPair k}
    (S : SplitPairProduct P Q) (D : AttachedDatum P) (E : AttachedDatum Q)
    (W : AttachedDatum (SplitPairProduct.pair S))
    (hP : Specs.GeometricRadicals.IsSemisimple P.G)
    (hQ : Specs.GeometricRadicals.IsSemisimple Q.G) :
    letI := D.comm
    letI := E.comm
    letI := W.comm
  letI : IsCommMonObj (P.T.group ⊗ Q.T.group).X := W.comm
    ∀ a : Root P.T ⊕ Root Q.T,
      cocharacterProduct P.T.group Q.T.group (W.toBased.datum.coroot (productRootEquiv P Q a)) =
        Sum.elim (fun i => (D.toBased.datum.coroot i, 0))
          (fun i => (0, E.toBased.datum.coroot i)) a := by
  letI := D.comm
  letI := E.comm
  letI := W.comm
  letI : IsCommMonObj (P.T.group ⊗ Q.T.group).X := W.comm
  letI : Finite (Root (SplitPairProduct.pair S).T) := W.datum.finiteRoots
  letI := W.datum.freeCharacters
  letI := D.toBased.freeX
  letI := D.toBased.finiteX
  letI := E.toBased.freeX
  letI := E.toBased.finiteX
  let A := W.datum.rootDatum
  let d := D.datum.rootDatum
  let e := E.datum.rootDatum
  let r : (Root P.T ⊕ Root Q.T) ≃ Root (SplitPairProduct.pair S).T := productRootEquiv P Q
  let π := cocharacterProduct P.T.group Q.T.group
  let χ := productCharacterEquiv P.T.group Q.T.group
  let l : D.toBased.X →ₗ[ℤ] W.toBased.X := χ.toLinearMap.comp (LinearMap.inl ℤ _ _)
  let m : E.toBased.X →ₗ[ℤ] W.toBased.X := χ.toLinearMap.comp (LinearMap.inr ℤ _ _)
  have hl (i : Root P.T) : l (d.root i) = A.root (r (.inl i)) := by
    change χ (d.root i, 0) = _
    erw [D.datum.root_eq, W.datum.root_eq]
    exact productCharacterEquiv_root_left P Q i
  have hm (i : Root Q.T) : m (e.root i) = A.root (r (.inr i)) := by
    change χ (0, e.root i) = _
    erw [E.datum.root_eq, W.datum.root_eq]
    exact productCharacterEquiv_root_right P Q i
  have pLeft (i : Root P.T) (y : W.toBased.Y) :
      A.toLinearMap (A.root (r (.inl i))) y = d.toLinearMap (d.root i) (π y).1 := by
    erw [rootPairing_eq W, rootPairing_eq D]
    exact productRoot_pairingLeft S i (Additive.toMul y)
  have pRight (i : Root Q.T) (y : W.toBased.Y) :
      A.toLinearMap (A.root (r (.inr i))) y = e.toLinearMap (e.root i) (π y).2 := by
    erw [rootPairing_eq W, rootPairing_eq E]
    exact productRoot_pairingRight S i (Additive.toMul y)
  let c (a : Root P.T ⊕ Root Q.T) : D.toBased.Y × E.toBased.Y :=
    Sum.elim (fun i => (d.coroot i, 0)) (fun i => (0, e.coroot i)) a
  intro a
  change π (A.coroot (r a)) = c a
  let v := π.symm (c a)
  have hv : π v = c a := π.apply_symm_apply _
  have htwo : A.toLinearMap (A.root (r a)) v = 2 := by
    cases a with
    | inl i => rw [pLeft, hv]; exact d.root_coroot_two i
    | inr i => rw [pRight, hv]; exact e.root_coroot_two i
  have hflip (x : W.toBased.X) : A.flip.toLinearMap v x = A.toLinearMap x v := rfl
  have hreflect : Set.MapsTo (preReflection (A.root (r a)) (A.flip.toLinearMap v))
      (Set.range A.root) (Set.range A.root) := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨j, rfl⟩ := r.surjective j
    cases a with
    | inl i =>
      cases j with
      | inl j =>
        refine ⟨r (.inl (d.reflectionPerm i j)), ?_⟩
        rw [preReflection_apply, hflip, pLeft, hv, ← hl, ← hl, ← hl]
        erw [← map_smul, ← map_sub]
        exact congrArg l (d.reflectionPerm_root i j).symm
      | inr j =>
        refine ⟨r (.inr j), ?_⟩
        rw [preReflection_apply, hflip, pRight, hv]
        change _ = _ - e.toLinearMap (e.root j) 0 • _
        rw [map_zero, zero_smul, sub_zero]
    | inr i =>
      cases j with
      | inl j =>
        refine ⟨r (.inl j), ?_⟩
        rw [preReflection_apply, hflip, pLeft, hv]
        change _ = _ - d.toLinearMap (d.root j) 0 • _
        rw [map_zero, zero_smul, sub_zero]
      | inr j =>
        refine ⟨r (.inr (e.reflectionPerm i j)), ?_⟩
        rw [preReflection_apply, hflip, pRight, hv, ← hm, ← hm, ← hm]
        erw [← map_smul, ← map_sub]
        exact congrArg m (e.reflectionPerm_root i j).symm
  let L := Submodule.span ℤ (Set.range A.root)
  have hf : L.subtype.dualMap (A.flip.toLinearMap (A.coroot (r a))) =
      L.subtype.dualMap (A.flip.toLinearMap v) :=
    Dual.eq_of_preReflection_mapsTo' (Set.finite_range A.root)
      (Submodule.subset_span (Set.mem_range_self (r a))) (A.coroot_root_two _)
      (A.mapsTo_reflection_root _) htwo hreflect
  have hh (i : Root (SplitPairProduct.pair S).T) :
      A.toLinearMap (A.root i) (A.coroot (r a)) = A.toLinearMap (A.root i) v :=
    LinearMap.congr_fun hf ⟨A.root i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hP' : Finite (D.toBased.X ⧸ Submodule.span ℤ (Set.range d.root)) :=
    (Submodule.finiteQuotient_iff _).mpr ((rootFullRank_iff P D).mp hP)
  have hQ' : Finite (E.toBased.X ⧸ Submodule.span ℤ (Set.range e.root)) :=
    (Submodule.finiteQuotient_iff _).mpr ((rootFullRank_iff Q E).mp hQ)
  rw [← hv]
  apply Prod.ext
  · apply eq_of_root_evaluations D.toBased hP'
    intro i
    exact (pLeft i _).symm.trans ((hh (r (.inl i))).trans (pLeft i _))
  · apply eq_of_root_evaluations E.toBased hQ'
    intro i
    exact (pRight i _).symm.trans ((hh (r (.inr i))).trans (pRight i _))

set_option maxHeartbeats 1200000 in
private theorem matrixProductPair (k : Type u) [Field k] :
    ∃ (P Q : SplitBorelPair k) (S : SplitPairProduct P Q)
      (W : AttachedDatum (SplitPairProduct.pair S)),
      Nonempty (SpecialMatrixPoints P.G 2) ∧ Nonempty (SpecialMatrixPoints Q.G 6) ∧
      ∃ (v : (Fin 1 ⊕ Fin 5) ≃ W.toBased.base.support)
        (b : Basis W.toBased.base.support ℤ W.toBased.Y),
        (∀ i, b i = W.toBased.datum.coroot i) ∧
        ∀ i j, W.toBased.datum.pairing (v i) (v j) = productCartan i j := by
  obtain ⟨P, D, hsP, hP, l, b, hb, hCartanP⟩ := matrixPair k 1
  obtain ⟨Q, E, hsQ, hQ, m, d, hd, hCartanQ⟩ := matrixPair k 5
  obtain ⟨S⟩ := existsSplitPairProduct P Q
  let W := Classification.Pinning.attachedDatum (SplitPairProduct.pair S)
  letI := D.comm
  letI := E.comm
  letI := W.comm
  letI : IsCommMonObj (P.T.group ⊗ Q.T.group).X := W.comm
  let r := productRootEquiv P Q
  let π := cocharacterProduct P.T.group Q.T.group
  let g := Equiv.sumCongr (l.trans (simpleRootSupport D).symm) (m.trans (simpleRootSupport E).symm)
  let v : (Fin 1 ⊕ Fin 5) ≃ W.toBased.base.support :=
    g.trans ((productSimpleEquiv S).trans (simpleRootSupport W))
  have hleft (i : Fin 1) : (v (.inl i)).val = r (.inl (l i).val) := rfl
  have hright (i : Fin 5) : (v (.inr i)).val = r (.inr (m i).val) := rfl
  have hc := productCoroots S D E W hP hQ
  let b' : Basis (Fin 1) ℤ (Additive (Cocharacter P.T.group)) := b.reindex l.symm
  let d' : Basis (Fin 5) ℤ (Additive (Cocharacter Q.T.group)) := d.reindex m.symm
  let C : Basis W.toBased.base.support ℤ W.toBased.Y := ((b'.prod d').map π.symm).reindex v
  have hC (i : Fin 1 ⊕ Fin 5) : π (C (v i)) = (b'.prod d') i := by
    erw [Basis.reindex_apply, v.symm_apply_apply, Basis.map_apply]
    exact π.apply_symm_apply _
  refine ⟨P, Q, S, W, hsP, hsQ, v, C, ?_, ?_⟩
  · intro i
    obtain ⟨i, rfl⟩ := v.surjective i
    apply π.injective
    rw [hC]
    cases i with
    | inl i =>
      rw [hleft, hc (.inl (l i).val)]
      apply Prod.ext
      · exact (Basis.prod_apply_inl_fst _ _ i).trans
          ((Basis.reindex_apply b l.symm i).trans (hb (l i)))
      · exact Basis.prod_apply_inl_snd _ _ _
    | inr i =>
      rw [hright, hc (.inr (m i).val)]
      apply Prod.ext
      · exact Basis.prod_apply_inr_fst _ _ _
      · exact (Basis.prod_apply_inr_snd _ _ i).trans
          ((Basis.reindex_apply d m.symm i).trans (hd (m i)))
  · have pLeft (i : Fin 1) (y : W.toBased.Y) :
        W.toBased.datum.toLinearMap (W.toBased.datum.root (v (.inl i)).val) y =
          D.toBased.datum.toLinearMap (D.toBased.datum.root (l i).val) (π y).1 := by
      rw [hleft, rootPairing_eq W, rootPairing_eq D]
      exact productRoot_pairingLeft S (l i).val (Additive.toMul y)
    have pRight (i : Fin 5) (y : W.toBased.Y) :
        W.toBased.datum.toLinearMap (W.toBased.datum.root (v (.inr i)).val) y =
          E.toBased.datum.toLinearMap (E.toBased.datum.root (m i).val) (π y).2 := by
      rw [hright, rootPairing_eq W, rootPairing_eq E]
      exact productRoot_pairingRight S (m i).val (Additive.toMul y)
    intro i j
    rw [← RootPairing.root_coroot_eq_pairing]
    cases i with
    | inl i =>
      rw [pLeft]
      cases j with
      | inl j =>
        rw [hleft, hc (.inl (l j).val)]
        exact hCartanP i j
      | inr j =>
        rw [hright, hc (.inr (m j).val)]
        exact map_zero _
    | inr i =>
      rw [pRight]
      cases j with
      | inl j =>
        rw [hleft, hc (.inl (l j).val)]
        exact map_zero _
      | inr j =>
        rw [hright, hc (.inr (m j).val)]
        exact hCartanQ i j

set_option maxHeartbeats 1000000 in
theorem twoBlocks : TwoBlocks.{u} := by
  intro F _ R hR P hP hSC f D e hCartan
  let classification := Classification.PinnedEquivalence.pinnedEquivalence.2 F
  obtain ⟨P₀, h₀⟩ := classification.1 R hR
  subst R
  let D₀ := Classification.Pinning.attachedDatum P₀
  obtain ⟨a⟩ := basedIsoOfScalarExtension P₀ P D₀ D f.symm
  obtain ⟨b, hb⟩ := corootBasis D hP hSC
  obtain ⟨Q₁, Q₂, S, E, hs₁, hs₂, v, c, hc, hQ⟩ := matrixProductPair F
  let j := e.symm.trans v
  have h (i l : D.toBased.base.support) :
      D.toBased.datum.pairing i l = E.toBased.datum.pairing (j i) (j l) := by
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective l
    simpa [j] using (hCartan i l).trans (hQ i l).symm
  obtain ⟨d, _⟩ := basedDatumComparison D.toBased E.toBased b c hb hc j h
  obtain ⟨w⟩ := forgetClassification_reverse P₀ (SplitPairProduct.pair S) D₀ E (d.val.comp a.val)
  exact ⟨Q₁.G, Q₂.G, splitOfPair Q₁, splitOfPair Q₂, hs₁, hs₂, ⟨w ≪≫ tensorProductIso _ _⟩⟩

end Product

end

end LinearAlgebraicGroups.Arithmetic.SplitLeviMatrixComparison
