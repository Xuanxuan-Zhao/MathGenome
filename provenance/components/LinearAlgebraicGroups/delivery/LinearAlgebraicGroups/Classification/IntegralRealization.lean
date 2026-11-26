import Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.Classification.PinnedDatumFromMarkedRootGroups
import LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.PolynomialAlgebra

open Module
open scoped TensorProduct nonZeroDivisors

set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.Classification.IntegralRealization

open Specs.Pinning (BasedRootDatum)

noncomputable section

private abbrev CorootLattice (D : BasedRootDatum.{u}) := D.datum.corootSpan ℤ

private abbrev CentralLattice (D : BasedRootDatum.{u}) :=
  ⨅ a : D.I, (D.datum.root' a).ker

private def restrictToCorootLattice (D : BasedRootDatum.{u}) :
    D.X →ₗ[ℤ] Dual ℤ (CorootLattice D) :=
  (CorootLattice D).subtype.dualMap.comp D.datum.toLinearMap

private def restrictToRootSpan (D : BasedRootDatum.{u}) :
    D.datum.rootSpan ℤ →ₗ[ℤ] Dual ℤ (CorootLattice D) :=
  (restrictToCorootLattice D).comp (D.datum.rootSpan ℤ).subtype

/-- On the root lattice, restriction to the coroot lattice is injective. -/
private theorem restrictToRootSpan_injective (D : BasedRootDatum.{u}) :
    Function.Injective (restrictToRootSpan D) := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hz (i : D.I) : D.datum.coroot' i x.val = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hx)
      ⟨D.datum.coroot i, Submodule.subset_span (Set.mem_range_self i)⟩
  apply Subtype.ext
  refine D.datum.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero x.property ?_
  simp [RootPairing.rootForm_apply_apply, hz]

private def derivedRoot (D : BasedRootDatum.{u}) : D.I ↪ Dual ℤ (CorootLattice D) where
  toFun i := restrictToCorootLattice D (D.datum.root i)
  inj' a b h := by
    apply D.datum.root.injective
    exact congrArg Subtype.val (restrictToRootSpan_injective D
      (a₁ := ⟨D.datum.root a, Submodule.subset_span (Set.mem_range_self a)⟩)
      (a₂ := ⟨D.datum.root b, Submodule.subset_span (Set.mem_range_self b)⟩) h)

private def derivedCoroot (D : BasedRootDatum.{u}) : D.I ↪ CorootLattice D where
  toFun i := ⟨D.datum.coroot i, Submodule.subset_span (Set.mem_range_self i)⟩
  inj' _ _ h := D.datum.coroot.injective (congrArg Subtype.val h)

private def derivedPairing (D : BasedRootDatum.{u}) :
    RootDatum (ι := D.I) (Dual ℤ (CorootLattice D)) (CorootLattice D) := by
  letI := D.freeY
  letI := D.finiteY
  exact
    { toLinearMap := LinearMap.id
      root := derivedRoot D
      coroot := derivedCoroot D
      root_coroot_two := D.datum.root_coroot_two
      reflectionPerm := D.datum.reflectionPerm
      reflectionPerm_root := fun i j => by
        change restrictToCorootLattice D (D.datum.root j) -
          D.datum.pairing j i • restrictToCorootLattice D (D.datum.root i) =
          restrictToCorootLattice D (D.datum.root (D.datum.reflectionPerm i j))
        rw [← map_smul, ← map_sub]
        exact congrArg (restrictToCorootLattice D) (D.datum.reflectionPerm_root i j)
      reflectionPerm_coroot := fun i j => by
        apply Subtype.ext
        exact D.datum.reflectionPerm_coroot i j }

private theorem derivedPairing_reduced (D : BasedRootDatum.{u}) :
    (derivedPairing D).IsReduced := by
  letI := D.reduced
  constructor
  intro i j h
  have hn : ¬ LinearIndependent ℤ ![D.datum.root i, D.datum.root j] := by
    intro independent
    let v : Fin 2 → D.datum.rootSpan ℤ :=
      ![⟨D.datum.root i, Submodule.subset_span (Set.mem_range_self i)⟩,
        ⟨D.datum.root j, Submodule.subset_span (Set.mem_range_self j)⟩]
    have hv : LinearIndependent ℤ v := LinearIndependent.of_comp
      (D.datum.rootSpan ℤ).subtype (by
        convert independent using 1
        funext j
        fin_cases j <;> rfl)
    have hm := hv.map' (restrictToRootSpan D)
      (LinearMap.ker_eq_bot.mpr (restrictToRootSpan_injective D))
    apply h
    convert hm using 1
    funext j
    fin_cases j <;> rfl
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := D.datum) i j hn with h₁ | h₂
  · exact Or.inl (congrArg (restrictToCorootLattice D) h₁)
  · apply Or.inr
    change restrictToCorootLattice D (D.datum.root i) =
      -restrictToCorootLattice D (D.datum.root j)
    rw [h₂, map_neg]

private theorem closure_image_lift {R : Type*} [Ring R] {V : Type*} [AddCommGroup V]
    [Module R V] {W : Submodule R V} {ι : Type*} (v : ι → W) (s : Set ι) (y : W)
    (h : y.val ∈ AddSubmonoid.closure ((fun i => (v i).val) '' s)) :
    y ∈ AddSubmonoid.closure (v '' s) := by
  let incl := W.subtype.toAddMonoidHom
  have h' : incl y ∈ (AddSubmonoid.closure (v '' s)).map incl := by
    rw [AddMonoidHom.map_mclosure, Set.image_image]
    exact h
  obtain ⟨z, hz, hz'⟩ := AddSubmonoid.mem_map.mp h'
  exact (Subtype.ext hz' : z = y) ▸ hz

private def derivedBase (D : BasedRootDatum.{u}) : (derivedPairing D).Base := by
  let v : D.I → D.datum.rootSpan ℤ := fun i =>
    ⟨D.datum.root i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hv : LinearIndependent ℤ (fun i : D.base.support => v i) :=
    D.base.linearIndepOn_root.linearIndependent.of_comp (D.datum.rootSpan ℤ).subtype
  refine
    { support := D.base.support
      linearIndepOn_root := hv.map' (restrictToRootSpan D)
        (LinearMap.ker_eq_bot.mpr (restrictToRootSpan_injective D))
      linearIndepOn_coroot := D.base.linearIndepOn_coroot.linearIndependent.of_comp
        (CorootLattice D).subtype
      root_mem_or_neg_mem := ?_
      coroot_mem_or_neg_mem := ?_ }
  · intro i
    let f := (restrictToCorootLattice D).toAddMonoidHom
    have pass (y : D.X)
        (hy : y ∈ AddSubmonoid.closure (D.datum.root '' (D.base.support : Set D.I))) :
        f y ∈ AddSubmonoid.closure ((derivedPairing D).root '' (D.base.support : Set D.I)) := by
      have hm : f y ∈ (AddSubmonoid.closure (D.datum.root '' (D.base.support : Set D.I))).map f :=
        AddSubmonoid.mem_map.mpr ⟨y, hy, rfl⟩
      rwa [AddMonoidHom.map_mclosure, Set.image_image] at hm
    rcases D.base.root_mem_or_neg_mem i with hi | hi
    · exact Or.inl (pass _ hi)
    · apply Or.inr
      change -f (D.datum.root i) ∈ _
      rw [← map_neg]
      exact pass _ hi
  · intro i
    rcases D.base.coroot_mem_or_neg_mem i with hi | hi
    · exact Or.inl (closure_image_lift (derivedCoroot D) _ (derivedCoroot D i) hi)
    · exact Or.inr (closure_image_lift (derivedCoroot D) _ (-derivedCoroot D i) hi)

/-- The semisimple datum on the coroot lattice and its full dual. -/
private abbrev derivedDatum (D : BasedRootDatum.{u}) : BasedRootDatum.{u} := by
  letI := D.freeY
  letI := D.finiteY
  exact
    { I := D.I
      X := Dual ℤ (CorootLattice D)
      Y := CorootLattice D
      finiteRoots := D.finiteRoots
      freeX := inferInstance
      freeY := inferInstance
      finiteX := inferInstance
      finiteY := inferInstance
      datum := derivedPairing D
      reduced := derivedPairing_reduced D
      base := derivedBase D }

private theorem derivedDatum_coroots_span (D : BasedRootDatum.{u}) :
    Submodule.span ℤ (Set.range (derivedDatum D).datum.coroot) = ⊤ := by
  change Submodule.span ℤ (Set.range (derivedCoroot D)) = ⊤
  rw [← Submodule.span_setOfPred_mem_eq_top]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact Set.mem_range_self i
  · rintro ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩

private theorem derivedBase_height (D : BasedRootDatum.{u}) (i : D.I) :
    (derivedDatum D).base.height i = D.base.height i := by
  obtain ⟨f, _, _, hf⟩ := D.base.exists_root_eq_sum_int i
  have hm : (derivedDatum D).datum.root i =
      ∑ j ∈ (derivedDatum D).base.support, f j • (derivedDatum D).datum.root j := by
    change restrictToCorootLattice D (D.datum.root i) =
      ∑ j ∈ D.base.support, f j • restrictToCorootLattice D (D.datum.root j)
    simpa only [map_sum, map_zsmul] using congrArg (restrictToCorootLattice D) hf
  rw [RootPairing.Base.height_eq_sum hm, RootPairing.Base.height_eq_sum hf]
  rfl

private theorem corootLattice_separates (D : BasedRootDatum.{u}) (y : CorootLattice D)
    (h : ∀ i : D.I, D.datum.root' i y.val = 0) : y = 0 := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  apply Subtype.ext
  refine D.datum.flip.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero y.property ?_
  simp [RootPairing.rootForm_apply_apply, RootPairing.coroot', h]

private theorem derivedDatum_semisimple (D : BasedRootDatum.{u}) :
    RootData.rationalRootAnnihilator (derivedDatum D).datum = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  change ℚ ⊗[ℤ] CorootLattice D at y
  let f : CorootLattice D →ₗ[ℤ] ℚ ⊗[ℤ] CorootLattice D :=
    TensorProduct.mk ℤ ℚ (CorootLattice D) 1
  letI : IsLocalizedModule ℤ⁰ f :=
    IsLocalization.tensorProduct_isLocalizedModule ℤ⁰ ℚ (M := CorootLattice D)
  obtain ⟨⟨x, n⟩, hn⟩ := IsLocalizedModule.surj ℤ⁰ f y
  have hx (i : D.I) : D.datum.root' i x.val = 0 := by
    let L : CorootLattice D →ₗ[ℤ] ℤ := (derivedDatum D).datum.root' i
    have hyi : RootData.extendFunctional ℚ L y = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy i)
    have h := congrArg (RootData.extendFunctional ℚ L) hn
    change RootData.extendFunctional ℚ L (n.val • y) =
      RootData.extendFunctional ℚ L (1 ⊗ₜ[ℤ] x) at h
    have hz : (L x : ℚ) = 0 := by
      rw [RootData.extendFunctional_one_tmul, LinearMap.map_smul_of_tower, hyi, smul_zero] at h
      exact h.symm
    exact_mod_cast hz
  have hz : f x = 0 := by rw [corootLattice_separates D x hx, map_zero]
  apply (smul_right_injective (ℚ ⊗[ℤ] CorootLattice D)
    (show (n.val : ℚ) ≠ 0 by exact_mod_cast nonZeroDivisors.coe_ne_zero n))
  change (n.val : ℚ) • y = (n.val : ℚ) • 0
  rw [Int.cast_smul_eq_zsmul, smul_zero]
  exact hn.trans hz

private def cocharacterSum (D : BasedRootDatum.{u}) :
    CorootLattice D × CentralLattice D →ₗ[ℤ] D.Y :=
  (CorootLattice D).subtype.coprod (CentralLattice D).subtype

private theorem cocharacterSum_injective (D : BasedRootDatum.{u}) :
    Function.Injective (cocharacterSum D) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨x, y⟩ h
  change x.val + y.val = 0 at h
  have hx (i : D.I) : D.datum.root' i x.val = 0 := by
    have hy := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp y.property i)
    simpa [hy] using congrArg (D.datum.root' i) h
  have hx' := corootLattice_separates D x hx
  subst x
  have hy : y = 0 := Subtype.ext (by simpa using h)
  simp [hy]

private def evaluateRoots (D : BasedRootDatum.{u}) :
    D.Y →ₗ[ℤ] Dual ℤ (D.datum.rootSpan ℤ) :=
  (D.datum.rootSpan ℤ).subtype.dualMap.comp D.datum.toLinearMap.flip

private theorem evaluateRoots_ker (D : BasedRootDatum.{u}) :
    (evaluateRoots D).ker = CentralLattice D := by
  ext y
  constructor
  · intro hy
    refine (Submodule.mem_iInf _).mpr fun i => LinearMap.mem_ker.mpr ?_
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hy)
      ⟨D.datum.root i, Submodule.subset_span (Set.mem_range_self i)⟩
  · intro hy
    apply LinearMap.mem_ker.mpr
    ext x
    change (D.datum.toLinearMap.flip y) x.val = 0
    have hx : x.val ∈ (D.datum.toLinearMap.flip y).ker :=
      (Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact (Submodule.mem_iInf _).mp hy i)) x.property
    exact LinearMap.mem_ker.mp hx

private theorem cocharacterSum_finrank (D : BasedRootDatum.{u}) :
    finrank ℤ (CorootLattice D × CentralLattice D) = finrank ℤ D.Y := by
  classical
  letI := D.freeX
  letI := D.finiteX
  letI := D.freeY
  letI := D.finiteY
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  have hdual : finrank ℤ (Dual ℤ (D.datum.rootSpan ℤ)) =
      finrank ℤ (D.datum.rootSpan ℤ) :=
    Module.finrank_of_isPerfPair LinearMap.id
  have hle : finrank ℤ (evaluateRoots D).range ≤ finrank ℤ (CorootLattice D) := by
    rw [D.datum.finrank_corootSpan_eq ℤ, ← hdual]
    exact Submodule.finrank_le _
  have hsum : finrank ℤ (evaluateRoots D).range + finrank ℤ (CentralLattice D) =
      finrank ℤ D.Y := by
    have h := congrArg Cardinal.toNat ((evaluateRoots D).rank_range_add_rank_ker)
    rw [evaluateRoots_ker] at h
    simpa [Module.finrank, Module.rank_lt_aleph0] using h
  apply le_antisymm
  · exact (cocharacterSum D).finrank_le_finrank_of_injective (cocharacterSum_injective D)
  · rw [← hsum, Module.finrank_prod]
    exact Nat.add_le_add_right hle _

private theorem cocharacterSum_finiteQuotient (D : BasedRootDatum.{u}) :
    Finite (D.Y ⧸ (cocharacterSum D).range) := by
  letI := D.freeY
  letI := D.finiteY
  apply Submodule.finiteQuotientOfFreeOfRankEq
  rw [(cocharacterSum D).finrank_range_of_inj (cocharacterSum_injective D)]
  exact cocharacterSum_finrank D

/-- Pullback of characters along the sum of the derived and central cocharacters. -/
private def characterRestriction (D : BasedRootDatum.{u}) :
    D.X →ₗ[ℤ] Dual ℤ (CorootLattice D × CentralLattice D) :=
  (cocharacterSum D).dualMap.comp D.datum.toLinearMap

private theorem characterRestriction_injective (D : BasedRootDatum.{u}) :
    Function.Injective (characterRestriction D) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  apply D.datum.toLinearMap.toPerfPair.injective
  ext y
  let range := (cocharacterSum D).range
  letI : Finite (D.Y ⧸ range) := cocharacterSum_finiteQuotient D
  let n := Nat.card (D.Y ⧸ range)
  have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨v, hv⟩ : n • y ∈ range := AddSubgroup.nsmul_index_mem range.toAddSubgroup y
  have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) v
  change D.datum.toLinearMap x (cocharacterSum D v) = 0 at h
  rw [hv, map_nsmul, nsmul_eq_mul] at h
  simpa using (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

private theorem characterRestriction_finiteQuotient (D : BasedRootDatum.{u}) :
    Finite (Dual ℤ (CorootLattice D × CentralLattice D) ⧸ (characterRestriction D).range) := by
  letI := D.freeX
  letI := D.finiteX
  letI := D.freeY
  letI := D.finiteY
  apply Submodule.finiteQuotientOfFreeOfRankEq
  rw [(characterRestriction D).finrank_range_of_inj (characterRestriction_injective D)]
  calc
    finrank ℤ D.X = finrank ℤ D.Y := Module.finrank_of_isPerfPair D.datum.toLinearMap
    _ = finrank ℤ (CorootLattice D × CentralLattice D) := (cocharacterSum_finrank D).symm
    _ = finrank ℤ (Dual ℤ (CorootLattice D × CentralLattice D)) :=
      (Module.finrank_of_isPerfPair LinearMap.id).symm

private theorem characterRestriction_root_central (D : BasedRootDatum.{u}) (a : D.I)
    (y : CentralLattice D) : characterRestriction D (D.datum.root a) (0, y) = 0 := by
  change D.datum.toLinearMap (D.datum.root a) ((0 : D.Y) + y.val) = 0
  rw [zero_add]
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp y.property a)

private abbrev CoverCharacters (D : BasedRootDatum.{u}) :=
  Dual ℤ (CorootLattice D × CentralLattice D)


/-- The cover characters split into the derived and central characters. -/
private def coverCharactersEquiv (D : BasedRootDatum.{u}) :
    CoverCharacters D ≃ₗ[ℤ] (derivedDatum D).X × Dual ℤ (CentralLattice D) :=
  (Module.dualProdDualEquivDual ℤ (CorootLattice D) (CentralLattice D)).symm

private theorem coverCharactersEquiv_root (D : BasedRootDatum.{u}) (a : D.I) :
    coverCharactersEquiv D (characterRestriction D (D.datum.root a)) =
      ((derivedDatum D).datum.root a, 0) := by
  apply (coverCharactersEquiv D).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change D.datum.root' a (x.val + y.val) = D.datum.root' a x.val + 0
  rw [map_add]
  congr 1
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp y.property a)

private abbrev KernelCharacters (D : BasedRootDatum.{u}) :=
  CoverCharacters D ⧸ (characterRestriction D).range

private def torusKernel (D : BasedRootDatum.{u}) :
    Multiplicative (CoverCharacters D) →* Multiplicative (KernelCharacters D) :=
  (characterRestriction D).range.mkQ.toAddMonoidHom.toMultiplicative

private theorem torusKernel_surjective (D : BasedRootDatum.{u}) :
    Function.Surjective (torusKernel D) :=
  (characterRestriction D).range.mkQ_surjective

/-- Characters of the quotient torus are exactly the original character lattice. -/
private def quotientCharacters (D : BasedRootDatum.{u}) :
    Multiplicative D.X ≃* (torusKernel D).ker := by
  let h : Multiplicative D.X →* (torusKernel D).ker :=
    MonoidHom.codRestrict (characterRestriction D).toAddMonoidHom.toMultiplicative
      (torusKernel D).ker (fun x => by
        change (characterRestriction D).range.mkQ (characterRestriction D x.toAdd) = 0
        exact (Submodule.Quotient.mk_eq_zero (p := (characterRestriction D).range)).mpr ⟨x.toAdd, rfl⟩)
  refine MulEquiv.ofBijective h ⟨fun x y eq =>
    characterRestriction_injective D (congrArg Subtype.val eq), ?_⟩
  rintro ⟨x, hx⟩
  have hx' : x.toAdd ∈ (characterRestriction D).range := by
    apply (Submodule.Quotient.mk_eq_zero (p := (characterRestriction D).range)).mp
    exact hx
  obtain ⟨y, hy⟩ := hx'
  exact ⟨Multiplicative.ofAdd y, Subtype.ext hy⟩

private def coverCoroot (D : BasedRootDatum.{u}) (a : D.I) :
    Multiplicative (CoverCharacters D) →* Multiplicative ℤ :=
  (Module.Dual.eval ℤ _ (derivedCoroot D a, 0)).toAddMonoidHom.toMultiplicative

private theorem coverCoroot_quotient (D : BasedRootDatum.{u}) (a : D.I) (x : D.X) :
    coverCoroot D a ((quotientCharacters D (Multiplicative.ofAdd x)).val) =
      Multiplicative.ofAdd (D.datum.coroot' a x) := by
  change D.datum.toLinearMap x (D.datum.coroot a + 0) = _
  rw [add_zero]
  rfl

private theorem coverRoot_kernel (D : BasedRootDatum.{u}) (a : D.I) :
    torusKernel D (Multiplicative.ofAdd (characterRestriction D (D.datum.root a))) = 1 :=
  (quotientCharacters D (Multiplicative.ofAdd (D.datum.root a))).property

private theorem coverRoots_enumerated (D : BasedRootDatum.{u})
    {negative positive : List D.I}
    (hn : Specs.OrderedRootProducts.Enumerates negative {a | ¬ D.base.IsPos a})
    (hp : Specs.OrderedRootProducts.Enumerates positive {a | D.base.IsPos a}) :
    (negative ++ positive).Nodup ∧ (∀ a, a ∈ negative ++ positive) := by
  classical
  constructor
  · refine List.nodup_append.mpr ⟨hn.1, hp.1, ?_⟩
    rintro a h₁ _ h₂ rfl
    exact (hn.2 a).mp h₁ ((hp.2 a).mp h₂)
  · intro a
    rw [List.mem_append, hn.2, hp.2]
    exact em (D.base.IsPos a) |>.symm

private theorem semisimpleModel_exists
    (semisimple : Specs.IntegralSemisimpleModel.Statement.{u}) (D : BasedRootDatum.{u}) :
    Nonempty (Specs.IntegralSemisimpleModel.Model (derivedDatum D)) :=
  (semisimple (derivedDatum D) (derivedDatum_semisimple D) (derivedDatum_coroots_span D)).2

section Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open LinearAlgebraicGroups.Specs.IntegralCentralQuotient
open LinearAlgebraicGroups.Specs.GeometricRadicals

variable {R : Type u} [CommRing R]

private def quotientTorusIso (D : BasedRootDatum.{u}) :
    HopfSpectrum IntegralRing.{u}
      (MonoidAlgebra IntegralRing.{u} (torusKernel D).ker) ≅
    Specs.IntegralSemisimpleModel.splitTorus D :=
  (hopfSpec (CommRingCat.of IntegralRing.{u})).mapIso
    (CommHopfAlgCat.isoMk
      (MonoidAlgebra.domCongrBialgEquiv IntegralRing.{u} IntegralRing.{u}
        (quotientCharacters D))).op

private theorem groupAlgebra_map_surjective {X M : Type u} [CommGroup X] [CommGroup M]
    (z : X →* M) (h : Function.Surjective z) :
    Function.Surjective (MonoidAlgebra.mapDomainBialgHom R z) := by
  intro v
  induction v using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
  | single m r =>
    obtain ⟨x, rfl⟩ := h m
    exact ⟨MonoidAlgebra.single x r, MonoidAlgebra.mapDomainBialgHom_single _ _ _⟩

private theorem algebraicClosure_fpqc (K : Type u) [Field K] :
    ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have hg : (algebraMap K (AlgebraicClosure K)).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hf := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom
    (algebraMap K (AlgebraicClosure K)))).mpr hg
  exact ⟨⟨hf.2, hf.1⟩, inferInstanceAs (QuasiCompact g)⟩

private theorem fieldFibreSmooth {T G : Grp (OverBase R)} (j : T ⟶ G)
    (h : ReductiveFibres j) (K : Type u) [Field K] [Algebra R K] :
    Smooth ((fibreGroup K).obj G).X.hom := by
  let Kbar := AlgebraicClosure K
  letI : Algebra R Kbar := (algebraMap K Kbar).comp (algebraMap R K) |>.toAlgebra
  obtain ⟨H, e, hc, hRed, hm⟩ := h Kbar
  let g := Spec.map (CommRingCat.ofHom (algebraMap K Kbar))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let B := G.X.hom
  have hcomp : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Kbar)) := by
    rw [← Spec.map_comp]
    rfl
  have hs : Smooth (pullback.snd B (g ≫ f)) := by
    rw [hcomp]
    let i := (Grp.forget _ ⋙ Over.forget _).mapIso e
    let z := i.hom
    letI : IsIso z := i.isIso_hom
    letI : Smooth H.val.X.hom := hRed.1
    have c : z ≫ H.val.X.hom = pullback.snd B (Spec.map (CommRingCat.ofHom
      (algebraMap R Kbar))) := Over.w e.hom.hom.hom
    rw [← c]
    exact MorphismProperty.comp_mem (@Smooth : MorphismProperty Scheme.{u})
      z H.val.X.hom (inferInstanceAs (Smooth z)) hRed.1
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := pullback.snd B f) (g := g) (algebraicClosure_fpqc K) ?_
  let p := (IsPullback.of_hasPullback (pullback.snd B f) g).paste_horiz
    (IsPullback.of_hasPullback B f)
  rw [← p.isoPullback_hom_snd]
  letI : Smooth (pullback.snd B (g ≫ f)) := hs
  exact smooth_comp p.isoPullback.hom _

private theorem fieldFibreConnected {T G : Grp (OverBase R)} (j : T ⟶ G)
    (h : ReductiveFibres j) (K : Type u) [Field K] [Algebra R K] :
    ConnectedSpace ((fibreGroup K).obj G).X.left := by
  let Kbar := AlgebraicClosure K
  letI : Algebra R Kbar := (algebraMap K Kbar).comp (algebraMap R K) |>.toAlgebra
  obtain ⟨H, e, hc, hRed, hm⟩ := h Kbar
  let g := Spec.map (CommRingCat.ofHom (algebraMap K Kbar))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let B := G.X.hom
  have hcomp : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Kbar)) := by
    rw [← Spec.map_comp]
    rfl
  letI : GeometricallyConnected H.val.X.hom := hRed.2.1
  have hH : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  let i := (Grp.forget _ ⋙ Over.forget _).mapIso e
  have hConn : ConnectedSpace (pullback (C := Scheme.{u}) B (g ≫ f)) := by
    rw [hcomp]
    exact i.hom.homeomorph.connectedSpace_iff.mpr hH
  let p := (IsPullback.of_hasPullback (pullback.snd B f) g).paste_horiz
    (IsPullback.of_hasPullback B f)
  letI : ConnectedSpace (pullback (C := Scheme.{u}) (pullback.snd B f) g) :=
    p.isoPullback.hom.homeomorph.connectedSpace_iff.mpr hConn
  letI : Surjective g := (algebraicClosure_fpqc K).1.1
  have hp : Surjective (pullback.fst (pullback.snd B f) g) := inferInstance
  exact hp.surj.connectedSpace (pullback.fst (pullback.snd B f) g).continuous

private theorem smoothConnectedOfGeometricFibres {T G : Grp (OverBase R)} (j : T ⟶ G)
    (h : ReductiveFibres j) [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    Smooth G.X.hom ∧ GeometricallyConnected G.X.hom := by
  constructor
  · refine Smooth.of_smooth_fiberToSpecResidueField G.X.hom (fun y => ?_)
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec (CommRingCat.of R)).fromSpecResidueField y)
    letI : Algebra R ((Spec (CommRingCat.of R)).residueField y) := φ.hom.toAlgebra
    change Smooth (pullback.snd G.X.hom ((Spec (CommRingCat.of R)).fromSpecResidueField y))
    rw [← hφ]
    exact fieldFibreSmooth j h ((Spec (CommRingCat.of R)).residueField y)
  · rw [GeometricallyConnected.eq_geometrically, geometrically_iff_of_commRing]
    intro K _ _ Y f g e
    have := fieldFibreConnected j h K
    exact e.isoPullback.hom.homeomorph.connectedSpace_iff.mpr this

end Geometry

section Coordinates

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory
open LinearAlgebraicGroups.Specs.IntegralCentralQuotient
open LinearAlgebraicGroups.Specs.IntegralSemisimpleModel

private abbrev R := Integers.{u}

private theorem affineSpectrum (G : IntegralGroup.{u}) (h : IsAffine G.X.left) :
    ∃ A : CommHopfAlgCat R.{u}, Nonempty (HopfSpectrum R.{u} A ≅ G) := by
  obtain ⟨A, e⟩ := essImage_hopfSpec.mpr h
  exact ⟨A.unop, e⟩

variable {A : Type u} [CommRing A] [HopfAlgebra R.{u} A]

private def coordinatePoints (S : IntegralAlgebra.{u}) :
    WithConv (A →ₐ[R.{u}] S) ≃* (integralPointFunctor (HopfSpectrum R.{u} A)).obj S :=
  Spec.mapMulEquiv

private theorem coordinatePoints_naturality {S T : IntegralAlgebra.{u}} (f : S ⟶ T)
    (a : WithConv (A →ₐ[R.{u}] S)) :
    (coordinatePoints T (toConv (f.hom.comp a.ofConv))) =
      (integralPointFunctor (HopfSpectrum R.{u} A)).map f (coordinatePoints S a) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (f.hom.comp a.ofConv).toRingHom) =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom a.ofConv.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem coordinatePoints_comp {B : Type u} [CommRing B] [HopfAlgebra R.{u} B]
    (f : B →ₐc[R.{u}] A) (S : IntegralAlgebra.{u}) (p : A →ₐ[R.{u}] S) :
    coordinatePoints S (toConv (p.comp f.toAlgHom)) =
      coordinatePoints S (toConv p) ≫ (spectrumOfHopfHom f).hom.hom := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (p.comp f.toAlgHom).toRingHom) =
    Spec.map (CommRingCat.ofHom p.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem coordinatePoints_polynomial (S : IntegralAlgebra.{u})
    (x : A →ₐ[R.{u}] Polynomial R.{u}) (a : S) :
    coordinatePoints S (toConv ((Polynomial.aeval a).comp x)) =
      additivePoint S a ≫ spectrumOfAlgHom x := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((Polynomial.aeval a).comp x).toRingHom) =
    Spec.map (CommRingCat.ofHom (Polynomial.aeval a : Polynomial R.{u} →ₐ[R.{u}] S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom x.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private def rankOneNatural (r : RankOneMap R.{u} A) :
    rankOnePoints.{u} ⟶ integralPointFunctor (HopfSpectrum R.{u} A) where
  app S := GrpCat.ofHom (Y := ↥((integralPointFunctor (HopfSpectrum R.{u} A)).obj S))
    ((coordinatePoints S).toMonoidHom.comp (r.hom S))
  naturality S T f := by
    apply GrpCat.ext
    intro a
    change coordinatePoints T (r.hom T (Matrix.SpecialLinearGroup.map f.hom.toRingHom a)) =
      (integralPointFunctor (HopfSpectrum R.{u} A)).map f (coordinatePoints S (r.hom S a))
    rw [← coordinatePoints_naturality]
    exact congrArg (coordinatePoints T) <| WithConv.ofConv_injective (r.naturality f a)

private def rankOneCoordinates
    (r : rankOnePoints.{u} ⟶ integralPointFunctor (HopfSpectrum R.{u} A)) :
    RankOneMap R.{u} A where
  hom S := (coordinatePoints S).symm.toMonoidHom.comp (r.app S).hom
  naturality {S T} f a := by
    apply WithConv.toConv_injective
    apply (coordinatePoints T).injective
    rw [coordinatePoints_naturality]
    change coordinatePoints T ((coordinatePoints T).symm
      (r.app T (Matrix.SpecialLinearGroup.map f.hom.toRingHom a))) =
      (integralPointFunctor (HopfSpectrum R.{u} A)).map f
        (coordinatePoints S ((coordinatePoints S).symm (r.app S a)))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (r.naturality f)) a

private theorem rankOneNatural_apply_upper (r : RankOneMap R.{u} A) (S : IntegralAlgebra.{u})
    (x : A →ₐ[R.{u}] Polynomial R.{u}) (h : ∀ a : S,
      (r.hom S (Specs.IntegralRootRelations.upper a)).ofConv = (Polynomial.aeval a).comp x)
    (a : S) :
    (rankOneNatural r).app S (Specs.IntegralRootRelations.upper a) =
      additivePoint S a ≫ spectrumOfAlgHom x := by
  change coordinatePoints S (r.hom S (Specs.IntegralRootRelations.upper a)) = _
  exact (congrArg (fun f => coordinatePoints S (toConv f)) (h a)).trans
    (coordinatePoints_polynomial S x a)

private theorem rankOneNatural_apply_lower (r : RankOneMap R.{u} A) (S : IntegralAlgebra.{u})
    (x : A →ₐ[R.{u}] Polynomial R.{u}) (h : ∀ a : S,
      (r.hom S (Specs.IntegralRootRelations.lower a)).ofConv = (Polynomial.aeval a).comp x)
    (a : S) :
    (rankOneNatural r).app S (Specs.IntegralRootRelations.lower a) =
      additivePoint S a ≫ spectrumOfAlgHom x := by
  change coordinatePoints S (r.hom S (Specs.IntegralRootRelations.lower a)) = _
  exact (congrArg (fun f => coordinatePoints S (toConv f)) (h a)).trans
    (coordinatePoints_polynomial S x a)

private theorem rankOneNatural_apply_diagonal {X : Type u} [CommGroup X]
    (r : RankOneMap R.{u} A) (S : IntegralAlgebra.{u}) (t : A →ₐc[R.{u}] MonoidAlgebra R.{u} X)
    (c : X →* Multiplicative ℤ) (h : ∀ s : Sˣ,
      (r.hom S (Specs.IntegralRootRelations.diagonal s)).ofConv =
        (cocharacterEval c S s).comp t.toAlgHom) (s : Sˣ) :
    (rankOneNatural r).app S (Specs.IntegralRootRelations.diagonal s) =
      coordinatePoints S (toConv (cocharacterEval c S s)) ≫ (spectrumOfHopfHom t).hom.hom := by
  change coordinatePoints S (r.hom S (Specs.IntegralRootRelations.diagonal s)) = _
  exact (congrArg (fun f => coordinatePoints S (toConv f)) (h s)).trans
    (coordinatePoints_comp t S (cocharacterEval c S s))

private def markedTorusCoordinates {B : Type u} [CommRing B] [HopfAlgebra R.{u} B]
    {G : IntegralGroup.{u}} (e : HopfSpectrum R.{u} A ≅ G) (t : HopfSpectrum R.{u} B ⟶ G) :
    A →ₐc[R.{u}] B :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of R.{u})).preimage (t ≫ e.inv)).unop.hom

private theorem markedTorusCoordinates_spec {B : Type u} [CommRing B] [HopfAlgebra R.{u} B]
    {G : IntegralGroup.{u}} (e : HopfSpectrum R.{u} A ≅ G) (t : HopfSpectrum R.{u} B ⟶ G) :
    spectrumOfHopfHom (markedTorusCoordinates e t) = t ≫ e.inv :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of R.{u})).map_preimage _

private def markedRootCoordinates {G : IntegralGroup.{u}} {L : AdditiveLine.{u}}
    (e : HopfSpectrum R.{u} A ≅ G) (x : L.group ⟶ G) :
    A →ₐ[R.{u}] Polynomial R :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R.{u})).preimage
    (x.hom.hom ≫ e.inv.hom.hom)).unop.hom

private theorem markedRootCoordinates_spec {G : IntegralGroup.{u}} {L : AdditiveLine.{u}}
    (e : HopfSpectrum R.{u} A ≅ G) (x : L.group ⟶ G) :
    spectrumOfAlgHom (markedRootCoordinates e x) = x.hom.hom ≫ e.inv.hom.hom :=
  (algSpec.fullyFaithful (R := CommRingCat.of R.{u})).map_preimage _

private theorem coordinates_surjective_of_closed {B : Type u} [CommRing B] [Algebra R.{u} B]
    (x : A →ₐ[R.{u}] B) (h : IsClosedImmersion (spectrumOfAlgHom x).left) :
    Function.Surjective x := by
  let f := CommRingCat.ofHom x.toRingHom
  letI : IsClosedImmersion (Spec.map f) := h
  let c₁ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv
  let c₂ := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  have hf : c₁ ≫ (Spec.map f).appTop ≫ c₂ = f := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  change Function.Surjective f
  rw [← hf]
  exact (ConcreteCategory.bijective_of_isIso c₂).2.comp
    (((IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2).comp
      (ConcreteCategory.bijective_of_isIso c₁).2)

private theorem markedTorusCoordinates_surjective {B : Type u} [CommRing B] [HopfAlgebra R.{u} B]
    {G : IntegralGroup.{u}} (e : HopfSpectrum R.{u} A ≅ G) (t : HopfSpectrum R.{u} B ⟶ G)
    (h : IsClosedImmersion t.hom.hom.left) :
    Function.Surjective (markedTorusCoordinates e t) := by
  apply coordinates_surjective_of_closed (markedTorusCoordinates e t).toAlgHom
  change IsClosedImmersion (spectrumOfHopfHom (markedTorusCoordinates e t)).hom.hom.left
  rw [markedTorusCoordinates_spec]
  let i := (Grp.forget _ ⋙ Over.forget _).mapIso e
  change IsClosedImmersion (t.hom.hom.left ≫ i.inv)
  letI : IsClosedImmersion t.hom.hom.left := h
  letI : IsIso i.inv := i.isIso_inv
  have hi : IsClosedImmersion i.inv :=
    { isClosedEmbedding := i.inv.homeomorph.isClosedEmbedding
      stalkMap_surjective := fun _ => (ConcreteCategory.bijective_of_isIso _).2 }
  exact @IsClosedImmersion.comp _ _ _ _ _ h hi

private theorem markedRootCoordinates_surjective {G : IntegralGroup.{u}} {L : AdditiveLine.{u}}
    (e : HopfSpectrum R.{u} A ≅ G) (x : L.group ⟶ G) (h : IsClosedImmersion x.hom.hom.left) :
    Function.Surjective (markedRootCoordinates e x) := by
  apply coordinates_surjective_of_closed
  rw [markedRootCoordinates_spec]
  let i := (Grp.forget _ ⋙ Over.forget _).mapIso e
  change IsClosedImmersion (x.hom.hom.left ≫ i.inv)
  letI : IsClosedImmersion x.hom.hom.left := h
  letI : IsIso i.inv := i.isIso_inv
  have hi : IsClosedImmersion i.inv :=
    { isClosedEmbedding := i.inv.homeomorph.isClosedEmbedding
      stalkMap_surjective := fun _ => (ConcreteCategory.bijective_of_isIso _).2 }
  exact @IsClosedImmersion.comp _ _ _ _ _ h hi



private def lineProductIso (L : AdditiveLine.{u}) {I : Type u} :
    (l : List I) → lineProduct R.{u} l ≅ product (fun _ : I => L.group.X) l
  | [] => Iso.refl _
  | _ :: l => MonoidalCategory.tensorIso (Iso.refl _) (lineProductIso L l)

set_option backward.isDefEq.respectTransparency false in
private theorem markedRootProduct_spec {G : IntegralGroup.{u}} {L : AdditiveLine.{u}} {I : Type u}
    (e : HopfSpectrum R.{u} A ≅ G) (x : I → (L.group ⟶ G)) (l : List I) :
    Specs.IntegralCentralQuotient.rootProduct (fun a => markedRootCoordinates e (x a)) l =
      (lineProductIso L l).hom ≫ Specs.IntegralSemisimpleModel.rootProduct L x l ≫
        e.inv.hom.hom := by
  induction l with
  | nil =>
    simp only [lineProductIso, Specs.IntegralCentralQuotient.rootProduct,
      Specs.IntegralSemisimpleModel.rootProduct, Iso.refl_hom, MonObj.one_comp]
    exact (Category.id_comp _).symm
  | cons a l ih =>
    simp only [lineProductIso, Specs.IntegralCentralQuotient.rootProduct,
      Specs.IntegralSemisimpleModel.rootProduct, markedRootCoordinates_spec,
      MonoidalCategory.tensorIso_hom, Iso.refl_hom, ih]
    rw [MonObj.mul_comp, MonObj.comp_mul]
    simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst_assoc,
      CartesianMonoidalCategory.tensorHom_snd_assoc, Category.id_comp]

private def cellDomainIso (T : IntegralGroup.{u}) (L : AdditiveLine.{u}) {I : Type u}
    (negative positive : List I) :=
  MonoidalCategory.tensorIso (lineProductIso L negative)
    (MonoidalCategory.tensorIso (Iso.refl T.X) (lineProductIso L positive))


private def torusValuesOfAlgHom {X : Type u} [CommGroup X] (S : IntegralAlgebra.{u})
    (f : MonoidAlgebra R.{u} X →ₐ[R.{u}] S) : X →* Sˣ :=
  (f.toMonoidHom.comp (MonoidAlgebra.of R.{u} X)).toHomUnits

private theorem torusValuesOfAlgHom_eq {X : Type u} [CommGroup X] (S : IntegralAlgebra.{u})
    (f : MonoidAlgebra R.{u} X →ₐ[R.{u}] S) :
    MonoidAlgebra.lift R.{u} S X ((Units.coeHom S).comp (torusValuesOfAlgHom S f)) = f := by
  exact (MonoidAlgebra.lift R.{u} S X).apply_symm_apply f

private theorem torusPoint_as_coordinates (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u})
    (p : TorusValues D S) :
    torusPoint D S p =
      coordinatePoints S (toConv (MonoidAlgebra.lift R.{u} S (Multiplicative D.X)
        ((Units.coeHom S).comp p))) := rfl

private def quotientCharacterMap (D : BasedRootDatum.{u}) :
    MonoidAlgebra R.{u} (Multiplicative D.X) →ₐc[R.{u}] MonoidAlgebra R.{u} (torusKernel D).ker :=
  (MonoidAlgebra.domCongrBialgEquiv R.{u} R.{u} (quotientCharacters D)).toBialgHom

set_option backward.isDefEq.respectTransparency false in
private theorem quotientTorusIso_hom (D : BasedRootDatum.{u}) :
    (quotientTorusIso D).hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom (quotientCharacterMap D).toAlgHom.toRingHom) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quotientTorus_cocharacter (D : BasedRootDatum.{u}) (a : D.I)
    (S : IntegralAlgebra.{u}) (s : Sˣ) :
    coordinatePoints S (toConv (cocharacterEval
        ((coverCoroot D a).comp (torusKernel D).ker.subtype) S s)) =
      torusPoint D S (cocharacter D (D.datum.coroot a) S s) ≫ (quotientTorusIso D).inv.hom.hom := by
  let e := (Grp.forget IntegralScheme.{u}).mapIso (quotientTorusIso D)
  apply (cancel_mono e.hom).mp
  change _ ≫ e.hom = (_ ≫ e.inv) ≫ e.hom
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [torusPoint_as_coordinates]
  have h : e.hom = (spectrumOfHopfHom (quotientCharacterMap D)).hom.hom :=
    Over.OverMorphism.ext (quotientTorusIso_hom D)
  rw [h, ← coordinatePoints_comp]
  apply congrArg (fun f : MonoidAlgebra R.{u} (Multiplicative D.X) →ₐ[R.{u}] S =>
    coordinatePoints S (toConv f))
  apply (MonoidAlgebra.lift R.{u} S (Multiplicative D.X)).symm.injective
  apply MonoidHom.ext
  intro x
  simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply]
  have hq : (quotientCharacterMap D).toAlgHom (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (quotientCharacters D x) 1 := by
    change MonoidAlgebra.domCongr R.{u} R.{u} (quotientCharacters D) _ = _
    simp
  rw [hq]
  simp only [← MonoidAlgebra.of_apply]
  unfold cocharacterEval
  rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]
  change (↑(s ^ (coverCoroot D a ((quotientCharacters D x).val)).toAdd) : S) =
    ↑(s ^ (D.datum.toLinearMap x.toAdd (D.datum.coroot a)))
  have hx := coverCoroot_quotient D a x.toAdd
  change coverCoroot D a ((quotientCharacters D x).val) =
    Multiplicative.ofAdd (D.datum.coroot' a x.toAdd) at hx
  rw [hx]
  rfl
section TorusRestriction

open WithConv Coalgebra Algebra.TensorProduct

variable {K C : Type u} [CommRing K] [CommRing C] [HopfAlgebra K C]
variable {X M : Type u} [CommGroup X] [CommGroup M]

private theorem torusRestriction_injective (z : X →* M) :
    Function.Injective (MonoidAlgebra.mapDomainBialgHom K z.ker.subtype) :=
  MonoidAlgebra.mapDomain_injective Subtype.val_injective

private def identityCoefficient (K M : Type u) [CommRing K] [CommGroup M] :
    MonoidAlgebra K M →ₗ[K] K :=
  (Finsupp.lapply (1 : M)).comp (MonoidAlgebra.coeffLinearEquiv K).toLinearMap

private theorem identityCoefficient_single_one (r : K) :
    identityCoefficient K M (MonoidAlgebra.single 1 r) = r := by
  change Finsupp.single (1 : M) r 1 = r
  simp

private theorem identityCoefficient_single_of_ne (m : M) (r : K) (h : m ≠ 1) :
    identityCoefficient K M (MonoidAlgebra.single m r) = 0 := by
  classical
  change Finsupp.single m r 1 = 0
  exact Finsupp.single_eq_of_ne h.symm

/-- Extract the coefficient of the identity character in the coaction. -/
private def invariantPart (π : C →ₐc[K] MonoidAlgebra K M) : C →ₗ[K] C :=
  (TensorProduct.rid K C).toLinearMap ∘ₗ
    (identityCoefficient K M).lTensor C ∘ₗ
    (rightCoaction π).toLinearMap

set_option maxHeartbeats 600000 in
private theorem rightCoaction_coassoc (π : C →ₐc[K] MonoidAlgebra K M) :
    (TensorProduct.assoc K C (MonoidAlgebra K M) (MonoidAlgebra K M)).toLinearMap ∘ₗ
      (rightCoaction π).toLinearMap.rTensor (MonoidAlgebra K M) ∘ₗ
      (rightCoaction π).toLinearMap =
    (comul (R := K) (A := MonoidAlgebra K M)).lTensor C ∘ₗ (rightCoaction π).toLinearMap := by
  let p := π.toAlgHom.toLinearMap
  have hp : TensorProduct.map p p ∘ₗ comul = (comul (R := K)).comp p :=
    CoalgHomClass.map_comp_comul π
  change (TensorProduct.assoc K C (MonoidAlgebra K M) (MonoidAlgebra K M)).toLinearMap ∘ₗ
    (p.lTensor C ∘ₗ comul).rTensor (MonoidAlgebra K M) ∘ₗ
    p.lTensor C ∘ₗ comul = (comul (R := K)).lTensor C ∘ₗ p.lTensor C ∘ₗ comul
  simp only [coassoc_simps, ← hp]

set_option maxHeartbeats 600000 in
private theorem invariantPart_mem (π : C →ₐc[K] MonoidAlgebra K M) (a : C) :
    invariantPart π a ∈ invariants π := by
  let P := MonoidAlgebra K M
  let l : P →ₗ[K] K := identityCoefficient K M
  let d := (rightCoaction π).toLinearMap
  let c (B : Type u) [AddCommGroup B] [Module K B] : B ⊗[K] P →ₗ[K] B :=
    (TensorProduct.rid K B).toLinearMap.comp (l.lTensor B)
  have hc :
      c (C ⊗[K] P) ∘ₗ (TensorProduct.assoc K C P P).symm.toLinearMap ∘ₗ
          (comul (R := K) (A := P)).lTensor C =
        (TensorProduct.mk K C P).flip 1 ∘ₗ c C := by
    apply TensorProduct.ext
    apply LinearMap.ext₂
    intro a m
    change (c (C ⊗[K] P) ∘ₗ (TensorProduct.assoc K C P P).symm.toLinearMap ∘ₗ
        (comul (R := K) (A := P)).lTensor C) (a ⊗ₜ[K] m) =
      ((TensorProduct.mk K C P).flip 1 ∘ₗ c C) (a ⊗ₜ[K] m)
    induction m using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | single m r =>
      have hm : comul (R := K) (MonoidAlgebra.single m r : P) =
          MonoidAlgebra.of K M m ⊗ₜ[K] MonoidAlgebra.single m r := by
        simp [MonoidAlgebra.comul_single, MonoidAlgebra.of_apply]
      simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, hm,
        TensorProduct.assoc_symm_tmul, c, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        LinearMap.flip_apply, TensorProduct.mk_apply]
      rw [TensorProduct.smul_tmul']
      by_cases h : m = 1
      · rw [h, map_one]
      · change identityCoefficient K M (MonoidAlgebra.single m r) • a ⊗ₜ[K] _ = _
        rw [identityCoefficient_single_of_ne m r h]
        simp
  have hn : c (C ⊗[K] P) ∘ₗ d.rTensor P = d ∘ₗ c C := by
    apply TensorProduct.ext
    apply LinearMap.ext₂
    intro a m
    simp [c]
  have h := LinearMap.congr_fun (rightCoaction_coassoc π) a
  have h' := congrArg (fun v => c (C ⊗[K] P) ((TensorProduct.assoc K C P P).symm v)) h
  change c (C ⊗[K] P) ((TensorProduct.assoc K C P P).symm
    ((TensorProduct.assoc K C P P) (d.rTensor P (d a)))) =
    (c (C ⊗[K] P) ∘ₗ (TensorProduct.assoc K C P P).symm.toLinearMap ∘ₗ
      (comul (R := K) (A := P)).lTensor C) (d a) at h'
  rw [LinearEquiv.symm_apply_apply, hc] at h'
  have hd := LinearMap.congr_fun hn (d a)
  exact hd.symm.trans h'

set_option maxHeartbeats 600000 in
private theorem invariantPart_restrict (z : X →* M)
    (t : C →ₐc[K] MonoidAlgebra K X) (a : C) :
    t (invariantPart ((MonoidAlgebra.mapDomainBialgHom K z).comp t) a) =
      invariantPart (MonoidAlgebra.mapDomainBialgHom K z) (t a) := by
  let P := MonoidAlgebra K M
  let T := MonoidAlgebra K X
  let l : P →ₗ[K] K := identityCoefficient K M
  let t' := t.toAlgHom.toLinearMap
  let z' := (MonoidAlgebra.mapDomainBialgHom K z).toAlgHom.toLinearMap
  have h : TensorProduct.map t' t' ∘ₗ comul = ((comul (R := K)).comp t') :=
    CoalgHomClass.map_comp_comul t
  have h₁ : t'.rTensor P ∘ₗ (z'.comp t').lTensor C ∘ₗ comul =
      z'.lTensor T ∘ₗ comul ∘ₗ t' := by
    change _ = z'.lTensor T ∘ₗ ((comul (R := K)).comp t')
    rw [← h]
    simp only [LinearMap.rTensor_def, LinearMap.lTensor_def, ← LinearMap.comp_assoc,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  have h₂ : t' ∘ₗ (TensorProduct.rid K C).toLinearMap ∘ₗ l.lTensor C =
      (TensorProduct.rid K T).toLinearMap ∘ₗ l.lTensor T ∘ₗ t'.rTensor P := by
    apply TensorProduct.ext
    apply LinearMap.ext₂
    intro a m
    simp
  change (t' ∘ₗ (TensorProduct.rid K C).toLinearMap ∘ₗ l.lTensor C ∘ₗ
      (z'.comp t').lTensor C ∘ₗ comul) a =
    ((TensorProduct.rid K T).toLinearMap ∘ₗ l.lTensor T ∘ₗ z'.lTensor T ∘ₗ comul ∘ₗ t') a
  have e : t' ∘ₗ (TensorProduct.rid K C).toLinearMap ∘ₗ l.lTensor C ∘ₗ
        (z'.comp t').lTensor C ∘ₗ comul =
      (TensorProduct.rid K T).toLinearMap ∘ₗ l.lTensor T ∘ₗ z'.lTensor T ∘ₗ comul ∘ₗ t' := by
    calc
      _ = (t' ∘ₗ (TensorProduct.rid K C).toLinearMap ∘ₗ l.lTensor C) ∘ₗ
          (z'.comp t').lTensor C ∘ₗ comul := by simp only [LinearMap.comp_assoc]
      _ = _ := by rw [h₂]; simp only [LinearMap.comp_assoc, h₁]
  exact LinearMap.congr_fun e a

private theorem invariantPart_torus (z : X →* M) (b : MonoidAlgebra K ↥z.ker) :
    let j := MonoidAlgebra.mapDomainBialgHom K z.ker.subtype
    invariantPart (MonoidAlgebra.mapDomainBialgHom K z) (j b) = j b := by
  classical
  dsimp only
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single x r =>
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    let m := (x : X)
    have hs : r • MonoidAlgebra.of K X m = MonoidAlgebra.single m r := by
      simp [MonoidAlgebra.of_apply]
    change invariantPart (MonoidAlgebra.mapDomainBialgHom K z) (MonoidAlgebra.single m r) =
      MonoidAlgebra.single m r
    rw [← hs, map_smul]
    have hz : z m = 1 := x.property
    simp [invariantPart, rightCoaction, MonoidAlgebra.of_apply,
      hz, identityCoefficient_single_one]

/-- The torus restriction of the quotient remains surjective on coordinate rings.
The identity component of the grading lifts each invariant torus function. -/
private theorem quotientTorusRestriction_surjective (z : X →* M)
    (t : C →ₐc[K] MonoidAlgebra K X) (ht : Function.Surjective t)
    {B : Type u} [CommRing B] [HopfAlgebra K B] (j : B →ₐc[K] C)
    (t₀ : B →ₐc[K] MonoidAlgebra K ↥z.ker)
    (hj : ∀ a ∈ invariants ((MonoidAlgebra.mapDomainBialgHom K z).comp t), ∃ b, j b = a)
    (hcomp : (MonoidAlgebra.mapDomainBialgHom K z.ker.subtype).comp t₀ = t.comp j) :
    Function.Surjective t₀ := by
  intro b
  let i := MonoidAlgebra.mapDomainBialgHom K z.ker.subtype
  obtain ⟨a, ha⟩ := ht (i b)
  obtain ⟨v, hv⟩ := hj _ (invariantPart_mem _ a)
  refine ⟨v, torusRestriction_injective (K := K) z ?_⟩
  change i (t₀ v) = i b
  rw [show i (t₀ v) = t (j v) from DFunLike.congr_fun hcomp v,
    hv, invariantPart_restrict, ha]
  exact invariantPart_torus z b

end TorusRestriction
section KernelCentrality

open Algebra.TensorProduct

variable {K C U M : Type u} [CommRing K] [CommRing C] [CommRing U]
  [HopfAlgebra K C] [Algebra K U] [CommGroup M]

/-- It suffices to test commutation after a schematically dominant affine restriction on the
ambient group. The universal test algebra still retains the entire kernel scheme. -/
private theorem central_of_restriction (π : C →ₐc[K] MonoidAlgebra K M)
    (f : C →ₐ[K] U) (hf : Function.Injective f)
    (h : Commute
      (toConv (includeLeft.comp f) : WithConv (C →ₐ[K] U ⊗[K] MonoidAlgebra K M))
      (toConv (includeRight.comp π.toAlgHom))) :
    IsCentral π := by
  let P := MonoidAlgebra K M
  let e := Algebra.TensorProduct.map f (AlgHom.id K P)
  have he : Function.Injective e :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := P) f.toLinearMap hf
  apply AlgHom.ext
  intro a
  apply he
  have h₁ :
      (lmul' K).comp
        (Algebra.TensorProduct.map (includeLeft.comp f : C →ₐ[K] U ⊗[K] P)
          (includeRight.comp π.toAlgHom)) =
      e.comp (Algebra.TensorProduct.map (AlgHom.id K C) π.toAlgHom) := by
    apply Algebra.TensorProduct.ext <;> ext <;> simp [e]
  have h₂ :
      (lmul' K).comp
        (Algebra.TensorProduct.map (includeRight.comp π.toAlgHom : C →ₐ[K] U ⊗[K] P)
          (includeLeft.comp f)) =
      (e.comp (Algebra.TensorProduct.comm K P C).toAlgHom).comp
        (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id K C)) := by
    apply Algebra.TensorProduct.ext <;> ext <;> simp [e]
  have eq := congrArg (fun x : WithConv (C →ₐ[K] U ⊗[K] P) => x.ofConv a) h.eq
  rw [AlgHom.convMul_def, AlgHom.convMul_def, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    h₁, h₂] at eq
  exact eq

end KernelCentrality
section ProductTorus

open Algebra.TensorProduct

variable {K : Type u} [CommRing K]

/-- The coordinate equivalence for a product of diagonalizable groups. -/
private def productGroupAlgebra (X Y : Type u) [CommGroup X] [CommGroup Y] :
    MonoidAlgebra K X ⊗[K] MonoidAlgebra K Y ≃ₐ[K] MonoidAlgebra K (X × Y) := by
  let a := (MonoidAlgebra.mapDomainBialgHom K (MonoidHom.inl X Y)).toAlgHom
  let b := (MonoidAlgebra.mapDomainBialgHom K (MonoidHom.inr X Y)).toAlgHom
  let l : MonoidAlgebra K X →ₐ[K] MonoidAlgebra K X ⊗[K] MonoidAlgebra K Y := includeLeft
  let r : MonoidAlgebra K Y →ₐ[K] MonoidAlgebra K X ⊗[K] MonoidAlgebra K Y := includeRight
  let f := Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)
  let g := MonoidAlgebra.lift K _ (X × Y)
    ((l.toMonoidHom.comp
      ((MonoidAlgebra.of K X).comp (MonoidHom.fst X Y))) *
      (r.toMonoidHom.comp ((MonoidAlgebra.of K Y).comp (MonoidHom.snd X Y))))
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply (MonoidAlgebra.lift K _ (X × Y)).symm.injective
    apply MonoidHom.ext
    rintro ⟨x, y⟩
    change f (g (MonoidAlgebra.of K (X × Y) (x, y))) = MonoidAlgebra.of K (X × Y) (x, y)
    rw [MonoidAlgebra.lift_of]
    change f (l (MonoidAlgebra.of K X x) *
      r (MonoidAlgebra.of K Y y)) = _
    have hx : f (l (MonoidAlgebra.of K X x)) =
        MonoidAlgebra.of K (X × Y) (x, 1) := by
      simp [l, f, a, MonoidAlgebra.of_apply]
    have hy : f (r (MonoidAlgebra.of K Y y)) =
        MonoidAlgebra.of K (X × Y) (1, y) := by
      simp [r, f, b, MonoidAlgebra.of_apply]
    rw [map_mul, hx, hy, ← map_mul]
    congr 1
    simp
  · apply Algebra.TensorProduct.ext
    · apply (MonoidAlgebra.lift K _ X).symm.injective
      apply MonoidHom.ext
      intro x
      change g (f (l (MonoidAlgebra.of K X x))) = l (MonoidAlgebra.of K X x)
      simp [l, r, f, a, g, MonoidAlgebra.of_apply, ← MonoidAlgebra.one_def]
    · apply (MonoidAlgebra.lift K _ Y).symm.injective
      apply MonoidHom.ext
      intro y
      change g (f (r (MonoidAlgebra.of K Y y))) = r (MonoidAlgebra.of K Y y)
      simp [l, r, f, b, g, MonoidAlgebra.of_apply, ← MonoidAlgebra.one_def]

end ProductTorus

section SplitTorusSmoothness

variable {K X : Type u} [CommRing K] [CommGroup X]

private theorem units_surjective_of_squareZero {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I ^ 2 = ⊥) :
    Function.Surjective (Units.map (Ideal.Quotient.mk I : S →+* S ⧸ I).toMonoidHom) := by
  intro a
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := I) a.val
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := I) a⁻¹.val
  have hm : x * y - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [hx, hy]
  have hn : IsNilpotent (x * y - 1) := by
    refine ⟨2, ?_⟩
    have h : (x * y - 1)^2 ∈ I ^ 2 := Ideal.pow_mem_pow hm 2
    simpa only [hI, Ideal.mem_bot] using h
  have hu : IsUnit (x * y) := by
    simpa using hn.isUnit_add_one
  obtain ⟨v, rfl⟩ := isUnit_of_mul_isUnit_left hu
  refine ⟨v, Units.ext ?_⟩
  exact hx

private theorem splitGroupAlgebra_smooth [IsNoetherianRing K]
    [Module.Free ℤ (Additive X)] [Module.Finite ℤ (Additive X)] :
    Algebra.Smooth K (MonoidAlgebra K X) := by
  letI : Group.FG X := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  intro S _ _ I hI g
  let q := Ideal.Quotient.mkₐ K I
  let t := (g.toMonoidHom.comp (MonoidAlgebra.of K X)).toHomUnits
  let b := Module.finBasis ℤ (Additive X)
  choose v hv using fun i => units_surjective_of_squareZero I hI (t (Additive.toMul (b i)))
  let r : X →* Sˣ := (b.constr ℤ (Additive.ofMul ∘ v)).toAddMonoidHom.toMultiplicative
  refine ⟨MonoidAlgebra.lift K S X ((Units.coeHom S).comp r), ?_⟩
  have hr : (Units.map q.toMonoidHom).comp r = t := by
    have e : ((Units.map q.toMonoidHom).comp r).toAdditive.toIntLinearMap =
        t.toAdditive.toIntLinearMap := by
      apply b.ext
      intro i
      have h := b.constr_basis ℤ (Additive.ofMul ∘ v) i
      change Additive.ofMul (Units.map q.toMonoidHom
        (Additive.toMul ((b.constr ℤ (Additive.ofMul ∘ v)) (b i)))) =
          Additive.ofMul (t (Additive.toMul (b i)))
      rw [h]
      exact congrArg Additive.ofMul (hv i)
    apply MonoidHom.ext
    intro x
    exact congrArg Additive.toMul (DFunLike.congr_fun e (Additive.ofMul x))
  apply (MonoidAlgebra.lift K (S ⧸ I) X).symm.injective
  apply MonoidHom.ext
  intro x
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply,
    ← MonoidAlgebra.of_apply, MonoidAlgebra.lift_of]
  change ((Units.map q.toMonoidHom) (r x)).val = (t x).val
  exact congrArg Units.val (DFunLike.congr_fun hr x)

end SplitTorusSmoothness

section FibreComparison

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open _root_.LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)

private def fibreIterateIso {K E : Type u} [Field K] [Field E] [Algebra R.{u} K] [Algebra K E]
    [Algebra R.{u} E]
    (hTower : (algebraMap K E).comp (algebraMap R.{u} K) = algebraMap R.{u} E)
    (G : Grp (OverBase R.{u})) :
    (groupBaseChange K E).obj ((fibreGroup K).obj G) ≅ (fibreGroup E).obj G := by
  let f := fieldSpecMap K E
  let g := Spec.map (CommRingCat.ofHom (algebraMap R.{u} K))
  have h : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R.{u} E)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hTower]
  let i := (Functor.mapGrpCompIso (F := Over.pullback g) (G := Over.pullback f)).symm ≪≫
    Functor.mapGrpNatIso (Over.pullbackComp f g).symm
  exact i.app G ≪≫ eqToIso
    (congrArg (fun m => (Over.pullback m).mapGrp.obj G) h)

private def fibreProductIso {K : Type u} [Field K] [Algebra R.{u} K] (G H : Grp (OverBase R.{u})) :
    (fibreGroup K).obj (G ⊗ H) ≅ (fibreGroup K).obj G ⊗ (fibreGroup K).obj H :=
  (Functor.Monoidal.μIso (fibreGroup K) G H).symm

attribute [local instance] integerAlgebra

private theorem forgetFibrePoint_injective {k : Type u} [Field k] (G : IntegralGroup.{u})
    (S : TestAlgebra k) :
    Function.Injective (forgetFibrePoint G S) := by
  intro p q h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left h
  · exact (Over.w p).trans (Over.w q).symm

private theorem forgetFibrePoint_surjective {k : Type u} [Field k] (G : IntegralGroup.{u})
    (S : TestAlgebra k) :
    Function.Surjective (forgetFibrePoint G S) := by
  intro p
  let T := (testSpec k).obj (op S)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
  have h : p.left ≫ G.X.hom = T.hom ≫ f := by
    rw [Over.w p]
    change Spec.map (CommRingCat.ofHom (algebraMap R.{u} S)) =
      Spec.map (CommRingCat.ofHom (algebraMap k S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext n
    exact (map_intCast (algebraMap k S) n.down).symm
  refine ⟨Over.homMk (pullback.lift p.left T.hom h) (pullback.lift_snd ..), ?_⟩
  apply Over.OverMorphism.ext
  exact pullback.lift_fst ..

set_option backward.isDefEq.respectTransparency false in
private theorem forgetFibrePoint_comp {k : Type u} [Field k] {G H : IntegralGroup.{u}}
    (f : G ⟶ H) (S : TestAlgebra k) (p : GroupPoints ((fibre k).obj G) S) :
    forgetFibrePoint H S (p ≫ ((fibre k).map f).hom.hom) =
      forgetFibrePoint G S p ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((fibre k).map f).hom.hom.left) ≫ pullback.fst _ _ =
    (p.left ≫ pullback.fst _ _) ≫ f.hom.hom.left
  simp only [Functor.mapGrp_map_hom_hom, Over.pullback_map_left]
  rw [Category.assoc, pullback.lift_fst, Category.assoc]

end FibreComparison

section CellCentrality

open WithConv Algebra.TensorProduct

set_option backward.isDefEq.respectTransparency false in
private theorem coordinatePoints_antipode (S : IntegralAlgebra.{u}) (p : A →ₐ[R.{u}] S) :
    coordinatePoints S (toConv (p.comp (HopfAlgebra.antipodeAlgHom R.{u} A))) =
      (coordinatePoints S (toConv p))⁻¹ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (p.comp (HopfAlgebra.antipodeAlgHom R.{u} A)).toRingHom) =
    Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom R.{u} A).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem additivePoint_surjective (S : IntegralAlgebra.{u}) :
    Function.Surjective (additivePoint S) := by
  intro q
  let a := ((algSpec.fullyFaithful (R := CommRingCat.of R.{u})).preimage q).unop.hom
  refine ⟨a Polynomial.X, ?_⟩
  have h : (Polynomial.aeval (a Polynomial.X) : Polynomial R.{u} →ₐ[R.{u}] S) = a :=
    Polynomial.algHom_ext (Polynomial.aeval_X _)
  unfold additivePoint
  rw [h]
  exact (algSpec.fullyFaithful (R := CommRingCat.of R.{u})).map_preimage q

set_option backward.isDefEq.respectTransparency false in
private theorem rootProduct_commutes {I : Type u} (S : IntegralAlgebra.{u})
    (x : I → A →ₐ[R.{u}] Polynomial R.{u}) (g : IntegralPoints (HopfSpectrum R.{u} A) S)
    (h : ∀ i a, Commute g (additivePoint S a ≫ spectrumOfAlgHom (x i))) :
    ∀ (l : List I) (p : integralSpec.obj (op S) ⟶ lineProduct R.{u} l),
      Commute g (p ≫ Specs.IntegralCentralQuotient.rootProduct x l) := by
  intro l
  induction l with
  | nil =>
    intro p
    rw [Specs.IntegralCentralQuotient.rootProduct, MonObj.comp_one]
    exact Commute.one_right g
  | cons i l ih =>
    intro p
    rw [Specs.IntegralCentralQuotient.rootProduct, MonObj.comp_mul, ← Category.assoc,
      ← Category.assoc]
    obtain ⟨a, ha⟩ := additivePoint_surjective S
      (p ≫ fst (additiveScheme.{u}) (lineProduct R.{u} l))
    exact (ha ▸ h i a).mul_right (ih (p ≫ snd _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem cellPoint_commutes {I X M : Type u} [CommGroup X] [CommGroup M]
    (z : X →* M) (t : A →ₐc[R.{u}] MonoidAlgebra R.{u} X) (x : I → A →ₐ[R.{u}] Polynomial R.{u})
    (α : I → X) (halpha : ∀ i, z (α i) = 1)
    (hscalar : ∀ i, RootScalarAction t (x i) (α i)) (negative positive : List I)
    (S : IntegralAlgebra.{u}) (v : MonoidAlgebra R.{u} M →ₐ[R.{u}] S)
    (p : integralSpec.obj (op S) ⟶ _) :
    Commute (coordinatePoints S (toConv (v.comp ((MonoidAlgebra.mapDomainBialgHom R.{u} z).comp t).toAlgHom)))
      (p ≫ Specs.IntegralCentralQuotient.cellMap t x negative positive) := by
  let s : MonoidAlgebra R.{u} X →ₐ[R.{u}] S := v.comp (MonoidAlgebra.mapDomainBialgHom R.{u} z).toAlgHom
  let g : IntegralPoints (HopfSpectrum R.{u} A) S :=
    coordinatePoints S (toConv (s.comp t.toAlgHom))
  have hr (i : I) (a : S) : Commute g (additivePoint S a ≫ spectrumOfAlgHom (x i)) := by
    have h := hscalar i S a s
    change _ = toConv ((Polynomial.aeval (s (MonoidAlgebra.of R.{u} X (α i)) * a)).comp (x i)) at h
    have ha : s (MonoidAlgebra.of R.{u} X (α i)) = 1 := by
      change v (MonoidAlgebra.mapDomainBialgHom R.{u} z (MonoidAlgebra.single (α i) 1)) = 1
      rw [MonoidAlgebra.mapDomainBialgHom_single, halpha, ← MonoidAlgebra.one_def, map_one]
    rw [ha, one_mul] at h
    have eq := congrArg (coordinatePoints S) h
    change _ = _ at eq
    simp only [map_mul, coordinatePoints_antipode, coordinatePoints_polynomial] at eq
    exact (mul_inv_eq_iff_eq_mul.mp eq)
  have ht (q : IntegralPoints (HopfSpectrum R.{u} (MonoidAlgebra R.{u} X)) S) :
      Commute g (q ≫ (spectrumOfHopfHom t).hom.hom) := by
    obtain ⟨q', rfl⟩ := (coordinatePoints S).surjective q
    change Commute g (coordinatePoints S (toConv q'.ofConv) ≫ (spectrumOfHopfHom t).hom.hom)
    have h : Commute (toConv s : WithConv (MonoidAlgebra R.{u} X →ₐ[R.{u}] S)) q' :=
      Commute.all _ _
    have e := congrArg (fun f => coordinatePoints S (toConv (f.ofConv.comp t.toAlgHom))) h.eq
    simp only [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv, map_mul] at e
    rw [← coordinatePoints_comp]
    exact e
  change Commute g _
  simp only [Specs.IntegralCentralQuotient.cellMap, MonObj.comp_mul, ← Category.assoc]
  exact (rootProduct_commutes S x g hr negative _).mul_right
    ((ht _).mul_right (rootProduct_commutes S x g hr positive _))

end CellCentrality

section CoverMaps

open Algebra.TensorProduct

private abbrev torusOf (X : Type u) [CommGroup X] : IntegralGroup.{u} :=
  HopfSpectrum R.{u} (MonoidAlgebra R.{u} X)

private def productTorusMap (X Y : Type u) [CommGroup X] [CommGroup Y] :
    torusOf (X × Y) ⟶ torusOf X ⊗ torusOf Y :=
  lift (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R.{u} (MonoidHom.inl X Y)))
    (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R.{u} (MonoidHom.inr X Y)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
private theorem productTorusMap_isIso (X Y : Type u) [CommGroup X] [CommGroup Y] :
    IsIso (productTorusMap X Y) := by
  let B := MonoidAlgebra R.{u} X
  let C := MonoidAlgebra R.{u} Y
  let E := MonoidAlgebra R.{u} (X × Y)
  let a : B →ₐc[R.{u}] E := MonoidAlgebra.mapDomainBialgHom R.{u} (MonoidHom.inl X Y)
  let b : C →ₐc[R.{u}] E := MonoidAlgebra.mapDomainBialgHom R.{u} (MonoidHom.inr X Y)
  let f : B ⊗[R.{u}] C ≃ₐ[R.{u}] E := productGroupAlgebra X Y
  let j := productTorusMap X Y
  let i : (torusOf (X × Y)).X.left ≅ ((torusOf X).X ⊗ (torusOf Y).X).left :=
    Scheme.Spec.mapIso f.toRingEquiv.toCommRingCatIso.op ≪≫ (pullbackSpecIso R.{u} B C).symm
  have hi : i.hom = j.hom.hom.left := by
    apply pullback.hom_ext
    · have h : j.hom.hom.left ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom a.toAlgHom.toRingHom) := by
        change (lift (spectrumOfHopfHom a).hom.hom (spectrumOfHopfHom b).hom.hom).left ≫ _ = _
        exact congrArg Over.Hom.left (lift_fst (spectrumOfHopfHom a).hom.hom
          (spectrumOfHopfHom b).hom.hom)
      have k : i.hom = Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
          (pullbackSpecIso R.{u} B C).inv := rfl
      rw [h, k, Category.assoc]
      change Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
        (pullbackSpecIso R.{u} B C).inv ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R.{u} B)))
            (Spec.map (CommRingCat.ofHom (algebraMap R.{u} C))) = _
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      apply congrArg (fun q : B →+* E => Spec.map (CommRingCat.ofHom q))
      apply RingHom.ext
      intro x
      change f (x ⊗ₜ[R.{u}] (1 : C)) = a x
      change a x * b 1 = a x
      rw [map_one, mul_one]
    · have h : j.hom.hom.left ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom b.toAlgHom.toRingHom) := by
        change (lift (spectrumOfHopfHom a).hom.hom (spectrumOfHopfHom b).hom.hom).left ≫ _ = _
        exact congrArg Over.Hom.left (lift_snd (spectrumOfHopfHom a).hom.hom
          (spectrumOfHopfHom b).hom.hom)
      have k : i.hom = Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
          (pullbackSpecIso R.{u} B C).inv := rfl
      rw [h, k, Category.assoc]
      change Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
        (pullbackSpecIso R.{u} B C).inv ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R.{u} B)))
            (Spec.map (CommRingCat.ofHom (algebraMap R.{u} C))) = _
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      apply congrArg (fun q : C →+* E => Spec.map (CommRingCat.ofHom q))
      apply RingHom.ext
      intro y
      change f ((1 : B) ⊗ₜ[R.{u}] y) = b y
      change a 1 * b y = b y
      rw [map_one, one_mul]
  let e : (torusOf (X × Y)).X ≅ (torusOf X).X ⊗ (torusOf Y).X :=
    Over.isoMk i (hi ▸ Over.w j.hom.hom)
  have h : e.hom = j.hom.hom := Over.OverMorphism.ext hi
  letI : IsMonHom e.hom := h ▸ j.hom.isMonHom_hom
  let e' : torusOf (X × Y) ≅ torusOf X ⊗ torusOf Y := Grp.mkIso' e
  have eq : e'.hom = productTorusMap X Y := Grp.hom_ext _ _ h
  exact eq ▸ e'.isIso_hom

private def productTorusIso (X Y : Type u) [CommGroup X] [CommGroup Y] :
    torusOf (X × Y) ≅ torusOf X ⊗ torusOf Y :=
  letI := productTorusMap_isIso X Y
  asIso (productTorusMap X Y)

private def coverProductCharacters (D : BasedRootDatum.{u}) :
    Multiplicative (derivedDatum D).X × Multiplicative (Dual ℤ (CentralLattice D)) ≃*
      Multiplicative (CoverCharacters D) where
  toFun x := Multiplicative.ofAdd ((coverCharactersEquiv D).symm (x.1.toAdd, x.2.toAdd))
  invFun x :=
    (Multiplicative.ofAdd ((coverCharactersEquiv D) x.toAdd).1,
      Multiplicative.ofAdd ((coverCharactersEquiv D) x.toAdd).2)
  left_inv x := by
    have h := (coverCharactersEquiv D).apply_symm_apply (x.1.toAdd, x.2.toAdd)
    exact congrArg (fun y : (derivedDatum D).X × Dual ℤ (CentralLattice D) =>
      (Multiplicative.ofAdd y.1, Multiplicative.ofAdd y.2)) h
  right_inv x := congrArg Multiplicative.ofAdd ((coverCharactersEquiv D).symm_apply_apply x.toAdd)
  map_mul' x y := congrArg Multiplicative.ofAdd ((coverCharactersEquiv D).symm.map_add
    (x.1.toAdd, x.2.toAdd) (y.1.toAdd, y.2.toAdd))

private abbrev centralTorus (D : BasedRootDatum.{u}) : IntegralGroup.{u} :=
  torusOf (Multiplicative (Dual ℤ (CentralLattice D)))

private def coverTorusProductIso (D : BasedRootDatum.{u}) :
    torusOf (Multiplicative (CoverCharacters D)) ≅ splitTorus (derivedDatum D) ⊗ centralTorus D :=
  (hopfSpec (CommRingCat.of R.{u})).mapIso
      (CommHopfAlgCat.isoMk
        (MonoidAlgebra.domCongrBialgEquiv R.{u} R.{u} (coverProductCharacters D))).op ≪≫
    productTorusIso _ _

private abbrev coverGroup {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :=
  H.group ⊗ centralTorus D

private def coverTorus {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    torusOf (Multiplicative (CoverCharacters D)) ⟶ coverGroup H :=
  (coverTorusProductIso D).hom ≫ (H.torus ⊗ₘ 𝟙 (centralTorus D))

private def coverRootMap {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) (a : D.I) :
    H.line.group ⟶ coverGroup H :=
  lift (H.root a) (0 : H.line.group ⟶ centralTorus D)

end CoverMaps

section CoverGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem tensorClosedImmersion {S : Scheme.{u}} {U V X Y : Over S}
    (f : U ⟶ X) (g : V ⟶ Y) [IsClosedImmersion f.left] [IsClosedImmersion g.left] :
    IsClosedImmersion (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left, pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem centralTorus_smooth (D : BasedRootDatum.{u}) :
    Smooth (centralTorus D).X.hom := by
  let M := Multiplicative (Dual ℤ (CentralLattice D))
  letI := D.freeY
  letI := D.finiteY
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R.{u} (MonoidAlgebra R.{u} M))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R.{u} (MonoidAlgebra R.{u} M)).Smooth
  letI : IsNoetherianRing R.{u} := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : Module.Free ℤ (Additive M) := inferInstanceAs
    (Module.Free ℤ (Dual ℤ (CentralLattice D)))
  letI : Module.Finite ℤ (Additive M) := inferInstanceAs
    (Module.Finite ℤ (Dual ℤ (CentralLattice D)))
  exact RingHom.smooth_algebraMap.mpr splitGroupAlgebra_smooth

private theorem coverGroup_affine {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    IsAffine (coverGroup H).X.left := by
  letI : IsAffine H.group.X.left := H.affine
  letI : IsAffine (centralTorus D).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra R.{u}
      (Multiplicative (Dual ℤ (CentralLattice D)))))))
  change IsAffine (pullback H.group.X.hom (centralTorus D).X.hom)
  infer_instance

private theorem coverGroup_smooth {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    Smooth (coverGroup H).X.hom := by
  letI : Smooth H.group.X.hom := H.smooth
  letI : Smooth (centralTorus D).X.hom := centralTorus_smooth D
  change Smooth (H.group.X ⊗ (centralTorus D).X).hom
  rw [Over.tensorObj_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem coverTorus_closed {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    IsClosedImmersion (coverTorus H).hom.hom.left := by
  letI : IsClosedImmersion H.torus.hom.hom.left := H.torusClosed
  let e := (Grp.forget IntegralScheme.{u} ⋙ Over.forget _).mapIso (coverTorusProductIso D)
  change IsClosedImmersion (e.hom ≫ (H.torus.hom.hom ⊗ₘ 𝟙 (centralTorus D).X).left)
  letI := tensorClosedImmersion H.torus.hom.hom (𝟙 (centralTorus D).X)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem coverRoot_closed {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) (a : D.I) :
    IsClosedImmersion (coverRootMap H a).hom.hom.left := by
  let p : (coverGroup H).X ⟶ H.group.X := fst _ _
  letI : IsAffine (centralTorus D).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra R.{u}
      (Multiplicative (Dual ℤ (CentralLattice D)))))))
  have hp : IsSeparated p.left := inferInstanceAs (IsSeparated
    (pullback.fst H.group.X.hom (centralTorus D).X.hom))
  have he : (coverRootMap H a).hom.hom.left ≫ p.left = (H.root a).hom.hom.left :=
    congrArg Over.Hom.left (lift_fst (H.root a).hom.hom (0 : H.line.group ⟶ centralTorus D).hom.hom)
  haveI : IsClosedImmersion ((coverRootMap H a).hom.hom.left ≫ p.left) := he ▸ H.rootClosed a
  exact IsClosedImmersion.of_comp (coverRootMap H a).hom.hom.left p.left

end CoverGeometry

section QuotientIdentity

open Coalgebra

/-- For flat affine models, two injective Hopf maps to the same coordinate algebra
with the same image determine canonically isomorphic group schemes. -/
private theorem exists_bialgEquiv_of_sameImage {k B C E : Type u} [CommRing k]
    [CommRing B] [CommRing C] [CommRing E]
    [Bialgebra k B] [Bialgebra k C] [Bialgebra k E]
    [Module.Flat k C] [Module.Flat k E]
    (f : B →ₐc[k] E) (g : C →ₐc[k] E)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (heq : f.toAlgHom.range = g.toAlgHom.range) :
    ∃ e : B ≃ₐc[k] C, g.comp e.toBialgHom = f := by
  let e := (AlgEquiv.ofInjective f.toAlgHom hf).trans
    ((Subalgebra.equivOfEq _ _ heq).trans (AlgEquiv.ofInjective g.toAlgHom hg).symm)
  have h : g.toAlgHom.comp (e : B →ₐ[k] C) = f.toAlgHom := by
    apply AlgHom.ext
    intro b
    have hh := (AlgEquiv.ofInjective g.toAlgHom hg).apply_symm_apply
      (Subalgebra.equivOfEq _ _ heq (AlgEquiv.ofInjective f.toAlgHom hf b))
    exact congrArg Subtype.val hh
  have hc : (Bialgebra.counitAlgHom k C).comp (e : B →ₐ[k] C) = Bialgebra.counitAlgHom k B := by
    rw [← g.counitAlgHom_comp, AlgHom.comp_assoc, h, f.counitAlgHom_comp]
  have hinj : Function.Injective (Algebra.TensorProduct.map g.toAlgHom g.toAlgHom) :=
    _root_.TensorProduct.map_injective_of_flat_flat g.toAlgHom.toLinearMap
      g.toAlgHom.toLinearMap hg hg
  have hm : (Algebra.TensorProduct.map (e : B →ₐ[k] C) (e : B →ₐ[k] C)).comp
      (Bialgebra.comulAlgHom k B) = (Bialgebra.comulAlgHom k C).comp (e : B →ₐ[k] C) := by
    apply AlgHom.ext
    intro b
    apply hinj
    change (((Algebra.TensorProduct.map g.toAlgHom g.toAlgHom).comp _).comp
      (Bialgebra.comulAlgHom k B)) b =
      (((Algebra.TensorProduct.map g.toAlgHom g.toAlgHom).comp
        (Bialgebra.comulAlgHom k C)).comp (e : B →ₐ[k] C)) b
    rw [← Algebra.TensorProduct.map_comp, h, f.map_comp_comulAlgHom,
      g.map_comp_comulAlgHom, AlgHom.comp_assoc, h]
  refine ⟨BialgEquiv.ofAlgEquiv e hc hm, ?_⟩
  exact BialgHom.ext (AlgHom.congr_fun h)

private theorem spectrumOfAlgHom_comp {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
    [Algebra R.{u} B] [Algebra R.{u} C] [Algebra R.{u} E] (f : B →ₐ[R.{u}] C) (g : C →ₐ[R.{u}] E) :
    spectrumOfAlgHom (g.comp f) = spectrumOfAlgHom g ≫ spectrumOfAlgHom f := by
  exact (integralSpec.map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op)

private theorem spectrumOfHopfHom_comp {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
    [HopfAlgebra R.{u} B] [HopfAlgebra R.{u} C] [HopfAlgebra R.{u} E]
    (f : B →ₐc[R.{u}] C) (g : C →ₐc[R.{u}] E) :
    spectrumOfHopfHom (g.comp f) = spectrumOfHopfHom g ≫ spectrumOfHopfHom f := by
  exact ((hopfSpec (CommRingCat.of R.{u})).map_comp (CommHopfAlgCat.ofHom g).op
    (CommHopfAlgCat.ofHom f).op)

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateRootProduct_comp {B C I : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra R.{u} B] [HopfAlgebra R.{u} C] (j : B →ₐc[R.{u}] C)
    (x : I → C →ₐ[R.{u}] Polynomial R.{u}) (l : List I) :
    Specs.IntegralCentralQuotient.rootProduct x l ≫ (spectrumOfHopfHom j).hom.hom =
      Specs.IntegralCentralQuotient.rootProduct (fun i => (x i).comp j.toAlgHom) l := by
  induction l with
  | nil => exact MonObj.one_comp _
  | cons i l ih =>
    simp only [Specs.IntegralCentralQuotient.rootProduct, MonObj.mul_comp, Category.assoc,
      ih, spectrumOfAlgHom_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateCell_comp {B C X I : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra R.{u} B] [HopfAlgebra R.{u} C] [CommGroup X] (j : B →ₐc[R.{u}] C)
    (t : C →ₐc[R.{u}] MonoidAlgebra R.{u} X) (x : I → C →ₐ[R.{u}] Polynomial R.{u})
    (negative positive : List I) :
    Specs.IntegralCentralQuotient.cellMap t x negative positive ≫ (spectrumOfHopfHom j).hom.hom =
      Specs.IntegralCentralQuotient.cellMap (t.comp j) (fun i => (x i).comp j.toAlgHom)
        negative positive := by
  simp only [Specs.IntegralCentralQuotient.cellMap, MonObj.mul_comp, Category.assoc,
    coordinateRootProduct_comp, spectrumOfHopfHom_comp]
  rfl

private theorem coordinateFlat_of_flatSpectrum {k B : Type u} [CommRing k] [CommRing B]
    [HopfAlgebra k B] (h : Flat (HopfSpectrum k B).X.hom) : Module.Flat k B := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap k B))) at h
  exact (RingHom.flat_algebraMap_iff).mp (HasRingHomProperty.Spec_iff.mp h)

end QuotientIdentity

section QuotientOrder

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] ULift.module in
/-- The descended torus, root maps and ordered cell agree under the isomorphism
between two flat invariant algebras inside the same cover. -/
private theorem quotientCell_open_of_sameImage {E B C X M I : Type u}
    [CommRing E] [CommRing B] [CommRing C] [CommGroup X] [CommGroup M]
    [HopfAlgebra R.{u} E] [HopfAlgebra R.{u} B] [HopfAlgebra R.{u} C]
    [Module.Flat R.{u} C] [Module.Flat R.{u} E]
    (z : X →* M) (t : E →ₐc[R.{u}] MonoidAlgebra R.{u} X) (x : I → E →ₐ[R.{u}] Polynomial R.{u})
    (f : B →ₐc[R.{u}] E) (g : C →ₐc[R.{u}] E)
    (tB : B →ₐc[R.{u}] MonoidAlgebra R.{u} z.ker) (tC : C →ₐc[R.{u}] MonoidAlgebra R.{u} z.ker)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hImage : Set.range f = Set.range g)
    (hB : (MonoidAlgebra.mapDomainBialgHom R.{u} z.ker.subtype).comp tB = t.comp f)
    (hC : (MonoidAlgebra.mapDomainBialgHom R.{u} z.ker.subtype).comp tC = t.comp g)
    (negative positive : List I)
    (hOpen : IsOpenImmersion
      (Specs.IntegralCentralQuotient.cellMap tC (fun i => (x i).comp g.toAlgHom)
        negative positive).left) :
    IsOpenImmersion
      (Specs.IntegralCentralQuotient.cellMap tB (fun i => (x i).comp f.toAlgHom)
        negative positive).left := by
  obtain ⟨e, he⟩ := exists_bialgEquiv_of_sameImage f g hf hg (SetLike.coe_injective hImage)
  have ht : tC.comp e.toBialgHom = tB := by
    apply BialgHom.ext
    intro b
    apply torusRestriction_injective (K := R.{u}) z
    change ((MonoidAlgebra.mapDomainBialgHom R.{u} z.ker.subtype).comp tC) (e b) =
      ((MonoidAlgebra.mapDomainBialgHom R.{u} z.ker.subtype).comp tB) b
    rw [hC, hB]
    exact congrArg t (DFunLike.congr_fun he b)
  have hx : (fun i => ((x i).comp g.toAlgHom).comp e.toBialgHom.toAlgHom) =
      (fun i => (x i).comp f.toAlgHom) := by
    funext i
    apply AlgHom.ext
    intro b
    exact congrArg (x i) (DFunLike.congr_fun he b)
  have hCell := coordinateCell_comp e.toBialgHom tC (fun i => (x i).comp g.toAlgHom)
    negative positive
  rw [ht, hx] at hCell
  rw [← hCell, Over.comp_left]
  let q := (hopfSpec (CommRingCat.of R.{u})).mapIso (CommHopfAlgCat.isoMk e).op
  letI : IsIso (spectrumOfHopfHom e.toBialgHom).hom.hom.left :=
    ((Grp.forget _ ⋙ Over.forget _).mapIso q).isIso_hom
  letI := hOpen
  infer_instance

private theorem range_eq_subalgebra {B : Type u} [CommRing B] [Algebra R.{u} B]
    (S : Subalgebra R.{u} B)
    (f : S → B) (hf : ∀ b, f b = (b : B)) : Set.range f = S := by
  ext b
  constructor
  · rintro ⟨c, rfl⟩
    exact (hf c).symm ▸ c.property
  · intro hb
    exact ⟨⟨b, hb⟩, hf _⟩

end QuotientOrder

section MarkedQuotient

/-- The quotient of a marked affine cover, with its marked ordered cells. -/
private structure MarkedQuotient (D : BasedRootDatum.{u}) where
  algebra : CommHopfAlgCat.{u} R.{u}
  torus : algebra →ₐc[R.{u}] MonoidAlgebra R.{u} (torusKernel D).ker
  root : D.I → algebra →ₐ[R.{u}] Polynomial R.{u}
  torusSurjective : Function.Surjective torus
  smooth : Smooth (HopfSpectrum R.{u} algebra).X.hom
  connected : GeometricallyConnected (HopfSpectrum R.{u} algebra).X.hom
  reductiveFibres : ReductiveFibres (spectrumOfHopfHom torus)
  negative : List D.I
  positive : List D.I
  negativeEnumerates : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i}
  positiveEnumerates : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}
  openCell : ∀ (negative positive : List D.I),
    Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i} →
    Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i} →
    IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap torus root negative positive).left
  rankOne : D.I → RankOneMap R.{u} algebra
  rootSurjective : ∀ a, Function.Surjective (root a)
  conjugation : ∀ a, RootScalarAction torus (root a)
    (quotientCharacters D (Multiplicative.ofAdd (D.datum.root a)))
  rankOneCompatible : ∀ a, RankOneCompatibility torus (root a)
    (root (D.datum.reflectionPerm a a)) ((coverCoroot D a).comp (torusKernel D).ker.subtype)
    (rankOne a)
  line : AdditiveLine.{u}
  rootMap : D.I → (line.group ⟶ HopfSpectrum R.{u} algebra)
  rootMap_eq : ∀ a, (rootMap a).hom.hom = spectrumOfAlgHom (root a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1350000 in
attribute [-instance] ULift.module in
private theorem markedQuotient_exists
    (quotient : Specs.IntegralCentralQuotient.Statement.{u})
    (D : BasedRootDatum.{u})
    (t : A →ₐc[R.{u}] MonoidAlgebra R.{u} (Multiplicative (CoverCharacters D)))
    (x : D.I → A →ₐ[R.{u}] Polynomial R.{u}) (r : D.I → RankOneMap R.{u} A)
    (line : AdditiveLine.{u}) (x' : D.I → (line.group ⟶ HopfSpectrum R.{u} A))
    (hx' : ∀ a, (x' a).hom.hom = spectrumOfAlgHom (x a))
    (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i})
    (ht : Function.Surjective t)
    (hc : IsCentral ((MonoidAlgebra.mapDomainBialgHom R.{u} (torusKernel D)).comp t))
    (hs : Smooth (HopfSpectrum R.{u} A).X.hom)
    (hRed : ReductiveFibres (spectrumOfHopfHom t))
    (hcell : ∀ (negative positive : List D.I),
      Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i} →
      Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i} →
      IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap t x negative positive).left)
    (hroot : ∀ i, Function.Surjective (x i) ∧
      RootScalarAction t (x i) (Multiplicative.ofAdd (characterRestriction D (D.datum.root i))) ∧
      RankOneCompatibility t (x i) (x (D.datum.reflectionPerm i i)) (coverCoroot D i) (r i)) :
    Nonempty (MarkedQuotient D) := by
  letI := D.freeY
  letI := D.finiteY
  letI : Finite (KernelCharacters D) := characterRestriction_finiteQuotient D
  letI : Finite (Multiplicative (KernelCharacters D)) :=
    Finite.of_equiv (KernelCharacters D) Multiplicative.ofAdd
  letI : Module.Free ℤ (Additive (Multiplicative (CoverCharacters D))) :=
    inferInstanceAs (Module.Free ℤ (CoverCharacters D))
  letI : Module.Finite ℤ (Additive (Multiplicative (CoverCharacters D))) :=
    inferInstanceAs (Module.Finite ℤ (CoverCharacters D))
  let z := torusKernel D
  let π := (MonoidAlgebra.mapDomainBialgHom R.{u} z).comp t
  let B := ↥(invariants π)
  obtain ⟨hnd, hall⟩ := coverRoots_enumerated D hn hp
  obtain ⟨hB, j, t₀, hj, _, hflat, hfp, hred, _, _, ht₀, _, _, hroot₀⟩ :=
    quotient.2.2 z t x negative positive (fun i => D.datum.reflectionPerm i i)
      (fun i => Multiplicative.ofAdd (characterRestriction D (D.datum.root i))) (coverCoroot D) r
      (torusKernel_surjective D) ht hc hs hRed hnd hall (hcell negative positive hn hp) hroot
  letI : Algebra R.{u} B := hB.toHopfAlgebraStruct.toBialgebra.toAlgebra
  letI : HopfAlgebra R.{u} B := hB
  letI : Flat (HopfSpectrum R.{u} B).X.hom := hflat
  letI : LocallyOfFinitePresentation (HopfSpectrum R.{u} B).X.hom := hfp
  obtain ⟨hs₀, hc₀⟩ := smoothConnectedOfGeometricFibres _ hred
  let x₀ (a : D.I) := (x a).comp j.toAlgHom
  have hsurj : Function.Surjective t₀ :=
    quotientTorusRestriction_surjective z t ht j t₀ (fun b hb => ⟨⟨b, hb⟩, hj _⟩) ht₀
  have marks (a : D.I) :
      Function.Surjective (x₀ a) ∧
      RootScalarAction t₀ (x₀ a) (quotientCharacters D (Multiplicative.ofAdd (D.datum.root a))) ∧
      ∃ q : RankOneMap R.{u} B,
        RankOneCompatibility t₀ (x₀ a) (x₀ (D.datum.reflectionPerm a a))
          ((coverCoroot D a).comp z.ker.subtype) q := by
    obtain ⟨hx, ha, hscalar, q, _, hr⟩ := hroot₀ a
    have ha' : (⟨_, ha⟩ : z.ker) =
        quotientCharacters D (Multiplicative.ofAdd (D.datum.root a)) :=
      Subtype.ext rfl
    exact ⟨hx, ha' ▸ hscalar, q, hr⟩
  choose r₀ hr₀ using fun a => (marks a).2.2
  have allCells (negative' positive' : List D.I)
      (hn' : Specs.OrderedRootProducts.Enumerates negative' {i | ¬ D.base.IsPos i})
      (hp' : Specs.OrderedRootProducts.Enumerates positive' {i | D.base.IsPos i}) :
      IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap t₀ x₀ negative' positive').left := by
    obtain ⟨hnd', hall'⟩ := coverRoots_enumerated D hn' hp'
    obtain ⟨hB', j', t₀', hj', _, hflat', _, _, _, _, ht₀', hc', _, _⟩ :=
      quotient.2.2 z t x negative' positive' (fun i => D.datum.reflectionPerm i i)
        (fun i => Multiplicative.ofAdd (characterRestriction D (D.datum.root i))) (coverCoroot D) r
        (torusKernel_surjective D) ht hc hs hRed hnd' hall' (hcell negative' positive' hn' hp') hroot
    have inj {f : B → A} (h : ∀ b, f b = (b : A)) : Function.Injective f :=
      fun b c eq => Subtype.ext ((h b).symm.trans (eq.trans (h c)))
    have hranges : Set.range j = Set.range j' :=
      (range_eq_subalgebra (invariants π) j hj).trans (range_eq_subalgebra (invariants π) j' hj').symm
    letI : Smooth (HopfSpectrum R.{u} A).X.hom := hs
    letI : Module.Flat R.{u} A := coordinateFlat_of_flatSpectrum
      (inferInstance : Flat (HopfSpectrum R.{u} A).X.hom)
    have flatB' := @coordinateFlat_of_flatSpectrum R.{u} B _ _ hB' hflat'
    exact @quotientCell_open_of_sameImage A B B _ _ D.I _ _ _ _ _
      _ hB hB' flatB' inferInstance z t x j j' t₀ t₀' (inj hj) (inj hj') hranges
      ht₀ ht₀' negative' positive' hc'
  refine ⟨⟨CommHopfAlgCat.of R.{u} B, t₀, x₀, hsurj, hs₀, hc₀, hred,
    negative, positive, hn, hp, allCells, r₀, fun a => (marks a).1, fun a => (marks a).2.1, hr₀,
    line, (fun a => x' a ≫ spectrumOfHopfHom j), fun a => ?_⟩⟩
  change (x' a).hom.hom ≫ (spectrumOfHopfHom j).hom.hom = spectrumOfAlgHom (x₀ a)
  rw [hx']
  exact (spectrumOfAlgHom_comp j.toAlgHom (x a)).symm

end MarkedQuotient

private theorem rootOrderings_exist (D : BasedRootDatum.{u}) :
    ∃ negative positive : List D.I,
      Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i} ∧
      Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i} := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  let negative := Finset.univ.filter (fun i => ¬ D.base.IsPos i)
  let positive := Finset.univ.filter (fun i => D.base.IsPos i)
  refine ⟨negative.toList, positive.toList, ⟨negative.nodup_toList, ?_⟩,
    ⟨positive.nodup_toList, ?_⟩⟩
  · intro i
    simp [negative]
  · intro i
    simp [positive]

private theorem derivedRootOrderings (D : BasedRootDatum.{u}) (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}) :
    Specs.OrderedRootProducts.Enumerates negative {i | ¬ (derivedDatum D).base.IsPos i} ∧
      Specs.OrderedRootProducts.Enumerates positive {i | (derivedDatum D).base.IsPos i} := by
  have h (i : D.I) : (derivedDatum D).base.IsPos i ↔ D.base.IsPos i := by
    change 0 < (derivedBase D).height i ↔ 0 < D.base.height i
    rw [derivedBase_height]
  exact ⟨⟨hn.1, fun i => (hn.2 i).trans (not_congr (h i).symm)⟩,
    ⟨hp.1, fun i => (hp.2 i).trans (h i).symm⟩⟩

private theorem coverRoot_eq_left (D : BasedRootDatum.{u}) (a : D.I) :
    coverProductCharacters D (Multiplicative.ofAdd ((derivedDatum D).datum.root a), 1) =
      Multiplicative.ofAdd (characterRestriction D (D.datum.root a)) := by
  apply (coverProductCharacters D).symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact (congrArg (fun y : (derivedDatum D).X × Dual ℤ (CentralLattice D) =>
    (Multiplicative.ofAdd y.1, Multiplicative.ofAdd y.2)) (coverCharactersEquiv_root D a)).symm

section QuotientMaps

private def quotientMarkedTorus {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) :
    splitTorus D ⟶ HopfSpectrum R.{u} Q.algebra :=
  (quotientTorusIso D).inv ≫ spectrumOfHopfHom Q.torus

set_option backward.isDefEq.respectTransparency false in
private theorem quotientMarkedTorus_closed {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) :
    IsClosedImmersion (quotientMarkedTorus Q).hom.hom.left := by
  let e := (Grp.forget IntegralScheme.{u} ⋙ Over.forget _).mapIso (quotientTorusIso D)
  let i := CommRingCat.ofHom Q.torus.toAlgHom.toRingHom
  letI : IsClosedImmersion (Spec.map i) := IsClosedImmersion.spec_of_surjective i Q.torusSurjective
  change IsClosedImmersion (e.inv ≫ Spec.map i)
  infer_instance

private theorem quotientRoot_closed {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) (a : D.I) :
    IsClosedImmersion (spectrumOfAlgHom (Q.root a)).left :=
  IsClosedImmersion.spec_of_surjective _ (Q.rootSurjective a)

set_option backward.isDefEq.respectTransparency false in
private theorem quotientRankOne_diagonal {D : BasedRootDatum.{u}} (Q : MarkedQuotient D)
    (a : D.I) (S : IntegralAlgebra.{u}) (s : Sˣ) :
    (rankOneNatural (Q.rankOne a)).app S (Specs.IntegralRootRelations.diagonal s) =
      torusPoint D S (cocharacter D (D.datum.coroot a) S s) ≫
        (quotientMarkedTorus Q).hom.hom := by
  rw [rankOneNatural_apply_diagonal (Q.rankOne a) S Q.torus
    ((coverCoroot D a).comp (torusKernel D).ker.subtype) ((Q.rankOneCompatible a).2 S) s,
    quotientTorus_cocharacter]
  change (_ ≫ (quotientTorusIso D).inv.hom.hom) ≫ (spectrumOfHopfHom Q.torus).hom.hom =
    _ ≫ ((quotientTorusIso D).inv.hom.hom ≫ (spectrumOfHopfHom Q.torus).hom.hom)
  exact Category.assoc _ _ _

end QuotientMaps

section SplitTorusIntegral

private theorem splitGroupAlgebra_domain {K X : Type u} [CommRing K] [IsDomain K]
    [CommGroup X] [Module.Free ℤ (Additive X)] [Module.Finite ℤ (Additive X)] :
    IsDomain (MonoidAlgebra K X) := by
  let b := Module.finBasis ℤ (Additive X)
  let e : X ≃* Multiplicative (Fin (Module.finrank ℤ (Additive X)) → ℤ) :=
    b.equivFun.toAddEquiv.toMultiplicative
  let f := MonoidAlgebra.domCongr K K e
  exact f.toRingEquiv.injective.isDomain f.toRingEquiv

end SplitTorusIntegral


section RankOneWord

open Specs.IntegralRootRelations (upper lower diagonal)

private def elementaryWord {K : Type u} [CommRing K] (s : Kˣ) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  upper (s : K) * lower (-(↑s⁻¹ : K)) * upper (s : K)

/-- A matrix identity over arbitrary test rings, including characteristic two. -/
private theorem elementaryWord_diagonal {K : Type u} [CommRing K] (s : Kˣ) :
    elementaryWord s = diagonal s * elementaryWord (1 : Kˣ) := by
  apply Subtype.ext
  change (!![1, (s : K); 0, 1] * !![1, 0; -(↑s⁻¹ : K), 1] * !![1, (s : K); 0, 1] : Matrix (Fin 2) (Fin 2) K) =
    !![(s : K), 0; 0, (↑s⁻¹ : K)] * (!![(1 : K), 1; 0, 1] * !![(1 : K), 0; -1, 1] * !![(1 : K), 1; 0, 1])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem rankOneWord_diagonal {K G : Type u} [CommRing K] [Group G]
    (r : Matrix.SpecialLinearGroup (Fin 2) K →* G) (s : Kˣ) :
    r (elementaryWord s) * (r (elementaryWord (1 : Kˣ)))⁻¹ = r (diagonal s) := by
  rw [elementaryWord_diagonal, map_mul, mul_inv_cancel_right]

end RankOneWord

section RankOneReflection

open Specs.IntegralRootRelations (upper lower diagonal)

private theorem elementaryWord_conjugation {K G : Type u} [CommRing K] [Group G]
    (r : Matrix.SpecialLinearGroup (Fin 2) K →* G) (t : G) (s : Kˣ)
    (hUpper : ∀ z : K, t * r (upper z) * t⁻¹ = r (upper ((s : K) * z)))
    (hLower : ∀ z : K, t * r (lower z) * t⁻¹ = r (lower ((↑s⁻¹ : K) * z))) :
    t * r (elementaryWord (1 : Kˣ)) * t⁻¹ = r (elementaryWord s) := by
  have hU : (MulAut.conj t) (r (upper (1 : K))) = r (upper (s : K)) := by
    simpa only [MulAut.conj_apply, mul_one] using hUpper 1
  have hL : (MulAut.conj t) (r (lower (-1 : K))) = r (lower (-(↑s⁻¹ : K))) := by
    simpa only [MulAut.conj_apply, mul_neg_one] using hLower (-1)
  change (MulAut.conj t) (r (elementaryWord (1 : Kˣ))) = _
  simp only [elementaryWord, inv_one, Units.val_one, map_mul, hU, hL]

/-- The Weyl word transforms torus points by the reflection with the marked coroot. -/
private theorem rankOneWord_reflection {K G : Type u} [CommRing K] [Group G]
    (r : Matrix.SpecialLinearGroup (Fin 2) K →* G) (t : G) (s : Kˣ)
    (hUpper : ∀ z : K, t * r (upper z) * t⁻¹ = r (upper ((s : K) * z)))
    (hLower : ∀ z : K, t * r (lower z) * t⁻¹ = r (lower ((↑s⁻¹ : K) * z)))
    (hComm : Commute t (r (diagonal s))) :
    r (elementaryWord (1 : Kˣ)) * t * (r (elementaryWord (1 : Kˣ)))⁻¹ =
      t * (r (diagonal s))⁻¹ := by
  let w := r (elementaryWord (1 : Kˣ))
  let d := r (diagonal s)
  have h : t * w * t⁻¹ = d * w := by
    change t * r (elementaryWord (1 : Kˣ)) * t⁻¹ = _
    rw [elementaryWord_conjugation r t s hUpper hLower, elementaryWord_diagonal s, map_mul]
  have h' : t * w = (d * w) * t := by
    calc
      t * w = (t * w * t⁻¹) * t := by simp [mul_assoc]
      _ = (d * w) * t := by rw [h]
  calc
    w * t * w⁻¹ = d⁻¹ * ((d * w) * t) * w⁻¹ := by simp [mul_assoc]
    _ = d⁻¹ * (t * w) * w⁻¹ := by rw [← h']
    _ = d⁻¹ * t := by simp [mul_assoc]
    _ = t * d⁻¹ := hComm.inv_right.eq.symm

end RankOneReflection


section TorusFibre

open Coalgebra Algebra.TensorProduct

attribute [-instance] ULift.module in
private def groupAlgebraScalarIso {K : Type u} [Field K] [Algebra R.{u} K]
    (M : Type u) [CommGroup M] :
    (K ⊗[R.{u}] MonoidAlgebra R.{u} M) ≃ₐc[K] MonoidAlgebra K M := by
  let f := MonoidAlgebra.scalarTensorEquiv R.{u} K (M := M)
  have hf (m : M) : f ((1 : K) ⊗ₜ[R.{u}] MonoidAlgebra.single m 1) =
      MonoidAlgebra.single m 1 := by
    apply f.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    exact (MonoidAlgebra.scalarTensorEquiv_symm_single (R := R.{u}) (A := K) m 1).symm
  refine BialgEquiv.ofAlgEquiv f ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    apply (MonoidAlgebra.lift R.{u} K M).symm.injective
    apply MonoidHom.ext
    intro m
    simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      includeRight_apply, Bialgebra.counitAlgHom_apply, AlgEquiv.toAlgHom_apply,
      TensorProduct.counit_tmul, MonoidAlgebra.counit_single, hf, CommSemiring.counit_apply]
    rw [Algebra.smul_def, map_one, one_mul]

  · apply Algebra.TensorProduct.ext_ring
    apply (MonoidAlgebra.lift R.{u} _ M).symm.injective
    apply MonoidHom.ext
    intro m
    simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      includeRight_apply, Bialgebra.comulAlgHom_apply, AlgEquiv.toAlgHom_apply,
      hf, TensorProduct.comul_tmul, CommSemiring.comul_apply, MonoidAlgebra.comul_single,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def hopfFibreIso {L C K : Type u} [CommRing L] [CommRing C] [HopfAlgebra L C]
    [Field K] [Algebra L K] :
    (fibreGroup K).obj (HopfSpectrum L C) ≅ HopfSpectrum K (K ⊗[L] C) := by
  let a := (Spec (CommRingCat.of C) ↘ Spec (CommRingCat.of L))
  let f := Spec.map (CommRingCat.ofHom (algebraMap L K))
  let e := pullbackSymmetry a f ≪≫ pullbackSpecIso' L K C
  have w : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[L] C))) =
      pullback.snd a f := by
    change (pullbackSymmetry a f).hom ≫ (pullbackSpecIso L K C).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[L] C))) = _
    rw [pullbackSpecIso_hom_fst']
    exact pullbackSymmetry_hom_comp_fst _ _
  let e' : ((fibreGroup K).obj (HopfSpectrum L C)).X ≅ (HopfSpectrum K (K ⊗[L] C)).X :=
    Over.isoMk e w
  haveI : IsMonHom e'.hom :=
    AlgebraicGeometry.instIsMonHomOverSchemeSpecOfAsOverHomTransPullbackSymmetryOverInferInstanceOverClassPullbackSpecIso'
      (R := L) (S := K) (T := C)
  exact Grp.mkIso' e'

private def torusFibreIso {K : Type u} [Field K] [Algebra R.{u} K]
    (M : Type u) [CommGroup M] :
    (fibreGroup K).obj (torusOf M) ≅ HopfSpectrum K (MonoidAlgebra K M) :=
  hopfFibreIso (L := R.{u}) (K := K) ≪≫ (hopfSpec (CommRingCat.of K)).mapIso
    (CommHopfAlgCat.isoMk (groupAlgebraScalarIso (K := K) M)).symm.op

end TorusFibre


section CoverCell

private def orderedCell {G T : IntegralGroup.{u}} {I : Type u} (L : AdditiveLine.{u})
    (t : T ⟶ G) (x : I → (L.group ⟶ G)) (negative positive : List I) :
    product (fun _ : I => L.group.X) negative ⊗
      (T.X ⊗ product (fun _ : I => L.group.X) positive) ⟶ G.X :=
  (fst _ _ ≫ Specs.IntegralSemisimpleModel.rootProduct L x negative) *
    (snd _ _ ≫ ((fst _ _ ≫ t.hom.hom) *
      (snd _ _ ≫ Specs.IntegralSemisimpleModel.rootProduct L x positive)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem markedCellCoordinates_spec {G : IntegralGroup.{u}} {L : AdditiveLine.{u}}
    {X I : Type u} [CommGroup X] (e : HopfSpectrum R.{u} A ≅ G)
    (t : torusOf X ⟶ G) (x : I → (L.group ⟶ G)) (negative positive : List I) :
    Specs.IntegralCentralQuotient.cellMap (markedTorusCoordinates e t)
        (fun a => markedRootCoordinates e (x a)) negative positive =
      (cellDomainIso (torusOf X) L negative positive).hom ≫
        orderedCell L t x negative positive ≫ e.inv.hom.hom := by
  simp only [Specs.IntegralCentralQuotient.cellMap, orderedCell, cellDomainIso,
    markedRootProduct_spec, markedTorusCoordinates_spec, MonObj.mul_comp, MonObj.comp_mul,
    MonoidalCategory.tensorIso_hom, Iso.refl_hom, CartesianMonoidalCategory.tensorHom_fst_assoc,
    CartesianMonoidalCategory.tensorHom_snd_assoc, Category.id_comp, Category.assoc]
  rfl

/-- Move the central torus outside the ordered cell. -/
private def cellProductIso (N T P C : IntegralScheme.{u}) :
    N ⊗ ((T ⊗ C) ⊗ P) ≅ (N ⊗ (T ⊗ P)) ⊗ C where
  hom := lift (lift (fst _ _)
      (lift (snd _ _ ≫ fst _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)))
    (snd _ _ ≫ fst _ _ ≫ snd _ _)
  inv := lift (fst _ _ ≫ fst _ _)
    (lift (lift (fst _ _ ≫ snd _ _ ≫ fst _ _) (snd _ _))
      (fst _ _ ≫ snd _ _ ≫ snd _ _))
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext
      · apply CartesianMonoidalCategory.hom_ext <;> simp
      · simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · apply CartesianMonoidalCategory.hom_ext <;> simp
    · simp

set_option backward.isDefEq.respectTransparency false in
private theorem coverRootProduct_fst {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (l : List D.I) :
    Specs.IntegralSemisimpleModel.rootProduct H.line (coverRootMap H) l ≫
      fst H.group.X (centralTorus D).X =
      Specs.IntegralSemisimpleModel.rootProduct H.line H.root l := by
  induction l with
  | nil => exact MonObj.one_comp _
  | cons a l ih =>
    simp only [Specs.IntegralSemisimpleModel.rootProduct, MonObj.mul_comp, Category.assoc, ih]
    congr 2
    exact lift_fst _ _

set_option backward.isDefEq.respectTransparency false in
private theorem coverRootProduct_snd {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (l : List D.I) :
    Specs.IntegralSemisimpleModel.rootProduct H.line (coverRootMap H) l ≫
      snd H.group.X (centralTorus D).X = 1 := by
  induction l with
  | nil => exact MonObj.one_comp _
  | cons a l ih =>
    simp only [Specs.IntegralSemisimpleModel.rootProduct, MonObj.mul_comp, Category.assoc, ih,
      MonObj.comp_one, mul_one]
    have e : (coverRootMap H a).hom.hom ≫ snd H.group.X (centralTorus D).X = 1 :=
      lift_snd _ _
    rw [e, MonObj.comp_one]

private def coverCellIso {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (negative positive : List D.I) :
    product (fun _ : D.I => H.line.group.X) negative ⊗
      ((torusOf (Multiplicative (CoverCharacters D))).X ⊗
        product (fun _ : D.I => H.line.group.X) positive) ≅
    (product (fun _ : D.I => H.line.group.X) negative ⊗
      ((splitTorus (derivedDatum D)).X ⊗ product (fun _ : D.I => H.line.group.X) positive)) ⊗
        (centralTorus D).X :=
  MonoidalCategory.tensorIso (Iso.refl _)
    (MonoidalCategory.tensorIso ((Grp.forget _).mapIso (coverTorusProductIso D)) (Iso.refl _)) ≪≫
    cellProductIso _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem coverTorus_fst {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    (coverTorus H).hom.hom ≫ fst H.group.X (centralTorus D).X =
      (coverTorusProductIso D).hom.hom.hom ≫ fst _ _ ≫ H.torus.hom.hom := by
  change ((coverTorusProductIso D).hom.hom.hom ≫ (H.torus.hom.hom ⊗ₘ 𝟙 _)) ≫ _ = _
  rw [Category.assoc, tensorHom_fst]

set_option backward.isDefEq.respectTransparency false in
private theorem coverTorus_snd {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    (coverTorus H).hom.hom ≫ snd H.group.X (centralTorus D).X =
      (coverTorusProductIso D).hom.hom.hom ≫ snd _ _ := by
  change ((coverTorusProductIso D).hom.hom.hom ≫ (H.torus.hom.hom ⊗ₘ 𝟙 _)) ≫ _ = _
  rw [Category.assoc, tensorHom_snd, Category.comp_id]


private def cellWord {N T P G : IntegralScheme.{u}} [MonObj G]
    (n : N ⟶ G) (t : T ⟶ G) (p : P ⟶ G) : N ⊗ (T ⊗ P) ⟶ G :=
  (fst _ _ ≫ n) * ((snd _ _ ≫ fst _ _ ≫ t) * (snd _ _ ≫ snd _ _ ≫ p))

private theorem cellWord_comp {N T P G H : IntegralScheme.{u}} [MonObj G] [MonObj H]
    (n : N ⟶ G) (t : T ⟶ G) (p : P ⟶ G) (j : G ⟶ H) [IsMonHom j] :
    cellWord n t p ≫ j = cellWord (n ≫ j) (t ≫ j) (p ≫ j) := by
  simp only [cellWord, MonObj.mul_comp, Category.assoc]

private theorem shiftCellWord {N S T P C G : IntegralScheme.{u}} [MonObj G]
    (f : S ⟶ T ⊗ C) (n : N ⟶ G) (t : T ⟶ G) (p : P ⟶ G) :
    ((𝟙 N) ⊗ₘ (f ⊗ₘ 𝟙 P)) ≫ (cellProductIso N T P C).hom ≫
        (cellWord n t p ⊗ₘ 𝟙 C) =
      lift (cellWord n (f ≫ fst T C ≫ t) p)
        (snd N (S ⊗ P) ≫ fst S P ≫ f ≫ snd T C) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, tensorHom_fst_assoc, cellProductIso, lift_fst_assoc, lift_fst,
        lift_snd_assoc, cellWord, MonObj.comp_mul, tensorHom_snd_assoc, Category.id_comp]
  · simp only [Category.assoc, tensorHom_snd, Category.comp_id, cellProductIso, lift_snd,
      tensorHom_snd_assoc, tensorHom_fst_assoc]

private theorem orderedCell_eq_cellWord {G T : IntegralGroup.{u}} {I : Type u} (L : AdditiveLine.{u})
    (t : T ⟶ G) (x : I → (L.group ⟶ G)) (negative positive : List I) :
    orderedCell L t x negative positive =
      cellWord (Specs.IntegralSemisimpleModel.rootProduct L x negative) t.hom.hom
        (Specs.IntegralSemisimpleModel.rootProduct L x positive) := by
  simp only [orderedCell, cellWord, MonObj.comp_mul]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem coverCell_eq {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (negative positive : List D.I) :
    orderedCell H.line (coverTorus H) (coverRootMap H) negative positive =
      (coverCellIso H negative positive).hom ≫
        (Specs.IntegralSemisimpleModel.cellMap H.line H.torus H.root negative positive ⊗ₘ
          𝟙 (centralTorus D).X) := by
  have hShift :
      (coverCellIso H negative positive).hom ≫
        (Specs.IntegralSemisimpleModel.cellMap H.line H.torus H.root negative positive ⊗ₘ
          𝟙 (centralTorus D).X) =
      lift (cellWord (Specs.IntegralSemisimpleModel.rootProduct H.line H.root negative)
        ((coverTorusProductIso D).hom.hom.hom ≫ fst _ _ ≫ H.torus.hom.hom)
        (Specs.IntegralSemisimpleModel.rootProduct H.line H.root positive))
        (snd _ _ ≫ fst _ _ ≫ (coverTorusProductIso D).hom.hom.hom ≫ snd _ _) := by
    change (((𝟙 _) ⊗ₘ ((coverTorusProductIso D).hom.hom.hom ⊗ₘ 𝟙 _)) ≫
      (cellProductIso _ _ _ _).hom) ≫
      (orderedCell H.line H.torus H.root negative positive ⊗ₘ 𝟙 _) = _
    rw [Category.assoc, orderedCell_eq_cellWord]
    exact shiftCellWord _ _ _ _
  rw [orderedCell_eq_cellWord, hShift]
  apply CartesianMonoidalCategory.hom_ext
  · rw [cellWord_comp, coverRootProduct_fst, coverTorus_fst, coverRootProduct_fst, lift_fst]
  · rw [cellWord_comp, coverRootProduct_snd, coverTorus_snd, coverRootProduct_snd, lift_snd]
    simp only [cellWord, MonObj.comp_one, one_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem coverCell_open {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}) :
    IsOpenImmersion (orderedCell H.line (coverTorus H) (coverRootMap H) negative positive).left := by
  obtain ⟨hn', hp'⟩ := derivedRootOrderings D negative positive hn hp
  letI := H.openCell negative positive hn' hp'
  rw [coverCell_eq, Over.comp_left]
  haveI : IsOpenImmersion
      (Specs.IntegralSemisimpleModel.cellMap H.line H.torus H.root negative positive ⊗ₘ
        𝟙 (centralTorus D).X).left := by
    rw [Over.tensorHom_left]
    infer_instance
  infer_instance

end CoverCell


section CellRestriction

open Algebra.TensorProduct

private theorem lineProduct_affine {I : Type u} (l : List I) :
    IsAffine (lineProduct R.{u} l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of R.{u})))
  | cons i l ih =>
    letI : IsAffine (lineProduct R.{u} l).left := ih
    letI : IsAffine additiveScheme.{u}.left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial R.{u}))))
    change IsAffine (pullback additiveScheme.{u}.hom (lineProduct R.{u} l).hom)
    infer_instance

private def lineProductPoint {I : Type u} (S : IntegralAlgebra.{u}) :
    (l : List I) → integralSpec.obj (op S) ⟶ lineProduct R.{u} l
  | [] => toUnit _
  | _ :: l => lift (additivePoint S 0) (lineProductPoint S l)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
attribute [-instance] ULift.module in
/-- If the affine ambient model is integral, its nonempty ordered open cell
detects centrality, including for a nonreduced diagonalizable kernel. -/
private theorem central_of_openRootCell {I X M : Type u} [CommGroup X] [CommGroup M]
    [_root_.IsReduced A] [IrreducibleSpace (HopfSpectrum R.{u} A).X.left]
    (z : X →* M) (t : A →ₐc[R.{u}] MonoidAlgebra R.{u} X) (x : I → A →ₐ[R.{u}] Polynomial R.{u})
    (α : I → X) (halpha : ∀ i, z (α i) = 1)
    (hscalar : ∀ i, RootScalarAction t (x i) (α i))
    (negative positive : List I)
    (hc : IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap t x negative positive).left) :
    IsCentral ((MonoidAlgebra.mapDomainBialgHom R.{u} z).comp t) := by
  let T := (HopfSpectrum R.{u} (MonoidAlgebra R.{u} X)).X
  let Ω := lineProduct R.{u} negative ⊗ (T ⊗ lineProduct R.{u} positive)
  let c : Ω ⟶ (HopfSpectrum R.{u} A).X := Specs.IntegralCentralQuotient.cellMap t x negative positive
  letI : IsAffine (lineProduct R.{u} negative).left := lineProduct_affine negative
  letI : IsAffine (lineProduct R.{u} positive).left := lineProduct_affine positive
  letI : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra R.{u} X))))
  have hΩ : IsAffine Ω.left := by
    change IsAffine (pullback (lineProduct R.{u} negative).hom (T ⊗ lineProduct R.{u} positive).hom)
    letI : IsAffine (T ⊗ lineProduct R.{u} positive).left :=
      inferInstanceAs (IsAffine (pullback T.hom (lineProduct R.{u} positive).hom))
    infer_instance
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr hΩ
  let f' := (coordinatePoints B.unop).symm (e.hom ≫ c)
  let f : A →ₐ[R.{u}] B.unop := f'.ofConv
  have hf : coordinatePoints B.unop f' = e.hom ≫ c :=
    (coordinatePoints B.unop).apply_symm_apply _
  let S₀ := CommAlgCat.of R.{u} R.{u}
  let p₀ : integralSpec.obj (op S₀) ⟶ Ω :=
    lift (lineProductPoint S₀ negative) (lift (1 : integralSpec.obj (op S₀) ⟶ T)
      (lineProductPoint S₀ positive))
  have hΩne : Nonempty Ω.left :=
    ⟨p₀.left (Classical.choice (inferInstance : Nonempty (PrimeSpectrum R.{u})))⟩
  letI : IsOpenImmersion c.left := hc
  have hd : DenseRange c.left := by
    exact c.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty c.left)
  have hfe : DenseRange (PrimeSpectrum.comap f.toRingHom) := by
    change DenseRange (coordinatePoints B.unop f').left
    rw [hf, Over.comp_left]
    have hs : Function.Surjective e.hom.left :=
      ((Over.forget _).mapIso e).hom.homeomorph.surjective
    exact hd.comp (hs.denseRange) c.left.continuous
  have hfi : Function.Injective f := by
    have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f.toRingHom).mp hfe
    rw [nilradical_eq_zero] at h
    exact (RingHom.injective_iff_ker_eq_bot _).mpr (le_bot_iff.mp h)
  let U : Type u := B.unop
  letI : CommRing U := B.unop.commRing
  letI : Algebra R.{u} U := B.unop.algebra
  let S := CommAlgCat.of R.{u} (U ⊗[R.{u}] MonoidAlgebra R.{u} M)
  let v : MonoidAlgebra R.{u} M →ₐ[R.{u}] S := includeRight
  let l : B.unop ⟶ S := CommAlgCat.ofHom includeLeft
  let p : integralSpec.obj (op S) ⟶ Ω := integralSpec.map l.op ≫ e.hom
  have hp : coordinatePoints S (toConv (l.hom.comp f)) = p ≫ c := by
    have hh := coordinatePoints_naturality l f'
    change coordinatePoints S (toConv (l.hom.comp f)) =
      integralSpec.map l.op ≫ coordinatePoints B.unop f' at hh
    rw [hh, hf]
    exact (Category.assoc _ _ _).symm
  apply central_of_restriction _ f hfi
  apply (coordinatePoints S).injective
  simp only [map_mul]
  change coordinatePoints S (toConv (l.hom.comp f)) *
      coordinatePoints S (toConv (v.comp _)) =
    coordinatePoints S (toConv (v.comp _)) *
      coordinatePoints S (toConv (l.hom.comp f))
  rw [hp]
  exact (cellPoint_commutes z t x α halpha hscalar negative positive S v p).symm.eq

end CellRestriction



section CoverIntegrality

open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

local instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
  ⟨fun e h => by
    letI := h
    exact IsIntegral.of_isIso e.hom⟩

set_option backward.isDefEq.respectTransparency false in
private theorem integralGroup_geometricallyIntegral (G : IntegralGroup.{u})
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [GeometricallyConnected G.X.hom] :
    GeometricallyIntegral G.X.hom := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let f := Spec.map (CommRingCat.ofHom (algebraMap R.{u} K))
  let G' := (fibreGroup K).obj G
  letI : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom f))
  letI : QuasiCompact G'.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom f))
  letI : GeometricallyConnected G'.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom f))
  letI : IrreducibleSpace G'.X.left := irreducible_of_geometricallyConnected G'
  letI : IsReduced G'.X.left := isReduced_of_smooth_over_field G'.X.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced G'.X.left

set_option backward.isDefEq.respectTransparency false in
private theorem centralTorus_geometricallyIntegral (D : BasedRootDatum.{u}) :
    GeometricallyIntegral (centralTorus D).X.hom := by
  letI := D.freeY
  letI := D.finiteY
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let M := Multiplicative (Dual ℤ (CentralLattice D))
  letI : Module.Free ℤ (Additive M) := inferInstanceAs
    (Module.Free ℤ (Dual ℤ (CentralLattice D)))
  letI : Module.Finite ℤ (Additive M) := inferInstanceAs
    (Module.Finite ℤ (Dual ℤ (CentralLattice D)))
  letI : IsDomain (MonoidAlgebra K M) := splitGroupAlgebra_domain
  let e := (Grp.forget _ ⋙ Over.forget _).mapIso (torusFibreIso (K := K) M)
  exact ObjectProperty.prop_of_iso (P := IsIntegral) e.symm
    (inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MonoidAlgebra K M)))))

set_option backward.isDefEq.respectTransparency false in
private theorem coverGroup_integral {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    IsIntegral (coverGroup H).X.left := by
  letI : IsDomain R.{u} :=
    ULift.ringEquiv.injective.isDomain (ULift.ringEquiv : R.{u} ≃+* ℤ)
  letI : IsNoetherianRing R.{u} := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : IsIntegral Base.{u} := inferInstanceAs (IsIntegral (Spec (CommRingCat.of R.{u})))
  letI : IsLocallyNoetherian Base.{u} :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R.{u})))
  letI : Smooth H.group.X.hom := H.smooth
  letI : QuasiCompact H.group.X.hom := H.quasiCompact
  letI : GeometricallyConnected H.group.X.hom := H.connected
  letI : GeometricallyIntegral H.group.X.hom := integralGroup_geometricallyIntegral H.group
  letI : IsIntegral H.group.X.left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian H.group.X.hom
  letI : IsLocallyNoetherian H.group.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian H.group.X.hom
  letI : Smooth (centralTorus D).X.hom := centralTorus_smooth D
  letI : GeometricallyIntegral (centralTorus D).X.hom := centralTorus_geometricallyIntegral D
  change IsIntegral (pullback H.group.X.hom (centralTorus D).X.hom)
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
    (pullback.fst H.group.X.hom (centralTorus D).X.hom)

end CoverIntegrality

section CoverCoordinates

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1250000

private def integralPointMap {G H : IntegralGroup.{u}} (f : G ⟶ H) (S : IntegralAlgebra.{u}) :
    IntegralPoints G S →* IntegralPoints H S :=
  ((yonedaGrp.map f).app (op (integralSpec.obj (op S)))).hom

private theorem integralPointMap_apply {G H : IntegralGroup.{u}} (f : G ⟶ H)
    (S : IntegralAlgebra.{u}) (p : IntegralPoints G S) :
    integralPointMap f S p = p ≫ f.hom.hom := rfl

private def coverInclusion {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    H.group ⟶ coverGroup H :=
  lift (𝟙 H.group) (0 : H.group ⟶ centralTorus D)

private theorem coverRootMap_eq {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) (a : D.I) :
    coverRootMap H a = H.root a ≫ coverInclusion H := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [coverRootMap, coverInclusion]

private def coverRankOneNatural {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (e : HopfSpectrum R.{u} A ≅ coverGroup H) (a : D.I) :
    rankOnePoints.{u} ⟶ integralPointFunctor (HopfSpectrum R.{u} A) :=
  H.rankOne a ≫ Functor.whiskerLeft integralSpec.rightOp (yonedaGrp.map (coverInclusion H ≫ e.inv))

private theorem coverRankOneNatural_apply {D : BasedRootDatum.{u}}
    (H : Model (derivedDatum D)) (e : HopfSpectrum R.{u} A ≅ coverGroup H) (a : D.I)
    (S : IntegralAlgebra.{u}) (v : Matrix.SpecialLinearGroup (Fin 2) S) :
    (coverRankOneNatural H e a).app S v =
      (H.rankOne a).app S v ≫ (coverInclusion H).hom.hom ≫ e.inv.hom.hom := rfl

private abbrev DerivedCharacters (D : BasedRootDatum.{u}) := Multiplicative (derivedDatum D).X

private abbrev CentralCharacters (D : BasedRootDatum.{u}) :=
  Multiplicative (Dual ℤ (CentralLattice D))

private def coverCharactersLeft (D : BasedRootDatum.{u}) :
    DerivedCharacters D →* Multiplicative (CoverCharacters D) :=
  (coverProductCharacters D).toMonoidHom.comp (MonoidHom.inl _ _)

private def coverCharactersRight (D : BasedRootDatum.{u}) :
    CentralCharacters D →* Multiplicative (CoverCharacters D) :=
  (coverProductCharacters D).toMonoidHom.comp (MonoidHom.inr _ _)

private theorem coverCharactersLeft_root (D : BasedRootDatum.{u}) (a : D.I) :
    coverCharactersLeft D (Multiplicative.ofAdd ((derivedDatum D).datum.root a)) =
      Multiplicative.ofAdd (characterRestriction D (D.datum.root a)) :=
  coverRoot_eq_left D a

private theorem domainCongrBialgEquiv_toBialgHom {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M ≃* N) :
    (MonoidAlgebra.domCongrBialgEquiv R.{u} R.{u} f).toBialgHom =
      MonoidAlgebra.mapDomainBialgHom R.{u} f.toMonoidHom := by
  apply BialgHom.ext
  intro x
  change MonoidAlgebra.domCongr R.{u} R.{u} f x = MonoidAlgebra.mapDomainBialgHom R.{u} f.toMonoidHom x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m c => simp only [MonoidAlgebra.domCongr_single, MonoidAlgebra.mapDomainBialgHom_single]
                  rfl

private theorem coverTorusProductIso_fst (D : BasedRootDatum.{u}) :
    ((coverTorusProductIso D).hom.hom.hom ≫ fst (torusOf (DerivedCharacters D)).X
      (torusOf (CentralCharacters D)).X).left =
      Spec.map (CommRingCat.ofHom
        (MonoidAlgebra.mapDomainBialgHom R.{u} (coverCharactersLeft D)).toAlgHom.toRingHom) := by
  let X := DerivedCharacters D
  let Y := CentralCharacters D
  let eqv := coverProductCharacters D
  let g := (MonoidAlgebra.domCongrBialgEquiv R.{u} R.{u} eqv).toBialgHom
  let h := MonoidAlgebra.mapDomainBialgHom R.{u} (MonoidHom.inl X Y)
  have hpr : (productTorusMap X Y).hom.hom ≫ fst (torusOf X).X (torusOf Y).X =
      (spectrumOfHopfHom h).hom.hom := lift_fst _ _
  change (((spectrumOfHopfHom g).hom.hom ≫ (productTorusMap X Y).hom.hom) ≫ _).left = _
  rw [Category.assoc, hpr, ← Grp.comp_hom_hom, ← spectrumOfHopfHom_comp]
  change Spec.map (CommRingCat.ofHom (g.comp h).toAlgHom.toRingHom) = _
  rw [show g = MonoidAlgebra.mapDomainBialgHom R.{u} eqv.toMonoidHom from
    domainCongrBialgEquiv_toBialgHom eqv]
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  rfl

private theorem coverTorusProductIso_snd (D : BasedRootDatum.{u}) :
    ((coverTorusProductIso D).hom.hom.hom ≫ snd (torusOf (DerivedCharacters D)).X
      (torusOf (CentralCharacters D)).X).left =
      Spec.map (CommRingCat.ofHom
        (MonoidAlgebra.mapDomainBialgHom R.{u} (coverCharactersRight D)).toAlgHom.toRingHom) := by
  let X := DerivedCharacters D
  let Y := CentralCharacters D
  let eqv := coverProductCharacters D
  let g := (MonoidAlgebra.domCongrBialgEquiv R.{u} R.{u} eqv).toBialgHom
  let h := MonoidAlgebra.mapDomainBialgHom R.{u} (MonoidHom.inr X Y)
  have hpr : (productTorusMap X Y).hom.hom ≫ snd (torusOf X).X (torusOf Y).X =
      (spectrumOfHopfHom h).hom.hom := lift_snd _ _
  change (((spectrumOfHopfHom g).hom.hom ≫ (productTorusMap X Y).hom.hom) ≫ _).left = _
  rw [Category.assoc, hpr, ← Grp.comp_hom_hom, ← spectrumOfHopfHom_comp]
  change Spec.map (CommRingCat.ofHom (g.comp h).toAlgHom.toRingHom) = _
  rw [show g = MonoidAlgebra.mapDomainBialgHom R.{u} eqv.toMonoidHom from
    domainCongrBialgEquiv_toBialgHom eqv]
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  rfl

private theorem coverCoroot_left (D : BasedRootDatum.{u}) (a : D.I) (m : DerivedCharacters D) :
    (coverCoroot D a (coverCharactersLeft D m)).toAdd =
      (derivedDatum D).datum.coroot' a m.toAdd := by
  change (Module.dualProdDualEquivDual ℤ (CorootLattice D) (CentralLattice D)
      (m.toAdd, 0)) (derivedCoroot D a, 0) = m.toAdd (derivedCoroot D a)
  simp

private theorem coverCoroot_right (D : BasedRootDatum.{u}) (a : D.I) (m : CentralCharacters D) :
    (coverCoroot D a (coverCharactersRight D m)).toAdd = 0 := by
  change (Module.dualProdDualEquivDual ℤ (CorootLattice D) (CentralLattice D)
      (0, m.toAdd)) (derivedCoroot D a, 0) = 0
  simp

private theorem groupAlgebra_comp_map_of {X Y : Type u} [CommGroup X] [CommGroup Y]
    (S : IntegralAlgebra.{u}) (s : MonoidAlgebra R.{u} X →ₐ[R.{u}] S) (f : Y →* X) (m : Y) :
    (s.comp (MonoidAlgebra.mapDomainBialgHom R.{u} f).toAlgHom) (MonoidAlgebra.of R.{u} Y m) =
      s (MonoidAlgebra.of R.{u} X (f m)) := by
  change s (MonoidAlgebra.mapDomainBialgHom R.{u} f (MonoidAlgebra.single m 1)) =
    s (MonoidAlgebra.single (f m) 1)
  rw [MonoidAlgebra.mapDomainBialgHom_single]

private theorem torusValuesOfAlgHom_apply {X : Type u} [CommGroup X] (S : IntegralAlgebra.{u})
    (s : MonoidAlgebra R.{u} X →ₐ[R.{u}] S) (m : X) :
    ((torusValuesOfAlgHom S s m : Sˣ) : S) = s (MonoidAlgebra.of R.{u} X m) := rfl

private theorem coverTorusPoint_fst (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u})
    (p : MonoidAlgebra R.{u} (Multiplicative (CoverCharacters D)) →ₐ[R.{u}] S) :
    coordinatePoints S (toConv p) ≫ (coverTorusProductIso D).hom.hom.hom ≫ fst _ _ =
      torusPoint (derivedDatum D) S
        (torusValuesOfAlgHom S (p.comp (MonoidAlgebra.mapDomainBialgHom R.{u}
          (coverCharactersLeft D)).toAlgHom)) := by
  let f := MonoidAlgebra.mapDomainBialgHom R.{u} (coverCharactersLeft D)
  rw [torusPoint_as_coordinates, torusValuesOfAlgHom_eq]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, coverTorusProductIso_fst]
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom (p.comp f.toAlgHom).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem coverTorusPoint_diagonal {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (a : D.I) (S : IntegralAlgebra.{u}) (s : Sˣ) :
    coordinatePoints S (toConv (cocharacterEval (coverCoroot D a) S s)) ≫
      (coverTorus H).hom.hom =
    torusPoint (derivedDatum D) S (cocharacter (derivedDatum D) ((derivedDatum D).datum.coroot a) S s) ≫
      H.torus.hom.hom ≫ (coverInclusion H).hom.hom := by
  let p := cocharacterEval (coverCoroot D a) S s
  let q : IntegralPoints (torusOf (Multiplicative (CoverCharacters D))) S := coordinatePoints S (toConv p)
  let l : IntegralPoints H.group S :=
    torusPoint (derivedDatum D) S (cocharacter (derivedDatum D) ((derivedDatum D).datum.coroot a) S s) ≫
      H.torus.hom.hom
  change q ≫ (coverTorus H).hom.hom = l ≫ (coverInclusion H).hom.hom
  have h₁ : (coverInclusion H).hom.hom ≫ fst H.group.X (centralTorus D).X = 𝟙 _ :=
    lift_fst _ _
  have h₂ : (coverInclusion H).hom.hom ≫ snd H.group.X (centralTorus D).X = 1 :=
    lift_snd _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, coverTorus_fst, h₁, Category.comp_id, ← Category.assoc _ _ H.torus.hom.hom]
    dsimp only [q, l]
    rw [← Category.assoc (coordinatePoints S (toConv p)) _ H.torus.hom.hom,
      coverTorusPoint_fst D S p]
    congr 2
    apply MonoidHom.ext
    intro m
    apply Units.ext
    rw [torusValuesOfAlgHom_apply, groupAlgebra_comp_map_of]
    unfold p cocharacterEval
    rw [MonoidAlgebra.lift_of]
    change (↑(s ^ (coverCoroot D a (coverCharactersLeft D m)).toAdd) : S) =
      (↑(s ^ (derivedDatum D).datum.coroot' a m.toAdd) : S)
    rw [coverCoroot_left]
  · rw [Category.assoc, Category.assoc, h₂, MonObj.comp_one, coverTorus_snd]
    let f := MonoidAlgebra.mapDomainBialgHom R.{u} (coverCharactersRight D)
    have hp : p.comp f.toAlgHom =
        (Algebra.ofId R.{u} S).comp (Bialgebra.counitAlgHom R.{u} (MonoidAlgebra R.{u} (CentralCharacters D))) := by
      apply (MonoidAlgebra.lift R.{u} S (CentralCharacters D)).symm.injective
      apply MonoidHom.ext
      intro m
      simp only [MonoidAlgebra.lift_symm_apply, ← MonoidAlgebra.of_apply]
      rw [show f = MonoidAlgebra.mapDomainBialgHom R.{u} (coverCharactersRight D) from rfl,
        groupAlgebra_comp_map_of]
      unfold p cocharacterEval
      rw [MonoidAlgebra.lift_of]
      change (↑(s ^ (coverCoroot D a (coverCharactersRight D m)).toAdd) : S) =
        algebraMap R.{u} S (Bialgebra.counitAlgHom R.{u} (MonoidAlgebra R.{u} (CentralCharacters D))
          (MonoidAlgebra.single m 1))
      rw [coverCoroot_right, zpow_zero, Units.val_one, Bialgebra.counitAlgHom_apply,
        MonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, coverTorusProductIso_snd]
    change Spec.map (CommRingCat.ofHom p.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) =
      (1 : IntegralPoints (centralTorus D) S).left
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hOne := congrArg Over.Hom.left
      ((coordinatePoints (A := MonoidAlgebra R.{u} (CentralCharacters D)) S).map_one)
    change Spec.map (CommRingCat.ofHom (p.comp f.toAlgHom).toRingHom) = _
    rw [hp]
    exact hOne

private theorem coverRankOne_compatible {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (e : HopfSpectrum R.{u} A ≅ coverGroup H) (a : D.I) :
    RankOneCompatibility (markedTorusCoordinates e (coverTorus H))
      (markedRootCoordinates e (coverRootMap H a))
      (markedRootCoordinates e (coverRootMap H (D.datum.reflectionPerm a a)))
      (coverCoroot D a) (rankOneCoordinates (coverRankOneNatural H e a)) := by
  constructor
  · intro S z
    have hx (b : D.I) :
        additivePoint S z ≫ spectrumOfAlgHom (markedRootCoordinates e (coverRootMap H b)) =
          additivePoint S z ≫ (H.root b).hom.hom ≫ (coverInclusion H).hom.hom ≫ e.inv.hom.hom := by
      rw [markedRootCoordinates_spec, coverRootMap_eq]
      rfl
    constructor
    · apply WithConv.toConv_injective
      apply (coordinatePoints S).injective
      change coordinatePoints S ((coordinatePoints S).symm
        ((coverRankOneNatural H e a).app S _)) = _
      rw [MulEquiv.apply_symm_apply, coordinatePoints_polynomial, hx,
        coverRankOneNatural_apply, H.rankOneUpper, Category.assoc]
    · apply WithConv.toConv_injective
      apply (coordinatePoints S).injective
      change coordinatePoints S ((coordinatePoints S).symm
        ((coverRankOneNatural H e a).app S _)) = _
      rw [MulEquiv.apply_symm_apply, coordinatePoints_polynomial, hx,
        coverRankOneNatural_apply, H.rankOneLower, Category.assoc]
      rfl
  · intro S s
    apply WithConv.toConv_injective
    apply (coordinatePoints S).injective
    change coordinatePoints S ((coordinatePoints S).symm
      ((coverRankOneNatural H e a).app S _)) = _
    rw [MulEquiv.apply_symm_apply, coordinatePoints_comp, markedTorusCoordinates_spec,
      Grp.comp_hom_hom, ← Category.assoc, coverTorusPoint_diagonal,
      coverRankOneNatural_apply, H.rankOneDiagonal, Category.assoc]
    simp only [Category.assoc]

private theorem coverConjugation {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (S : IntegralAlgebra.{u})
    (p : IntegralPoints (torusOf (Multiplicative (CoverCharacters D))) S)
    (v : TorusValues (derivedDatum D) S)
    (hp : p ≫ (coverTorusProductIso D).hom.hom.hom ≫
      fst (splitTorus (derivedDatum D)).X (centralTorus D).X = torusPoint (derivedDatum D) S v)
    (a : D.I) (z : S) :
    let g : IntegralPoints (coverGroup H) S := p ≫ (coverTorus H).hom.hom
    let x (c : S) : IntegralPoints (coverGroup H) S :=
      H.line.point S c ≫ (coverRootMap H a).hom.hom
    g * x z * g⁻¹ =
      x ((v (Multiplicative.ofAdd ((derivedDatum D).datum.root a)) : S) * z) := by
  let G := H.group
  let C := centralTorus D
  let f := integralPointMap (fst G C) S
  let h := integralPointMap (snd G C) S
  let g : IntegralPoints (coverGroup H) S := p ≫ (coverTorus H).hom.hom
  let x (c : S) : IntegralPoints (coverGroup H) S :=
    H.line.point S c ≫ (coverRootMap H a).hom.hom
  let y : IntegralPoints H.group S := torusPoint (derivedDatum D) S v ≫ H.torus.hom.hom
  have hg : f g = y := by
    change (p ≫ (coverTorus H).hom.hom) ≫ fst G.X C.X = _
    rw [Category.assoc, coverTorus_fst]
    change p ≫ ((_ ≫ _) ≫ H.torus.hom.hom) = _
    rw [← Category.assoc, hp]
  have hx (c : S) : f (x c) = H.line.point S c ≫ (H.root a).hom.hom := by
    have eq : (coverRootMap H a).hom.hom ≫ fst G.X C.X = (H.root a).hom.hom :=
      lift_fst _ _
    change (H.line.point S c ≫ (coverRootMap H a).hom.hom) ≫ fst G.X C.X = _
    rw [Category.assoc, eq]
  have hx' (c : S) : h (x c) = 1 := by
    have eq : (coverRootMap H a).hom.hom ≫ snd G.X C.X = 1 :=
      lift_snd _ _
    change (H.line.point S c ≫ (coverRootMap H a).hom.hom) ≫ snd G.X C.X = _
    rw [Category.assoc, eq, MonObj.comp_one]
  change g * x z * g⁻¹ = _
  apply CartesianMonoidalCategory.hom_ext
  · change f (_ * _ * _) = f _
    rw [map_mul, map_mul, map_inv, hg, hx, hx]
    exact H.conjugation S v a z
  · change h (_ * _ * _) = h _
    rw [map_mul, map_mul, map_inv, hx', hx', mul_one, mul_inv_cancel]

private theorem coverRootScalarAction {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (e : HopfSpectrum R.{u} A ≅ coverGroup H) (a : D.I) :
    RootScalarAction (markedTorusCoordinates e (coverTorus H))
      (markedRootCoordinates e (coverRootMap H a))
      (Multiplicative.ofAdd (characterRestriction D (D.datum.root a))) := by
  intro S z p
  dsimp only
  apply (coordinatePoints S).injective
  simp only [map_mul, coordinatePoints_antipode, coordinatePoints_comp,
    coordinatePoints_polynomial, markedRootCoordinates_spec, markedTorusCoordinates_spec,
    Grp.comp_hom_hom, ← Category.assoc]
  let f := integralPointMap e.inv S
  change f _ * f _ * (f _)⁻¹ = f _
  rw [← map_inv, ← map_mul, ← map_mul]
  let v := torusValuesOfAlgHom S
    (p.comp (MonoidAlgebra.mapDomainBialgHom R.{u} (coverCharactersLeft D)).toAlgHom)
  have hv : (v (Multiplicative.ofAdd ((derivedDatum D).datum.root a)) : S) =
      p (MonoidAlgebra.of R.{u} _ (Multiplicative.ofAdd
        (characterRestriction D (D.datum.root a)))) := by
    rw [torusValuesOfAlgHom_apply, groupAlgebra_comp_map_of, coverCharactersLeft_root]
  refine congrArg f ?_
  have hh := coverConjugation H S (coordinatePoints S (toConv p)) v
    (coverTorusPoint_fst D S p) a z
  simpa only [hv] using hh

private theorem cover_algebraicQuotient
    (quotient : Specs.IntegralCentralQuotient.Statement.{u})
    {D : BasedRootDatum.{u}} (H : Model (derivedDatum D))
    (hRed : ReductiveFibres (coverTorus H)) : Nonempty (MarkedQuotient D) := by
  obtain ⟨E, ⟨e⟩⟩ := affineSpectrum (coverGroup H) (coverGroup_affine H)
  let t := markedTorusCoordinates e (coverTorus H)
  let x (a : D.I) := markedRootCoordinates e (coverRootMap H a)
  let r (a : D.I) := rankOneCoordinates (coverRankOneNatural H e a)
  have ht := markedTorusCoordinates_surjective e (coverTorus H) (coverTorus_closed H)
  let f := (Grp.forget IntegralScheme.{u} ⋙ Over.forget _).mapIso e
  have hs : Smooth (HopfSpectrum R.{u} E).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    change Smooth (f.hom ≫ (coverGroup H).X.hom)
    letI := coverGroup_smooth H
    infer_instance
  have hcell (negative positive : List D.I)
      (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
      (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}) :
      IsOpenImmersion (Specs.IntegralCentralQuotient.cellMap t x negative positive).left := by
    dsimp only [t, x]
    rw [markedCellCoordinates_spec, Over.comp_left, Over.comp_left]
    let i := (Over.forget _).mapIso
      (cellDomainIso (torusOf (Multiplicative (CoverCharacters D))) H.line negative positive)
    letI := coverCell_open H negative positive hn hp
    change IsOpenImmersion (i.hom ≫ (orderedCell H.line (coverTorus H)
      (coverRootMap H) negative positive).left ≫ f.inv)
    infer_instance
  obtain ⟨negative, positive, hn, hp⟩ := rootOrderings_exist D
  letI : IsIntegral ((Grp.forget IntegralScheme.{u} ⋙ Over.forget _).obj (coverGroup H)) :=
    coverGroup_integral H
  letI : IsIntegral (Spec (CommRingCat.of E)) := IsIntegral.of_isIso f.inv
  letI : _root_.IsReduced E := (affine_isReduced_iff (CommRingCat.of E)).mp inferInstance
  letI : IrreducibleSpace (HopfSpectrum R.{u} E).X.left :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of E)))
  have hc := central_of_openRootCell (torusKernel D) t x
    (fun a => Multiplicative.ofAdd (characterRestriction D (D.datum.root a))) (coverRoot_kernel D)
    (coverRootScalarAction H e) negative positive (hcell negative positive hn hp)
  have hRed' : ReductiveFibres (spectrumOfHopfHom t) := by
    rw [markedTorusCoordinates_spec]
    intro K _ _ _
    obtain ⟨V, i, h, hv⟩ := hRed K
    let B := fibreGroup (R := R.{u}) K
    have hj : B.map (coverTorus H ≫ e.inv) ≫ (B.mapIso e ≪≫ i).hom =
        B.map (coverTorus H) ≫ i.hom := by
      change B.map (coverTorus H ≫ e.inv) ≫ (B.map e.hom ≫ i.hom) = _
      have hIso : B.map e.inv ≫ B.map e.hom = 𝟙 (B.obj (coverGroup H)) :=
        (B.mapIso e).inv_hom_id
      rw [Functor.map_comp, Category.assoc, reassoc_of% hIso]
    refine ⟨V, B.mapIso e ≪≫ i, ?_⟩
    rw [hj]
    exact ⟨h, hv⟩
  exact markedQuotient_exists quotient D t x r H.line (fun a => coverRootMap H a ≫ e.inv)
    (fun a => (markedRootCoordinates_spec e (coverRootMap H a)).symm)
    negative positive hn hp ht hc hs hRed' hcell
    (fun a => ⟨markedRootCoordinates_surjective e (coverRootMap H a) (coverRoot_closed H a),
      coverRootScalarAction H e a, coverRankOne_compatible H e a⟩)

end CoverCoordinates

section IntegralQuotientMarks

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000

private abbrev quotientMarkedGroup {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) :
    IntegralGroup.{u} := HopfSpectrum R.{u} Q.algebra

private theorem quotientMarkedRoot_closed {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) (a : D.I) :
    IsClosedImmersion (Q.rootMap a).hom.hom.left := by
  rw [Q.rootMap_eq a]
  exact quotientRoot_closed Q a

private theorem quotientMarkedRankOne_upper {D : BasedRootDatum.{u}} (Q : MarkedQuotient D)
    (a : D.I) (S : IntegralAlgebra.{u}) (z : S) :
    (rankOneNatural (Q.rankOne a)).app S (Specs.IntegralRootRelations.upper z) =
      Q.line.point S z ≫ (Q.rootMap a).hom.hom := by
  rw [Q.rootMap_eq a]
  exact rankOneNatural_apply_upper _ S _ (fun z => ((Q.rankOneCompatible a).1 S z).1) z

private theorem quotientMarkedRankOne_lower {D : BasedRootDatum.{u}} (Q : MarkedQuotient D)
    (a : D.I) (S : IntegralAlgebra.{u}) (z : S) :
    (rankOneNatural (Q.rankOne a)).app S (Specs.IntegralRootRelations.lower z) =
      Q.line.point S z ≫ (Q.rootMap (D.datum.reflectionPerm a a)).hom.hom := by
  rw [Q.rootMap_eq]
  exact rankOneNatural_apply_lower _ S _ (fun z => ((Q.rankOneCompatible a).1 S z).2) z

private def quotientTorusCoordinates (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u})
    (w : TorusValues D S) : MonoidAlgebra R.{u} (torusKernel D).ker →ₐ[R.{u}] S :=
  MonoidAlgebra.lift R.{u} S _ ((Units.coeHom S).comp (w.comp (quotientCharacters D).symm.toMonoidHom))

private theorem quotientTorusCoordinates_apply (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u})
    (w : TorusValues D S) (x : Multiplicative D.X) :
    quotientTorusCoordinates D S w (MonoidAlgebra.of R.{u} _ (quotientCharacters D x)) = (w x : S) := by
  rw [quotientTorusCoordinates, MonoidAlgebra.lift_of]
  change (w ((quotientCharacters D).symm (quotientCharacters D x)) : S) = _
  rw [MulEquiv.symm_apply_apply]

private theorem quotientTorusPoint_coordinates (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u})
    (w : TorusValues D S) :
    torusPoint D S w ≫ (quotientTorusIso D).inv.hom.hom =
      coordinatePoints S (toConv (quotientTorusCoordinates D S w)) := by
  let i := (Grp.forget IntegralScheme.{u}).mapIso (quotientTorusIso D)
  apply (cancel_mono i.hom).mp
  change (_ ≫ i.inv) ≫ i.hom = _
  rw [Category.assoc, i.inv_hom_id, Category.comp_id, torusPoint_as_coordinates]
  have h : i.hom = (spectrumOfHopfHom (quotientCharacterMap D)).hom.hom :=
    Over.OverMorphism.ext (quotientTorusIso_hom D)
  rw [h, ← coordinatePoints_comp]
  apply congrArg (fun f : MonoidAlgebra R.{u} (Multiplicative D.X) →ₐ[R.{u}] S =>
    coordinatePoints S (toConv f))
  apply (MonoidAlgebra.lift R.{u} S (Multiplicative D.X)).symm.injective
  apply MonoidHom.ext
  intro m
  simp only [MonoidAlgebra.lift_symm_apply, ← MonoidAlgebra.of_apply, MonoidAlgebra.lift_of]
  change (w m : S) = quotientTorusCoordinates D S w (quotientCharacterMap D (MonoidAlgebra.of R.{u} _ m))
  rw [quotientCharacterMap, domainCongrBialgEquiv_toBialgHom]
  change (w m : S) = quotientTorusCoordinates D S w
    (MonoidAlgebra.mapDomainBialgHom R.{u} (quotientCharacters D).toMonoidHom
      (MonoidAlgebra.single m 1))
  rw [MonoidAlgebra.mapDomainBialgHom_single, ← MonoidAlgebra.of_apply]
  exact (quotientTorusCoordinates_apply D S w m).symm

private theorem quotientMarkedConjugation {D : BasedRootDatum.{u}} (Q : MarkedQuotient D)
    (S : IntegralAlgebra.{u}) (t : TorusValues D S) (a : D.I) (z : S) :
    let g : IntegralPoints (quotientMarkedGroup Q) S :=
      torusPoint D S t ≫ (quotientMarkedTorus Q).hom.hom
    g * (Q.line.point S z ≫ (Q.rootMap a).hom.hom) * g⁻¹ =
      Q.line.point S ((t (Multiplicative.ofAdd (D.datum.root a)) : S) * z) ≫
        (Q.rootMap a).hom.hom := by
  dsimp only
  have h := congrArg (coordinatePoints S) (Q.conjugation a S z (quotientTorusCoordinates D S t))
  simp only [map_mul, coordinatePoints_antipode, coordinatePoints_comp, coordinatePoints_polynomial,
    quotientTorusCoordinates_apply] at h
  rw [← quotientTorusPoint_coordinates] at h
  simp only [quotientMarkedTorus, Grp.comp_hom_hom, ← Category.assoc, Q.rootMap_eq]
  exact h

private theorem quotientRootProduct_eq {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) :
    ∀ (l : List D.I), (lineProductIso Q.line l).inv ≫ Specs.IntegralCentralQuotient.rootProduct Q.root l =
      Specs.IntegralSemisimpleModel.rootProduct Q.line Q.rootMap l := by
  intro l
  induction l with
  | nil => simp [lineProductIso, Specs.IntegralCentralQuotient.rootProduct,
      Specs.IntegralSemisimpleModel.rootProduct]
  | cons a l ih =>
    simp only [lineProductIso, Specs.IntegralCentralQuotient.rootProduct,
      Specs.IntegralSemisimpleModel.rootProduct, Q.rootMap_eq, MonoidalCategory.tensorIso_inv,
      Iso.refl_inv, MonObj.comp_mul, CartesianMonoidalCategory.tensorHom_fst_assoc,
      CartesianMonoidalCategory.tensorHom_snd_assoc, Category.id_comp, ih]

private theorem quotientMarkedCell_open {D : BasedRootDatum.{u}} (Q : MarkedQuotient D)
    (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}) :
    IsOpenImmersion (Specs.IntegralSemisimpleModel.cellMap Q.line (quotientMarkedTorus Q) Q.rootMap
      negative positive).left := by
  let I := Grp.forget IntegralScheme.{u}
  let e := MonoidalCategory.tensorIso (lineProductIso Q.line negative).symm
    (MonoidalCategory.tensorIso (I.mapIso (quotientTorusIso D)).symm
      (lineProductIso Q.line positive).symm)
  have he : e.hom ≫ Specs.IntegralCentralQuotient.cellMap Q.torus Q.root negative positive =
      Specs.IntegralSemisimpleModel.cellMap Q.line (quotientMarkedTorus Q) Q.rootMap
        negative positive := by
    change ((lineProductIso Q.line negative).inv ⊗ₘ
      ((quotientTorusIso D).inv.hom.hom ⊗ₘ (lineProductIso Q.line positive).inv)) ≫ _ = _
    simp only [Specs.IntegralCentralQuotient.cellMap, Specs.IntegralSemisimpleModel.cellMap,
      MonObj.comp_mul,
      CartesianMonoidalCategory.tensorHom_fst_assoc, CartesianMonoidalCategory.tensorHom_snd_assoc,
      quotientRootProduct_eq, quotientMarkedTorus, Grp.comp_hom_hom]
  rw [← he, Over.comp_left]
  let i := (Over.forget _).mapIso e
  letI := Q.openCell negative positive hn hp
  change IsOpenImmersion
    (i.hom ≫ (Specs.IntegralCentralQuotient.cellMap Q.torus Q.root negative positive).left)
  infer_instance

end IntegralQuotientMarks

end Coordinates

section AssembleModel

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.IntegralCentralQuotient (ReductiveFibres fibreGroup)
open Specs.IntegralSemisimpleModel
open Specs.Pinning (RootCoordinate SplitBorelPair)
open Specs.RationalRealization (Realization)
open Specs.RootGroups (HasScalarAction IsRootSubgroup rootPoint)

open private maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private maximalOfSourceIso
  from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private forgetFibrePoint_comp restrictToIntegers rankOneFibre rankOneFibre_apply
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

private theorem reductiveFibres_precompose {S T G : IntegralGroup.{u}}
    (e : S ≅ T) (t : T ⟶ G) (h : ReductiveFibres t) :
    ReductiveFibres (e.hom ≫ t) := by
  intro K _ _ _
  let F := fibreGroup K (R := Integers.{u})
  obtain ⟨H, i, hc, hH, hm⟩ := h K
  refine ⟨H, i, ?_⟩
  change ∃ hc : IsClosedImmersion (F.map (e.hom ≫ t) ≫ i.hom).hom.hom.left, _
  rw [Functor.map_comp, Category.assoc]
  obtain ⟨hc', hm'⟩ := maximalOfSourceIso (F.mapIso e) (F.map t ≫ i.hom) hc hm
  exact ⟨hc', hH, hm'⟩

private theorem model_reductiveFibres {D : BasedRootDatum.{u}} (H : Model D) :
    ReductiveFibres H.torus := by
  intro K _ _ a
  have ha : a = integerAlgebra K := by
    apply Algebra.algebra_ext
    intro n
    let e : ℤ ≃+* Integers.{u} := ULift.ringEquiv.symm
    exact DFunLike.congr_fun (RingHom.ext_int (a.algebraMap.comp e.toRingHom)
      ((integerAlgebra K).algebraMap.comp e.toRingHom)) n.down
  subst a
  obtain ⟨_, F, e, t, _, he, _, _, _⟩ := H.fieldFibre K
  let P := F.pinned.pair
  have hm := maximalTorus_of_geometricallyMaximal P.G P.T
    (lattice_torus_of_split P.split) P.maximal
  refine ⟨P.G, e, ?_⟩
  change ∃ hc : IsClosedImmersion (((fibre K).map H.torus) ≫ e.hom).hom.hom.left, _
  rw [he]
  obtain ⟨hc, ht⟩ := maximalOfSourceIso t P.T.inclusion P.T.isClosedImmersion hm
  exact ⟨hc, P.reductive, ht⟩

private theorem cover_reductiveFibres {D : BasedRootDatum.{u}} (H : Model (derivedDatum D)) :
    ReductiveFibres (coverTorus H) := by
  letI := D.freeY
  letI := D.finiteY
  letI : Module.Free ℤ (Additive (Multiplicative (derivedDatum D).X)) := (derivedDatum D).freeX
  letI : Module.Finite ℤ (Additive (Multiplicative (derivedDatum D).X)) := (derivedDatum D).finiteX
  letI : Module.Free ℤ (Additive (Multiplicative (Dual ℤ (CentralLattice D)))) :=
    inferInstanceAs (Module.Free ℤ (Dual ℤ (CentralLattice D)))
  letI : Module.Finite ℤ (Additive (Multiplicative (Dual ℤ (CentralLattice D)))) :=
    inferInstanceAs (Module.Finite ℤ (Dual ℤ (CentralLattice D)))
  exact reductiveFibres_precompose (coverTorusProductIso D) (H.torus ⊗ₘ 𝟙 (centralTorus D))
    (ReductiveProductWithSplitTorus.reductiveFibresTensorSplitTorus H.torus (model_reductiveFibres H))

private def quotientMarking {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) :
    IntegralMarking D where
  group := quotientMarkedGroup Q
  affine := inferInstanceAs (IsAffine (Spec (CommRingCat.of Q.algebra)))
  locallyOfFinitePresentation := by
    letI := Q.smooth
    infer_instance
  quasiCompact := by
    letI : IsAffine (quotientMarkedGroup Q).X.left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of Q.algebra)))
    letI : IsAffine Base.{u} := inferInstanceAs (IsAffine (Spec (CommRingCat.of Integers.{u})))
    infer_instance
  smooth := Q.smooth
  connected := Q.connected
  line := Q.line
  torus := quotientMarkedTorus Q
  torusClosed := quotientMarkedTorus_closed Q
  root := Q.rootMap
  rootClosed := quotientMarkedRoot_closed Q
  conjugation := quotientMarkedConjugation Q
  openCell := quotientMarkedCell_open Q
  rankOne := fun a => rankOneNatural (Q.rankOne a)
  rankOneUpper := quotientMarkedRankOne_upper Q
  rankOneLower := quotientMarkedRankOne_lower Q
  rankOneDiagonal := quotientRankOne_diagonal Q

private theorem quotient_reductiveFibres {D : BasedRootDatum.{u}} (Q : MarkedQuotient D) :
    ReductiveFibres (quotientMarking Q).torus :=
  reductiveFibres_precompose (quotientTorusIso D).symm _ Q.reductiveFibres

private def modelOfMarking {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (hRed : ReductiveFibres M.torus) (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}) : Model D where
  toIntegralMarking := M
  fieldFibre := by
    intro k _
    letI := M.affine
    letI := M.smooth
    let H := Specs.IntegralFibreRootCoordinates.fibreAlgebraicGroup k M.group
    obtain ⟨hT, A, e, χ, hH, hSplit, hMax, hLine, hχ, b, hb⟩ :=
      IntegralFibreRootCoordinates.integralFibreRootCoordinates D M.group M.line M.torus M.root
        M.torusClosed M.rootClosed hRed M.conjugation negative positive hn hp
        (M.openCell negative positive hn hp) k
    let T : ClosedSubgroup H.val := ⟨_, (fibre k).map M.torus, hT⟩
    let f (a : D.I) : A.group ⟶ H.val := e.hom ≫ (fibre k).map (M.root a)
    have hRoot (α : Root T) :
        ∃ h : IsClosedImmersion (f (b.symm α)).hom.hom.left,
          IsRootSubgroup T ⟨A.group, f (b.symm α), h⟩ α.val ∧
            HasScalarAction T α.val (f (b.symm α)) := by
      simpa only [Equiv.apply_symm_apply] using (hb (b.symm α)).2
    let U : Specs.OrderedRootProducts.RootSubgroupFamily T := fun α =>
      ⟨⟨A.group, f (b.symm α), (hRoot α).choose⟩, (hRoot α).choose_spec.1⟩
    let c (α : Root T) : RootCoordinate A T (U α).val α.val :=
      ⟨Iso.refl _, by
        change HasScalarAction T α.val (𝟙 A.group ≫ f (b.symm α))
        rw [Category.id_comp]
        exact (hRoot α).choose_spec.2⟩
    let W : Specs.PinnedDatumFromMarkedRootGroups.Marking D H T A :=
      ⟨χ, b, fun a => (hb a).1, U, c⟩
    have hW (a : D.I) : W.rootMap a = f a := by
      change 𝟙 A.group ≫ f (b.symm (b a)) = _
      rw [Category.id_comp, Equiv.symm_apply_apply]
    have hv (a : D.I) (R : TestAlgebra k) (r : R) :
        forgetFibrePoint M.group R (rootPoint (f a) R r) =
          M.line.point ((restrictToIntegers k).obj R) r ≫ (M.root a).hom.hom := by
      dsimp only [f]
      rw [rootPoint_comp, forgetFibrePoint_comp, hLine]
    let ρ : Specs.PinnedDatumFromMarkedRootGroups.RankOneRelations W :=
      { hom := fun a => rankOneFibre M a
        upper_eq := fun a R r => by
          apply (IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective
          change forgetFibrePoint M.group R
            ((rankOneFibre M a).app R (Specs.IntegralRootRelations.upper r)) = _
          rw [rankOneFibre_apply, hW, hv]
          exact M.rankOneUpper a ((restrictToIntegers k).obj R) r
        lower_eq := fun a R r => by
          apply (IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective
          change forgetFibrePoint M.group R
            ((rankOneFibre M a).app R (Specs.IntegralRootRelations.lower r)) = _
          rw [rankOneFibre_apply, hW, hv]
          exact M.rankOneLower a ((restrictToIntegers k).obj R) r
        diagonal_eq := fun a R s => by
          let S := (restrictToIntegers k).obj R
          let v := cocharacter D (D.datum.coroot a) S s
          obtain ⟨t, ht⟩ := (IntegralSemisimpleModel.forgetFibrePoint_bijective
            (splitTorus D) R).surjective (torusPoint D S v)
          refine ⟨t, ?_, fun x => hχ R t v ht x⟩
          apply (IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective
          change forgetFibrePoint M.group R
            ((rankOneFibre M a).app R (Specs.IntegralRootRelations.diagonal s)) =
            forgetFibrePoint M.group R (t ≫ ((fibre k).map M.torus).hom.hom)
          rw [rankOneFibre_apply, forgetFibrePoint_comp, ht]
          exact M.rankOneDiagonal a S s }
    obtain ⟨B, hB, hTB, E, d, p, z, _, hWeight, hIndex, hPin, hz⟩ :=
      PinnedDatumFromMarkedRootGroups.pinnedDatumFromMarkedRootGroups D k H hH T hSplit hMax A W ρ
    let P : SplitBorelPair k := Specs.PinnedDatumFromMarkedRootGroups.markedBorelPair hH hSplit hMax B hB hTB
    let F : Realization D A := ⟨⟨P, U, p⟩, E, d⟩
    refine ⟨A, F, Iso.refl _, Iso.refl _, (fun a => z (d.val.indexEquiv a)), ?_, ?_, ?_, ?_⟩
    · change ((fibre k).map M.torus) ≫ 𝟙 _ = 𝟙 _ ≫ ((fibre k).map M.torus)
      rw [Category.comp_id, Category.id_comp]
    · intro i
      exact (hPin (F.simpleRoot i)).symm
    · intro R s v hs x
      change characterValue (Additive.toMul (d.val.weightEquiv x)) R (s ≫ 𝟙 _) =
        (v (Multiplicative.ofAdd x) : R)
      rw [Category.comp_id, hWeight]
      exact hχ R s v hs x
    · intro a R r
      change forgetFibrePoint M.group R
        (rootPoint ((z (d.val.indexEquiv a)).val.hom ≫
          (U (d.val.indexEquiv a)).val.inclusion ≫ 𝟙 _) R r) = _
      rw [Category.comp_id, hz, hIndex]
      exact (congrArg (fun j => forgetFibrePoint M.group R (rootPoint j R r)) (hW a)).trans (hv a R r)

/-- Every finite based reduced root datum is realized by a split pinned
affine model over the integers, with the prescribed marking in every field. -/
theorem integralRealization : Specs.IntegralRealization.Statement.{u} := by
  intro D
  obtain ⟨H⟩ := semisimpleModel_exists IntegralSemisimpleModel.integralSemisimpleModel D
  obtain ⟨Q⟩ := cover_algebraicQuotient IntegralCentralQuotient.integralCentralQuotient H
    (cover_reductiveFibres H)
  exact ⟨modelOfMarking (quotientMarking Q) (quotient_reductiveFibres Q)
    Q.negative Q.positive
    Q.negativeEnumerates Q.positiveEnumerates⟩

end AssembleModel

end

end LinearAlgebraicGroups.Classification.IntegralRealization
