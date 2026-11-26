import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatum
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Batteries.Tactic.OpenPrivate

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.TypeCSplitRecognition

open _root_.LinearAlgebraicGroups.Specs
open Specs.TypeCSplitRecognition
open Specs.Pinning (BasedRootDatum BasedIso AttachedDatum SplitBorelPair PinnedGroup PinnedIso)
open Specs.SymplecticDatumTorusAndBorel (RootLabel coordinate sign rootVector simpleLabel HyperbolicIndex)
open Specs.SymplecticDatum (simpleCoroot corootVector)
open Specs.SymplecticMatrixStructure (symplecticPoints PointGroup)

noncomputable section

private theorem simpleLabel_injective (n : ℕ) :
    Function.Injective (@simpleLabel n) := by
  let first : RootLabel (n + 1) → Fin (n + 1)
    | .long i _ => i
    | .short i _ _ _ _ => i
  have h (i : Fin (n + 1)) : first (simpleLabel i) = i := by
    unfold simpleLabel
    split <;> rfl
  exact Function.LeftInverse.injective h

open private corootVector_simpleLabel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatum

private def cartan {n : ℕ} (i j : Fin (n + 1)) : ℤ :=
  ∑ p, rootVector (simpleLabel i) p * corootVector (simpleLabel j) p

private theorem cartan_formula {n : ℕ} (i j : Fin (n + 1)) :
    cartan i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
        (if i.val = n then -2 else -1) else 0 := by
  have hsum (a b : Fin (n + 1)) :
      ∑ p : Fin (n + 1), coordinate a p * coordinate b p = (if a = b then 1 else 0) := by
    simp [coordinate, Pi.single_apply, eq_comm]
  have hroot : rootVector (simpleLabel i) =
      if h : i.val < n then coordinate i - coordinate ⟨i.val + 1, by omega⟩
      else fun p => 2 * coordinate i p := by
    by_cases h : i.val < n
    · simp [simpleLabel, h, rootVector, sign, sub_eq_add_neg]
    · simp [simpleLabel, h, rootVector, sign, zsmul_eq_mul]
      rfl
  rw [cartan, hroot, corootVector_simpleLabel]
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  all_goals
    simp only [hi, hj, dite_true, dite_false, simpleCoroot, Pi.sub_apply, Pi.zero_apply, sub_zero,
      sub_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hsum, Fin.ext_iff]
    split_ifs <;> omega

private theorem cartan_rigid {n : ℕ} (p : Fin (n + 1) ≃ Fin (n + 1))
    (hp : ∀ i j, cartan (p i) (p j) = cartan i j) (i : Fin (n + 1)) : p i = i := by
  let last : Fin (n + 1) := ⟨n, by omega⟩
  have hn : p last = last := by
    by_cases h : n = 0
    · apply Fin.ext
      have := (p last).isLt
      change (p last).val = n
      omega
    · let prev : Fin (n + 1) := ⟨n - 1, by omega⟩
      have hv : last.val = n := rfl
      have hv' : prev.val = n - 1 := rfl
      have hl : cartan last prev = -2 := by
        rw [cartan_formula]
        split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
      have hh := (hp last prev).trans hl
      rw [cartan_formula] at hh
      apply Fin.ext
      change (p last).val = n
      split_ifs at hh <;> omega
  have hadj (a b : Fin (n + 1)) :
      cartan a b < 0 ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val := by
    rw [cartan_formula]
    split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
  suffices h : ∀ d : ℕ, ∀ j : Fin (n + 1), n - j.val = d → p j = j by
    exact h _ i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j hd
    by_cases hj : j.val = n
    · have : j = last := Fin.ext hj
      rwa [this]
    let next : Fin (n + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
    have hnext : p next = next := ih (n - next.val) (by
      change n - (j.val + 1) < d
      have := j.isLt
      omega) next rfl
    have hneg : cartan (p j) (p next) < 0 := by
      rw [hp]
      exact (hadj j next).2 (Or.inl rfl)
    rw [hnext, hadj] at hneg
    rcases hneg with hprev | hsucc
    · exact Fin.ext (by change (p j).val + 1 = j.val + 1 at hprev; omega)
    · have hfix : p (p j) = p j := ih (n - (p j).val) (by
        change j.val + 1 + 1 = (p j).val at hsucc
        have := j.isLt
        omega) (p j) rfl
      have he := p.injective hfix
      have hv := congrArg Fin.val he
      change j.val + 1 + 1 = (p j).val at hsucc
      omega

private def simpleIndex {n : ℕ} {D : BasedRootDatum.{u}} (c : TypeCCoordinates n D) :
    Fin (n + 1) ≃ ↥D.base.support :=
  Equiv.ofBijective (fun i => ⟨c.roots (simpleLabel i), (c.simple _).2 ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => simpleLabel_injective n (c.roots.injective (congrArg Subtype.val h)),
      fun ⟨a, ha⟩ => by
        have h := (c.simple (c.roots.symm a)).1 (by simpa only [Equiv.apply_symm_apply] using ha)
        obtain ⟨i, hi⟩ := h
        refine ⟨i, Subtype.ext ?_⟩
        exact (congrArg c.roots hi.symm).trans (c.roots.apply_symm_apply a)⟩

private theorem base_mem_iff {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    e.val.indexEquiv i ∈ E.base.support ↔ i ∈ D.base.support := by
  let f := e.val.indexEquiv
  change f i ∈ (E.base.support : Set E.I) ↔ i ∈ (D.base.support : Set D.I)
  have hf : f '' (D.base.support : Set D.I) = E.base.support := e.property
  rw [← hf]
  simp only [Set.mem_image, f.injective.eq_iff, exists_eq_right]

private def basePermutation {n : ℕ} {D : BasedRootDatum.{u}} (c : TypeCCoordinates n D)
    (e : BasedIso D D) : Fin (n + 1) ≃ Fin (n + 1) :=
  (simpleIndex c).trans ((e.val.indexEquiv.subtypeEquiv (fun a => (base_mem_iff e a).symm)).trans (simpleIndex c).symm)

private theorem basePermutation_spec {n : ℕ} {D : BasedRootDatum.{u}} (c : TypeCCoordinates n D)
    (e : BasedIso D D) (i : Fin (n + 1)) :
    c.roots (simpleLabel (basePermutation c e i)) = e.val.indexEquiv (c.roots (simpleLabel i)) := by
  let a := (e.val.indexEquiv.subtypeEquiv (fun a => (base_mem_iff e a).symm)) (simpleIndex c i)
  exact congrArg Subtype.val ((simpleIndex c).apply_symm_apply a)

private theorem simpleCorootBasisOfCoordinates {n : ℕ} {D : BasedRootDatum.{u}}
    (c : TypeCCoordinates n D) :
    ∃ b : Module.Basis (Fin (n + 1)) ℤ D.Y,
      ∀ i, b i = D.datum.coroot (c.roots (simpleLabel i)) := by
  obtain ⟨b, hb⟩ := RootData.SymplecticDatum.simpleCorootBasis n
  refine ⟨b.map c.cocharacters.symm, fun i => c.cocharacters.injective ?_⟩
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, hb, c.coroot,
    corootVector_simpleLabel]

theorem basedRigidity : BasedRigidity.{u} := by
  intro n D c d
  let e := d.asIso.hom
  let p := basePermutation c e
  have hcart (i j : Fin (n + 1)) :
      D.datum.pairing (c.roots (simpleLabel i)) (c.roots (simpleLabel j)) = cartan i j := by
    rw [← RootPairing.root_coroot_eq_pairing, c.pairing, c.root, c.coroot]
    rfl
  have hp (i j : Fin (n + 1)) : cartan (p i) (p j) = cartan i j := by
    rw [← hcart, ← hcart, basePermutation_spec, basePermutation_spec]
    exact e.val.toHom.pairing
  have hbase (i : Fin (n + 1)) :
      e.val.indexEquiv (c.roots (simpleLabel i)) = c.roots (simpleLabel i) := by
    rw [← basePermutation_spec, show basePermutation c e i = i from cartan_rigid p hp i]
  obtain ⟨b, hb⟩ := simpleCorootBasisOfCoordinates c
  have hy : e.val.coweightMap = LinearMap.id := by
    apply b.ext
    intro i
    rw [hb, LinearMap.id_apply, e.val.toHom.coroot_coweightMap_apply]
    congr 1
    exact e.val.indexEquiv.symm_apply_eq.mpr (hbase i).symm
  have hx (x : D.X) : e.val.weightEquiv x = x := by
    apply D.datum.toPerfPair.injective
    ext y
    rw [show D.datum.toPerfPair (e.val.weightEquiv x) y =
      D.datum.toLinearMap (e.val.weightEquiv x) y from rfl,
      e.val.toLinearMap_weightEquiv]
    change D.datum.toLinearMap x (e.val.coweightMap y) = D.datum.toLinearMap x y
    rw [hy, LinearMap.id_apply]
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.datum
  ext x
  exact hx x

private def coordinatesIso {n : ℕ} {D E : BasedRootDatum.{u}} (x : TypeCCoordinates n D)
    (y : TypeCCoordinates n E) : BasedIso D E := by
  let X := x.characters.trans y.characters.symm
  let Y := y.cocharacters.trans x.cocharacters.symm
  let e := x.roots.symm.trans y.roots
  refine ⟨{
    weightMap := X
    coweightMap := Y
    indexEquiv := e
    bijective_weightMap := X.bijective
    bijective_coweightMap := Y.bijective
    weight_coweight_transpose := ?_
    root_weightMap := ?_
    coroot_coweightMap := ?_ }, ?_⟩
  · ext a b
    change E.datum.toLinearMap (X b) a = D.datum.toLinearMap b (Y a)
    rw [x.pairing, y.pairing]
    simp only [X, Y, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  · funext a
    obtain ⟨a, rfl⟩ := x.roots.surjective a
    apply y.characters.injective
    change y.characters (y.characters.symm (x.characters (D.datum.root (x.roots a)))) =
      y.characters (E.datum.root (y.roots (x.roots.symm (x.roots a))))
    rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply, x.root, y.root]
  · funext a
    obtain ⟨a, rfl⟩ := y.roots.surjective a
    apply x.cocharacters.injective
    change x.cocharacters (x.cocharacters.symm (y.cocharacters (E.datum.coroot (y.roots a)))) =
      x.cocharacters (D.datum.coroot (x.roots (y.roots.symm (y.roots a))))
    rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply, x.coroot, y.coroot]
  · ext a
    obtain ⟨a, rfl⟩ := y.roots.surjective a
    change y.roots a ∈ e '' (D.base.support : Set D.I) ↔ y.roots a ∈ E.base.support
    have he : e (x.roots a) = y.roots a := by simp [e]
    conv_lhs => rw [← he]
    simp only [Set.mem_image, e.injective.eq_iff, exists_eq_right]
    exact (x.simple a).trans (y.simple a).symm

open private pinnedLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

theorem pinnedRecognition : PinnedRecognition.{u} := by
  intro k _ A n P Q D E x y
  let e := coordinatesIso x y
  obtain ⟨f, hf⟩ := pinnedLift P Q D E e
  refine ⟨e, f, fun _ => rfl, fun _ => rfl, fun a => ?_, ?_, ?_⟩
  · change y.roots (x.roots.symm (x.roots a)) = y.roots a
    rw [Equiv.symm_apply_apply]
  · rw [← hf]
    intro χ
    rfl
  · rw [← hf]
    intro z
    rfl

section Splitting

open _root_.LinearAlgebraicGroups.SymplecticMatrixStructure
  (symplecticGroup symplecticGroupPointsIso baseChangeSymplecticPointsIso)
open _root_.LinearAlgebraicGroups.Classification.Pinning
  (pinningsExist inducedBasedIso standardAdditiveLine)
open Specs.RootGroups (AdditiveLine)
open _root_.LinearAlgebraicGroups.Descent.Forms
  (spectrumIso finiteLevelIsomorphisms)
open private exists_coordinate_model spectrumIsoEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

open Specs.GeometricRadicals (IsReductive IsTorus IsSplitTorus IsMaximalTorus GeometricGroup)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open private extendSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private factor_torus_through_centralizer from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private groupBaseChangeTower smooth_baseChange_iff connected_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private fibreTowerIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private alignPairs pinAlignedPairs from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem split_torus_over_separably_closed {k K : Type u}
    [Field k] [Field K] [Algebra k K] [IsSepClosed K]
    {T : GroupScheme k} (hT : IsTorus T) :
    IsSplitTorus ((groupBaseChange k K).obj T) := by
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := hT
  let f : E →ₐ[k] K := IsSepClosed.lift
  let : Algebra E K := f.toRingHom.toAlgebra
  let : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  obtain ⟨s, ⟨j⟩⟩ := splitTorus_baseChange (K := K) (T := (groupBaseChange k E).obj T)
    ⟨r, ⟨e⟩⟩
  exact ⟨s, ⟨(groupBaseChangeTower (K := E) K).app T ≪≫ j⟩⟩

private theorem centralizer_of_extended_torus {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme k} (T : ClosedSubgroup G)
    (hT : RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g)) :
    RepresentsSubgroup (extendSubgroup K T)
      (fun _ g ↦ Centralizes (extendSubgroup K T).inclusion g) := by
  obtain ⟨_, h⟩ := centralizerSchemeBaseChange k K T.inclusion T hT
  exact h

private theorem split_maximal_after_extension {k K : Type u}
    [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsTorus T.group) (hm : IsGeometricallyMaximal T)
    (hs : IsSplitTorus ((groupBaseChange k K).obj T.group)) :
    IsGeometricallyMaximal (extendSubgroup K T) := by
  have hC : RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g) :=
    Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT hm
  let U := extendSubgroup K T
  let L := AlgebraicClosure K
  let V := extendSubgroup L U
  have hV : RepresentsSubgroup V (fun _ g ↦ Centralizes V.inclusion g) :=
    centralizer_of_extended_torus U (centralizer_of_extended_torus T hC)
  have hsV : IsSplitTorus V.group := splitTorus_baseChange (K := L) hs
  have hmax : IsMaximalTorus V := by
    refine ⟨lattice_torus_of_split hsV, ?_⟩
    intro W hW hVW
    have hc := torus_commutative
      (closedSubgroupAlgebraicGroup (G := GeometricGroup (baseChangedAlgebraicGroup K G)) W) hW
    exact factor_torus_through_centralizer hV hc hVW
  exact ⟨V.isClosedImmersion, hmax⟩

theorem separableBorelPair : SeparableBorelPair.{u} := by
  intro k S _ _ _ _ G hG
  let := hG.2.1
  let : IsSepClosed S := IsSepClosure.sep_closed k
  have hc : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  obtain ⟨T, hT, hm⟩ := MaximalToriExist.geometricallyMaximalTorusExists G hG.1 hc
  have hs := split_torus_over_separably_closed (K := S) hT
  have hmax := split_maximal_after_extension G hG T hT hm hs
  have hGS := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := S) G hG.1 hG.2.1).mpr hG
  exact ⟨splitBorelPair (baseChangedAlgebraicGroup S G) hGS (extendSubgroup S T) hs hmax, rfl⟩

private def transportCoordinates {n : ℕ} {D E : BasedRootDatum.{u}}
    (e : BasedIso D E) (c : TypeCCoordinates n E) : TypeCCoordinates n D where
  characters := e.val.weightEquiv.trans c.characters
  cocharacters := e.val.coweightEquiv.symm.trans c.cocharacters
  roots := c.roots.trans e.val.indexEquiv.symm
  pairing x y := by
    change D.datum.toLinearMap x y =
      ∑ i, c.characters (e.val.weightEquiv x) i * c.cocharacters (e.val.coweightEquiv.symm y) i
    rw [← c.pairing, e.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]
  root a := by
    change c.characters (e.val.weightEquiv (D.datum.root (e.val.indexEquiv.symm (c.roots a)))) =
      rootVector a
    have h := RootPairing.Hom.root_weightMap_apply D.datum E.datum
      (e.val.indexEquiv.symm (c.roots a)) e.val.toHom
    change e.val.weightEquiv _ = E.datum.root (e.val.indexEquiv _) at h
    rw [h, Equiv.apply_symm_apply, c.root]
  coroot a := by
    change c.cocharacters (e.val.coweightEquiv.symm
      (D.datum.coroot (e.val.indexEquiv.symm (c.roots a)))) = corootVector a
    rw [← RootPairing.Hom.coroot_coweightMap_apply _ _ (c.roots a) e.val.toHom]
    exact (congrArg c.cocharacters (e.val.coweightEquiv.symm_apply_apply _)).trans (c.coroot a)
  simple a := by
    change e.val.indexEquiv.symm (c.roots a) ∈ D.base.support ↔ _
    rw [← base_mem_iff e, Equiv.apply_symm_apply, c.simple]

private theorem corootSpanOfCoordinates {n : ℕ} {D : BasedRootDatum.{u}}
    (c : TypeCCoordinates n D) : D.datum.corootSpan ℤ = ⊤ := by
  obtain ⟨b, hb⟩ := simpleCorootBasisOfCoordinates c
  apply eq_top_iff.mpr
  rw [← b.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨c.roots (simpleLabel i), (hb i).symm⟩

private def simpleCorootBasis {D : BasedRootDatum.{u}} (h : D.datum.corootSpan ℤ = ⊤) :
    Module.Basis ↥D.base.support ℤ D.Y :=
  Module.Basis.mk D.base.linearIndepOn_coroot (by
    change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.coroot ∘ ((↑) : ↥D.base.support → D.I)))
    rw [Set.range_comp, Subtype.range_coe_subtype, Finset.setOfPred_mem,
      D.base.span_coroot_support, h])

private theorem simpleCorootBasis_apply {D : BasedRootDatum.{u}}
    (h : D.datum.corootSpan ℤ = ⊤) (i : ↥D.base.support) :
    simpleCorootBasis h i = D.datum.coroot i :=
  Module.Basis.mk_apply _ _ i

/-- A paired image of the simple roots extends to every root by the two
reflection formulas, with the same index for each root and coroot. -/
private theorem rootPairInImage {D E : BasedRootDatum.{u}}
    (s : ↥D.base.support ≃ ↥E.base.support) (f : D.X ≃ₗ[ℤ] E.X) (g : D.Y ≃ₗ[ℤ] E.Y)
    (hPair : ∀ x y, E.datum.toLinearMap (f x) (g y) = D.datum.toLinearMap x y)
    (hf : ∀ i : ↥D.base.support, f (D.datum.root i) = E.datum.root (s i))
    (hg : ∀ i : ↥D.base.support, g (D.datum.coroot i) = E.datum.coroot (s i))
    (i : D.I) : ∃ j, f (D.datum.root i) = E.datum.root j ∧
      g (D.datum.coroot i) = E.datum.coroot j := by
  let := D.finiteRoots
  let := D.reduced
  have hp {a b : D.I} {a' b' : E.I}
      (ha : f (D.datum.root a) = E.datum.root a')
      (hb : g (D.datum.coroot b) = E.datum.coroot b') :
      E.datum.pairing a' b' = D.datum.pairing a b := by
    rw [← RootPairing.root_coroot_eq_pairing, ← ha, ← hb, hPair,
      RootPairing.root_coroot_eq_pairing]
  apply D.base.induction_reflect i
  · rintro a ⟨a', ha, ha'⟩
    refine ⟨E.datum.reflectionPerm a' a', ?_, ?_⟩
    · simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg, ha]
    · simp only [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self, map_neg, ha']
  · intro a ha
    exact ⟨s ⟨a, ha⟩, hf ⟨a, ha⟩, hg ⟨a, ha⟩⟩
  · rintro a b ⟨a', ha, ha'⟩ hb
    let j : ↥D.base.support := ⟨b, hb⟩
    have hfb : f (D.datum.root b) = E.datum.root (s j) := hf j
    have hgb : g (D.datum.coroot b) = E.datum.coroot (s j) := hg j
    refine ⟨E.datum.reflectionPerm (s j) a', ?_, ?_⟩
    · simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
        map_sub, map_smul, ha, hfb, hp ha hgb]
    · simp only [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_coroot,
        map_sub, map_smul, ha', hgb, hp hfb ha']

set_option maxHeartbeats 700000 in
private def basedIsoFromCartan {D E : BasedRootDatum.{u}}
    (hD : D.datum.corootSpan ℤ = ⊤) (hE : E.datum.corootSpan ℤ = ⊤)
    (s : ↥D.base.support ≃ ↥E.base.support)
    (hCartan : ∀ i j : ↥D.base.support,
      E.datum.pairing (s i) (s j) = D.datum.pairing i j) : BasedIso D E := by
  let g := (simpleCorootBasis hD).equiv (simpleCorootBasis hE) s
  let f := D.datum.toPerfPair.trans (g.symm.dualMap.trans E.datum.toPerfPair.symm)
  have hPair (x : D.X) (y : D.Y) :
      E.datum.toLinearMap (f x) (g y) = D.datum.toLinearMap x y := by
    change E.datum.toPerfPair (f x) (g y) = D.datum.toPerfPair x y
    simp [f]
  have hg (i : ↥D.base.support) : g (D.datum.coroot i) = E.datum.coroot (s i) := by
    rw [← simpleCorootBasis_apply hD i]
    change (simpleCorootBasis hD).equiv (simpleCorootBasis hE) s ((simpleCorootBasis hD) i) = _
    rw [Module.Basis.equiv_apply, simpleCorootBasis_apply]
  have hf (i : ↥D.base.support) : f (D.datum.root i) = E.datum.root (s i) := by
    apply E.datum.toPerfPair.injective
    apply (simpleCorootBasis hE).ext
    intro j
    obtain ⟨j, rfl⟩ := s.surjective j
    have h := (simpleCorootBasis_apply hE (s j)).trans (hg j).symm
    change E.datum.toLinearMap _ (simpleCorootBasis hE (s j)) =
      E.datum.toLinearMap _ (simpleCorootBasis hE (s j))
    rw [h, hPair, hg j, RootPairing.root_coroot_eq_pairing, RootPairing.root_coroot_eq_pairing,
      hCartan]
  have hi := rootPairInImage s f g hPair hf hg
  have hj := rootPairInImage s.symm f.symm g.symm
    (fun x y => by simpa only [LinearEquiv.apply_symm_apply] using (hPair (f.symm x) (g.symm y)).symm)
    (fun i => f.symm_apply_eq.mpr (by simpa only [Equiv.apply_symm_apply] using (hf (s.symm i)).symm))
    (fun i => g.symm_apply_eq.mpr (by simpa only [Equiv.apply_symm_apply] using (hg (s.symm i)).symm))
  let index (i : D.I) : E.I := (hi i).choose
  have hroot (i : D.I) : f (D.datum.root i) = E.datum.root (index i) := (hi i).choose_spec.1
  have hcoroot (i : D.I) : g (D.datum.coroot i) = E.datum.coroot (index i) := (hi i).choose_spec.2
  have hInjective : Function.Injective index := by
    intro a b h
    apply D.datum.root.injective
    apply f.injective
    rw [hroot, hroot, h]
  have hSurjective : Function.Surjective index := by
    intro b
    obtain ⟨a, ha, _⟩ := hj b
    refine ⟨a, E.datum.root.injective ((hroot a).symm.trans ?_)⟩
    rw [← ha, LinearEquiv.apply_symm_apply]
  let e : D.I ≃ E.I := Equiv.ofBijective index ⟨hInjective, hSurjective⟩
  have hs (i : ↥D.base.support) : e i = (s i).val :=
    E.datum.root.injective ((hroot i).symm.trans (hf i))
  refine ⟨{
    weightMap := f
    coweightMap := g.symm
    indexEquiv := e
    bijective_weightMap := f.bijective
    bijective_coweightMap := g.symm.bijective
    weight_coweight_transpose := ?_
    root_weightMap := funext hroot
    coroot_coweightMap := ?_ }, ?_⟩
  · ext y x
    change E.datum.toLinearMap (f x) y = D.datum.toLinearMap x (g.symm y)
    simpa only [LinearEquiv.apply_symm_apply] using hPair x (g.symm y)
  · funext j
    change g.symm (E.datum.coroot j) = D.datum.coroot (e.symm j)
    have h : g (D.datum.coroot (e.symm j)) = E.datum.coroot (e (e.symm j)) :=
      hcoroot (e.symm j)
    rw [Equiv.apply_symm_apply] at h
    exact g.symm_apply_eq.mpr h.symm
  · ext j
    change j ∈ e '' (D.base.support : Set D.I) ↔ j ∈ E.base.support
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hs ⟨i, hi⟩]
      exact (s ⟨i, hi⟩).property
    · intro hj
      let i := s.symm ⟨j, hj⟩
      exact ⟨i, i.property, (hs i).trans (congrArg Subtype.val (s.apply_symm_apply ⟨j, hj⟩))⟩

private theorem basedIsoOfGroupIso {k : Type u} [Field k]
    (P Q : SplitBorelPair k) (D : AttachedDatum P) (E : AttachedDatum Q)
    (f : P.G.val ≅ Q.G.val) : Nonempty (BasedIso D.toBased E.toBased) := by
  obtain ⟨F, t, b, ht, hb⟩ := alignPairs P Q f
  obtain ⟨P', Q', hP, hQ, ⟨f'⟩⟩ := pinAlignedPairs P Q (standardAdditiveLine k) F t ht b hb
  subst P
  subst Q
  exact ⟨inducedBasedIso f' D E⟩

/-- The integral model of the first pair has the same full based datum in every
field fibre. Classification identifies the scalar extension with that fibre. -/
private theorem basedIsoOfScalarExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
    (P : SplitBorelPair k) (D : AttachedDatum P)
    (Q : SplitBorelPair K) (E : AttachedDatum Q)
    (f : (groupBaseChange k K).obj P.G.val ≅ Q.G.val) :
    Nonempty (BasedIso D.toBased E.toBased) := by
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨_, F, i, _, _, _, _, _, _⟩ := M.fieldFibre k
  obtain ⟨_, F', j, _, _, _, _, _, _⟩ := M.fieldFibre K
  obtain ⟨e⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 k).2.1
    P F.pinned.pair D F.attached).mpr ⟨F.datumIso.val⟩
  let a := (groupBaseChange k K).mapIso (i ≪≫ e.symm)
  let b := j.symm ≪≫ (fibreTowerIso k K).app M.group ≪≫ a ≪≫ f
  obtain ⟨g⟩ := basedIsoOfGroupIso F'.pinned.pair Q F'.attached E b
  exact ⟨show D.toBased ⟶ E.toBased from F'.datumIso ≫ g⟩

theorem geometricApplicability : GeometricApplicability.{u} := by
  intro k S _ _ _ _ n G hG
  obtain ⟨Q, E, hQ, ⟨c⟩⟩ := hG
  have hGeo : IsReductive (GeometricGroup G) := hQ ▸ Q.reductive
  have hSmooth : Smooth G.val.X.hom :=
    (smooth_baseChange_iff (K := AlgebraicClosure k) G.val.X).mp hGeo.1
  let := hGeo.2.1
  have hc : ConnectedSpace (GeometricGroup G).val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (GeometricGroup G).val.X.hom
  let : ConnectedSpace G.val.X.left := (connected_baseChange_iff (K := AlgebraicClosure k) G).mp hc
  have hR := (Reductive.RadicalBaseChange.reductiveFieldExtension G hSmooth
    (geometricallyConnected_of_connected G)).mp hGeo
  obtain ⟨P, hP⟩ := separableBorelPair (S := S) G hR
  let D := Classification.Pinning.attachedDatum P
  let K := AlgebraicClosure k
  let i : S →ₐ[k] K := IsAlgClosed.lift
  let : Algebra S K := i.toRingHom.toAlgebra
  let : IsScalarTower k S K := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hP' : P.G.val = (groupBaseChange k S).obj G.val := congrArg Subtype.val hP
  have hQ' : Q.G.val = (groupBaseChange k K).obj G.val := congrArg Subtype.val hQ
  let f : (groupBaseChange S K).obj P.G.val ≅ Q.G.val :=
    (groupBaseChange S K).mapIso (eqToIso hP') ≪≫
      ((groupBaseChangeTower (K := S) K).app G.val).symm ≪≫ eqToIso hQ'.symm
  obtain ⟨e⟩ := basedIsoOfScalarExtension P D Q E f
  exact ⟨P, D, ⟨transportCoordinates e c⟩, ⟨eqToIso hP'.symm⟩⟩

private theorem matrixBasedCoordinates {k : Type u} [Field k] (n : ℕ)
    (H : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj H.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))) :
    ∃ (A : AdditiveLine k) (P : PinnedGroup A) (D : AttachedDatum P.pair),
      P.pair.G = H ∧ Nonempty (TypeCCoordinates n D.toBased) := by
  obtain ⟨P, hP, _, D, X, Y, r, _, _, A, U, pin, _, _, _, _, _, _, _, _, hp, _, _, _,
    hr, _, _, _, _, hs, _⟩ := RootData.SymplecticDatum.basedComputation k n H c
  let J : PinnedGroup A := ⟨P, U, pin⟩
  refine ⟨A, J, D, hP, ⟨⟨X, Y, r, ?_, fun a => (hr a).1, fun a => (hr a).2, hs⟩⟩⟩
  let := D.comm
  intro x y
  exact (D.datum.pairing_eq (Additive.toMul x) (Additive.toMul y)).trans
    (hp (Additive.toMul x) (Additive.toMul y))

open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)
open private torusIso_of_isIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem geometricCorootSpan {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (P : SplitBorelPair (AlgebraicClosure k)) (D : AttachedDatum P)
    (hP : P.G = GeometricGroup G) : D.toBased.datum.corootSpan ℤ = ⊤ := by
  let := D.comm
  have hGeom : IsSemisimple (GeometricGroup G) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  have hPs : IsSemisimple P.G := hP.symm ▸ hGeom
  obtain ⟨Q, E, f, τ, hQ, _, hf, hτ, _, eY, heY⟩ :=
    Classification.SimplyConnectedLattice.splitCover P.G hPs P.T P.split P.maximal D.datum
  let := E.comm
  have : IsIso f := by
    unfold GeometricallySimplyConnected at hSC
    rw [← hP] at hSC
    exact hSC Q.G hQ f hf
  have : IsIso τ := torusIso_of_isIso Q P f τ hτ
  change corootLatticeOf D.datum = ⊤
  apply eq_top_iff.mpr
  intro y _
  have hy := (eY (Additive.ofMul (y.toMul ≫ inv τ))).property
  rwa [heY, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hy

theorem geometricTypeCFromCartan : GeometricTypeCFromCartan.{u} := by
  intro k _ n G hG hSC ht
  obtain ⟨P, D, hP, s, hs⟩ := ht
  let K := AlgebraicClosure k
  let H := symplecticGroup K (HyperbolicIndex.{u} (n + 1))
  obtain ⟨_, Q, E, _, ⟨c⟩⟩ :=
    matrixBasedCoordinates n H (symplecticGroupPointsIso K (HyperbolicIndex.{u} (n + 1)))
  let t := simpleIndex c
  have hCartan (i j : Fin (n + 1)) :
      E.toBased.datum.pairing (t i) (t j) = cartanEntry n j i := by
    change E.toBased.datum.pairing (c.roots (simpleLabel i)) (c.roots (simpleLabel j)) = _
    rw [← RootPairing.root_coroot_eq_pairing, c.pairing, c.root, c.coroot]
    exact cartan_formula i j
  have h (a b : ↥D.toBased.base.support) :
      E.toBased.datum.pairing ((s.symm.trans t) a) ((s.symm.trans t) b) =
        D.toBased.datum.pairing a b := by
    obtain ⟨i, rfl⟩ := s.surjective a
    obtain ⟨j, rfl⟩ := s.surjective b
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using (hCartan i j).trans (hs j i).symm
  let e := basedIsoFromCartan (geometricCorootSpan G hG hSC P D hP)
    (corootSpanOfCoordinates c) (s.symm.trans t) h
  exact ⟨P, D, hP, ⟨transportCoordinates e c⟩⟩

private theorem finiteLevelSchemeIso {k S : Type u} [Field k] [Field S] [Algebra k S]
    [IsSepClosure k S] (H G : AffineAlgebraicGroup k)
    (f : (groupBaseChange k S).obj H.val ≅ (groupBaseChange k S).obj G.val) :
    ∃ L : FiniteGaloisIntermediateField k S,
      Nonempty ((groupBaseChange k L).obj H.val ≅ (groupBaseChange k L).obj G.val) := by
  obtain ⟨B, hB, ⟨g⟩⟩ := exists_coordinate_model H
  obtain ⟨C, hC, ⟨h⟩⟩ := exists_coordinate_model G
  let t := extendedGroupIso (k := k) S
  let i : specGroup (extendedHopf S B) ≅ specGroup (extendedHopf S C) :=
    t B ≪≫ (groupBaseChange k S).mapIso g ≪≫ f ≪≫
      ((groupBaseChange k S).mapIso h).symm ≪≫ (t C).symm
  let i' := (spectrumIsoEquiv (extendedHopf S B) (extendedHopf S C)).symm i
  let L₀ : FiniteGaloisIntermediateField k S := ⊥
  obtain ⟨L, j, _, _⟩ := finiteLevelIsomorphisms B C hB hC L₀ i'
  let tL := extendedGroupIso (k := k) L
  exact ⟨L, ⟨((tL B) ≪≫ (groupBaseChange k L).mapIso g).symm ≪≫
    spectrumIso j ≪≫ (tL C) ≪≫ (groupBaseChange k L).mapIso h⟩⟩

theorem finiteSplitRecognition : FiniteSplitRecognition.{u} := by
  intro k S _ _ _ _ n G H c hType
  obtain ⟨P, D, ⟨d⟩, ⟨i⟩⟩ := hType
  let Hₛ := Specs.Unipotent.baseChangedAlgebraicGroup S H
  obtain ⟨A, Q, E, hQ, ⟨e⟩⟩ :=
    matrixBasedCoordinates n Hₛ (baseChangeSymplecticPointsIso S c)
  obtain ⟨U, ⟨p⟩⟩ := pinningsExist A P
  let P' : PinnedGroup A := ⟨P, U, p⟩
  obtain ⟨_, f, _⟩ := pinnedRecognition n Q P' E D e d
  have j : (groupBaseChange k S).obj H.val ≅ P.G.val := by
    have hf : Q.pair.G.val ≅ P.G.val := f.group
    rw [hQ] at hf
    exact hf
  exact finiteLevelSchemeIso H G (j ≪≫ i.symm)

theorem rankOneIdentification : Specs.SymplecticDatum.RankOneIdentification.{u} :=
  RootData.SymplecticDatum.rankOneIdentification

end Splitting

section Twisting

open Specs.AutomorphismSequence
open Specs.RootGroups (AdditiveLine)
open _root_.LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open _root_.LinearAlgebraicGroups.SymplecticMatrixStructure
  (symplecticGroup symplecticGroupPointsIso)
open Specs.RelativeFormComparison
open Specs.QuasiSplitInnerForms
open Specs.SchemeDerivedGroup (RepresentsQuotient)
open Specs.SymplecticDatumAdjointDescent (GroupPoints)
open Specs.SymplecticDatum (MatrixAlgebra adjoint conjugateMatrix)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle pointAction)
open _root_.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
  (automorphismSequences splitKernel liftInnerCocycle)
open _root_.LinearAlgebraicGroups.Descent.RelativeFormComparison (schemeIsomorphismComparison)
open private groupSectionsMap groupSections_isSheaf groupSectionsMap_locallySurjective
  descends_iso_of_locallySurjective projection_eq_one_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open _root_.LinearAlgebraicGroups.Descent.AutomorphismSequence (innerAut_eq_one_iff)
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Both projections identify sections up to the identical scheme centre. -/
private theorem adjointComparison {H Q : AffineAlgebraicGroup k} (V : AdjointQuotient H)
    (Z : ClosedSubgroup H.val) (q : H.val ⟶ Q.val)
    (hZ : CentralTorus.IsSchemeCentre Z) (hk : IsSchemeKernel q Z)
    (hRep : RepresentsQuotient Z q) :
    ∃ e : groupSections V.quotient.val ≅ groupSections Q.val,
      groupSectionsMap V.projection ≫ e.hom = groupSectionsMap q := by
  have hloc : Presheaf.IsLocallySurjective (fppfOver k) (groupSectionsMap q) := by
    obtain ⟨e, he⟩ := hRep
    have : Sheaf.IsLocallySurjective (Specs.rightQuotientProjection Z) :=
      LinearAlgebraicGroups.rightQuotientLocalLifts Z
    have h : Sheaf.IsLocallySurjective ((fppfOver k).uliftYoneda.{u+1}.map q.hom.hom) := by
      rw [← he]
      infer_instance
    constructor
    intro U a
    let a' : ((fppfOver k).uliftYoneda.{u+1}.obj Q.val.X).obj.obj (op U) := ⟨a.down⟩
    refine (fppfOver k).superset_covering ?_ (h.imageSieve_mem a')
    intro W b hb
    obtain ⟨x, hx⟩ := hb
    exact ⟨⟨x.down⟩, ULift.ext (congrArg ULift.down hx)⟩
  refine descends_iso_of_locallySurjective (groupSectionsMap V.projection) (groupSectionsMap q)
    (Iso.refl _) (groupSectionsMap_locallySurjective V.projection V.fppf) hloc
    (groupSections_isSheaf _) (groupSections_isSheaf _) ?_
  intro U x y
  rw [← div_eq_one (a := (groupSectionsMap V.projection).app U x), ← map_div]
  change (groupSectionsMap V.projection).app U (x / y) = 1 ↔
    (groupSectionsMap q).app U x = (groupSectionsMap q).app U y
  rw [← div_eq_one (a := (groupSectionsMap q).app U x), ← map_div]
  let g : U.unop ⟶ H.val.X := (x / y).down
  change ULift.up (g ≫ V.projection.hom.hom) = ULift.up 1 ↔
    ULift.up (g ≫ q.hom.hom) = ULift.up 1
  rw [ULift.up_inj, ULift.up_inj]
  exact (projection_eq_one_iff V g).trans
    ((innerAut_eq_one_iff g).trans ((hZ _ g).trans (schemeKernel_sections hk g)))

open private restrict_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

local instance : TopologicalSpace (Gal(K/k)) := krullTopology k K
local instance (G : GroupScheme k) :
    TopologicalSpace (RelativeAut G (fieldTest k K)) := ⊥

private theorem restrictIso_comp {H G : GroupScheme k} {U V W : SchemeOver k}
    (a : U ⟶ V) (b : V ⟶ W) (i : relativePoints H W ≅ relativePoints G W) :
    restrictIso (a ≫ b) i = restrictIso a (restrictIso b i) := by
  apply Iso.ext
  rfl

set_option maxHeartbeats 1000000 in
private theorem transportedAut_mul {H G : GroupScheme k}
    (i : relativePoints H (fieldTest k K) ≅ relativePoints G (fieldTest k K))
    (σ τ : Gal(K/k)) :
    transportedAut k K i (σ * τ) =
      transportedAut k K i σ * automorphismAction k K H σ (transportedAut k K i τ) := by
  let r := fieldMap k K σ
  let s := fieldMap k K τ
  have hσ : (transportedAut k K i σ).asIso = restrictIso r i ≪≫ i.symm := rfl
  have hτ : (automorphismAction k K H σ (transportedAut k K i τ)).asIso =
      restrictIso r (restrictIso s i ≪≫ i.symm) := rfl
  have hmul : (transportedAut k K i (σ * τ)).asIso =
      restrictIso (r ≫ s) i ≪≫ i.symm := by
    change restrictIso (fieldMap k K (σ * τ)) i ≪≫ i.symm = _
    rw [fieldMap_mul]
  apply Aut.ext
  rw [Aut.mul_asIso, hσ, hτ, hmul, restrictIso_comp, restrict_trans]
  have hsymm : restrictIso r i.symm = (restrictIso r i).symm := by
    apply Iso.ext
    rfl
  rw [hsymm]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem transportedAut_cocycle {H G : GroupScheme k} [FiniteDimensional k K]
    (i : relativePoints H (fieldTest k K) ≅ relativePoints G (fieldTest k K)) :
    ∃ a : Cocycle (automorphismAction k K H), ∀ σ, a σ = transportedAut k K i σ := by
  have hc : Continuous (transportedAut k K i) := continuous_of_discreteTopology
  exact ⟨⟨transportedAut k K i, hc, transportedAut_mul i⟩, fun _ => rfl⟩

private theorem matrixPoint_inner {I : Type u} [Fintype I] [DecidableEq I]
    {H Q : AffineAlgebraicGroup k} {q : H.val ⟶ Q.val}
    (c : (groupPointsFunctor k).obj H.val ≅ symplecticPoints k I)
    (inn : groupSections Q.val ⟶ automorphisms H.val)
    (hinn : ∀ (S : SchemeOver k) (g : S ⟶ H.val.X),
      inn.app (op S) ⟨g ≫ q.hom.hom⟩ = innerAut g)
    (action : ∀ R : TestAlgebra k, GroupPoints Q.val R →*
        (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R))
    (hMap : ∀ (R S : TestAlgebra k) (b : R ⟶ S) (a : GroupPoints Q.val R) X,
      (action R a X).map b.hom = action S (((groupPointsFunctor k).obj Q.val).map b a)
        (X.map b.hom))
    (hAction : ∀ (R : TestAlgebra k) (g : GroupPoints H.val R) X,
      action R (((groupPointsFunctor k).map q).app R g) X = conjugateMatrix (c.hom.app R g) X)
    (hLift : ∀ (R : TestAlgebra k) (a : GroupPoints Q.val R),
      ∃ (S : TestAlgebra k) (b : R ⟶ S) (g : GroupPoints H.val S),
        b.hom.toRingHom.FaithfullyFlat ∧ b.hom.toRingHom.FinitePresentation ∧
        ((groupPointsFunctor k).map q).app S g = ((groupPointsFunctor k).obj Q.val).map b a)
    {V : SchemeOver k} (R : TestAlgebra k) (ρ : (testSpec k).obj (op R) ⟶ V)
    (a : V ⟶ Q.val.X) (g : GroupPoints H.val R) :
    let h := ((inn.app (op V) ⟨a⟩).asIso.hom.app (op (Over.mk ρ))).hom g
    (show PointGroup I R from c.hom.app R h).val =
      action R (ρ ≫ a) (show PointGroup I R from c.hom.app R g).val := by
  let T := (testSpec k).obj (op R)
  let U := Over.mk ρ
  let F := (inn.app (op V) ⟨a⟩).asIso.hom
  let h : GroupPoints H.val R := (F.app (op U)).hom g
  obtain ⟨S, b, l, hb, _, hl⟩ := hLift R (ρ ≫ a)
  let β : (testSpec k).obj (op S) ⟶ T := (testSpec k).map b.op
  let U' := Over.mk (β ≫ ρ)
  let j : U' ⟶ U := Over.homMk β
  have he := ConcreteCategory.congr_hom (F.naturality j.op) g
  change (F.app (op U')).hom (β ≫ g) = β ≫ h at he
  have hn := ConcreteCategory.congr_hom (inn.naturality (β ≫ ρ).op)
    (ULift.up a : (groupSections Q.val).obj (op V))
  change inn.app (op ((testSpec k).obj (op S))) ⟨(β ≫ ρ) ≫ a⟩ =
    restrictAut (β ≫ ρ) (inn.app (op V) ⟨a⟩) at hn
  have hl' : l ≫ q.hom.hom = (β ≫ ρ) ≫ a := by
    change l ≫ q.hom.hom = β ≫ (ρ ≫ a) at hl
    exact hl.trans (Category.assoc _ _ _).symm
  let l₀ : (testSpec k).obj (op S) ⟶ H.val.X := l
  have hn' : innerAut l₀ =
      restrictAut (β ≫ ρ) (inn.app (op V) ⟨a⟩) :=
    ((hinn _ l).symm.trans (congrArg (fun a : (testSpec k).obj (op S) ⟶ Q.val.X =>
      inn.app (op ((testSpec k).obj (op S))) ⟨a⟩) hl')).trans hn
  let Uid := Over.mk (𝟙 ((testSpec k).obj (op S)))
  have hv := congrArg
    (fun d : RelativeAut H.val ((testSpec k).obj (op S)) =>
      (d.asIso.hom.app (op Uid)).hom (β ≫ g)) hn'
  change l₀ * (β ≫ g) * l₀⁻¹ = (F.app (op U')).hom (β ≫ g) at hv
  have hh : β ≫ h = l₀ * (β ≫ g) * l₀⁻¹ := he.symm.trans hv.symm
  have hc (x : GroupPoints H.val R) :
      ((show PointGroup I R from c.hom.app R x).val).map b.hom =
        (show PointGroup I S from c.hom.app S (β ≫ x)).val := by
    exact congrArg Subtype.val (ConcreteCategory.congr_hom (c.hom.naturality b) x).symm
  let mat (T : TestAlgebra k) : GroupPoints H.val T →* PointGroup I T :=
    (c.hom.app T).hom
  change (mat R h).val = action R (ρ ≫ a) (mat R g).val
  suffices heq : (mat R h).val.map b.hom =
      (action R (ρ ≫ a) (mat R g).val).map b.hom by
    apply Matrix.ext
    intro p r
    exact hb.injective (congrArg (fun M => M p r) heq)
  calc
    _ = (mat S (β ≫ h)).val := hc h
    _ = (mat S (l₀ * (β ≫ g) * l₀⁻¹)).val :=
      congrArg (fun x : (testSpec k).obj (op S) ⟶ H.val.X => (mat S x).val) hh
    _ = conjugateMatrix (mat S l) (mat S (β ≫ g)).val := by
      let v : GroupPoints H.val S := β ≫ g
      have hm : mat S (l * v * l⁻¹) = mat S l * mat S v * (mat S l)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      exact congrArg Subtype.val hm
    _ = action S (((groupPointsFunctor k).map q).app S l) (mat S (β ≫ g)).val :=
      (hAction S l _).symm
    _ = action S (((groupPointsFunctor k).obj Q.val).map b (ρ ≫ a))
          ((mat R g).val.map b.hom) :=
      congrArg₂ (fun z X => action S z X) hl (hc g).symm
    _ = _ := (hMap R S b _ _).symm

private theorem liftMatrixCocycle {H Q : AffineAlgebraicGroup k} [FiniteDimensional k K]
    {A : AdditiveLine k} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hD : ∀ d : Aut D.toBased, d = 1)
    (l : Aut D.toBased ≃* Aut P) (V : AdjointQuotient P.pair.G)
    (E : SplitSequence P D l V)
    (Z : ClosedSubgroup P.pair.G.val) (q : P.pair.G.val ⟶ Q.val)
    (hz : CentralTorus.IsSchemeCentre Z) (hk : IsSchemeKernel q Z)
    (hRep : RepresentsQuotient Z q)
    (i : relativePoints P.pair.G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K)) :
    ∃ (inn : groupSections Q.val ⟶ automorphisms P.pair.G.val)
      (d : @Cocycle (Gal(K/k)) (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
        k K Q.val.X) _ (krullTopology k K) _ ⊥ (pointAction k K Q.val.X)),
      (∀ (S : SchemeOver k) (g : S ⟶ P.pair.G.val.X),
        inn.app (op S) ⟨g ≫ q.hom.hom⟩ = innerAut g) ∧
      ∀ σ, inn.app (op (fieldTest k K)) ⟨d σ⟩ = transportedAut k K i σ := by
  obtain ⟨e, he⟩ := adjointComparison V Z q hz hk hRep
  let inn := e.inv ≫ E.inner
  have inverse (S : SchemeOver k) (z : (groupSections V.quotient.val).obj (op S)) :
      e.inv.app (op S) (e.hom.app (op S) z) = z :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id (op S)) z
  have hLift (S : SchemeOver k) (g : S ⟶ P.pair.G.val.X) :
      inn.app (op S) ⟨g ≫ q.hom.hom⟩ = innerAut g := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app he (op S)) (ULift.up g)
    change e.hom.app (op S) ⟨g ≫ V.projection.hom.hom⟩ = ⟨g ≫ q.hom.hom⟩ at h
    change E.inner.app (op S) (e.inv.app (op S) ⟨g ≫ q.hom.hom⟩) = _
    exact (congrArg (E.inner.app (op S)) ((congrArg (e.inv.app (op S)) h.symm).trans
      (inverse S _))).trans (E.onLift S g)
  let T := fieldTest k K
  have hInj : Function.Injective (inn.app (op T)) :=
    (E.innerInjective (op T)).comp ((e.app (op T)).symm.groupIsoToMulEquiv.injective)
  obtain ⟨a, ha⟩ := transportedAut_cocycle i
  have hRange (σ : Gal(K/k)) : a σ ∈ (inn.app (op T)).hom.range := by
    obtain ⟨b, hb⟩ := (splitKernel E (a σ)).1 (hD _)
    refine ⟨e.hom.app (op T) b, ?_⟩
    change E.inner.app (op T) (e.inv.app (op T) (e.hom.app (op T) b)) = _
    exact (congrArg (E.inner.app (op T)) (inverse T b)).trans hb
  obtain ⟨d, hd, _⟩ := liftInnerCocycle _ _ inn hInj a hRange
  exact ⟨inn, d, hLift, fun σ => (hd σ).trans (ha σ)⟩

theorem twistingForTrivialization : TwistingForTrivialization.{u} := by
  intro k K _ _ _ _ _ n G H c f
  obtain ⟨A, P, D, hP, ⟨C⟩⟩ := matrixBasedCoordinates n H c
  -- Use the same underlying scheme throughout the F06 sequence and the
  -- action of the matrix adjoint quotient.
  subst H
  obtain ⟨D', l, V, E, _, _⟩ := automorphismSequences P
  let e : D.toBased ≅ D'.toBased :=
    (Groupoid.isoEquivHom (X := D.toBased) (Y := D'.toBased)).symm
      (inducedBasedIso (PinnedIso.refl P) D D')
  have hD' (d : Aut D'.toBased) : d = 1 := by
    apply (Aut.autMulEquivOfIso e.symm).injective
    rw [map_one]
    exact basedRigidity n D.toBased C _
  obtain ⟨j, hj⟩ := schemeIsomorphismComparison (k := k) (S := K) P.pair.G.val G.val
  let i := j f
  have hi : IsInduced k K f i := (hj f i).2 rfl
  obtain ⟨Z, Q, q, hz, hz', hk, hRep, hLift, action, _, _, hAdj, hMap, hAction, _⟩ :=
    RootData.SymplecticDatum.adjointQuotientAction k (HyperbolicIndex.{u} (n + 1)) P.pair.G c
  obtain ⟨inn, d, hInner, hd⟩ := liftMatrixCocycle P D' hD' l V E Z q hz hk hRep i
  refine ⟨⟨i, hi, Z, hz, hz', Q, q, hk, hRep, d, action, hAdj, hMap, hAction, ?_⟩⟩
  intro σ R g
  dsimp only
  rw [← hd σ]
  exact matrixPoint_inner c inn hInner action hMap hAction hLift
    ((restrictTestAlgebra k K).obj R) (sliceTest (k := k) R).hom (d σ) g

theorem typeCSplitRecognition : Specs.TypeCSplitRecognition.Statement.{u} := by
  intro k S _ _ _ _ n G hType
  let H := symplecticGroup k (HyperbolicIndex.{u} (n + 1))
  let c := symplecticGroupPointsIso k (HyperbolicIndex.{u} (n + 1))
  obtain ⟨L, ⟨f⟩⟩ :=
    finiteSplitRecognition (S := S) n G H c (geometricApplicability (S := S) n G hType)
  exact ⟨H, c, L, f, twistingForTrivialization n G H c f⟩

theorem typeCSplitRecognitionFromCartan : StatementFromCartan.{u} := by
  intro k S _ _ _ _ n G hG hSC hType
  exact typeCSplitRecognition (S := S) n G (geometricTypeCFromCartan n G hG hSC hType)

end Twisting

end

end LinearAlgebraicGroups.TypeCSplitRecognition
