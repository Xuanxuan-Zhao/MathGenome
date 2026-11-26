import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedGroupComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedPairCompatibility
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (BasedRootDatum)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.PinnedPairDescent (DescendedPair)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalPinnedBaseChange (ExtendsDiagram)
open Specs.ExceptionalValuedTorusNormalizer
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

universe u

open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open private quadraticAut_cases from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

section Diagram

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  {σ : Gal(L/F)} {β : Gal(K/k)} {e : (L ⊗[F] k) ≃ₐ[F] K}

/-- The compositum embedding of the original diagram field. -/
def diagramEmbedding (e : (L ⊗[F] k) ≃ₐ[F] K) : L →ₐ[F] K :=
  e.toAlgHom.comp Algebra.TensorProduct.includeLeft

omit [IsScalarTower F k K] in
theorem diagramEmbedding_equivariant (h : ExtendsDiagram F L k K σ β e) (x : L) :
    β (diagramEmbedding e x) = diagramEmbedding e (σ x) :=
  h.2 x

omit [IsScalarTower F k K] in
theorem tensorDiagram_equivariant (h : ExtendsDiagram F L k K σ β e) (x : L ⊗[F] k) :
    β (e x) = e (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F k) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hs (w : L) : (w ⊗ₜ[F] (1 : k)) * ((1 : L) ⊗ₜ[F] y) = w ⊗ₜ[F] y := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    calc
      β (e (z ⊗ₜ[F] y)) = β (e (z ⊗ₜ[F] (1 : k))) *
          β (e ((1 : L) ⊗ₜ[F] y)) := by rw [← hs z, map_mul, map_mul]
      _ = e ((σ z) ⊗ₜ[F] y) := by rw [h.2, h.1, AlgEquiv.commutes, ← h.1, ← map_mul, hs]
  | add x y hx hy => simp only [map_add, hx, hy]

end Diagram

section Quadratic

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra k K] [FiniteDimensional F L] [FiniteDimensional k K]
  [IsGalois F L] [IsGalois k K]

/-- A quadratic diagram action is determined by its nonidentity automorphism. -/
noncomputable def quadraticDiagramEquiv (hL : Module.finrank F L = 2) (hK : Module.finrank k K = 2)
    {σ : Gal(L/F)} {β : Gal(K/k)} (hσ : σ ≠ 1) (hβ : β ≠ 1) :
    Gal(K/k) ≃* Gal(L/F) := by
  classical
  have hσσ : σ * σ = 1 := by
    rcases quadraticAut_cases hL σ hσ (σ * σ) with h | h
    · exact h
    · exact (hσ (mul_right_cancel (h.trans (one_mul σ).symm))).elim
  have hββ : β * β = 1 := by
    rcases quadraticAut_cases hK β hβ (β * β) with h | h
    · exact h
    · exact (hβ (mul_right_cancel (h.trans (one_mul β).symm))).elim
  let f (a : Gal(K/k)) := if a = 1 then 1 else σ
  let g (a : Gal(L/F)) := if a = 1 then 1 else β
  exact {
    toFun := f
    invFun := g
    left_inv := fun a => by
      rcases quadraticAut_cases hK β hβ a with rfl | rfl <;> simp [f, g, hσ, hβ]
    right_inv := fun a => by
      rcases quadraticAut_cases hL σ hσ a with rfl | rfl <;> simp [f, g, hσ, hβ]
    map_mul' := fun a b => by
      rcases quadraticAut_cases hK β hβ a with ha | ha <;>
        rcases quadraticAut_cases hK β hβ b with hb | hb <;>
        simp [f, ha, hb, hσσ, hββ, hβ] }

theorem quadraticDiagramEquiv_apply (hL : Module.finrank F L = 2)
    (hK : Module.finrank k K = 2) {σ : Gal(L/F)} {β : Gal(K/k)} (hσ : σ ≠ 1)
    (hβ : β ≠ 1) : quadraticDiagramEquiv hL hK hσ hβ β = σ := by
  simp [quadraticDiagramEquiv, hβ]

end Quadratic

section CoefficientPoints

open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private extensionPointEquiv extensionPoint_normalizes
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {F k : Type u} [Field F] [Field k] [Algebra F k]

private theorem normalizes_coefficient_iff (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val)
    (g : 𝟙_ (SchemeOver k) ⟶ ((groupBaseChange F k).obj G.val).X) :
    Normalizes ((groupBaseChange F k).map T.inclusion) g ↔
      Normalizes T.inclusion (extensionPointEquiv G.val g) := by
  obtain ⟨N, hN⟩ := normalizerScheme F G T
  exact (extensionPoint_normalizes T N hN g).trans (hN _ _).symm

private theorem normalizes_groundSections_iff (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val)
    (x : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    Normalizes T.inclusion ((groundIso (k := F)).hom ≫ x) ↔ Normalizes T.inclusion x := by
  obtain ⟨N, hN⟩ := normalizerScheme F G T
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (hN _ _).mp hx
    exact (hN _ _).mpr ⟨(groundIso (k := F)).inv ≫ n, by
      rw [Category.assoc, hn, Iso.inv_hom_id_assoc]⟩
  · intro hx
    obtain ⟨n, hn⟩ := (hN _ _).mp hx
    exact (hN _ _).mpr ⟨(groundIso (k := F)).hom ≫ n, by rw [Category.assoc, hn]⟩

/-- Once the largest split subtorus in the marked torus survives extension, its
scheme centralizer and the comparison on actual coefficient points follow. -/
theorem splitMaximal_of_extendedLargest
    (G : AffineAlgebraicGroup F) (S T : ClosedSubgroup G.val)
    (hs : IsSplitTorus S.group) (hST : IsSubgroupOf S T) (hZ : IsCentralizer S T)
    (hS : IsClosedImmersion ((groupBaseChange F k).map S.inclusion).hom.hom.left)
    (hT : IsClosedImmersion ((groupBaseChange F k).map T.inclusion).hom.hom.left)
    (hlargest : ∀ U : ClosedSubgroup ((groupBaseChange F k).obj G.val),
      IsSplitTorus U.group → IsSubgroupOf U (baseChangedSubgroup k T hT) →
        IsSubgroupOf U (baseChangedSubgroup k S hS)) :
    IsMaximalSplitTorus (baseChangedSubgroup k S hS) ∧
      ∀ g : Specs.AdjointRepresentation.GroupPoints G.val (CommAlgCat.of F k),
        Normalizes S.inclusion g ↔ Normalizes T.inclusion g := by
  let Sk := baseChangedSubgroup k S hS
  let Tk := baseChangedSubgroup k T hT
  obtain ⟨_, hC⟩ := centralizerSchemeBaseChange F k S.inclusion T hZ
  have hCk : IsCentralizer Sk Tk := hC
  obtain ⟨j, hj⟩ := hST
  have hjk : IsSubgroupOf Sk Tk :=
    ⟨(groupBaseChange F k).map j, by
      change (groupBaseChange F k).map j ≫ (groupBaseChange F k).map T.inclusion = _
      rw [← Functor.map_comp, hj]
      rfl⟩
  obtain ⟨hM, hN⟩ := ExceptionalValuedTorusNormalizer.centralizingSplitTorusNormalizer
    (baseChangedAlgebraicGroup k G) Tk Sk (splitTorus_baseChange hs) hjk hCk hlargest
  refine ⟨hM, ?_⟩
  intro g
  obtain ⟨x, rfl⟩ := (extensionPointEquiv (K := k) G.val).surjective g
  exact (normalizes_coefficient_iff G S x).symm.trans ((hN x).trans (normalizes_coefficient_iff G T x))

end CoefficientPoints

section CoefficientHopf

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.AdjointCocharacters renaming coordinateHopf → pairCoordinates
open Specs.AdjointBorelCohomology (PermutedCharacterBasis)
open Specs.CharacterDescent (GeometricCharacters IsDiagonalizable)
open _root_.LinearAlgebraicGroups.CharacterDescent
  (extendedHopfTower extendedHopfFunctor baseChangeCharacterMap baseChangeCharacterMap_bijective)
open private extendedHopfTower_apply extendedHopfTower_symm_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

attribute [local simp] extendedHopfTower_apply extendedHopfTower_symm_apply

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [Algebra L K]
  [IsScalarTower F k K] [IsScalarTower F L K]

private noncomputable def coefficientHopfComparison (A : HopfAlgebraCategory F) :
    extendedHopf K (extendedHopf L A) ≅ extendedHopf K (extendedHopf k A) :=
  extendedHopfTower (K := L) K A ≪≫ (extendedHopfTower (K := k) K A).symm

private noncomputable abbrev raiseDiagramElement (A : HopfAlgebraCategory F) (x : extendedHopf L A) :
    extendedHopf K (extendedHopf k A) :=
  (coefficientHopfComparison A).hom.hom ((1 : K) ⊗ₜ[L] x)

private theorem raiseDiagramElement_tmul (A : HopfAlgebraCategory F) (z : L) (x : A) :
    raiseDiagramElement A (z ⊗ₜ[F] x) =
      (algebraMap L K z) ⊗ₜ[k] ((1 : k) ⊗ₜ[F] x) := by
  change (extendedHopfTower (K := k) K A).inv.hom
    ((extendedHopfTower (K := L) K A).hom.hom ((1 : K) ⊗ₜ[L] (z ⊗ₜ[F] x))) = _
  rw [extendedHopfTower_apply, extendedHopfTower_symm_apply, Algebra.smul_def, mul_one]

private theorem raiseDiagramElement_equivariant
    (A : HopfAlgebraCategory F) (σ : Gal(L/F)) (β : Gal(K/k))
    (h : ∀ z, β (algebraMap L K z) = algebraMap L K (σ z))
    (x : extendedHopf L A) :
    (SemilinearAction.scalarExtension (K := K) (extendedHopf k A)).act β
      (raiseDiagramElement A x) =
    raiseDiagramElement A ((SemilinearAction.scalarExtension (K := L) A).act σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    change _ = raiseDiagramElement A (σ z ⊗ₜ[F] x)
    rw [raiseDiagramElement_tmul, raiseDiagramElement_tmul]
    change (β (algebraMap L K z)) ⊗ₜ[k] ((1 : k) ⊗ₜ[F] x) = _
    rw [h]
  | add x y hx hy => simpa only [raiseDiagramElement, TensorProduct.tmul_add, map_add] using (congrArg₂ (· + ·) hx hy)

private theorem raiseDiagramElement_natural {A B : HopfAlgebraCategory F}
    (f : A ⟶ B) (x : extendedHopf L A) :
    (extendedHopfMap K (extendedHopfMap k f)).hom (raiseDiagramElement A x) =
      raiseDiagramElement B ((extendedHopfMap L f).hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    change _ = raiseDiagramElement B (z ⊗ₜ[F] f.hom x)
    rw [raiseDiagramElement_tmul, raiseDiagramElement_tmul]
    rfl
  | add x y hx hy => simpa only [raiseDiagramElement, TensorProduct.tmul_add, map_add] using (congrArg₂ (· + ·) hx hy)

open private groupLikeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private noncomputable def raisedCharacterEquiv (A : HopfAlgebraCategory F)
    (h : IsDiagonalizable (extendedHopf L A)) :
    GeometricCharacters L A ≃* GeometricCharacters K (extendedHopf k A) :=
  (MulEquiv.ofBijective (baseChangeCharacterMap K (extendedHopf L A))
    (baseChangeCharacterMap_bijective K (extendedHopf L A) h)).trans
      (groupLikeIso (coefficientHopfComparison A))

private theorem raisedCharacterEquiv_apply (A : HopfAlgebraCategory F)
    (h : IsDiagonalizable (extendedHopf L A)) (x : GeometricCharacters L A) :
    (raisedCharacterEquiv (k := k) (K := K) A h x).val = raiseDiagramElement A x.val := rfl

private noncomputable def raisedCharacterBasis {I : Type u} (A : HopfAlgebraCategory F)
    (h : IsDiagonalizable (extendedHopf L A))
    (b : Module.Basis I ℤ (Additive (GeometricCharacters L A))) :
    Module.Basis I ℤ (Additive (GeometricCharacters K (extendedHopf k A))) :=
  b.map (raisedCharacterEquiv (k := k) (K := K) A h).toAdditive.toIntLinearEquiv

private theorem raisedCharacterBasis_apply {I : Type u} (A : HopfAlgebraCategory F)
    (h : IsDiagonalizable (extendedHopf L A))
    (b : Module.Basis I ℤ (Additive (GeometricCharacters L A))) (i : I) :
    (raisedCharacterBasis (k := k) (K := K) A h b i).toMul.val = raiseDiagramElement A (b i).toMul.val := by
  rw [raisedCharacterBasis, Module.Basis.map_apply]
  exact raisedCharacterEquiv_apply (k := k) (K := K) A h (b i).toMul

private theorem raisedBasis_permutation {I : Type u} (A : HopfAlgebraCategory F)
    (h : IsDiagonalizable (extendedHopf L A))
    (b : Module.Basis I ℤ (Additive (GeometricCharacters L A)))
    (α : Gal(K/k) →* Gal(L/F))
    (hα : ∀ tau z, tau (algebraMap L K z) = algebraMap L K (α tau z))
    (r : Gal(L/F) →* Equiv.Perm I)
    (hr : ∀ σ i, (SemilinearAction.scalarExtension (K := L) A).act σ (b i).toMul.val =
      (b (r σ i)).toMul.val) :
    ∀ tau i, (SemilinearAction.scalarExtension (K := K) (extendedHopf k A)).act tau
      (raisedCharacterBasis (k := k) (K := K) A h b i).toMul.val =
      (raisedCharacterBasis A h b ((r.comp α) tau i)).toMul.val := by
  intro tau i
  rw [raisedCharacterBasis_apply, raisedCharacterBasis_apply, raiseDiagramElement_equivariant
    A (α tau) tau (hα tau), hr]
  rfl

open private splitBaseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private baseHom_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private presentationIso presentationIso_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private extendedCoordinateIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private coordinatePresentationMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private specGroupMap_comp tensorMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private noncomputable def orbitIndicesEquiv {I : Type u}
    (r : Gal(L/F) →* Equiv.Perm I) (a : Gal(K/k) ≃* Gal(L/F)) :
    OrbitIndices r ≃ OrbitIndices (r.comp a.toMonoidHom) :=
  Quotient.congrRight (fun i j => show (∃ σ, r σ j = i) ↔ (∃ β, r (a β) j = i) from
    ⟨fun ⟨σ, h⟩ => ⟨a.symm σ, by simpa only [MulEquiv.apply_symm_apply] using h⟩,
      fun ⟨β, h⟩ => ⟨a β, h⟩⟩)

omit [Algebra F k] [Algebra F K] [Algebra L K] [IsScalarTower F k K] [IsScalarTower F L K] in
private theorem orbitIndicesEquiv_apply {I : Type u}
    (r : Gal(L/F) →* Equiv.Perm I) (a : Gal(K/k) ≃* Gal(L/F)) (i : I) :
    orbitIndicesEquiv r a (orbitIndex r i) = orbitIndex (r.comp a.toMonoidHom) i := rfl

private theorem extendedDiagonalizable {A : HopfAlgebraCategory F}
    (h : IsDiagonalizable (extendedHopf L A)) :
    IsDiagonalizable (extendedHopf K (extendedHopf k A)) := by
  obtain ⟨M, ⟨j⟩⟩ := splitBaseChange (K := K) _ h
  exact ⟨M, ⟨j ≪≫ coefficientHopfComparison A⟩⟩

private theorem diagonalizable_of_iso {E : Type u} [Field E] {A B : HopfAlgebraCategory E}
    (e : A ≅ B) (h : IsDiagonalizable B) : IsDiagonalizable A := by
  obtain ⟨M, ⟨j⟩⟩ := h
  exact ⟨M, ⟨j ≪≫ e.symm⟩⟩

open Specs.DiagonalizableGroups (groupAlgebra)
open _root_.LinearAlgebraicGroups.CharacterDescent (groupAlgebraBaseChange)
open private extendedGroupIso_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private splitTorusCoordinateDiagonalizable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 2048 in
private theorem coefficientSplitSubtorusLargest [IsGalois k K]
    {I : Type u} [Finite I] {r : Gal(L/F) →* Equiv.Perm I} {G : AffineAlgebraicGroup F}
    (T : ClosedSubgroup G.val) (a : Gal(K/k) ≃* Gal(L/F))
    (ha : ∀ tau z, tau (algebraMap L K z) = algebraMap L K (a tau z))
    (c : PermutedCharacterBasis L I (closedSubgroupAlgebraicGroup T) r)
    (hc : IsDiagonalizable (extendedHopf L (pairCoordinates (closedSubgroupAlgebraicGroup T))))
    (q : pairCoordinates (closedSubgroupAlgebraicGroup T) ⟶
      groupAlgebra F (Multiplicative (OrbitIndices r →₀ ℤ)))
    (hqsurj : Function.Surjective q.hom)
    (hq : ∀ i, (extendedHopfMap L q).hom (c.basis i).toMul.val =
        (1 : L) ⊗ₜ[F] MonoidAlgebra.of F (Multiplicative (OrbitIndices r →₀ ℤ))
          (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1)))
    (h : IsClosedImmersion (specGroupMap q ≫ (coordinateHopfIso
      (closedSubgroupAlgebraicGroup T)).hom).hom.hom.left) :
    let S := Specs.GeometricBorelConjugacy.subgroupOfSubgroup T
      ⟨_, specGroupMap q ≫ (coordinateHopfIso (closedSubgroupAlgebraicGroup T)).hom, h⟩
    let hS := baseChangeClosedSubgroup F k S.inclusion S.isClosedImmersion
    let hT := baseChangeClosedSubgroup F k T.inclusion T.isClosedImmersion
    ∀ U : ClosedSubgroup ((groupBaseChange F k).obj G.val),
      IsSplitTorus U.group → IsSubgroupOf U (Specs.GeometricRadicals.baseChangedSubgroup k T hT) →
        IsSubgroupOf U (Specs.GeometricRadicals.baseChangedSubgroup k S hS) := by
  classical
  intro S hS hT U hU hUT
  let H := closedSubgroupAlgebraicGroup T
  let Tk := Specs.GeometricRadicals.baseChangedSubgroup k T hT
  let J := closedSubgroupAlgebraicGroup (G := Specs.Unipotent.baseChangedAlgebraicGroup k G) Tk
  let A := pairCoordinates H
  let p := presentationIso J (extendedHopf k A) (extendedCoordinateIso (K := k) H)
  let pK : extendedHopf K (pairCoordinates J) ≅ extendedHopf K (extendedHopf k A) :=
    (extendedHopfFunctor K).mapIso p
  let b := raisedCharacterBasis (k := k) (K := K) A hc c.basis
  let b' := b.map (groupLikeIso pK.symm).toAdditive.toIntLinearEquiv
  have hb (i : I) : (b' i).toMul.val = pK.inv.hom (b i).toMul.val := by
    rw [Module.Basis.map_apply]
    rfl
  let rk := r.comp a.toMonoidHom
  have hb' (tau : Gal(K/k)) (i : I) :
      (SemilinearAction.scalarExtension (K := K) (pairCoordinates J)).act tau (b' i).toMul.val =
        (b' (rk tau i)).toMul.val := by
    rw [hb, hb]
    have he := baseHom_equivariant (K := K) p.inv tau (b i).toMul.val
    change pK.inv.hom ((SemilinearAction.scalarExtension (K := K) (extendedHopf k A)).act tau
      (b i).toMul.val) = (SemilinearAction.scalarExtension (K := K) (pairCoordinates J)).act tau
      (pK.inv.hom (b i).toMul.val) at he
    exact he.symm.trans (congrArg pK.inv.hom
      (raisedBasis_permutation A hc c.basis a.toMonoidHom ha r c.permutation tau i))
  let ck : PermutedCharacterBasis K I J rk := ⟨b', hb'⟩
  have hck : IsDiagonalizable (extendedHopf K (pairCoordinates J)) :=
    diagonalizable_of_iso pK (extendedDiagonalizable hc)
  let M := Multiplicative (OrbitIndices r →₀ ℤ)
  let Mk := Multiplicative (OrbitIndices rk →₀ ℤ)
  let O := groupAlgebra F M
  let Ok := groupAlgebra k Mk
  let m : M ≃* Mk :=
    (Finsupp.domLCongr (R := ℤ) (M := ℤ) (orbitIndicesEquiv r a)).toAddEquiv.toMultiplicative
  let scalarIso : extendedHopf k O ≅ groupAlgebra k M :=
    CommHopfAlgCat.isoMk (groupAlgebraBaseChange F k M)
  let basisIso : groupAlgebra k M ≅ Ok :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k m)
  let v := scalarIso ≪≫ basisIso
  let qk : pairCoordinates J ⟶ Ok := p.hom ≫ extendedHopfMap k q ≫ v.hom
  have hqk : ∀ i, (extendedHopfMap K qk).hom (ck.basis i).toMul.val =
      (1 : K) ⊗ₜ[k] MonoidAlgebra.of k Mk (Multiplicative.ofAdd (Finsupp.single (orbitIndex rk i) 1)) := by
    intro i
    change (extendedHopfMap K qk).hom (b' i).toMul.val = _
    rw [hb, raisedCharacterBasis_apply]
    let f := extendedHopfFunctor (k := k) K
    have hmul : extendedHopfMap K qk =
        pK.hom ≫ extendedHopfMap K (extendedHopfMap k q) ≫ extendedHopfMap K v.hom := by
      change f.map (p.hom ≫ extendedHopfMap k q ≫ v.hom) = _
      simp only [Functor.map_comp]
      rfl
    have hcomp : pK.inv ≫ extendedHopfMap K qk =
        extendedHopfMap K (extendedHopfMap k q) ≫ extendedHopfMap K v.hom := by
      rw [hmul, pK.inv_hom_id_assoc]
    rw [show (extendedHopfMap K qk).hom
      (pK.inv.hom (raiseDiagramElement A (c.basis i).toMul.val)) =
      (pK.inv ≫ extendedHopfMap K qk).hom (raiseDiagramElement A (c.basis i).toMul.val) from rfl,
      hcomp]
    change (extendedHopfMap K v.hom).hom
      ((extendedHopfMap K (extendedHopfMap k q)).hom (raiseDiagramElement A (c.basis i).toMul.val)) = _
    rw [raiseDiagramElement_natural, hq, raiseDiagramElement_tmul, map_one]
    change (1 : K) ⊗ₜ[k] (basisIso.hom.hom
      (scalarIso.hom.hom ((1 : k) ⊗ₜ[F]
        MonoidAlgebra.of F M (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1))))) = _
    congr 1
    have hscalar (j : M) : scalarIso.hom.hom ((1 : k) ⊗ₜ[F] MonoidAlgebra.of F M j)
        = MonoidAlgebra.of k M j := by
      apply (groupAlgebraBaseChange F k M).symm.injective
      change (groupAlgebraBaseChange F k M).symm
        ((groupAlgebraBaseChange F k M) ((1 : k) ⊗ₜ[F] MonoidAlgebra.single j 1)) =
        (groupAlgebraBaseChange F k M).symm (MonoidAlgebra.single j 1)
      rw [BialgEquiv.symm_apply_apply]
      exact (MonoidAlgebra.scalarTensorEquiv_symm_single j (1 : k)).symm
    rw [hscalar]
    change MonoidAlgebra.mapDomainBialgHom k (m : M →* Mk)
      (MonoidAlgebra.single _ 1) = MonoidAlgebra.single _ 1
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    have hm : m (Multiplicative.ofAdd (Finsupp.single (orbitIndex r i) 1)) =
        Multiplicative.ofAdd (Finsupp.single (orbitIndex rk i) 1) := by
      change Multiplicative.ofAdd (Finsupp.domLCongr (R := ℤ) (M := ℤ) (orbitIndicesEquiv r a)
        (Finsupp.single (orbitIndex r i) 1)) = _
      rw [Finsupp.domLCongr_single, orbitIndicesEquiv_apply]
    exact congrArg (fun t : Mk => MonoidAlgebra.single t (1 : k)) hm
  have hqks : Function.Surjective qk.hom :=
    (ConcreteCategory.bijective_of_isIso v.hom).2.comp
      ((tensorMap_surjective (K := k) q.hom.toAlgHom hqsurj).comp
        (ConcreteCategory.bijective_of_isIso p.hom).2)
  obtain ⟨j, hj⟩ := hUT
  let V := closedSubgroupAlgebraicGroup (G := Specs.Unipotent.baseChangedAlgebraicGroup k G) U
  let f := coordinateHopfMap (G := V) (H := J) j
  obtain ⟨g, hg, _⟩ := ExceptionalValuedTorusNormalizer.permutationSplitFactorization ck hck
    qk hqks hqk (pairCoordinates V) (splitTorusCoordinateDiagonalizable V hU) f
  let eO := extendedGroupIso k O
  let i := specGroupMap q ≫ (coordinateHopfIso H).hom
  let i' := specGroupMap qk ≫ (coordinateHopfIso J).hom
  have hi : i' = specGroupMap v.hom ≫ eO.hom ≫ (groupBaseChange F k).map i := by
    dsimp only [i', qk, i, eO, p]
    simp only [specGroupMap_comp, Category.assoc, presentationIso_spec, Iso.inv_hom_id,
      Category.comp_id]
    change specGroupMap v.hom ≫ specGroupMap (extendedHopfMap k q) ≫
      (extendedGroupIso k A).hom ≫ (groupBaseChange F k).map (coordinateHopfIso H).hom = _
    rw [← Category.assoc (specGroupMap (extendedHopfMap k q)), extendedGroupIso_natural,
      Category.assoc, ← Functor.map_comp]
  let j' := (coordinateHopfIso V).inv ≫ specGroupMap g
  have hj' : j' ≫ i' = j := by
    dsimp only [j', i', f]
    simp only [Category.assoc]
    rw [← Category.assoc (specGroupMap g), ← specGroupMap_comp, hg]
    rw [coordinatePresentationMap]
    simp
  refine ⟨j' ≫ specGroupMap v.hom ≫ eO.hom, ?_⟩
  change (j' ≫ specGroupMap v.hom ≫ eO.hom) ≫ (groupBaseChange F k).map
    (i ≫ T.inclusion) = U.inclusion
  calc
    _ = (j' ≫ i') ≫ Tk.inclusion := by
      rw [hi, Functor.map_comp]
      rfl_cat
    _ = U.inclusion := by rw [hj', hj]

end CoefficientHopf

section MarkedFibreComparison

open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre integralTestAlgebra markedFibrePoint)
open Specs.Pinning (BasedRootDatum)
open Specs.AdjointRepresentation (GroupPoints)

attribute [local instance] integerAlgebra

variable {F k : Type u} [Field F] [Field k] [Algebra F k]
  {D : BasedRootDatum.{u}} {M : Model D}

set_option backward.isDefEq.respectTransparency false in
/-- On each coefficient test algebra, the two split marked point functors
are identified through the integral marking. -/
theorem markedFibreRestrictedPoints (C : MarkedFibre M F) (Ck : MarkedFibre M k) :
    ∃ e : (groupPointsFunctor k).obj Ck.realization.pinned.pair.G.val ≅
        restrictTestAlgebra F k ⋙ (groupPointsFunctor F).obj C.realization.pinned.pair.G.val,
      ∀ R p, markedFibrePoint C ((restrictTestAlgebra F k).obj R) (e.hom.app R p) =
        markedFibrePoint Ck R p := by
  obtain ⟨i, hi⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
  obtain ⟨j, hj⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison Ck
  let b := restrictTestAlgebra F k
  let J := Specs.IntegralSemisimpleModel.integralPointFunctor M.group
  let h : b ⋙ (groupPointsFunctor F).obj C.realization.pinned.pair.G.val ≅
      integralTestAlgebra k ⋙ J := Functor.isoWhiskerLeft b i
  let e := j ≪≫ h.symm
  refine ⟨e, fun R p => ?_⟩
  rw [← hi, ← hj]
  exact ConcreteCategory.congr_hom (h.app R).inv_hom_id (j.hom.app R p)


open private groupBaseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

set_option backward.isDefEq.respectTransparency false in
private theorem groupIsoOfPointIso {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj H.val) :
    ∃ j : G.val ≅ H.val, (groupPointsFunctor k).map j.hom = e.hom := by
  have hGH := groupHomComparison k G.val H.val G.property.1
  have hHG := groupHomComparison k H.val G.val H.property.1
  obtain ⟨f, hf⟩ := hGH.surjective e.hom
  obtain ⟨g, hg⟩ := hHG.surjective e.inv
  change (groupPointsFunctor k).map f = e.hom at hf
  change (groupPointsFunctor k).map g = e.inv at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (groupHomComparison k G.val G.val G.property.1).injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G.val)
    calc
      _ = 𝟙 _ := by rw [Functor.map_comp, hf, hg, e.hom_inv_id]
      _ = _ := ((groupPointsFunctor k).map_id G.val).symm
  · apply (groupHomComparison k H.val H.val H.property.1).injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H.val)
    calc
      _ = 𝟙 _ := by rw [Functor.map_comp, hf, hg, e.inv_hom_id]
      _ = _ := ((groupPointsFunctor k).map_id H.val).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- The isomorphism of the split group fibres induced by identifying the
points in the specified integral marking. -/
theorem markedSplitGroupComparison (C : MarkedFibre M F) (Ck : MarkedFibre M k) :
    ∃ j : Ck.realization.pinned.pair.G.val ≅ (groupBaseChange F k).obj C.realization.pinned.pair.G.val,
      ∀ (R : TestAlgebra k) (p : GroupPoints Ck.realization.pinned.pair.G.val R),
        markedFibrePoint C ((restrictTestAlgebra F k).obj R)
          (baseChangePoint F k C.realization.pinned.pair.G.val.X R (p ≫ j.hom.hom.hom)) =
          markedFibrePoint Ck R p := by
  obtain ⟨e, he⟩ := markedFibreRestrictedPoints C Ck
  let A := C.realization.pinned.pair.G
  let H := Specs.Unipotent.baseChangedAlgebraicGroup k A
  let q := groupBaseChangePointIso k A.val
  obtain ⟨j, hj⟩ := groupIsoOfPointIso Ck.realization.pinned.pair.G H (e ≪≫ q.symm)
  refine ⟨j, fun R p => ?_⟩
  have h := ConcreteCategory.congr_hom (congrArg (fun f => f.app R) hj) p
  change p ≫ j.hom.hom.hom = q.inv.app R (e.hom.app R p) at h
  have hq (x : GroupPoints H.val R) : baseChangePoint F k A.val.X R x = q.hom.app R x := rfl
  rw [hq, h]
  exact (congrArg (markedFibrePoint C ((restrictTestAlgebra F k).obj R))
    (ConcreteCategory.congr_hom (q.app R).inv_hom_id (e.hom.app R p))).trans (he R p)

end MarkedFibreComparison

section MarkedDescent

open Specs.Pinning (AttachedDatum PinnedGroup transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Character Cocharacter)
open _root_.LinearAlgebraicGroups.Descent.AutomorphismSequence
  (exactSequence_exists adjointTorus_exists splitSequence_of_geometry)
open _root_.LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private pinnedLifts recognizesBasedAction_of_lattices localPairAlignment
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false in
/-- Use the automorphism sequence for the attached datum already present in a
pinning, using the based isomorphism induced by the identity on the pair. -/
private theorem splitSequenceForAttached {k : Type u} [Field k] {A : AdditiveLine k}
    (P : PinnedGroup A) (D : AttachedDatum P.pair) :
    ∃ (l : Aut D.toBased ≃* Aut P) (Q : AdjointQuotient P.pair.G),
      Nonempty (SplitSequence P D l Q) := by
  obtain ⟨D', l', hl'⟩ := pinnedLifts P
  let f : D.toBased ≅ D'.toBased :=
    (Groupoid.isoEquivHom D.toBased D'.toBased).symm (inducedBasedIso (𝟙 P) D D')
  let t := Aut.autMulEquivOfIso f
  let l := t.trans l'
  have hw (x : Additive (Character P.pair.T.group)) : f.hom.val.weightEquiv x = x := by
    change Additive.ofMul (transportCharacter (Iso.refl _) x.toMul) = x
    simp [transportCharacter]
  have hc (x : Additive (Cocharacter P.pair.T.group)) : f.hom.val.coweightEquiv x = x := by
    change Additive.ofMul (x.toMul ≫ 𝟙 _) = x
    rw [Category.comp_id]
    rfl
  have hlo (d : Aut D.toBased) :
      (∀ χ : Character P.pair.T.group, d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (transportCharacter (l d).asIso.hom.torus χ)) ∧
      (∀ c : Cocharacter P.pair.T.group, d.asIso.hom.val.coweightEquiv (Additive.ofMul c) =
        Additive.ofMul (c ≫ (l d).asIso.hom.torus.inv)) := by
    have h := hl' (t d)
    have hwi (x : Additive (Character P.pair.T.group)) : f.inv.val.weightEquiv x = x := by
      have hf := congrArg (fun j : D.toBased ⟶ D.toBased => j.val.weightEquiv x) f.hom_inv_id
      change f.inv.val.weightEquiv (f.hom.val.weightEquiv x) = x at hf
      rwa [hw] at hf
    have hci (x : Additive (Cocharacter P.pair.T.group)) : f.inv.val.coweightEquiv x = x := by
      have hf := congrArg (fun j : D'.toBased ⟶ D'.toBased => j.val.coweightEquiv x) f.inv_hom_id
      change f.inv.val.coweightEquiv (f.hom.val.coweightEquiv x) = x at hf
      rwa [hc] at hf
    have htw (x : Additive (Character P.pair.T.group)) :
        (t d).asIso.hom.val.weightEquiv x = d.asIso.hom.val.weightEquiv x := by
      change f.hom.val.weightEquiv (d.asIso.hom.val.weightEquiv (f.inv.val.weightEquiv x)) = _
      rw [hwi, hw]
    have htc (x : Additive (Cocharacter P.pair.T.group)) :
        (t d).asIso.hom.val.coweightEquiv x = d.asIso.hom.val.coweightEquiv x := by
      change f.inv.val.coweightEquiv (d.asIso.hom.val.coweightEquiv (f.hom.val.coweightEquiv x)) = _
      rw [hc, hci]
    exact ⟨fun χ => (htw _).symm.trans (h.1 χ), fun c => (htc _).symm.trans (h.2 c)⟩
  obtain ⟨Q, _, ⟨E⟩⟩ := exactSequence_exists P.pair.G
  obtain ⟨T⟩ := adjointTorus_exists P D Q
  exact ⟨l, Q, splitSequence_of_geometry l hlo E T (recognizesBasedAction_of_lattices l hlo)
    (localPairAlignment P)⟩

/-- Choosing a marked fibre over the coefficient field and transferring the
diagram action determines its descent along the quadratic compositum. -/
theorem coefficientPinnedPair
    {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
    [Algebra F L] [Algebra k K] [FiniteDimensional F L] [FiniteDimensional k K]
    [IsGalois F L] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Specs.IntegralSemisimpleModel.Model D}
    (C : MarkedFibre M F) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {ω : Gal(L/F) →* Aut C.realization.attached.toBased}
    (d : DescendedPair L (l := l) ω) (a : Gal(K/k) ≃* Gal(L/F)) :
    ∃ (Ck : MarkedFibre M k)
      (lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned)
      (Qk : AdjointQuotient Ck.realization.pinned.pair.G)
      (ωk : Gal(K/k) →* Aut Ck.realization.attached.toBased)
      (dk : DescendedPair K (l := lk) ωk)
      (_ : SplitSequence Ck.realization.pinned Ck.realization.attached lk Qk),
      ∀ tau, markedDiagramEquiv Ck.realization (dk.data.outer tau) =
        markedDiagramEquiv C.realization (d.data.outer (a tau)) := by
  obtain ⟨Ck⟩ := ExceptionalMarkedRootDescent.markedFibreExists M k
  obtain ⟨lk, Qk, ⟨Ek⟩⟩ := splitSequenceForAttached Ck.realization.pinned Ck.realization.attached
  let e := (markedDiagramEquiv C.realization).trans (markedDiagramEquiv Ck.realization).symm
  let ωk := e.toMonoidHom.comp (d.data.outer.comp a.toMonoidHom)
  obtain ⟨dk⟩ := _root_.LinearAlgebraicGroups.Descent.PinnedPairDescent.pinnedPairDescent Ek ωk
  refine ⟨Ck, lk, Qk, ωk, dk, Ek, fun tau => ?_⟩
  rw [dk.outer_eq]
  exact (markedDiagramEquiv Ck.realization).apply_symm_apply _

end MarkedDescent

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The marked maximal split subtorus is maximal at every coefficient level
whose quadratic diagram extension is the specified tensor compositum. -/
theorem splitTorusAtLevels : Specs.ExceptionalPinnedBaseChange.SplitTorusAtLevels.{u} := by
  intro F L _ _ _ _ _ D M C l Q ω d σ E hL hσ hD
  let := D.finiteRoots
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis D.base.support ℤ D.Y,
      (∃ h, b = simpleCorootBasis D h) ∨ (∃ h, b = fundamentalCoweightBasis D h) := by
    rcases hD with h | h
    · exact ⟨simpleCorootBasis D h, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨fundamentalCoweightBasis D h, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨c, _, hc, _⟩ := ExceptionalValuedTorusNormalizer.markedPinnedTorus D C.realization E d.data b hb
  obtain ⟨q, h, hs, hST, hm, hq⟩ :=
    ExceptionalValuedTorusNormalizer.largestSplitPermutationSubtorus d.torus c hc
  let H := closedSubgroupAlgebraicGroup d.torus
  let p := Specs.AdjointCocharacters.coordinateHopfIso H
  let S := Specs.GeometricBorelConjugacy.subgroupOfSubgroup d.torus
    ⟨_, specGroupMap q ≫ p.hom, h⟩
  have qsurj : Function.Surjective q.hom := by
    apply (hopfMapClosedImmersion F q).mp
    have : IsIso p.hom.hom.hom.left := (Grp.forget (SchemeOver F) ⋙ Over.forget _).map_isIso p.hom
    apply (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
      (specGroupMap q).hom.hom.left p.hom.hom.hom.left).mp
    exact h
  have hTB : IsSubgroupOf d.torus d.borel := ⟨d.inclusion, d.inclusion_comm⟩
  have hZ : IsCentralizer S d.torus :=
    ExceptionalValuedTorusNormalizer.borelSplitTorusCentralizer d.group d.reductive d.borel d.torus
      S d.isKBorel d.isTorus d.isMaximal hTB hST hm
  obtain ⟨hS, hN⟩ := ExceptionalValuedTorusNormalizer.centralizingSplitTorusNormalizer
    d.group d.torus S hs hST hZ hm
  refine ⟨S, hST, hS, hm, ?_, ?_⟩
  · intro g
    let x := (groundIso (k := F)).inv ≫ g
    have hg : (groundIso (k := F)).hom ≫ x = g := Iso.hom_inv_id_assoc _ _
    rw [← hg]
    exact (normalizes_groundSections_iff d.group S x).trans
      ((hN x).trans (normalizes_groundSections_iff d.group d.torus x).symm)
  · intro k K _ _ _ _ _ _ _ _ hK β hβ e he
    let a := quadraticDiagramEquiv hL hK hσ hβ
    let j := diagramEmbedding e
    let : Algebra L K := j.toRingHom.toAlgebra
    let : IsScalarTower F L K := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    have ha (tau : Gal(K/k)) (z : L) : tau (algebraMap L K z) = algebraMap L K (a tau z) := by
      rcases quadraticAut_cases hK β hβ tau with ht | ht
      · rw [ht, map_one]
        rfl
      · rw [ht, show a β = σ from quadraticDiagramEquiv_apply hL hK hσ hβ]
        exact diagramEmbedding_equivariant he z
    let hSk := baseChangeClosedSubgroup F k S.inclusion S.isClosedImmersion
    let hTk := baseChangeClosedSubgroup F k d.torus.inclusion d.torus.isClosedImmersion
    have hmk := coefficientSplitSubtorusLargest (k := k) d.torus a ha c hc q qsurj hq h
    refine ⟨hSk, splitMaximal_of_extendedLargest d.group S d.torus hs hST hZ hSk hTk hmk⟩

set_option backward.isDefEq.respectTransparency false in
/-- The pinned pair obtained by transferring the diagram cocycle is the
scalar extension of the given pair, with its marked coefficient points. -/
theorem pinnedBaseChange : Specs.ExceptionalPinnedBaseChange.Statement.{u} := by
  intro F L _ _ _ _ _ D M C l Q ω d σ E hL hσ _ k K _ _ _ _ _ _ _ _ hK β hβ e he
  let a := quadraticDiagramEquiv hL hK hσ hβ
  obtain ⟨Ck, lk, Qk, ωk, dk, Ek, haction⟩ := coefficientPinnedPair C d a
  have haβ : a β = σ := quadraticDiagramEquiv_apply hL hK hσ hβ
  have hactionβ := haction β
  rw [haβ] at hactionβ
  have hbased : (markedDiagramEquiv Ck.realization (dk.data.outer β)).asIso.hom =
      (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom :=
    congrArg (fun f => f.asIso.hom) hactionβ
  obtain ⟨c, j, hc, hj⟩ :=
    ExceptionalPinnedGroupComparison.pinnedGroupComparison C Ck E Ek d.data dk.data
      σ β e hbased.symm hL hK hσ hβ he.1 he.2
  have hpair := ExceptionalPinnedPairCompatibility.pinnedPairCompatibility
    C Ck d.data dk.data e he.1 c j hc hj
  exact ⟨Ck, lk, Qk, ωk, dk, Ek, hbased, j, hpair⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
