import Specs.LinearAlgebraicGroups.Arithmetic.F4SplitFields
import LinearAlgebraicGroups.Arithmetic.F4LiftedAlbertAction
import LinearAlgebraicGroups.Arithmetic.F4LiftedChevalley
import LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Classification.IntegralRealization
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Field.Shrink
import Mathlib.Basic.Countable.Small

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped RatFunc

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.F4SplitFields

open LinearAlgebraicGroups.Specs
open SplitAlbertLocalFormsSpecification
open F4SplitFieldsSpecification
open LinearAlgebraicGroups.Specs.GeometricRadicals (GeometricGroup IsSemisimple IsSplitReductive)
open Pinning (AttachedDatum BasedIso BasedRootDatum PinnedGroup PinnedIso SplitBorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open RelativeRank (relativeRank)
open IntegralSemisimpleModel (Model fibre)
open LinearAlgebraicGroups.Albert.AutomorphismTypeSpecification
  (chevalleyChange cartanMatrix)
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private maximal_of_square from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private split_dimension_le_rank dimension_of_iso standard_torus_dimension empty_power_iso
  from LinearAlgebraicGroups.Descent.RelativeRank
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private fibreTowerIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private sepClosedBorelPair sepClosedBorelPair_group geometricBorelPair geometricBorelPair_group
  geometricDatumEquiv rootSpan_of_datumEquiv
  from LinearAlgebraicGroups.Arithmetic.OctonionForms
open private rootSpan_of_cartan_inverse inverseF4Cartan inverseF4Cartan_mul mul_inverseF4Cartan
  from LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
open private rootFullRank_iff semisimple_iff_corootFullRank restrictCharacters
  restrictCharacters_injective from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private basedIso_cartan basedIso_rootSystem
  from LinearAlgebraicGroups.Arithmetic.F4LiftedChevalley

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- An absolute type F₄ group has positive geometric rank, as its geometric
maximal torus has a nontrivial root character. -/
theorem geometricRank_pos {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (h : IsAbsoluteF4 G) : 0 < Specs.RelativeRank.geometricRank G := by
  obtain ⟨_, P, hP, D, a, _⟩ := h
  let α := (a 0).val
  have hα : α.val ≠ 1 := α.property.1
  obtain ⟨r, ⟨e⟩⟩ := P.split
  have hr : 0 < r := by
    by_contra! hn
    have he : r = 0 := Nat.eq_zero_of_le_zero hn
    subst r
    have hi := (Grp.isZero_trivial (SchemeOver (AlgebraicClosure k))).of_iso
      (e ≪≫ empty_power_iso)
    exact hα (hi.eq_of_src _ _)
  suffices 0 < relativeRank P.G by simpa only [Specs.RelativeRank.geometricRank, ← hP]
  apply lt_of_lt_of_le _ (split_dimension_le_rank P.G P.T ⟨r, ⟨e⟩⟩)
  rw [dimension_of_iso e, standard_torus_dimension]
  exact_mod_cast hr

/-- A group isomorphism from a split Borel pair transports its torus, including
maximality after base change. The positive rank follows from the absolute type. -/
theorem splittingOfIso {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (h : IsAbsoluteF4 G) (P : SplitBorelPair k) (e : P.G.val ≅ G.val) :
    HasSplitMaximalTorus G := by
  let T := pushSubgroup e P.T
  obtain ⟨hP, hm⟩ := P.maximal
  let L := AlgebraicClosure k
  let F := groupBaseChange k L
  let TL := extendSubgroup L T
  have hTL : IsGeometricallyMaximal T := by
    refine ⟨TL.isClosedImmersion, ?_⟩
    refine maximal_of_square (F.mapIso e)
      (GeometricRadicals.baseChangedSubgroup L P.T hP) TL (Iso.refl _) ?_ hm
    change 𝟙 _ ≫ F.map (P.T.inclusion ≫ e.hom) = F.map P.T.inclusion ≫ F.map e.hom
    rw [Category.id_comp, F.map_comp]
  have hR := reductive_of_semisimple G h.1
  have hs : IsSplitReductive G := ⟨hR, T, P.split, hTL⟩
  exact ⟨⟨T, P.split, hTL⟩,
    ((LinearAlgebraicGroups.Descent.RelativeRank.rankComparison G hR).2 hs).symm ▸
      geometricRank_pos G h⟩

/-- Universe-zero specialization using the checked arithmetic comparison with
the integral split Albert model. -/
theorem smallFieldSplitting :
    LocalSplitting.{0} ∧ FunctionFieldSplitting.{0,0} ∧ FiniteCompletionSplitting.{0,0} := by
  obtain ⟨S, hl, hf, hc⟩ := SplitAlbertLocalForms.absoluteGroupSplitting
  have split {k : Type} [Field k] (G : AffineAlgebraicGroup k) (h : IsAbsoluteF4 G)
      (hi : Nonempty (G.val ≅ (chevalleyChange k).obj S.chevalley.group)) :
      HasSplitMaximalTorus G := by
    obtain ⟨g⟩ := hi
    obtain ⟨_, P, p, _⟩ := S.chevalley.fieldFibre k
    exact splittingOfIso G h P.pinned.pair (p.symm ≪≫ g.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro k _ _ _ _ G h
    exact split G h (hl k G h)
  · intro k _ F _ _ _ _ G h
    exact split G h (hf (F := F) G h)
  · intro k _ D w G h
    exact split G h (hc D w G h)

/-- The universe-zero ground-field result permits a finite constant field in
any universe, by transporting the scalar action along its small copy. -/
theorem smallFunctionFieldSplitting : FunctionFieldSplitting.{0,v} := by
  intro k _ F _ _ _ _ G hG
  let F₀ := Shrink.{0} F
  let e₀ : Shrink.{0} F ≃+* F := (equivShrink.{0,v} F).symm.ringEquiv
  let e : F⟮X⟯ ≃+* F₀⟮X⟯ :=
    IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv e₀.symm)
  let : Finite F₀ := Finite.of_equiv F e₀.symm.toEquiv
  let : Algebra F₀⟮X⟯ k := ((algebraMap F⟮X⟯ k).comp e.symm.toRingHom).toAlgebra
  let : Module.Finite F₀⟮X⟯ k := Module.Finite.of_equiv_equiv e (RingEquiv.refl k) (by
    ext x
    change algebraMap F⟮X⟯ k (e.symm (e x)) = algebraMap F⟮X⟯ k x
    rw [e.symm_apply_apply])
  exact smallFieldSplitting.2.1 (F := F₀) G hG

private theorem rootSystem_of_f4Cartan {k : Type u} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (hS : IsSemisimple P.G) (h : HasF4Cartan D.toBased) :
    D.toBased.datum.IsRootSystem := by
  let := D.comm
  let := D.datum.freeCharacters
  let := D.datum.finiteCharacters
  let := D.datum.freeCocharacters
  let := D.datum.finiteCocharacters
  obtain ⟨a, ha⟩ := h
  let R := D.datum.rootDatum
  have hroot : Function.Injective (restrictCharacters R) :=
    restrictCharacters_injective R ((Submodule.finiteQuotient_iff _).mpr
      ((semisimple_iff_corootFullRank P D).mp hS))
  have hcoroot : Function.Injective (restrictCharacters R.flip) :=
    restrictCharacters_injective R.flip ((Submodule.finiteQuotient_iff _).mpr
      ((rootFullRank_iff P D).mp hS))
  have hflip : inverseF4Cartan.transpose * (Matrix.of cartanMatrix).transpose = 1 := by
    rw [← Matrix.transpose_mul, mul_inverseF4Cartan, Matrix.transpose_one]
  exact ⟨rootSpan_of_cartan_inverse R D.base a _ _ ha inverseF4Cartan_mul hroot,
    rootSpan_of_cartan_inverse R.flip D.base.flip a _ _ (fun i j => ha j i) hflip hcoroot⟩

/-- An absolute type F₄ group is a separable form of a split integral realization
of its actual geometric based datum. -/
theorem separableForm {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k) (hG : IsAbsoluteF4 G) :
    ∃ (D : Pinning.BasedRootDatum.{u}) (M : Model D),
      HasF4Cartan D ∧ D.datum.IsRootSystem ∧
      Nonempty (((groupBaseChange k S).obj G.val) ≅ (fibre S).obj M.group) := by
  let E := AlgebraicClosure k
  let L := AlgebraicClosure S
  let : IsSepClosed S := IsSepClosure.sep_closed k
  obtain ⟨hSs, Q, hQ, C, hC⟩ := hG
  have hQss : IsSemisimple Q.G := hQ ▸
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension
      (K := E) G hSs.1 hSs.2.1).mpr hSs
  have hCsystem := rootSystem_of_f4Cartan C hQss hC
  obtain ⟨M⟩ := LinearAlgebraicGroups.Classification.IntegralRealization.integralRealization C.toBased
  refine ⟨C.toBased, M, hC, hCsystem, ?_⟩
  obtain ⟨_, QE, fE, _⟩ := M.fieldFibre E
  obtain ⟨_, QL, fL, _⟩ := M.fieldFibre L
  obtain ⟨_, QS, fS, _⟩ := M.fieldFibre S
  obtain ⟨gE⟩ :=
    ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 E).2.1
      Q QE.pinned.pair C QE.attached).mpr ⟨QE.datumIso.val⟩
  have g : Nonempty ((GeometricGroup G).val ≅ (fibre E).obj M.group) := by
    rw [← hQ]
    exact ⟨gE ≪≫ fE.symm⟩
  obtain ⟨g⟩ := g
  let GS := Unipotent.baseChangedAlgebraicGroup S G
  have hR := reductive_of_semisimple G hSs
  have hRS := (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := S) G hR.1 hR.2.1).mpr hR
  let P := sepClosedBorelPair GS hRS
  let Pg := geometricBorelPair P
  have hP : P.G = GS := sepClosedBorelPair_group GS hRS
  have hPg : Pg.G = GeometricGroup GS := (geometricBorelPair_group P).trans (congrArg _ hP)
  let : Algebra k L := inferInstanceAs (Algebra k (AlgebraicClosure S))
  let j : E →ₐ[k] L := IsAlgClosed.lift
  let : Algebra E L := j.toRingHom.toAlgebra
  let : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let tS := groupBaseChangeTower (k := k) (K := S) L
  let tE := groupBaseChangeTower (k := k) (K := E) L
  let gL : Pg.G.val ≅ QL.pinned.pair.G.val := by
    rw [hPg]
    change ((groupBaseChange S L).obj GS.val) ≅ QL.pinned.pair.G.val
    exact (tS.app G.val).symm ≪≫ tE.app G.val ≪≫ (groupBaseChange E L).mapIso g ≪≫
      ((fibreTowerIso E L).app M.group).symm ≪≫ fL
  let DP := LinearAlgebraicGroups.Classification.Pinning.attachedDatum P
  let DPg := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Pg
  obtain ⟨d⟩ := ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 L).2.1
    Pg QL.pinned.pair DPg QL.attached).mp ⟨gL⟩
  let e := (QL.datumIso.val.symm _ _).comp d
  have hspan := rootSpan_of_datumEquiv (e.symm _ _) hCsystem.span_root_eq_top
  obtain ⟨dp⟩ := geometricDatumEquiv P DP DPg hspan
  obtain ⟨gS⟩ := ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 S).2.1
    P QS.pinned.pair DP QS.attached).mpr ⟨QS.datumIso.val.comp (e.comp dp)⟩
  have hi : Nonempty (P.G.val ≅ (fibre S).obj M.group) := ⟨gS ≪≫ fS.symm⟩
  rw [hP] at hi
  exact hi

section InnerForms

open AutomorphismSequence (innerAut relativePoints RelativeAut restrictIso restrictAut)
open RelativeFormComparison (fieldTest fieldMap transportedAut)
open Composition.OctonionAutomorphismSpecification (HasTrivialCentre)
open scoped CategoryTheory.MonObj

open private cartan_preserving_permutation from LinearAlgebraicGroups.Arithmetic.AlbertFrames
open private basedIso_base_iff basedIso_ext_weight
  from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private trivial_centre_of_root_lattice
  from LinearAlgebraicGroups.Composition.OctonionAutomorphisms
open private adjointCoercion_bijective finiteTrivialization
  from LinearAlgebraicGroups.Arithmetic.OctonionForms

private theorem basedAutomorphisms_subsingleton (D : BasedRootDatum.{u})
    (h : HasF4Cartan D) (hr : Submodule.span ℤ (Set.range D.datum.root) = ⊤) :
    Subsingleton (Aut D) := by
  obtain ⟨a, ha⟩ := h
  have identity (s : Aut D) : s = 1 := by
    let e : BasedIso D D := s.asIso.hom
    let g := e.val.indexEquiv.subtypeEquiv (basedIso_base_iff e)
    let p := a.trans (g.trans a.symm)
    have hpa (i : Fin 4) : a (p i) = g (a i) := a.apply_symm_apply _
    have hCartan (i j : Fin 4) : cartanMatrix (p i) (p j) = cartanMatrix i j := by
      rw [← ha, hpa, hpa, ← ha]
      exact e.val.toHom.pairing
    have hfix (i : D.I) (hi : i ∈ D.base.support) : e.val.weightEquiv (D.datum.root i) =
        D.datum.root i := by
      obtain ⟨j, hj⟩ := a.surjective ⟨i, hi⟩
      have hgj : g (a j) = a j := by
        rw [← hpa, cartan_preserving_permutation p hCartan j]
      have he : e.val.indexEquiv i = i := by
        have ht : g ⟨i, hi⟩ = ⟨i, hi⟩ := by rwa [hj] at hgj
        exact congrArg Subtype.val ht
      rw [show e.val.weightEquiv (D.datum.root i) = D.datum.root (e.val.indexEquiv i) from
        e.val.toHom.root_weightMap_apply D.datum D.datum i, he]
    apply Aut.ext
    apply Iso.ext
    apply basedIso_ext_weight
    intro x
    change e.val.weightEquiv x = x
    have hx : x ∈ Submodule.span ℤ (D.datum.root '' (D.base.support : Set D.I)) := by
      rw [D.base.span_int_root_support, hr]
      trivial
    induction hx using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hfix i hi
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul r x _ hx => rw [map_smul, hx]
  exact ⟨fun s t => (identity s).trans (identity t).symm⟩

private theorem trivialCentre {k : Type u} [Field k] (P : SplitBorelPair k)
    (D : AttachedDatum P) (hs : Submodule.span ℤ (Set.range D.toBased.datum.root) = ⊤) :
    HasTrivialCentre P.G.val := by
  let := D.comm
  open SchemeCentre CharacterPairing in
  have hr : rootLattice P.T = ⊤ := by
    apply Subgroup.toAddSubgroup.injective
    apply AddSubgroup.toIntSubmodule.injective
    change (rootLattice P.T).toAddSubgroup.toIntSubmodule = ⊤
    change Submodule.span ℤ (Set.range D.datum.rootDatum.root) = ⊤ at hs
    have he : Set.range D.datum.rootDatum.root = Additive.toMul ⁻¹' absoluteRoots P.T := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        rw [show D.datum.rootDatum.root i = Additive.ofMul i.val from D.datum.root_eq i]
        exact i.property
      · intro hx
        exact ⟨⟨Additive.toMul x, hx⟩, D.datum.root_eq _⟩
    apply Submodule.toAddSubgroup_injective
    change (rootLattice P.T).toAddSubgroup = ((⊤ : Submodule ℤ _)).toAddSubgroup
    rw [← hs, he, Submodule.span_int_eq_addSubgroupClosure, rootLattice,
      Subgroup.toAddSubgroup_closure]
  exact trivial_centre_of_root_lattice LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre
    P.reductive P.T P.split P.maximal hr

private theorem splitAutomorphisms_inner {k : Type u} [Field k] {A : RootGroups.AdditiveLine k}
    (P : PinnedGroup A) (D : AttachedDatum P.pair) (h : HasF4Cartan D.toBased)
    (hr : Submodule.span ℤ (Set.range D.toBased.datum.root) = ⊤) (U : SchemeOver k) :
    Function.Bijective (fun g : U ⟶ P.pair.G.val.X => (innerAut g : RelativeAut P.pair.G.val U)) := by
  obtain ⟨E, l, Q, seq, _, _⟩ :=
    LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.automorphismSequences P
  let e := LinearAlgebraicGroups.Classification.Pinning.inducedBasedIso (PinnedIso.refl P) D E
  have hE := basedIso_cartan e h
  let : Subsingleton (Aut E.toBased) :=
    basedAutomorphisms_subsingleton E.toBased hE (rootSpan_of_datumEquiv e.val hr)
  exact adjointCoercion_bijective seq (trivialCentre P.pair D hr) U

open private innerAut_mul restrict_innerAut
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private restrict_trans from LinearAlgebraicGroups.Descent.RelativeFormComparison

private theorem restrictComp {k : Type u} [Field k] {G H : GroupScheme k}
    {S T U : SchemeOver k} (f : T ⟶ S) (g : U ⟶ T)
    (i : relativePoints G S ≅ relativePoints H S) :
    restrictIso (g ≫ f) i = restrictIso g (restrictIso f i) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply GrpCat.ext
  intro x
  let α := (Over.mapComp g f).hom.app X.unop
  change X.unop.left ⟶ G.X at x
  let X₁ := (Over.map (g ≫ f)).obj X.unop
  let X₂ := (Over.map f).obj ((Over.map g).obj X.unop)
  have he := NatTrans.naturality_apply i.hom α.op x
  change (i.hom.app (op X₁) (α.left ≫ x) : X.unop.left ⟶ H.X) =
    α.left ≫ (i.hom.app (op X₂) x : X.unop.left ⟶ H.X) at he
  change (i.hom.app (op X₁) x : X.unop.left ⟶ H.X) =
    (i.hom.app (op X₂) x : X.unop.left ⟶ H.X)
  rw [show α.left = 𝟙 X.unop.left from rfl] at he
  have hx : 𝟙 X.unop.left ≫ x = x := Category.id_comp x
  rw [hx] at he
  exact he.trans (Category.id_comp (show X.unop.left ⟶ H.X from i.hom.app (op X₂) x))

private theorem displacement_mul {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (σ τ : Gal(K/k)) :
    transportedAut k K i (σ * τ) =
      transportedAut k K i σ * restrictAut (fieldMap k K σ) (transportedAut k K i τ) := by
  apply Aut.ext
  change restrictIso (fieldMap k K (σ * τ)) i ≪≫ i.symm =
    restrictIso (fieldMap k K σ) (restrictIso (fieldMap k K τ) i ≪≫ i.symm) ≪≫
      (restrictIso (fieldMap k K σ) i ≪≫ i.symm)
  rw [RelativeFormComparison.fieldMap_mul, restrictComp, restrict_trans]
  let i₁ := restrictIso (fieldMap k K σ) i
  let i₂ := restrictIso (fieldMap k K σ) (restrictIso (fieldMap k K τ) i)
  change i₂ ≪≫ i.symm = (i₂ ≪≫ i₁.symm) ≪≫ (i₁ ≪≫ i.symm)
  rw [Iso.trans_assoc, ← Iso.trans_assoc i₁.symm i₁ i.symm, Iso.symm_self_id, Iso.refl_trans]

private theorem exists_inner_cocycle {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (hi : Function.Bijective
      (fun g : fieldTest k K ⟶ G.X => (innerAut g : RelativeAut G (fieldTest k K)))) :
    ∃ c : Gal(K/k) → (fieldTest k K ⟶ G.X),
      (∀ σ, innerAut (c σ) = transportedAut k K i σ) ∧ c 1 = 1 ∧
        ∀ σ τ, c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ) := by
  choose c hc using fun σ => hi.surjective (transportedAut k K i σ)
  have hm (σ τ : Gal(K/k)) : c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ) := by
    apply hi.injective
    change innerAut (c (σ * τ)) = innerAut (c σ * (fieldMap k K σ ≫ c τ))
    change ∀ σ, innerAut (c σ) = transportedAut k K i σ at hc
    rw [innerAut_mul, ← restrict_innerAut, hc, hc, hc, displacement_mul]
  have h := hm 1 1
  rw [one_mul, RelativeFormComparison.fieldMap_one, Category.id_comp] at h
  refine ⟨c, hc, ?_, hm⟩
  have he : c 1 * 1 = c 1 * c 1 := (mul_one (c 1)).trans h
  exact (mul_left_cancel he).symm

/-- A group of absolute type F₄ is an inner form of a split F₄ group over
a finite Galois extension. The displacement of any chosen comparison has
a unique lift to a point of the split group, and those lifts form a cocycle. -/
theorem finiteInnerForm {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (h : IsAbsoluteF4 G) :
    ∃ (A : RootGroups.AdditiveLine k) (P : PinnedGroup A) (D : AttachedDatum P.pair)
      (K : FiniteGaloisIntermediateField k (SeparableClosure k))
      (i : relativePoints P.pair.G.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K)),
      HasF4Cartan D.toBased ∧ D.toBased.datum.IsRootSystem ∧
        ∃ c : Gal(K/k) → (fieldTest k K ⟶ P.pair.G.val.X),
          (∀ σ, innerAut (c σ) = transportedAut k K i σ) ∧ c 1 = 1 ∧
            ∀ σ τ, c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ) := by
  let S := SeparableClosure k
  obtain ⟨D, M, hD, hs, ⟨j⟩⟩ := separableForm (S := S) G h
  obtain ⟨A, P, p, _⟩ := M.fieldFibre k
  let e := P.datumIso
  let r := (fibreTowerIso k S).app M.group
  let t := (groupBaseChange k S).mapIso p.symm ≪≫ r.symm ≪≫ j.symm
  obtain ⟨K, ⟨i⟩⟩ := finiteTrivialization P.pinned.pair.G G S t
  have hc := basedIso_cartan e hD
  have hPsystem := basedIso_rootSystem e hs
  exact ⟨A, P.pinned, P.attached, K, i, hc, hPsystem, exists_inner_cocycle i
    (splitAutomorphisms_inner P.pinned P.attached hc hPsystem.span_root_eq_top (fieldTest k K))⟩

open private descendInvariantRelativeIso from LinearAlgebraicGroups.Arithmetic.OctonionForms

/-- An inner coboundary changes the splitting isomorphism into an invariant
one, so the actual split torus descends to the original group. -/
theorem splittingOfInnerCoboundary {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (G : AffineAlgebraicGroup k) (hG : IsAbsoluteF4 G)
    (P : SplitBorelPair k)
    (i : relativePoints P.G.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K))
    (b : fieldTest k K ⟶ P.G.val.X)
    (hb : ∀ σ : Gal(K/k), transportedAut k K i σ =
      innerAut (b * (fieldMap k K σ ≫ b)⁻¹)) :
    HasSplitMaximalTorus G := by
  let a := (innerAut b).asIso
  let j := a ≪≫ i
  have hj (σ : Gal(K/k)) : restrictIso (fieldMap k K σ) j = j := by
    let f := fieldMap k K σ
    have hσ : restrictIso f i = (transportedAut k K i σ).asIso ≪≫ i := by
      change restrictIso f i = (restrictIso f i ≪≫ i.symm) ≪≫ i
      simp
    have hcomp : (transportedAut k K i σ) * innerAut (f ≫ b) = innerAut b := by
      rw [hb σ, ← innerAut_mul, inv_mul_cancel_right]
    have hcomp' : (innerAut (f ≫ b)).asIso ≪≫ (transportedAut k K i σ).asIso = a :=
      congrArg Aut.asIso hcomp
    have hres : restrictIso f a = (innerAut (f ≫ b)).asIso :=
      congrArg Aut.asIso (restrict_innerAut f b)
    change restrictIso (fieldMap k K σ) (a ≪≫ i) = a ≪≫ i
    rw [restrict_trans, hres, hσ, ← Iso.trans_assoc, hcomp']
  obtain ⟨e⟩ := descendInvariantRelativeIso P.G G j hj
  exact splittingOfIso G hG P e

end InnerForms

section AlbertDescent

open LinearAlgebraicGroups.Albert.SplitSpecification
open LinearAlgebraicGroups.Descent (SemilinearAction)
open AutomorphismSequence (innerAut relativePoints)
open RelativeFormComparison (fieldTest fieldMap transportedAut)
open scoped TensorProduct CategoryTheory.MonObj

/-- A point-valued cocycle twists scalar Galois action on the split Albert
module. Equivariance of the point action and preservation of the split law
make the unit and its quadratic operator invariant under the twisted action. -/
theorem albertSemilinearAction {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H : GroupScheme k} {M : Type v} [AddCommGroup M] [Module k M]
    (J₀ : ParaQuadratic k M)
    (a : (fieldTest k K ⟶ H.X) →* (K ⊗[k] M ≃ₗ[K] K ⊗[k] M))
    (hA : ∀ g, a g (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit ∧
      ∀ x y, a g (J₀.op K x y) = J₀.op K (a g x) (a g y))
    (hNat : ∀ σ g x, (SemilinearAction.scalarExtension M).act σ (a g x) =
      a (fieldMap k K σ ≫ g) ((SemilinearAction.scalarExtension M).act σ x))
    (c : Gal(K/k) → (fieldTest k K ⟶ H.X)) (h₁ : c 1 = 1)
    (hMul : ∀ σ τ, c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ)) :
    ∃ ρ : SemilinearAction k K (K ⊗[k] M),
      (∀ σ x, ρ.act σ x = a (c σ) ((SemilinearAction.scalarExtension M).act σ x)) ∧
      (∀ σ, ρ.act σ (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit) ∧
      ∀ σ x y, ρ.act σ (J₀.op K x y) = J₀.op K (ρ.act σ x) (ρ.act σ y) := by
  let s := SemilinearAction.scalarExtension (k := k) (K := K) M
  let act (σ : Gal(K/k)) := (s.act σ).trans (a (c σ)).toAddEquiv
  have eval (σ : Gal(K/k)) (x : K ⊗[k] M) : act σ x = a (c σ) (s.act σ x) := rfl
  have one : ∀ x, act 1 x = x := by
    intro x
    rw [eval, h₁, map_one, s.one_act]
    rfl
  have mul (σ τ : Gal(K/k)) (x : K ⊗[k] M) : act (σ * τ) x = act σ (act τ x) := by
    rw [eval, eval, eval, s.mul_act, hNat, hMul, map_mul]
    rfl
  have smul (σ : Gal(K/k)) (r : K) (x : K ⊗[k] M) : act σ (r • x) = σ r • act σ x := by
    rw [eval, eval, s.map_smul, map_smul]
  refine ⟨⟨act, one, mul, smul⟩, eval, ?_, ?_⟩
  · intro σ
    have hu : s.act σ (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit := by
      change (σ 1) ⊗ₜ[k] J₀.unit = 1 ⊗ₜ[k] J₀.unit
      rw [map_one]
    change act σ (1 ⊗ₜ[k] J₀.unit) = _
    rw [eval, hu, (hA (c σ)).1]
  · intro σ x y
    have hσ (z : K ⊗[k] M) : s.act σ z = σ.toAlgHom.toLinearMap.rTensor M z := rfl
    change act σ (J₀.op K x y) = J₀.op K (act σ x) (act σ y)
    rw [eval, eval, eval, hσ, J₀.natural, ← hσ, ← hσ, (hA (c σ)).2]

private theorem split_laws_iso {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module k M] {N : Type w} [AddCommGroup N] [Module k N]
    (J₀ : ParaQuadratic k M) (J : ParaQuadratic k N)
    (h₀ : IsSplitModel J₀ .octonion) (h : IsSplitModel J .octonion) :
    ∃ e : M ≃ₗ[k] N, J₀.IsIso J e := by
  obtain ⟨a, ha, hop₀⟩ := h₀
  obtain ⟨b, hb, hop⟩ := h
  let e := a.trans b.symm
  refine ⟨e, (J₀.isIso_iff_ground J e).mpr ⟨?_, ?_⟩⟩
  · apply b.injective
    simp only [e, LinearEquiv.trans_apply, b.apply_symm_apply, ha, hb]
  · intro x y
    apply b.injective
    rw [show b (e (J₀.groundOp x y)) = a (J₀.groundOp x y) from b.apply_symm_apply _,
      hop (e x) (e y), show b (e x) = a x from b.apply_symm_apply _,
      show b (e y) = a y from b.apply_symm_apply _, hop₀]

private theorem algebra_trivializes_cocycle {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H : GroupScheme k} {M : Type v} [AddCommGroup M] [Module k M]
    {N : Type w} [AddCommGroup N] [Module k N]
    (J₀ : ParaQuadratic k M) (J : ParaQuadratic k N)
    (h₀ : IsSplitModel J₀ .octonion) (h : IsSplitModel J .octonion)
    (a : (fieldTest k K ⟶ H.X) →* (K ⊗[k] M ≃ₗ[K] K ⊗[k] M))
    (ha : Function.Injective a)
    (hr : Set.range a = {g | g (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit ∧
      ∀ x y, g (J₀.op K x y) = J₀.op K (g x) (g y)})
    (c : Gal(K/k) → (fieldTest k K ⟶ H.X))
    (C : K ⊗[k] N ≃ₗ[K] K ⊗[k] M)
    (hU : C (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J₀.unit)
    (hOp : ∀ x y, C (J.op K x y) = J₀.op K (C x) (C y))
    (hNat : ∀ σ g x, (SemilinearAction.scalarExtension M).act σ (a g x) =
      a (fieldMap k K σ ≫ g) ((SemilinearAction.scalarExtension M).act σ x))
    (hC : ∀ (σ : Gal(K/k)) x, a (c σ) ((SemilinearAction.scalarExtension M).act σ (C x)) =
      C ((SemilinearAction.scalarExtension N).act σ x)) :
    ∃ b : fieldTest k K ⟶ H.X, ∀ σ, c σ = b * (fieldMap k K σ ≫ b)⁻¹ := by
  obtain ⟨e, he⟩ := split_laws_iso J₀ J h₀ h
  let E := e.baseChange k K
  let B := E.trans C
  have hB : B ∈ Set.range a := by
    rw [hr]
    refine ⟨?_, ?_⟩
    · change C (E (1 ⊗ₜ[k] J₀.unit)) = _
      rw [show E (1 ⊗ₜ[k] J₀.unit) = (1 : K) ⊗ₜ[k] J.unit by
        rw [LinearEquiv.baseChange_tmul, he.1], hU]
    · intro x y
      change C (E (J₀.op K x y)) = J₀.op K (C (E x)) (C (E y))
      have he' : E (J₀.op K x y) = J.op K (E x) (E y) := he.2 K x y
      rw [he', hOp]
  obtain ⟨b, hb⟩ := hB
  let s := SemilinearAction.scalarExtension (k := k) (K := K) M
  let t := SemilinearAction.scalarExtension (k := k) (K := K) N
  have hE (σ : Gal(K/k)) (x : K ⊗[k] M) : t.act σ (E x) = E (s.act σ x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨b, fun σ => eq_mul_inv_of_mul_eq ?_⟩
  apply ha
  rw [map_mul]
  apply LinearEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (s.act σ).surjective y
  change a (c σ) (a (fieldMap k K σ ≫ b) (s.act σ x)) = a b (s.act σ x)
  rw [← hNat, hb]
  exact (hC σ (E x)).trans (congrArg C (hE σ x))

/-- A descended Albert law suffices to split the group once the algebra
splitting result applies. Only the split group's points over the finite
trivialization field are used in this comparison. -/
theorem splittingOfAlbertDescent {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G : AffineAlgebraicGroup k) (hG : IsAbsoluteF4 G) (P : SplitBorelPair k)
    (i : relativePoints P.G.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K))
    {M N : Type v} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (J₀ : ParaQuadratic k M) (J : ParaQuadratic k N)
    (h₀ : IsSplitModel J₀ .octonion) (hJ : IsAlbert J) (hS : AlbertSplits.{u,v} k)
    (a : (fieldTest k K ⟶ P.G.val.X) →* (K ⊗[k] M ≃ₗ[K] K ⊗[k] M))
    (ha : Function.Injective a)
    (hr : Set.range a = {g | g (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit ∧
      ∀ x y, g (J₀.op K x y) = J₀.op K (g x) (g y)})
    (c : Gal(K/k) → (fieldTest k K ⟶ P.G.val.X))
    (hc : ∀ σ, innerAut (c σ) = transportedAut k K i σ)
    (C : K ⊗[k] N ≃ₗ[K] K ⊗[k] M)
    (hU : C (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J₀.unit)
    (hOp : ∀ x y, C (J.op K x y) = J₀.op K (C x) (C y))
    (hNat : ∀ σ g x, (SemilinearAction.scalarExtension M).act σ (a g x) =
      a (fieldMap k K σ ≫ g) ((SemilinearAction.scalarExtension M).act σ x))
    (hC : ∀ (σ : Gal(K/k)) x, a (c σ) ((SemilinearAction.scalarExtension M).act σ (C x)) =
      C ((SemilinearAction.scalarExtension N).act σ x)) :
    HasSplitMaximalTorus G := by
  obtain ⟨b, hb⟩ := algebra_trivializes_cocycle J₀ J h₀ (hS J hJ) a ha hr c C hU hOp hNat hC
  exact splittingOfInnerCoboundary G hG P i b (fun σ => (hc σ).symm.trans (congrArg innerAut (hb σ)))

section FixedLaw

open TensorProduct

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Extend a quadratic operator using a bilinear representative on a basis.
The diagonal of this representative recovers the given quadratic map in
every characteristic. -/
private def extendQuadraticOperator (B : LinearMap.BilinMap k V (Module.End k V))
    (S : Type u) [CommRing S] [Algebra k S] :
    QuadraticMap S (S ⊗[k] V) (Module.End S (S ⊗[k] V)) :=
  ((LinearMap.baseChangeHom k S V V).liftBaseChange S).compQuadraticMap
    (B.baseChange S).toQuadraticMap

private theorem extendBilinearOperator_natural (B : LinearMap.BilinMap k V (Module.End k V))
    {S T : Type u} [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    (f : S →ₐ[k] T) (x z y : S ⊗[k] V) :
    let e := f.toLinearMap.rTensor V
    e (((LinearMap.baseChangeHom k S V V).liftBaseChange S) (B.baseChange S x z) y) =
      ((LinearMap.baseChangeHom k T V V).liftBaseChange T) (B.baseChange T (e x) (e z)) (e y) := by
  dsimp only
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction z using TensorProduct.inductionOn with
    | tmul b z =>
      induction y using TensorProduct.inductionOn with
      | tmul c y =>
        simp only [LinearMap.BilinMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.baseChangeHom_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
          smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_mul]
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

private theorem extendQuadraticOperator_pure (B : LinearMap.BilinMap k V (Module.End k V))
    (S : Type u) [CommRing S] [Algebra k S] (x : V) :
    extendQuadraticOperator B S (1 ⊗ₜ[k] x) = (B x x).baseChange S := by
  simp only [extendQuadraticOperator, LinearMap.compQuadraticMap_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.baseChange_tmul, mul_one,
    LinearMap.liftBaseChange_one_tmul, LinearMap.baseChangeHom_apply]

variable {K : Type u} [Field K] [Algebra k K] [Module K V] [IsScalarTower k K V]

private def restrictOperatorToFixed (ρ : SemilinearAction k K V)
    (Q : QuadraticMap K V (Module.End K V))
    (hQ : ∀ σ x y, ρ.act σ (Q x y) = Q (ρ.act σ x) (ρ.act σ y))
    (x : ρ.fixed) : Module.End k ρ.fixed :=
  ρ.restrict ρ (Q x.val) (fun σ y => by rw [hQ, x.property σ])

private def quadraticOnFixed (ρ : SemilinearAction k K V)
    (Q : QuadraticMap K V (Module.End K V))
    (hQ : ∀ σ x y, ρ.act σ (Q x y) = Q (ρ.act σ x) (ρ.act σ y)) :
    QuadraticMap k ρ.fixed (Module.End k ρ.fixed) := by
  refine QuadraticMap.ofPolar (restrictOperatorToFixed ρ Q hQ) ?_ ?_ ?_
  · intro r x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change Q (r • x.val) y.val = (r * r) • Q x.val y.val
    rw [← IsScalarTower.algebraMap_smul K r x.val, QuadraticMap.map_smul,
      LinearMap.smul_apply, ← map_mul, IsScalarTower.algebraMap_smul]
  · intro x y z
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (QuadraticMap.polar Q (x.val + y.val) z.val) w.val =
      (QuadraticMap.polar Q x.val z.val + QuadraticMap.polar Q y.val z.val) w.val
    rw [QuadraticMap.polar_add_left]
  · intro r x y
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change (QuadraticMap.polar Q (r • x.val) y.val) z.val =
      r • (QuadraticMap.polar Q x.val y.val) z.val
    rw [← IsScalarTower.algebraMap_smul K r x.val, QuadraticMap.polar_smul_left,
      LinearMap.smul_apply, IsScalarTower.algebraMap_smul]

private theorem descendQuadraticLaw [FiniteDimensional k K] [IsGalois k K]
    (ρ : SemilinearAction k K V) (e : V) (Q : QuadraticMap K V (Module.End K V))
    (he : ∀ σ, ρ.act σ e = e) (hOne : Q e = 1)
    (hQ : ∀ σ x y, ρ.act σ (Q x y) = Q (ρ.act σ x) (ρ.act σ y)) :
    ∃ J : ParaQuadratic k ρ.fixed,
      ρ.descentEquiv (1 ⊗ₜ[k] J.unit) = e ∧
      ∀ x y, ρ.descentEquiv (J.op K x y) = Q (ρ.descentEquiv x) (ρ.descentEquiv y) := by
  let e₀ : ρ.fixed := ⟨e, he⟩
  let q := quadraticOnFixed ρ Q hQ
  let b := Module.Free.chooseBasis k ρ.fixed
  let : LinearOrder (Module.Free.ChooseBasisIndex k ρ.fixed) :=
    IsWellOrder.linearOrder WellOrderingRel
  let B := q.toBilin b
  have diagonal (x : ρ.fixed) : B x x = q x :=
    DFunLike.congr_fun (QuadraticMap.toQuadraticMap_toBilin q b) x
  have hq : q e₀ = 1 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change Q e y.val = y.val
    rw [hOne, Module.End.one_apply]
  let J : ParaQuadratic k ρ.fixed :=
    { unit := e₀
      op := fun S _ _ => extendQuadraticOperator B S
      natural := fun f x y => extendBilinearOperator_natural B f x x y
      op_unit := fun S _ _ => by
        rw [extendQuadraticOperator_pure, diagonal, hq, LinearMap.baseChange_one] }
  let C := ρ.descentEquiv
  have pure (r : K) (x : ρ.fixed) : C (r ⊗ₜ[k] x) = r • x.val := rfl
  refine ⟨J, (pure 1 e₀).trans (one_smul K e), ?_⟩
  have hOp : C.conj.toLinearMap.compQuadraticMap (J.op K) = Q.comp C.toLinearMap := by
    apply baseChange_ext
    apply fun x => LinearMap.ext fun y => ?_
    obtain ⟨z, rfl⟩ := C.surjective y
    change C (extendQuadraticOperator B K (1 ⊗ₜ[k] x) (C.symm (C z))) =
      Q (C (1 ⊗ₜ[k] x)) (C z)
    rw [C.symm_apply_apply, extendQuadraticOperator_pure, diagonal, pure, one_smul]
    induction z using TensorProduct.inductionOn with
    | tmul r y => rw [LinearMap.baseChange_tmul, pure, pure, map_smul]; rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  intro x y
  have hy := congrArg (fun f : QuadraticMap K (K ⊗[k] ρ.fixed) (Module.End K V) =>
    f x (C y)) hOp
  change C (J.op K x (C.symm (C y))) = Q (C x) (C y) at hy
  simpa only [C.symm_apply_apply] using hy

end FixedLaw

open LinearAlgebraicGroups.Albert.IntrinsicCubicSpecification (SplitChart)

/-- Over fields where Albert algebras split, an absolute F₄ group with an
equivariant split Albert action for its finite inner form is split. -/
theorem splittingOfSplitAlbertAction {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (G : AffineAlgebraicGroup k) (hG : IsAbsoluteF4 G) (P : SplitBorelPair k)
    (i : relativePoints P.G.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K))
    {M : Type u} [AddCommGroup M] [Module k M] (J₀ : ParaQuadratic k M)
    (h₀ : IsSplitModel J₀ .octonion) (chart : SplitChart J₀ K)
    (hS : AlbertSplits.{u,u} k)
    (a : (fieldTest k K ⟶ P.G.val.X) →* (K ⊗[k] M ≃ₗ[K] K ⊗[k] M))
    (ha : Function.Injective a)
    (hr : Set.range a = {g | g (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit ∧
      ∀ x y, g (J₀.op K x y) = J₀.op K (g x) (g y)})
    (hNat : ∀ σ g x, (SemilinearAction.scalarExtension M).act σ (a g x) =
      a (fieldMap k K σ ≫ g) ((SemilinearAction.scalarExtension M).act σ x))
    (c : Gal(K/k) → (fieldTest k K ⟶ P.G.val.X))
    (hc : ∀ σ, innerAut (c σ) = transportedAut k K i σ)
    (hOne : c 1 = 1) (hMul : ∀ σ τ, c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ)) :
    HasSplitMaximalTorus G := by
  have hA (g) : a g (1 ⊗ₜ[k] J₀.unit) = 1 ⊗ₜ[k] J₀.unit ∧
      ∀ x y, a g (J₀.op K x y) = J₀.op K (a g x) (a g y) :=
    show a g ∈ _ from hr ▸ Set.mem_range_self g
  obtain ⟨ρ, hρ, hu, hQ⟩ := albertSemilinearAction J₀ a hA hNat c hOne hMul
  obtain ⟨J, hU, hOp⟩ :=
    descendQuadraticLaw ρ (1 ⊗ₜ[k] J₀.unit) (J₀.op K) hu (J₀.op_unit K) hQ
  have hJ : IsAlbert J := by
    apply (albert_iff_split_octonion_after_cover J).mpr
    exact ⟨K, inferInstance, inferInstance, inferInstance, ρ.descentEquiv.trans chart.coordinates,
      (congrArg chart.coordinates hU).trans chart.unit,
      fun x y => (congrArg chart.coordinates (hOp x y)).trans (chart.op _ _)⟩
  apply splittingOfAlbertDescent G hG P i J₀ J h₀ hJ hS a ha hr c hc ρ.descentEquiv hU hOp hNat
  intro σ x
  rw [← hρ]
  exact (SemilinearAction.descent_equivariant ρ σ x).symm

section SplitAction

open LinearAlgebraicGroups.Albert (weightedHermitianJordan)
open LinearAlgebraicGroups.Albert.LowerRankSpecification (untwisted)
open LinearAlgebraicGroups.Composition (Zorn)
open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open private modelBaseChange modelBaseChange_tmul modelBaseChange_operator mapModel_unit
  from LinearAlgebraicGroups.Albert.IntrinsicCubic
open private ground_operator from LinearAlgebraicGroups.Albert.QuadraticOperators

private theorem splitAlbertCharts (k : Type u) [Field k] :
    ∃ Q : QuadraticJordan k (SplitRank.octonion.Model k),
      IsSplitModel (ParaQuadratic.ofJordan Q) .octonion ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        Nonempty (SplitChart (ParaQuadratic.ofJordan Q) K) := by
  let Q := weightedHermitianJordan (untwisted k) (Zorn.isOctonion k)
  refine ⟨Q, ⟨LinearEquiv.refl k _, rfl, ground_operator _ (Zorn.isOctonion k)⟩, ?_⟩
  intro K _ _
  let e := modelBaseChange k K
  refine ⟨⟨e, ?_, fun x y => modelBaseChange_operator x y⟩⟩
  change e (1 ⊗ₜ[k] Q.unit) = _
  rw [show e (1 ⊗ₜ[k] Q.unit) = (1 : K) • _ from modelBaseChange_tmul 1 Q.unit, one_smul]
  exact mapModel_unit (algebraMap k K)

/-- An affine group representing the split Albert law and its compatible
linear actions on all test algebras. -/
theorem splitAlbertRepresentation (k : Type u) [Field k] :
    ∃ (J : ParaQuadratic k (SplitRank.octonion.Model k)) (H : GroupScheme k),
      IsSplitModel J .octonion ∧ IsAffine H.X.left ∧
      (∀ (K : Type u) [Field K] [Algebra k K], Nonempty (SplitChart J K)) ∧
      ∃ a : ∀ S : TestAlgebra k, ((testSpec k).obj (op S) ⟶ H.X) →*
            (S ⊗[k] SplitRank.octonion.Model k ≃ₗ[S] S ⊗[k] SplitRank.octonion.Model k),
        (∀ S, Function.Injective (a S) ∧ Set.range (a S) =
          {g | g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
            ∀ x y, g (J.op S x y) = J.op S (g x) (g y)}) ∧
        ∀ {S T : TestAlgebra k} (f : S ⟶ T) (p : (testSpec k).obj (op S) ⟶ H.X) (x),
          f.hom.toLinearMap.rTensor _ (a S p x) =
            a T ((testSpec k).map f.op ≫ p) (f.hom.toLinearMap.rTensor _ x) := by
  obtain ⟨Q, hQ, hChart⟩ := splitAlbertCharts k
  let J := ParaQuadratic.ofJordan Q
  obtain ⟨H⟩ := LinearAlgebraicGroups.Albert.Automorphisms.quadraticAutomorphismScheme Q
  let equiv (S : TestAlgebra k) := LinearMap.GeneralLinearGroup.generalLinearEquiv S
    (S ⊗[k] SplitRank.octonion.Model k)
  let a (S : TestAlgebra k) := (equiv S).toMonoidHom.comp
    ((quadraticStabilizer Q S).subtype.comp (H.subgroupPoints S).toMonoidHom)
  refine ⟨J, H.group, hQ, H.groupAffine, hChart, a, ?_, ?_⟩
  · intro S
    refine ⟨(equiv S).injective.comp (Subtype.val_injective.comp (H.subgroupPoints S).injective), ?_⟩
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      exact (mem_quadraticStabilizer _ _ _).mp (H.subgroupPoints S p).property
    · intro hg
      let g' := (equiv S).symm g
      have hg' := (mem_quadraticStabilizer Q S g').mpr hg
      obtain ⟨p, hp⟩ := (H.subgroupPoints S).surjective ⟨g', hg'⟩
      refine ⟨p, ?_⟩
      change equiv S (H.subgroupPoints S p).val = g
      rw [hp]
      exact (equiv S).apply_symm_apply g
  · intro S T f p x
    let j := (schemePoints k).map H.inclusion
    have hn := NatTrans.naturality_apply j f p
    have h := H.scalarChange f (j.app S p) x
    rw [← hn, H.evaluatesInclusion, H.evaluatesInclusion] at h
    exact h.symm

end SplitAction

end AlbertDescent

private theorem splitF4PairsIso {k : Type u} [Field k] {P Q : SplitBorelPair k}
    (D : AttachedDatum P) (E : AttachedDatum Q)
    (hD : HasF4Cartan D.toBased) (hE : HasF4Cartan E.toBased)
    (hDsystem : D.toBased.datum.IsRootSystem) (hEsystem : E.toBased.datum.IsRootSystem) :
    Nonempty (P.G.val ≅ Q.G.val) := by
  let := hDsystem
  let := hEsystem
  let := D.toBased.reduced
  let := E.toBased.reduced
  let := D.toBased.finiteRoots
  let := E.toBased.finiteRoots
  obtain ⟨a, ha⟩ := hD
  obtain ⟨b, hb⟩ := hE
  let j := a.symm.trans b
  have hCartan (i l : D.toBased.base.support) :
      E.toBased.base.cartanMatrix (j i) (j l) = D.toBased.base.cartanMatrix i l := by
    obtain ⟨i, rfl⟩ := a.surjective i
    obtain ⟨l, rfl⟩ := a.surjective l
    change E.toBased.datum.pairingIn ℤ (b (a.symm (a i))).val (b (a.symm (a l))).val =
      D.toBased.datum.pairingIn ℤ (a i).val (a l).val
    simp only [Equiv.symm_apply_apply]
    have hb' : E.toBased.datum.pairingIn ℤ (b i).val (b l).val =
        E.toBased.datum.pairing (b i).val (b l).val :=
      E.toBased.datum.algebraMap_pairingIn ℤ _ _
    have ha' : D.toBased.datum.pairingIn ℤ (a i).val (a l).val =
        D.toBased.datum.pairing (a i).val (a l).val :=
      D.toBased.datum.algebraMap_pairingIn ℤ _ _
    rw [hb', ha', hb, ha]
  exact ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 k).2.1
    P Q D E).mpr ⟨D.toBased.base.equivOfCartanMatrixEq E.toBased.base j hCartan⟩

open RelativeFormComparison (fieldTest fieldMap)
open scoped CategoryTheory.MonObj

/-- The splitting of Albert algebras over the ground field trivializes the
finite inner form of an absolute (F₄) group. -/
theorem splittingOfAlbertSplits {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsAbsoluteF4 G) (hS : AlbertSplits.{u,u} k) :
    HasSplitMaximalTorus G := by
  obtain ⟨S, _⟩ := LinearAlgebraicGroups.Albert.AutomorphismType.automorphismType
  let R := IntegralSemisimpleModel.Integers.{0}
  obtain ⟨B, ⟨g⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of R)).mpr S.chevalley.affine
  let A : Type := B.unop
  let H := (fibre k).obj (F4LiftedChevalleySpecification.liftedGroup.{u} A)
  obtain ⟨Q, E, hQ, hEsystem, ⟨eQ⟩⟩ := F4LiftedChevalley.splitFibre.{u} S A g k
  obtain ⟨_, P, D, K, i, hP, hDsystem, c, hc, hOne, hMul⟩ := finiteInnerForm G hG
  obtain ⟨e⟩ := splitF4PairsIso D E hP hQ hDsystem hEsystem
  let f : P.pair.G.val ≅ H := e ≪≫ eQ
  let points : (fieldTest k K ⟶ P.pair.G.val.X) ≃* (fieldTest k K ⟶ H.X) :=
    ((yonedaGrp.mapIso f).app (op (fieldTest k K))).groupIsoToMulEquiv
  obtain ⟨J, chart, hJ, a, ha, hr, hNat⟩ :=
    F4LiftedAlbertAction.liftedAlbertAction.{u} S A g k K
  let action := a.comp points.toMonoidHom
  refine splittingOfSplitAlbertAction G hG P.pair i J hJ chart hS action
    (ha.comp points.injective) ?_ ?_ c hc hOne hMul
  · change Set.range (a ∘ points) = _
    rw [points.surjective.range_comp, hr]
  · intro σ p x
    have hp : points (fieldMap k K σ ≫ p) = fieldMap k K σ ≫ points p := by
      change (fieldMap k K σ ≫ p) ≫ f.hom.hom.hom =
        fieldMap k K σ ≫ p ≫ f.hom.hom.hom
      exact Category.assoc _ _ _
    change _ = a (points (fieldMap k K σ ≫ p)) _
    rw [hp]
    exact hNat σ (points p) x

/-- Every absolute type F₄ group over a nonarchimedean local field is split. -/
theorem localSplitting : LocalSplitting.{u} := by
  intro k _ _ _ _ G hG
  exact splittingOfAlbertSplits G hG (SplitAlbertLocalForms.localAlbertSplitting.{u,u} k)

/-- Every absolute type F₄ group over a global function field is split. -/
theorem functionFieldSplitting : FunctionFieldSplitting.{u,v} := by
  intro k _ F _ _ _ _ G hG
  apply splittingOfAlbertSplits G hG
  let F' := Shrink.{u} F
  let c : F' ≃+* F := (equivShrink.{u,v} F).symm.ringEquiv
  let e : F⟮X⟯ ≃+* F'⟮X⟯ :=
    IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv c.symm)
  let : Finite F' := Finite.of_equiv F c.symm.toEquiv
  let : Algebra F'⟮X⟯ k := ((algebraMap F⟮X⟯ k).comp e.symm.toRingHom).toAlgebra
  let : Module.Finite F'⟮X⟯ k := Module.Finite.of_equiv_equiv e (RingEquiv.refl k) (by
    ext x
    change algebraMap F⟮X⟯ k (e.symm (e x)) = algebraMap F⟮X⟯ k x
    rw [e.symm_apply_apply])
  intro M _ _ J hJ
  exact SplitAlbertLocalForms.functionFieldAlbertSplitting.{u,u} (k := k) (F := F') J hJ

/-- The valued topology on an actual finite completion is the one used by
the local splitting statement. -/
theorem finiteCompletionSplitting_of_local (h : LocalSplitting.{u}) :
    FiniteCompletionSplitting.{u,v} := by
  intro k _ D w G hG
  exact h (D.FiniteCompletion w) G hG

/-- Every absolute type F₄ group over a finite completion of a global field is split. -/
theorem finiteCompletionSplitting : FiniteCompletionSplitting.{u,v} :=
  finiteCompletionSplitting_of_local localSplitting

/-- The rational function field of a separating parameter acts on the original
global function field with finite degree. -/
theorem functionFieldSplitting_of_parameter (h : FunctionFieldSplitting.{u,v})
    {k : Type u} [Field k] {F : Type v} [Field F] [Finite F] [Algebra F k]
    (t : SeparatingParameter F k) (G : AffineAlgebraicGroup k) (hG : IsAbsoluteF4 G) :
    HasSplitMaximalTorus G := by
  let := t.rationalAlgebra
  exact h (F := F) G hG

end
end LinearAlgebraicGroups.Arithmetic.F4SplitFields
