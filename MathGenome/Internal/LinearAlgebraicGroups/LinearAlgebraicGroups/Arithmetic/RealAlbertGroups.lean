import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RealAlbertGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealF4AdjointPointComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealPolarFixedPoints
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ComplexToralInvolutions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ComplexF4ToralCentralizers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter Topology Module
open CategoryTheory.CartesianMonoidalCategory
open scoped Matrix.Norms.Operator
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.RealAlbertGroups

open LinearAlgebraicGroups.Specs
open AdelicGroups (PointsIn asMatrix)
open Specs.ArchimedeanLieChart (expUnit exponentialLines conjugate tangentMatrix)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage)
open AnisotropicAdNilpotents (IsAnisotropic)
open CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open Specs.RealAlbertGroups (HasAbsoluteTypeF4)
open Specs.SimplyConnectedLattice (corootLattice GeometricallySimplyConnected)
open Specs.Pinning (PinnedGroup PinnedIso)
open Specs.AbsoluteDynkinTypes (HasDynkinType integralDiagram)
open RootData (integralCartan)
open IntegralModels (MatrixRealization)
open Specs.Arithmetic.ProjectiveRecurrence (parabolicRadicalPoints)
open Specs.LocalCompactnessCriterion (LocalFieldCompactness)

open private dimension_of_iso empty_power_iso standard_torus_dimension
  reductive_of_semisimple whole_of_isCentral contracting_trivial_of_whole
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private asMatrix_isClosedEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private isOpen_of_full_lines from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
open private parabolicTransport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private transportSubgroup innerIso innerMap comp_innerMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper

open private subgroupRealization subgroupMatrix subgroupDifferential
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
open private semisimple_iff_corootFullRank noCentralCovers_of_span
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private connectedDiagram_of_basedIso connectedSplitNormalSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
open private coroot_span_of_equiv nontrivial_of_root
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

universe u

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000

private theorem f4_diagram_connected {I : Type u} (A : Matrix I I ℤ)
    (h : HasDynkinType A .F4) : (integralDiagram A).IsConnected := by
  obtain ⟨e, he⟩ := h
  change I ≃ Fin 4 at e
  change ∀ i j, A i j = CartanMatrix.F₄ (e i) (e j) at he
  have hc : (integralDiagram CartanMatrix.F₄).IsConnected := by
    refine ⟨inferInstance, ?_⟩
    have adj01 : Relation.EqvGen (fun i j => (integralDiagram CartanMatrix.F₄).edges i j ≠ 0) 0 1 :=
      .rel _ _ (by simp [integralDiagram, CartanMatrix.F₄, show (0 : Fin 4) ≠ 1 by decide])
    have adj12 : Relation.EqvGen (fun i j => (integralDiagram CartanMatrix.F₄).edges i j ≠ 0) 1 2 :=
      .rel _ _ (by simp [integralDiagram, CartanMatrix.F₄, show (1 : Fin 4) ≠ 2 by decide])
    have adj23 : Relation.EqvGen (fun i j => (integralDiagram CartanMatrix.F₄).edges i j ≠ 0) 2 3 :=
      .rel _ _ (by simp [integralDiagram, CartanMatrix.F₄, show (2 : Fin 4) ≠ 3 by decide])
    have fromZero (i : Fin 4) : Relation.EqvGen
        (fun i j => (integralDiagram CartanMatrix.F₄).edges i j ≠ 0) 0 i := by
      fin_cases i
      · exact .refl _
      · exact adj01
      · exact .trans _ _ _ adj01 adj12
      · exact .trans _ _ _ adj01 (.trans _ _ _ adj12 adj23)
    exact fun i j => .trans _ _ _ (.symm _ _ (fromZero i)) (fromZero j)
  have hEdge (a b : I) : (integralDiagram A).edges a b =
      (integralDiagram CartanMatrix.F₄).edges (e a) (e b) := by
    classical
    by_cases hab : a = b
    · subst b
      simp [integralDiagram]
    · simp [integralDiagram, hab, e.injective.ne hab, he]
  refine ⟨⟨e.symm 0⟩, ?_⟩
  have hpath (i j : Fin 4) (p : Relation.EqvGen
      (fun i j => (integralDiagram CartanMatrix.F₄).edges i j ≠ 0) i j) :
      Relation.EqvGen (fun a b => (integralDiagram A).edges a b ≠ 0) (e.symm i) (e.symm j) := by
    induction p with
    | rel i j hij => exact .rel _ _ (by simpa only [hEdge, e.apply_symm_apply] using hij)
    | refl i => exact .refl _
    | symm i j p ih => exact .symm _ _ ih
    | trans i j k p q ihp ihq => exact .trans _ _ _ ihp ihq
  intro i j
  simpa only [Equiv.symm_apply_apply] using hpath (e i) (e j) (hc.2 (e i) (e j))

/-- The F₄ Cartan matrix makes the absolute form simply connected, and
its connected diagram gives absolute almost simplicity. -/
theorem absolute_simple_and_simply_connected_of_type_f4
    {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (h : HasAbsoluteTypeF4 G) :
    Specs.IsAbsolutelyAlmostSimple G ∧ GeometricallySimplyConnected G := by
  obtain ⟨hG, P, hP, D, hF⟩ := h
  letI := D.comm
  letI := D.toBased.finiteRoots
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hPss : IsSemisimple P.G := hP ▸
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := AlgebraicClosure k)
      G hG.1 hG.2.1).mpr hG
  have hD : corootLattice D = ⊤ :=
    RealF4AdjointPointComparison.f4_coroot_span_eq_top D.datum.rootDatum D.base
      ((semisimple_iff_corootFullRank P D).mp hPss) hF
  have hc := f4_diagram_connected (integralCartan D.datum.rootDatum D.base) hF
  have hsc : GeometricallySimplyConnected G := by
    unfold GeometricallySimplyConnected
    rw [← hP]
    exact noCentralCovers_of_span P D hD
  obtain ⟨A⟩ := Classification.Pinning.additiveLineExists (AlgebraicClosure k)
  obtain ⟨U, pin, E, ⟨W⟩⟩ := RootData.AbsoluteDynkinTypes.splitPinnedComparison A P
  let Q : PinnedGroup A := ⟨P, U, pin⟩
  let e := Classification.Pinning.inducedBasedIso (PinnedIso.refl Q) D E
  letI := E.toBased.finiteRoots
  have hE := coroot_span_of_equiv _ _ e.val hD
  have hEc := connectedDiagram_of_basedIso e hc
  letI := E.comm
  obtain ⟨a⟩ := hEc.1
  refine ⟨⟨hG, ?_, ?_⟩, hsc⟩
  · rw [← hP]
    rintro ⟨f⟩
    exact nontrivial_of_root P a.val ((Grp.isZero_trivial _).of_iso f)
  · rw [← hP]
    intro N hN
    rcases connectedSplitNormalSubgroup E hPss hE hEc W N hN with hz | hIso
    · exact Or.inl ⟨hz.iso (Grp.isZero_trivial _)⟩
    · exact Or.inr hIso

private theorem rank_pos_of_not_anisotropic (G : AffineAlgebraicGroup ℝ)
    (h : ¬ IsAnisotropic G.val) : 0 < RelativeRank.relativeRank G := by
  unfold IsAnisotropic at h
  push Not at h
  obtain ⟨S, hS, hn⟩ := h
  obtain ⟨r, ⟨e⟩⟩ := hS
  have hr : 0 < r := Nat.pos_of_ne_zero (fun he => by
    subst r
    exact hn ⟨e ≪≫ empty_power_iso⟩)
  have hd : topologicalKrullDim S.group.X.left ≤ RelativeRank.relativeRank G :=
    le_iSup (fun T : {T : ClosedSubgroup G.val // GeometricRadicals.IsSplitTorus T.group} =>
      topologicalKrullDim T.val.group.X.left) ⟨S, ⟨r, ⟨e⟩⟩⟩
  rw [dimension_of_iso e, standard_torus_dimension] at hd
  exact lt_of_lt_of_le (by exact_mod_cast hr) hd

private theorem cocharacter_ne_one_of_contracting_direction
    (G : AffineAlgebraicGroup ℝ) (hG : GeometricRadicals.IsReductive G)
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    (v : Lie ℝ G.val) (hv : v ∈ lieImage D.contracting) (hn : v ≠ 0) :
    c.hom.hom ≠ 1 := by
  intro hc
  have central : RelativeRank.IsCentralCocharacter c := by
    intro X x
    apply (centralizes_iff c x).mpr
    intro Y t a
    rw [hc, MonObj.comp_one]
    exact Commute.one_right _
  letI := whole_of_isCentral c D central
  obtain ⟨e⟩ := contracting_trivial_of_whole G hG c D
  have hterm : IsTerminal D.contracting.group.X :=
    isTerminalTensorUnit.ofIso ((Grp.forget (SchemeOver ℝ)).mapIso e).symm
  obtain ⟨z, rfl⟩ := hv
  have hz : z = 0 := by
    apply Subtype.ext
    apply hterm.hom_ext
  exact hn (hz ▸ map_zero (mapPointKernel D.contracting.inclusion))

/-- Noncompactness produces a nontrivial cocharacter and a nonzero tangent
direction in the unipotent radical of its limit parabolic. -/
theorem exists_contracting_direction_of_noncompact
    (hcompact : LocalFieldCompactness.{0}) (G : AffineAlgebraicGroup ℝ)
    (i : MatrixRealization G) (hG : IsSemisimple G)
    (hn : ¬ CompactSpace (PointsIn i ℝ)) :
    ∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      c.hom.hom ≠ 1 ∧ BorelProper.IsParabolic G D.parabolic ∧
      StandardParabolicLevi.IsContractingRadical D ∧
      ∃ v : Lie ℝ G.val, v ∈ lieImage D.contracting ∧ v ≠ 0 := by
  have hAn : ¬ IsAnisotropic G.val := fun h => hn ((hcompact G i hG).mpr h)
  have hred := reductive_of_semisimple G hG
  obtain ⟨S, _, c, D, v, hv, hn⟩ := LocalCocharacterEvaluation.isotropicContractingLie
    G hG (rank_pos_of_not_anisotropic G hAn)
  exact ⟨c ≫ S.inclusion, D,
    cocharacter_ne_one_of_contracting_direction G hred _ D v hv hn,
    (Descent.RelativeRank.properDynamicParabolic G hred _ D).1,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hred _ D, v, hv, hn⟩

/-- A closed normal subgroup with a nonzero exponential direction is open
in the real point group of an algebraic group with simple real Lie algebra. -/
theorem isOpen_of_normal_and_nonzero_direction
    (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (s : IdentityLieStructure G.val)
    (hs : letI := s.lieRing; letI := s.lieAlgebra; LieAlgebra.IsSimple ℝ (Lie ℝ G.val))
    (N : Subgroup (PointsIn i ℝ)) [N.Normal] (hN : IsClosed (N : Set (PointsIn i ℝ)))
    (v : Lie ℝ G.val) (hv : v ≠ 0)
    (hline : tangentMatrix i v ∈ exponentialLines (N.map (asMatrix i ℝ))) :
    IsOpen (N : Set (PointsIn i ℝ)) := by
  classical
  let z : Lie ℝ G.val := 0
  let A := Matrix (Unipotent.Index i.size) (Unipotent.Index i.size) ℝ
  let m := asMatrix i ℝ
  have hm : IsClosedEmbedding m := asMatrix_isClosedEmbedding i ℝ
  letI : IsTopologicalGroup (PointsIn i ℝ) := hm.isInducing.isTopologicalGroup m
  let : LieRing (Lie ℝ G.val) := s.lieRing
  let : AddCommGroup (Lie ℝ G.val) := s.lieRing.toAddCommGroup
  let : AddCommMonoid (Lie ℝ G.val) := s.lieRing.toAddCommGroup.toAddCommMonoid
  let : LieAlgebra ℝ (Lie ℝ G.val) := s.lieAlgebra
  let : Module ℝ (Lie ℝ G.val) := s.lieAlgebra.toModule
  obtain ⟨d, hd, hdval, hdline, _, hdderiv⟩ := ArchimedeanLieChart.matrixTangentComparison ℝ G i s
  have hclosed : IsClosed (N.map m : Set Aˣ) := hm.isClosedMap _ hN
  obtain ⟨chartN⟩ := ArchimedeanLieChart.closedSubgroupExponential A (N.map m) hclosed
  obtain ⟨chartG⟩ := ArchimedeanLieChart.closedSubgroupExponential A m.range hm.isClosed_range
  let W : Submodule ℝ (Lie ℝ G.val) := chartN.tangent.comap d
  have hWv : v ∈ W := (chartN.mem_tangent _).mpr (by simpa only [hdval] using hline)
  have hz : s.lieRing.toAddCommGroup.toAddGroup.toZero.zero = z :=
    congrArg (fun a : AddGroup (PointKernel G.val) => a.toZero.zero) s.group_law
  have hWne : W ≠ ⊥ := fun h => hv (((Submodule.mem_bot ℝ).mp (h ▸ hWv)).trans hz)
  have hnormal (g : PointsIn i ℝ) (y : A) (hy : y ∈ chartN.tangent) :
      conjugate (m g) y ∈ chartN.tangent := by
    apply (chartN.mem_tangent _).mpr
    have hy' := (chartN.mem_tangent _).mp hy
    intro t
    have hte := hy' t
    obtain ⟨a, ha, he⟩ := hte
    refine ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› a ha g, ?_⟩
    rw [map_mul, map_mul, map_inv, he]
    symm
    apply Units.ext
    simp only [conjugate, ArchimedeanLieChart.expUnit_val, Units.val_mul]
    have hsmul : t • ((m g : Aˣ).val * y * (m g)⁻¹.val) =
        (m g : Aˣ).val * (t • y) * (m g)⁻¹.val := by
      calc
        _ = t • ((m g : Aˣ).val * y) * (m g)⁻¹.val := by rw [smul_mul_assoc]
        _ = _ := by rw [mul_smul_comm]
    rw [hsmul]
    symm
    apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ)
      (MulSemiringAction.toRingHom (ConjAct Aˣ) A (ConjAct.toConjAct (m g)))
      (continuous_const_smul (ConjAct.toConjAct (m g)))
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hbr (x y : Lie ℝ G.val) (hy : y ∈ W) : ⁅x, y⁆ ∈ W := by
    have he (t : ℝ) : ∃ g, m g = expUnit (t • d x) :=
      (hdline _).mpr ⟨x, rfl⟩ t
    let f (t : ℝ) := conjugate (expUnit (t • d x)) (d y)
    have hf (t : ℝ) : f t ∈ chartN.tangent := by
      obtain ⟨g, hg⟩ := he t
      change conjugate (expUnit (t • d x)) (d y) ∈ chartN.tangent
      rw [← hg]
      exact hnormal g (d y) hy
    exact chartN.tangent.closed_of_finiteDimensional.mem_of_tendsto
      (hdderiv x y).tendsto_slope_zero
      (Eventually.of_forall fun t => chartN.tangent.smul_mem _ (chartN.tangent.sub_mem (hf (0 + t)) (hf 0)))
  let I : LieIdeal ℝ (Lie ℝ G.val) := { W with lie_mem := fun {x y} hy => hbr x y hy }
  have hWtop : W = ⊤ := by
    rcases hs.eq_bot_or_eq_top I with h | h
    · exact (hWne (congrArg LieSubmodule.toSubmodule h)).elim
    · exact congrArg LieSubmodule.toSubmodule h
  apply isOpen_of_full_lines m hm.isEmbedding N chartG
  intro x hx
  obtain ⟨y, rfl⟩ := (hdline x).mp ((chartG.mem_tangent x).mp hx)
  exact (chartN.mem_tangent _).mp (show y ∈ W from hWtop ▸ Submodule.mem_top)

/-- The closed normal subgroup generated by a contracting radical is open
when the real Lie algebra is simple and the radical has a nonzero tangent. -/
theorem isOpen_normal_closure_of_contracting_direction
    (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (hG : Specs.IsAbsolutelyAlmostSimple G)
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    (v : Lie ℝ G.val) (hv : v ∈ lieImage D.contracting) (hn : v ≠ 0) :
    let U : Subgroup (PointsIn i ℝ) :=
      ((((groupPointsFunctor ℝ).map D.contracting.inclusion).app
        (CommAlgCat.of ℝ ℝ)).hom).range
    IsOpen ((Subgroup.normalClosure (U : Set (PointsIn i ℝ))).topologicalClosure :
      Set (PointsIn i ℝ)) := by
  dsimp only
  let H := Unipotent.closedSubgroupAlgebraicGroup D.contracting
  let j := subgroupRealization i D.contracting
  let incl : PointsIn j ℝ →* PointsIn i ℝ :=
    (((groupPointsFunctor ℝ).map D.contracting.inclusion).app (CommAlgCat.of ℝ ℝ)).hom
  let M := Subgroup.normalClosure (incl.range : Set (PointsIn i ℝ))
  let N := M.topologicalClosure
  letI : N.Normal := Subgroup.is_normal_topologicalClosure M
  let s := identityLieStructure G
  have hs := LinearAlgebraicGroups.Arithmetic.absoluteSimpleLocalLie ℝ G hG s
  apply isOpen_of_normal_and_nonzero_direction G i s hs N M.isClosed_topologicalClosure v hn
  obtain ⟨z, hz⟩ := hv
  obtain ⟨d, _, hdm, hdline, _, _⟩ :=
    ArchimedeanLieChart.matrixTangentComparison ℝ H j (identityLieStructure H)
  have he : d z = tangentMatrix i v := by
    rw [hdm]
    exact (subgroupDifferential i D.contracting z).trans (congrArg (tangentMatrix i) hz)
  intro t
  obtain ⟨x, hx⟩ := (hdline _).mpr ⟨z, rfl⟩ t
  refine ⟨incl x, M.le_topologicalClosure (Subgroup.subset_normalClosure ⟨x, rfl⟩), ?_⟩
  rw [← he, ← subgroupMatrix i D.contracting x]
  exact hx

private theorem conjugate_mem_parabolic_radical_points
    {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    (g x : PointsIn i ℝ) (hx : x ∈ parabolicRadicalPoints G) :
    g * x * g⁻¹ ∈ parabolicRadicalPoints G := by
  obtain ⟨P, hp, U, hu, p, rfl⟩ := hx
  let X := (testSpec ℝ).obj (Opposite.op (CommAlgCat.of ℝ ℝ))
  let base : 𝟙_ (SchemeOver ℝ) ≅ X := Over.isoMk (Iso.refl _) (by
    change (𝟙 (Spec (CommRingCat.of ℝ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℝ ℝ)) = 𝟙 _
    rw [Category.id_comp]
    exact Spec.map_id _)
  let g₀ : X ⟶ G.val.X := g
  let g' : 𝟙_ (SchemeOver ℝ) ⟶ G.val.X := base.hom ≫ g₀
  let e := innerIso g'
  refine ⟨transportSubgroup P e, parabolicTransport hp e, U, hu, p, ?_⟩
  let q : X ⟶ G.val.X := p ≫ (U.inclusion ≫ P.inclusion).hom.hom
  change p ≫ (U.inclusion ≫ P.inclusion ≫ e.hom).hom.hom =
    g₀ * q * g₀⁻¹
  rw [← Category.assoc, Grp.comp_hom_hom, ← Category.assoc]
  change q ≫ (innerMap g').hom.hom = _
  have hg : toUnit X ≫ g' = g₀ := by
    change toUnit X ≫ base.hom ≫ g₀ = g₀
    rw [show toUnit X = base.inv from Subsingleton.elim _ _, Iso.inv_hom_id_assoc]
  rw [comp_innerMap, hg]

/-- If conjugates of one contracting radical generate a dense subgroup, all
rational parabolic radicals generate a dense subgroup as well. -/
theorem dense_parabolic_radical_points_of_dense_conjugates
    {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    (hp : BorelProper.IsParabolic G D.parabolic)
    (hr : StandardParabolicLevi.IsContractingRadical D)
    (hd : let U : Subgroup (PointsIn i ℝ) :=
        ((((groupPointsFunctor ℝ).map D.contracting.inclusion).app
          (CommAlgCat.of ℝ ℝ)).hom).range
      Dense (Subgroup.normalClosure (U : Set (PointsIn i ℝ)) : Set (PointsIn i ℝ))) :
    Dense (Subgroup.closure (G := PointsIn i ℝ) (parabolicRadicalPoints G) :
      Set (PointsIn i ℝ)) := by
  apply hd.mono
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨u, hu, hux⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hux
  obtain ⟨p, rfl⟩ := hu
  apply Subgroup.subset_closure
  apply conjugate_mem_parabolic_radical_points (i := i)
  refine ⟨D.parabolic, hp, BorelsAndChambers.contractingSubgroup D, hr.1, p, ?_⟩
  change (((groupPointsFunctor ℝ).map
    (D.contractingToParabolic ≫ D.parabolic.inclusion)).app (CommAlgCat.of ℝ ℝ)).hom p = _
  rw [D.contracting_in_G]

/-- A connected, noncompact real form of type F₄ has the specified
contracting radical and both dense-generation properties. -/
theorem noncompact_parabolic_generation_of_connected
    (hcompact : LocalFieldCompactness.{0}) (G : AffineAlgebraicGroup ℝ)
    (i : MatrixRealization G) (hG : HasAbsoluteTypeF4 G)
    (hconn : ConnectedSpace (PointsIn i ℝ))
    (hn : ¬ CompactSpace (PointsIn i ℝ)) :
    (∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      let U : Subgroup (PointsIn i ℝ) :=
        ((((groupPointsFunctor ℝ).map D.contracting.inclusion).app
          (CommAlgCat.of ℝ ℝ)).hom).range
      c.hom.hom ≠ 1 ∧ BorelProper.IsParabolic G D.parabolic ∧
      StandardParabolicLevi.IsContractingRadical D ∧
      (∃ v : Lie ℝ G.val, v ∈ lieImage D.contracting ∧ v ≠ 0) ∧
      Dense (Subgroup.normalClosure (U : Set (PointsIn i ℝ)) : Set (PointsIn i ℝ))) ∧
    Dense (Subgroup.closure (G := PointsIn i ℝ) (parabolicRadicalPoints G) :
      Set (PointsIn i ℝ)) := by
  obtain ⟨c, D, hc, hp, hr, v, hv, hv0⟩ :=
    exists_contracting_direction_of_noncompact hcompact G i hG.1 hn
  have hsimple := (absolute_simple_and_simply_connected_of_type_f4 G hG).1
  have hopen := isOpen_normal_closure_of_contracting_direction G i hsimple c D v hv hv0
  let U : Subgroup (PointsIn i ℝ) :=
    ((((groupPointsFunctor ℝ).map D.contracting.inclusion).app
      (CommAlgCat.of ℝ ℝ)).hom).range
  let M := Subgroup.normalClosure (U : Set (PointsIn i ℝ))
  have hd : Dense (M : Set (PointsIn i ℝ)) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe]
    exact IsClopen.eq_univ ⟨M.isClosed_topologicalClosure, hopen⟩
      ⟨1, M.topologicalClosure.one_mem⟩
  exact ⟨⟨c, D, hc, hp, hr, ⟨v, hv, hv0⟩, hd⟩,
    dense_parabolic_radical_points_of_dense_conjugates i c D hp hr hd⟩

open Specs.Pinning (AttachedDatum SplitBorelPair)
open private closed_points_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ComplexToralInvolutions

/-- A continuous multiplicative equivalence carries a connected centralizer
to a connected centralizer. -/
private theorem connected_centralizer_image {A B : Type} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃* B) (he : Continuous e)
    (a : A) (h : ConnectedSpace {x : A // Commute x a}) :
    ConnectedSpace {y : B // Commute y (e a)} := by
  letI := h
  let f (x : {x : A // Commute x a}) : {y : B // Commute y (e a)} :=
    ⟨e x.val, x.property.map e⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hy : Commute (e.symm y.val) a := by
      apply Commute.of_map e.injective
      simpa only [e.apply_symm_apply] using y.property
    exact ⟨⟨e.symm y.val, hy⟩, Subtype.ext (e.apply_symm_apply _)⟩
  exact hsurj.connectedSpace ((he.comp continuous_subtype_val).subtype_mk _)

/-- A square-one complex point has connected centralizer in the matrix
topology, by conjugating it into the specified maximal torus. -/
private theorem connected_complex_centralizer
    (H : AffineAlgebraicGroup ℂ) (i : MatrixRealization H) (hH : IsSemisimple H)
    (P : SplitBorelPair ℂ) (hP : P.G = H) (D : AttachedDatum P)
    (hF : letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4)
    (x : PointsIn i ℂ) (hx : x * x = 1) :
    ConnectedSpace {y : PointsIn i ℂ // Commute y x} := by
  subst H
  obtain ⟨g, t, hgt⟩ := ComplexToralInvolutions.toralInvolutions P i x hx
  let torusPoint : AdjointRepresentation.GroupPoints P.T.group (CommAlgCat.of ℂ ℂ) →*
      PointsIn i ℂ :=
    (((groupPointsFunctor ℂ).map P.T.inclusion).app (CommAlgCat.of ℂ ℂ)).hom
  have hconj : MulAut.conj g x = torusPoint t := hgt
  have ht : t ^ 2 = 1 := by
    apply closed_points_injective P.T.inclusion P.T.isClosedImmersion
    change torusPoint (t ^ 2) = torusPoint 1
    rw [map_pow, map_one, ← hconj, ← map_pow, pow_two, hx, map_one]
  have htorus : ConnectedSpace {y : PointsIn i ℂ // Commute y (torusPoint t)} :=
    ComplexF4ToralCentralizers.toralCentralizerConnected P D hH hF i t ht
  have hconjCont : Continuous ((MulAut.conj g).symm : PointsIn i ℂ → PointsIn i ℂ) := by
    change Continuous (fun y : PointsIn i ℂ => g⁻¹ * y * g)
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hx' : (MulAut.conj g).symm (torusPoint t) = x := by
    rw [← hconj, MulEquiv.symm_apply_apply]
  exact hx' ▸ connected_centralizer_image (MulAut.conj g).symm hconjCont (torusPoint t) htorus

/-- The real points of every real group of absolute type F₄ are connected. -/
theorem realPointsConnected : Specs.RealAlbertGroups.RealPointsConnected := by
  intro G i hG
  obtain ⟨hss, P, hP, D, hF⟩ := hG
  obtain ⟨hC, ⟨PC, hPC, DC, hFC⟩, j, s, sC, hfin, hsemi, _, σ, n, b, _, _, aC, aR,
      haC, _, _, _⟩ := RealF4AdjointPointComparison.adjointPointComparison G i hss P hP D hF
  let L := Lie ℂ (Specs.RealF4AdjointPointComparison.complexGroup G).val
  letI : LieRing L := sC.lieRing
  letI : LieAlgebra ℂ L := sC.lieAlgebra
  letI : FiniteDimensional ℂ L := hfin
  letI := Specs.RealF4AdjointPointComparison.coordinateTopology b
  have hfixed : ConnectedSpace {g : L ≃ₗ⁅ℂ⁆ L //
      LieAlgebrasAndRepresentations.RealForms.Intertwines σ σ g} := by
    apply RealPolarFixedPoints.connected_fixed_points σ n b hsemi
    intro a ha
    have hx : aC.symm a * aC.symm a = 1 := by rw [← map_mul, ha, map_one]
    have h := connected_complex_centralizer _ j hC PC hPC DC hFC (aC.symm a) hx
    exact (aC.apply_symm_apply a) ▸ connected_centralizer_image aC haC (aC.symm a) h
  letI : ConnectedSpace (Specs.RealF4AdjointPointComparison.fixedAutomorphisms σ) := hfixed
  exact aR.symm.surjective.connectedSpace aR.symm.continuous

/-- A noncompact real group of absolute type F₄ is topologically generated
by the real points of its parabolic radicals. -/
theorem noncompactRealParabolicGeneration :
    Specs.RealAlbertGroups.NoncompactRealParabolicGeneration := by
  intro G i hG hn
  exact noncompact_parabolic_generation_of_connected LocalCompactnessCriterion.localFieldCompactness
    G i hG (realPointsConnected G i hG) hn

end LinearAlgebraicGroups.Arithmetic.RealAlbertGroups
