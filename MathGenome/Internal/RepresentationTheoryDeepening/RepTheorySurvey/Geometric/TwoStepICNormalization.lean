import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepICNormalization
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitCone
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepIntersectionComplex
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology TopologicalSpace
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.TwoStepICNormalization

open Analytic AnalyticAction
open Analytic.IntersectionComplex (DimensionFiltration FiltrationIso attachmentInclusion complex
  shiftedConstant surfaceFiltration)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs RankTwoSchubertStrataSpecs
open ConvolutionUnitConeSpecs TwoStepICNormalizationSpecs
open ConvolutionAnalyticChartsSpecs (surface)
open ConvolutionBundleSpecs (secondPlane)
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open ConvolutionConstantDescentSpec (shiftedConstantPullback)
open ClosedEquivarianceExtensionSpecs (parameterInclusion)
open EquivariantIntersectionComplexes
open private latticeSubspace_positive from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private surfacePointEquiv from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitCone
open private colength_inclusion_closed scalar_colength colength_positive colength_bound
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
open private schubert_point_homeomorph boundedSubspace_injective
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
open private boundedVal_closedEmbedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology
open private embeddingIsoOfRange embeddingIsoOfRange_comp
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private abbrev Gr : TopCat.{0} := TopCat.of GL2Lattice

private theorem terminalLatticeChart (d : SplittingData) :
    ∃ e : surface ≃ₜ Colength 2,
      (∀ p, secondPlane p =
        (latticeSubspace 0 2 (e p).val).map twoStepCoordinates.toLinearMap) ∧
      (e d.point).val = scalarPoint := by
  obtain ⟨a, ha⟩ := surfacePointEquiv
  obtain ⟨b, hb, _⟩ := MinusculeAndTwoStep.twoStepStableModel.2.1
  let e := a.trans b.symm
  have h (p : surface) :
      secondPlane p = (latticeSubspace 0 2 (e p).val).map twoStepCoordinates.toLinearMap := by
    rw [← hb (e p)]
    change secondPlane p = grassmannianSubspace twoStepBasis twoStepRank (b (b.symm (a p))).val
    rw [b.apply_symm_apply]
    rw [ha]
    rfl
  refine ⟨e, h, ?_⟩
  let x : Colength 2 := ⟨scalarPoint, scalar_colength⟩
  have he : a d.point = b x := by
    apply Subtype.ext
    apply grassmannianSubspace_injective _ _
    rw [ha, hb]
    exact d.scalar.2.1
  change (b.symm (a d.point)).val = x.val
  rw [he, b.symm_apply_apply]

private theorem twoStepClosure : closureLattices twoStepPair = colength 2 := by
  let ab := twoStepPair
  have hsum : ab.val.1 - ab.val.2 = 2 := rfl
  have h₀ (cd : DominantPair) (h : Below cd ab) : cd = ab ∨ cd = scalarPair := by
    obtain ⟨j, hj, h₁, h₂⟩ := h
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact Or.inl (Subtype.ext (Prod.ext (by simpa using h₁) (by simpa using h₂)))
    · right
      apply Subtype.ext
      exact Prod.ext h₁ h₂
  have hscalar := MinusculeAndTwoStep.twoStepOrbits.2.1
  have hmain := MinusculeAndTwoStep.twoStepOrbits.2.2.1
  have hc := MinusculeAndTwoStep.twoStepOrbits.2.2.2.1
  ext L
  constructor
  · rintro ⟨cd, hcd, hL⟩
    rcases h₀ cd hcd with rfl | rfl
    · exact ((Set.ext_iff.mp hmain L).mp hL).1
    · rw [hscalar, Set.mem_singleton_iff] at hL
      exact hL.symm ▸ hc
  · intro hL
    by_cases h : L = scalarPoint
    · refine ⟨scalarPair, ⟨1, by decide, rfl, rfl⟩, ?_⟩
      rw [hscalar]
      exact h
    · refine ⟨twoStepPair, ⟨0, by decide, rfl, rfl⟩, ?_⟩
      rw [hmain]
      exact ⟨hL, h⟩

/-- Identify a closed analytic chart with the occupied Schubert scheme
of the same lattices in any admissible symmetric window. -/
private theorem schubertModelOfChart {Y : TopCat.{0}} (j : Y ⟶ Gr)
    (hj : IsClosedEmbedding j)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (hRange : Set.range j = closureLattices ab) :
    ∃ (e : Y ≅ SchubertSpace ab N hN) (L : Y → BoundedLattice 2 N),
      ∀ y, (L y).val = j y ∧ schubertPointSubspace (e.hom y) = boundedSubspace (L y) := by
  obtain ⟨E, hE⟩ := schubert_point_homeomorph ab N hN
  let k : schubertLatticeSet ab N → Gr := fun b ↦ b.val.val
  have hk : IsEmbedding k := (boundedVal_closedEmbedding N).isEmbedding.comp IsEmbedding.subtypeVal
  have hr : Set.range k = closureLattices ab := by
    ext L
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro hL
      obtain ⟨b, hb⟩ := RankTwoSchubertStrata.closureLattices_bounded hN hL
      refine ⟨⟨b, ?_⟩, hb⟩
      change b.val ∈ closureLattices ab
      rwa [hb]
  let t := hj.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (hRange.trans hr.symm)).trans hk.toHomeomorph.symm)
  let e : Y ≃ₜ SchubertSpace ab N hN := t.trans E.symm
  refine ⟨TopCat.isoOfHomeo e, fun y ↦ (t y).val, fun y ↦ ⟨?_, ?_⟩⟩
  · have ht := congrArg Subtype.val (hk.toHomeomorph.apply_symm_apply
      (Homeomorph.setCongr (hRange.trans hr.symm) (hj.isEmbedding.toHomeomorph y)))
    exact ht
  · change schubertPointSubspace (E.symm (t y)) = _
    rw [hE, E.apply_symm_apply]

private theorem actionCommutesWithSchubertModel
    {c : ContinuousJets} {Y : TopCat.{0}} {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (A : JetAction (jetSystem c) Y) (B : JetAction (jetSystem c) (SchubertSpace ab N hN))
    (hB : ActualSchubertAction ab N hN B) (f : Y ⟶ SchubertSpace ab N hN)
    (L : Y → BoundedLattice 2 N)
    (hf : ∀ y, schubertPointSubspace (f y) = boundedSubspace (L y))
    (actual : ∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (y : Y),
      (L ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y))).val =
        positiveGLMap 2 g • (L y).val) :
    EquivariantIntersectionComplexesSpecs.Intertwines A B f := by
  intro k hx hy
  apply TopCat.ext
  rintro ⟨q, y⟩
  obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 _ (Nat.succ_pos k) q
  apply (show Function.Injective (schubertPointSubspace (ab := ab) (N := N) (hN := hN)) from by
    obtain ⟨E, hE⟩ := schubert_point_homeomorph ab N hN
    intro p r hr
    apply E.injective
    apply Subtype.ext
    apply boundedSubspace_injective N
    simpa only [hE] using hr)
  change schubertPointSubspace ((B.action k hy).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, f y)) =
    schubertPointSubspace (f ((A.action k hx).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y)))
  rw [hB.2.1 k hy g (f y) (L y) (hf y), hf]
  change _ = latticeSubspace (-(N : ℤ)) (2 * N) _
  rw [actual]

private def jetActionAbove {J : JetSystem.{0}} {X : TopCat.{0}} {n : ℕ}
    (A : AnalyticAction (J.group n) X) : JetAction J X where
  cutoff := n
  action k hk :=
    { act := J.parameterMap hk (𝟙 X) ≫ A.act
      one_act x := by
        change A.act (J.truncate n k hk 1, x) = x
        rw [J.truncate_one, A.one_act]
      mul_act g h x := by
        change A.act (J.truncate n k hk (g * h), x) =
          A.act (J.truncate n k hk g, A.act (J.truncate n k hk h, x))
        rw [J.truncate_mul, A.mul_act] }
  factors := by
    intro k l hk hkl
    apply TopCat.ext
    rintro ⟨g, x⟩
    change A.act (J.truncate n k hk (J.truncate k l hkl g), x) =
      A.act (J.truncate n l (hk.trans hkl) g, x)
    exact congrArg (fun p ↦ A.act (p, x))
      (congrArg (fun f : (J.group l).space ⟶ (J.group n).space ↦ f g) (J.truncate_comp hk hkl))

private theorem jetActionAbove_at {J : JetSystem.{0}} {X : TopCat.{0}} {n : ℕ}
    (A : AnalyticAction (J.group n) X) : ((jetActionAbove A).action n (le_refl n)).act = A.act := by
  apply TopCat.ext
  rintro ⟨g, x⟩
  change A.act (J.truncate n n (le_refl n) g, x) = A.act (g, x)
  rw [J.truncate_id]
  rfl

private theorem terminalPlane_positive (g : GL (Fin 2) O) (L : GL2Lattice) :
    ((latticeSubspace 0 2 L).map twoStepCoordinates.toLinearMap).map
        (twoTermJetLinear (reduceGL 2 2 (by decide) g)) =
      (latticeSubspace 0 2 (positiveGLMap 2 g • L)).map twoStepCoordinates.toLinearMap := by
  rw [← latticeSubspace_positive 0 (m := 2) (by decide : 1 ≤ 2) (le_refl 2) g L,
    ← Submodule.map_comp, ← Submodule.map_comp]
  apply congrArg (fun T : Window 2 0 2 →ₗ[ℂ] (V × V) ↦ (latticeSubspace 0 2 L).map T)
  simp only [twoTermJetLinear, LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id]

private theorem constantArrowChange {W Z : TopCat.{0}} {a b : W ⟶ Z}
    (p : W ⟶ Z) (d : ℕ) (h : a = b) :
    (shiftedConstantPullback a d ≪≫ (shiftedConstantPullback p d).symm).hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj (shiftedConstant Z d).obj) h) ≫
        (shiftedConstantPullback b d ≪≫ (shiftedConstantPullback p d).symm).hom := by
  subst b
  simp

private theorem twoStepCoordinates_injective :
    Function.Injective (fun L : Colength 2 ↦
      (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap) := by
  intro L M h
  obtain ⟨e, he, _⟩ := BoundedLattices.windowLatticeComparison 2 0 2
  let l : WindowLattice 2 0 2 := ⟨L.val, colength_bound L.property, L.property.1⟩
  let m : WindowLattice 2 0 2 := ⟨M.val, colength_bound M.property, M.property.1⟩
  have h' := (Submodule.map_injective_of_injective twoStepCoordinates.injective) h
  have he' : (e l).val = (e m).val := (he l).trans (h'.trans (he m).symm)
  exact Subtype.ext (congrArg (fun q : WindowLattice 2 0 2 ↦ q.val)
    (e.injective (Subtype.ext he')))

private theorem actionOnTerminalLattices (c : ContinuousJets) (d : SplittingData)
    (e : surface ≃ₜ Colength 2)
    (he : ∀ p, secondPlane p =
      (latticeSubspace 0 2 (e p).val).map twoStepCoordinates.toLinearMap) :
    let A := jetActionAbove (J := jetSystem c) (n := 1) d.terminalAction
    ∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (p : surface),
      (e ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p))).val =
        positiveGLMap 2 g • (e p).val := by
  intro A k hk g p
  let z := d.terminalAction.act (reduceGL 2 2 (by decide) g, p)
  have hact : (A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p) = z := by
    change d.terminalAction.act (jetTruncation (show 1 ≤ k from hk)
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g), p) = z
    have hreduce :
        jetTruncation (show 1 ≤ k from hk) (reduceGL 2 (k + 1) (Nat.succ_pos k) g) =
          reduceGL 2 2 (by decide) g := by
      apply Units.ext
      apply Matrix.ext
      intro i j'
      rfl
    rw [hreduce]
  rw [hact]
  have hpos : positiveGLMap 2 g • (e p).val ∈ colength 2 :=
    (colength_positive g (e p).property.1).mpr (e p).property
  apply congrArg Subtype.val (twoStepCoordinates_injective (a₁ := e z)
    (a₂ := ⟨_, hpos⟩) ?_)
  change (latticeSubspace 0 2 (e z).val).map twoStepCoordinates.toLinearMap = _
  rw [← he, d.terminal_action, he, terminalPlane_positive]

private theorem chartPreimageTopOrbit {bound : OrbitBound twoStepPair 2}
    {m : surface ≅ SchubertSpace twoStepPair 2 bound} {L : surface → BoundedLattice 2 2}
    {e : surface ≃ₜ Colength 2} {x : surface}
    (vertex : (e x).val = scalarPoint)
    (hL : ∀ p, (L p).val = (e p).val ∧ schubertPointSubspace (m.hom p) = boundedSubspace (L p))
    (p : surface) :
    m.hom p ∈ stagePoints twoStepPair 2 bound 0 ↔ p ≠ x := by
  have hOrbit : (L p).val ∈ gl2Orbit twoStepPair ↔ p ≠ x := by
    rw [MinusculeAndTwoStep.twoStepOrbits.2.2.1, (hL p).1]
    change ((e p).val ∈ colength 2 ∧ (e p).val ∉ ({scalarPoint} : Set GL2Lattice)) ↔ _
    simp only [(e p).property, true_and, Set.mem_singleton_iff, ← vertex]
    exact not_congr (show (e p).val = (e x).val ↔ p = x from
      ⟨fun h ↦ e.injective (Subtype.ext h), fun h ↦ congrArg (fun w ↦ (e w).val) h⟩)
  let i₀ : OrbitIndex twoStepPair := ⟨0, by decide⟩
  have hlabel : orbitLabel twoStepPair i₀ = twoStepPair := rfl
  constructor
  · rintro ⟨i, hi, M, hM, hcoords⟩
    have hi' : i = i₀ := Fin.ext (Nat.le_zero.mp hi)
    rw [hi', hlabel] at hM
    have hML : M = L p := boundedSubspace_injective 2 (hcoords.symm.trans (hL p).2)
    exact hOrbit.mp (hML ▸ hM)
  · intro hp
    exact ⟨i₀, le_rfl, L p, hlabel.symm ▸ hOrbit.mpr hp, (hL p).2⟩

private theorem modelFiltrationAt {bound : OrbitBound twoStepPair 2}
    {m : surface ≅ SchubertSpace twoStepPair 2 bound} {x : surface}
    (hx : IsClosed ({x} : Set surface))
    (htop : ∀ p, m.hom p ∈ stagePoints twoStepPair 2 bound 0 ↔ p ≠ x)
    {P : Stratification (SchubertSpace twoStepPair 2 bound)}
    {s : ℕ} {D : DimensionFiltration (SchubertSpace twoStepPair 2 bound) s}
    (h : IsNormalizedOrbitIC twoStepPair 2 bound (𝟙 _) 1 P D)
    (hs : 0 = s) :
    FiltrationIso m (hs ▸ surfaceFiltration x hx) D := by
  revert hs
  cases h with
  | attach _ _ _ k hk _ prev _ _ _ _ _ =>
    intro hs
    have hrange : Set.range k = stagePoints twoStepPair 2 bound 0 := by
      simpa only [Category.comp_id] using (orbitStageRealizes prev).2.1
    cases prev with
    | top =>
      let U := complementOpen {x} hx
      let j := openInclusion U
      have hEmb : IsEmbedding (j ≫ m.hom) :=
        (TopCat.homeoOfIso m).isEmbedding.comp U.isOpenEmbedding.isEmbedding
      have hr : Set.range (j ≫ m.hom) = Set.range k := by
        rw [hrange]
        ext y
        constructor
        · rintro ⟨p, rfl⟩
          exact (htop p.val).mpr p.property
        · intro hy
          let p := m.inv y
          let Y := SchubertSpace twoStepPair 2 bound
          have hp : m.hom p = y := congrArg (fun f : Y ⟶ Y ↦ f y) m.inv_hom_id
          have hpx := (htop p).mp (by rw [hp]; exact hy)
          exact ⟨⟨p, hpx⟩, hp⟩
      let v := embeddingIsoOfRange (j ≫ m.hom) k hEmb hk.isEmbedding hr
      have hv : j ≫ m.hom = v.hom ≫ k :=
        (embeddingIsoOfRange_comp (j ≫ m.hom) k hEmb hk.isEmbedding hr).symm
      exact FiltrationIso.attach (.top v 2) hv

private theorem complementIso {X Y : TopCat.{0}} (e : X ≅ Y) {x : X} {y : Y}
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) (he : e.hom x = y) :
    ∃ v : TopCat.of (complementOpen {x} hx) ≅ TopCat.of (complementOpen {y} hy),
      openInclusion (complementOpen {x} hx) ≫ e.hom =
        v.hom ≫ openInclusion (complementOpen {y} hy) := by
  let U := complementOpen {x} hx
  let V := complementOpen {y} hy
  let j := openInclusion U
  let k := openInclusion V
  have hEmb : IsEmbedding (j ≫ e.hom) :=
    (TopCat.homeoOfIso e).isEmbedding.comp U.isOpenEmbedding.isEmbedding
  have hr : Set.range (j ≫ e.hom) = Set.range k := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨⟨e.hom p.val, ?_⟩, rfl⟩
      change e.hom p.val ≠ y
      rw [← he]
      exact fun h ↦ p.property ((TopCat.homeoOfIso e).injective h)
    · rintro ⟨p, rfl⟩
      let w := e.inv p.val
      have hw : e.hom w = p.val := congrArg (fun f : Y ⟶ Y ↦ f p.val) e.inv_hom_id
      refine ⟨⟨w, ?_⟩, hw⟩
      change w ≠ x
      intro r
      exact p.property (hw.symm.trans ((congrArg e.hom r).trans he))
  exact ⟨embeddingIsoOfRange (j ≫ e.hom) k hEmb V.isOpenEmbedding.isEmbedding hr,
    (embeddingIsoOfRange_comp (j ≫ e.hom) k hEmb V.isOpenEmbedding.isEmbedding hr).symm⟩

private def constantPullbackPlus {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (boundedBelowInverseImage f).obj (shiftedConstant Y n) ≅ shiftedConstant X n :=
  ObjectProperty.isoMk _ (shiftedConstantPullback f n)

open Analytic.IntersectionComplex (attachment pullbackSquare)

private theorem transportConstantIdentification {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    {e : X ≅ Y} {v : U ≅ V} (h : j ≫ e.hom = v.hom ≫ k)
    (a : DerivedAdjunctions.{0})
    (i : shiftedConstant Y 2 ≅ (attachment k hk 0).obj (shiftedConstant V 2))
    (hi : (boundedBelowInverseImage k).map i.hom ≫
      attachmentRestrictionApp k hk 0 (a k) (shiftedConstant V 2) = (constantPullbackPlus k 2).hom) :
    ∃ t : shiftedConstant X 2 ≅ (attachment j hj 0).obj (shiftedConstant U 2),
      (boundedBelowInverseImage j).map t.hom ≫
        attachmentRestrictionApp j hj 0 (a j) (shiftedConstant U 2) = (constantPullbackPlus j 2).hom := by
  obtain ⟨z, hz⟩ := attachmentIsoTransport hj hk h 0 (a j) (a k)
    (constantPullbackPlus v.hom 2).symm
  let E := boundedBelowInverseImage e.hom
  let J := boundedBelowInverseImage j
  let V' := boundedBelowInverseImage v.hom
  let S := pullbackSquare h
  let Rx := attachmentRestrictionApp j hj 0 (a j) (shiftedConstant U 2)
  let Ry := attachmentRestrictionApp k hk 0 (a k) (shiftedConstant V 2)
  let t := (constantPullbackPlus e.hom 2).symm ≪≫ E.mapIso i ≪≫ z.symm
  refine ⟨t, ?_⟩
  have hz' : J.map z.inv ≫ Rx =
      S.hom.app ((attachment k hk 0).obj (shiftedConstant V 2)) ≫
        V'.map Ry ≫ (constantPullbackPlus v.hom 2).hom := by
    apply (cancel_epi (J.map z.hom)).mp
    rw [← Functor.map_comp_assoc, z.hom_inv_id, J.map_id, Category.id_comp]
    rw [reassoc_of% hz]
    change Rx = Rx ≫ (constantPullbackPlus v.hom 2).inv ≫ (constantPullbackPlus v.hom 2).hom
    rw [Iso.inv_hom_id, Category.comp_id]
  change J.map ((constantPullbackPlus e.hom 2).inv ≫ E.map i.hom ≫ z.inv) ≫ Rx = _
  simp only [Functor.map_comp, Category.assoc, hz']
  have hn : J.map (E.map i.hom) ≫ S.hom.app ((attachment k hk 0).obj (shiftedConstant V 2)) =
      S.hom.app (shiftedConstant Y 2) ≫ V'.map ((boundedBelowInverseImage k).map i.hom) :=
    S.hom.naturality i.hom
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hi]
  have hcoeff : S.hom.app (shiftedConstant Y 2) ≫ V'.map (constantPullbackPlus k 2).hom ≫
      (constantPullbackPlus v.hom 2).hom =
    J.map (constantPullbackPlus e.hom 2).hom ≫ (constantPullbackPlus j 2).hom := by
    apply ObjectProperty.hom_ext
    change ((pullbackSquare h).hom.app (shiftedConstant Y 2)).hom ≫
        (derivedInverseImage v.hom).map (shiftedConstantPullback k 2).hom ≫
          (shiftedConstantPullback v.hom 2).hom =
      (derivedInverseImage j).map (shiftedConstantPullback e.hom 2).hom ≫
        (shiftedConstantPullback j 2).hom
    rw [DerivedPullbackPasting.squareBoundedBelowCompatibility]
    exact constantPullbackSquare h 2
  rw [← Category.assoc (S.hom.app (shiftedConstant Y 2)), Category.assoc, hcoeff,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, J.map_id, Category.id_comp]

private theorem terminalConstantIdentification (a : DerivedAdjunctions.{0}) (d : SplittingData)
    (chart : surface ≅ TwoStepIntersectionComplexSpecs.X)
    (hchart : (chart.hom d.point).val = scalarPoint) :
    ∃ i : shiftedConstant surface 2 ≅ IntersectionComplex.surface d.point d.closed,
      IsGS10Identification (@a) d ((DerivedCategory.Plus.ι (C := Sheaves surface)).mapIso i) ∧
      (let U := complementOpen {d.point} d.closed
       let j := openInclusion U
       (boundedBelowInverseImage j).map i.hom ≫
         attachmentRestrictionApp j U.isOpenEmbedding 0 (a j) (shiftedConstant (TopCat.of U) 2) =
           (constantPullbackPlus j 2).hom) := by
  let x := TwoStepIntersectionComplexSpecs.vertex scalar_colength
  have hpoint : chart.hom d.point = x := Subtype.ext hchart
  have hx : IsClosed ({x} : Set TwoStepIntersectionComplexSpecs.X) := by
    have hc := (TopCat.homeoOfIso chart).isClosedMap _ d.closed
    rw [Set.image_singleton] at hc
    change IsClosed {chart.hom d.point} at hc
    rwa [hpoint] at hc
  obtain ⟨v, hv⟩ := complementIso chart d.closed hx hpoint
  let j := openInclusion (complementOpen {d.point} d.closed)
  let k := TwoStepIntersectionComplexSpecs.inclusion x hx
  obtain ⟨i, _, hi⟩ := TwoStepIntersectionComplex.constantIdentification scalar_colength hx (a k)
  have hI : (boundedBelowInverseImage k).map i.hom ≫
      attachmentRestrictionApp k (TwoStepIntersectionComplexSpecs.U x hx).isOpenEmbedding 0 (a k)
        (TwoStepIntersectionComplexSpecs.shifted x hx) = (constantPullbackPlus k 2).hom := by
    exact hi
  obtain ⟨t, ht⟩ := transportConstantIdentification
    (complementOpen {d.point} d.closed).isOpenEmbedding
    (TwoStepIntersectionComplexSpecs.U x hx).isOpenEmbedding hv (@a) i hI
  refine ⟨t, ?_, ht⟩
  let K := shiftedConstant surface 2
  let F := shiftedConstant (TopCat.of (complementOpen {d.point} d.closed)) 2
  change (t.hom ≫ (attachmentInclusion j (complementOpen {d.point} d.closed).isOpenEmbedding 0).app F).hom =
    ((a j).homEquiv K F (constantPullbackPlus j 2).hom).hom
  apply congrArg (fun (f : K ⟶ (derivedDirectImage j).obj F) ↦ f.hom)
  apply ((a j).homEquiv K F).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  exact ht

private theorem pullbackMorphism_conjugate {W Y X : TopCat.{0}}
    {f g : Y ⟶ X} {f' g' : W ⟶ X} (q : W ⟶ Y) (hf : q ≫ f = f') (hg : q ≫ g = g')
    {F G : Derived X} (e : F ≅ G)
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    pullbackMorphism q hf hg
      ((derivedInverseImage f).map e.inv ≫ v ≫ (derivedInverseImage g).map e.hom) =
    (derivedInverseImage f').map e.inv ≫ pullbackMorphism q hf hg v ≫
      (derivedInverseImage g').map e.hom := by
  subst f'
  subst g'
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  have hl : (derivedInverseImageComposition q f).hom.app G ≫
      (derivedInverseImage q).map ((derivedInverseImage f).map e.inv) =
    (derivedInverseImage (q ≫ f)).map e.inv ≫ (derivedInverseImageComposition q f).hom.app F :=
    ((derivedInverseImageComposition q f).hom.naturality e.inv).symm
  have hr : (derivedInverseImage q).map ((derivedInverseImage g).map e.hom) ≫
      (derivedInverseImageComposition q g).inv.app G =
    (derivedInverseImageComposition q g).inv.app F ≫ (derivedInverseImage (q ≫ g)).map e.hom :=
    (derivedInverseImageComposition q g).inv.naturality e.hom
  rw [reassoc_of% hl, hr]

private def transportActionDatum {H : AnalyticGroup.{0}} {X : TopCat.{0}}
    {A : AnalyticAction H X} {F G : Derived X}
    (α : A.Equivariance F) (e : F ≅ G) : A.Equivariance G where
  iso := (derivedInverseImage A.act).mapIso e.symm ≪≫ α.iso ≪≫
    (derivedInverseImage (projection H X)).mapIso e
  identity := by
    rw [show ((derivedInverseImage A.act).mapIso e.symm ≪≫ α.iso ≪≫
      (derivedInverseImage (projection H X)).mapIso e).hom =
        (derivedInverseImage A.act).map e.inv ≫ α.iso.hom ≫
          (derivedInverseImage (projection H X)).map e.hom from rfl]
    rw [pullbackMorphism_conjugate, α.identity]
    simp [← Functor.map_comp]
  multiplication := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, pullbackMorphism_conjugate]
    rw [α.multiplication]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private def transportJetDatum {J : JetSystem.{0}} {X : TopCat.{0}}
    {A : JetAction J X} {F G : Derived X} (α : A.Equivariance F) (e : F ≅ G) :
    A.Equivariance G where
  datum k hk := transportActionDatum (α.datum k hk) e
  compatibility hk h := by
    simp only [transportActionDatum, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      pullbackMorphism_conjugate, α.compatibility]
    rfl

private theorem terminalMap_intertwines {J : JetSystem.{0}} {X : TopCat.{0}}
    {A : JetAction J X} {F G : Derived X} (α : A.Equivariance F) (e : F ≅ G) :
    ∀ k hk, ConvolutionEquivariantSplittingSpecs.Intertwines
      (α.datum k hk) ((transportJetDatum α e).datum k hk) e.hom := by
  intro k hk
  simp only [ConvolutionEquivariantSplittingSpecs.Intertwines, transportJetDatum,
    transportActionDatum, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem restrictedArrow_transport {J : JetSystem.{0}} {U X : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J U} {j : U ⟶ X} (h : Intertwines B A j)
    {F G : Derived X} (α : A.Equivariance F) (e : F ≅ G) (k : ℕ)
    (hu : B.cutoff ≤ k) (hx : A.cutoff ≤ k) :
    restrictedArrow h (transportJetDatum α e) k hu hx =
      (derivedInverseImage (B.action k hu).act).map ((derivedInverseImage j).map e.inv) ≫
        restrictedArrow h α k hu hx ≫
        (derivedInverseImage (projection (J.group k) U)).map ((derivedInverseImage j).map e.hom) := by
  simp only [restrictedArrow, transportJetDatum, transportActionDatum, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, pullbackMorphism_conjugate, Category.assoc]
  have hl := ((derivedInverseImageComposition (B.action k hu).act j).inv.naturality e.inv).symm
  have hr := ((derivedInverseImageComposition (projection (J.group k) U) j).hom.naturality e.hom).symm
  simp only [Functor.comp_map] at hl hr
  rw [reassoc_of% hl, hr]

private theorem complement_invariant {H : AnalyticGroup.{0}} {X : TopCat.{0}}
    (A : AnalyticAction H X) {x : X} (hx : IsClosed ({x} : Set X))
    (fixes : ∀ g, A.act (g, x) = x) :
    invariantRange A (openInclusion (complementOpen {x} hx)) := by
  intro g p
  refine ⟨⟨A.act (g, p.val), ?_⟩, rfl⟩
  change A.act (g, p.val) ≠ x
  intro he
  have hp := p.property
  change p.val ≠ x at hp
  apply hp
  simpa only [← A.mul_act, inv_mul_cancel, A.one_act, fixes] using
    congrArg (fun y ↦ A.act (g⁻¹, y)) he

private theorem normalizedTerminalDatum {J : JetSystem.{0}} {X : TopCat.{0}}
    (a : DerivedAdjunctions.{0}) (A : JetAction J X) {x : X} (hx : IsClosed ({x} : Set X))
    (fixes : ∀ k hk g, (A.action k hk).act (g, x) = x)
    (i : shiftedConstant X 2 ≅ IntersectionComplex.surface x hx)
    (hi : let U := complementOpen {x} hx
      let j := openInclusion U
      (boundedBelowInverseImage j).map i.hom ≫
        attachmentRestrictionApp j U.isOpenEmbedding 0 (a j) (shiftedConstant (TopCat.of U) 2) =
          (constantPullbackPlus j 2).hom) :
    NormalizedICDatum (@a) A (surfaceFiltration x hx)
      (transportJetDatum (constantJetDatum A 2)
        ((DerivedCategory.Plus.ι (C := Sheaves X)).mapIso i)) := by
  let U := complementOpen {x} hx
  let j := openInclusion U
  let L := boundedBelowInverseImage j
  let T := (DerivedCategory.Plus.ι (C := Sheaves X)).mapIso i
  let D := DimensionFiltration.top (TopCat.of U) 2
  let r := attachmentRestriction (s := 0) D j U.isOpenEmbedding (a j)
  let B := restrictJetAction A U.isOpenEmbedding.isEmbedding
    (fun k hk ↦ complement_invariant (A.action k hk) hx (fixes k hk))
  have hj : Intertwines B A j := restrictJetAction_commutes _ _ _
  let α := constantJetDatum A 2
  let β := constantJetDatum B 2
  change L.map i.hom ≫ r = (constantPullbackPlus j 2).hom at hi
  have hr : r = L.map i.inv ≫ (constantPullbackPlus j 2).hom := by
    apply (cancel_epi (L.map i.hom)).mp
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact hi
  have hR : IsIso r := by rw [hr]; infer_instance
  have hInv : (@asIso _ _ _ _ _ hR).inv =
      (constantPullbackPlus j 2).inv ≫ L.map i.hom := by
    apply (cancel_mono r).mp
    change (@asIso _ _ _ _ _ hR).inv ≫ (@asIso _ _ _ _ _ hR).hom = _
    rw [Iso.inv_hom_id]
    change 𝟙 _ = ((constantPullbackPlus j 2).inv ≫ L.map i.hom) ≫ r
    rw [Category.assoc, hi, Iso.inv_hom_id]
  refine NormalizedICDatum.attach (D := D) (hj := U.isOpenEmbedding) (hs := by decide)
    (B := B) rfl hj (transportJetDatum α T) β (normalizedConstantDatum (@a) B 2) hR ?_
  intro k hu hxk
  have hα : IntertwinesPullback hj β α (shiftedConstantPullback j 2).inv := by
    intro l hB hA
    exact (commutes_iff hj β α _ l hB hA).mp <|
      constantDatum_commutes (hj l hB hA) 2
        (constantDatum_iso (B.action l hB) 2) (constantDatum_iso (A.action l hA) 2)
  change (derivedInverseImage (B.action k hu).act).map (@asIso _ _ _ _ _ hR).inv.hom ≫
      restrictedArrow hj (transportJetDatum α T) k hu hxk =
    (β.datum k hu).iso.hom ≫
      (derivedInverseImage (projection (J.group k) (TopCat.of U))).map (@asIso _ _ _ _ _ hR).inv.hom
  rw [hInv]
  change (derivedInverseImage (B.action k hu).act).map
      ((shiftedConstantPullback j 2).inv ≫ (derivedInverseImage j).map T.hom) ≫
    restrictedArrow hj (transportJetDatum α T) k hu hxk =
      (β.datum k hu).iso.hom ≫ (derivedInverseImage (projection (J.group k) (TopCat.of U))).map
        ((shiftedConstantPullback j 2).inv ≫ (derivedInverseImage j).map T.hom)
  let Q := derivedInverseImage (B.action k hu).act
  let P := derivedInverseImage (projection (J.group k) (TopCat.of U))
  let M := derivedInverseImage j
  rw [restrictedArrow_transport]
  change Q.map ((shiftedConstantPullback j 2).inv ≫ M.map T.hom) ≫
      (Q.map (M.map T.inv) ≫ restrictedArrow hj α k hu hxk ≫ P.map (M.map T.hom)) =
    (β.datum k hu).iso.hom ≫ P.map ((shiftedConstantPullback j 2).inv ≫ M.map T.hom)
  simp only [Q.map_comp, P.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc (M.map T.hom) (M.map T.inv), ← M.map_comp T.hom T.inv,
    T.hom_inv_id, M.map_id, Q.map_id, Category.id_comp]
  exact (reassoc_of% (hα k hu hxk)) (P.map (M.map T.hom))

/-- The GS10 constant summand is the normalized equivariant IC on the
occupied two-step Schubert model. -/
theorem terminalICNormalization : TwoStepICNormalizationSpecs.Expected.TerminalICNormalization := by
  intro c a d bound B P D hD β hβ
  obtain ⟨e, he, hpoint⟩ := terminalLatticeChart d
  let chart : surface ≅ TwoStepIntersectionComplexSpecs.X := TopCat.isoOfHomeo e
  let j : surface ⟶ Gr :=
    TopCat.ofHom ⟨fun p ↦ (e p).val, continuous_subtype_val.comp e.continuous⟩
  have hj : IsClosedEmbedding j :=
    (colength_inclusion_closed (m := 2) (Or.inr rfl)).comp e.isClosedEmbedding
  have hrange : Set.range j = colength 2 := by
    ext L
    constructor
    · rintro ⟨p, rfl⟩
      exact (e p).property
    · intro hL
      exact ⟨e.symm ⟨L, hL⟩, congrArg Subtype.val (e.apply_symm_apply ⟨L, hL⟩)⟩
  obtain ⟨m, L, hL⟩ := schubertModelOfChart j hj twoStepPair 2 bound
    (hrange.trans twoStepClosure.symm)
  have hF : FiltrationIso m (surfaceFiltration d.point d.closed) D :=
    modelFiltrationAt d.closed (chartPreimageTopOrbit hpoint hL) hD rfl
  let A : JetAction (jetSystem c) surface := jetActionAbove (J := jetSystem c) (n := 1) d.terminalAction
  have ha : (A.action 1 (le_refl 1)).act = d.terminalAction.act :=
    jetActionAbove_at (J := jetSystem c) (n := 1) d.terminalAction
  have hA : Intertwines A B.action m.hom := by
    apply actionCommutesWithSchubertModel A B.action B.actual m.hom L (fun p ↦ (hL p).2)
    intro k hk g p
    rw [(hL _).1, (hL p).1]
    exact actionOnTerminalLattices c d e he k hk g p
  obtain ⟨i, hi, hRest⟩ := terminalConstantIdentification (@a) d chart hpoint
  let t := (DerivedCategory.Plus.ι (C := Sheaves surface)).mapIso i
  let α := constantJetDatum A 2
  let γ := transportJetDatum α t
  have hγ : NormalizedICDatum (@a) A (surfaceFiltration d.point d.closed) γ :=
    normalizedTerminalDatum (@a) A d.closed
      (fun k hk g ↦ d.fixes ((jetSystem c).truncate 1 k hk g)) i hRest
  have hcut : A.cutoff ≤ B.action.cutoff := by
    rw [B.actual.1]
    exact le_refl 1
  obtain ⟨β', v, hβ', hv⟩ := normalizedEquivarianceTransport (@a) hF hA hcut hγ
  obtain ⟨β₀, _, hUnique⟩ := normalizedSchubertEquivariance (@a) B.actual hD
  have heb : β' = β := (hUnique _ hβ').trans (hUnique _ hβ).symm
  rw [heb] at hv
  refine ⟨{
    latticeChart := chart
    chartScalar := hpoint
    model := m
    lattice := L
    chartCoordinates := fun p ↦ (hL p).1.symm
    terminalCoordinates := fun p ↦ by rw [(hL p).1]; exact he p
    modelCoordinates := fun p ↦ (hL p).2
    modelFiltration := hF
    action := A
    cutoff := rfl
    actsAtTwo := ha
    modelAction := hA
    constantDatum := α
    constantCoefficients := fun k hk ↦ constantDatum_iso (A.action k hk) 2
    constantAtTwo := ?_
    intersectionDatum := γ
    normalized := hγ
    constantIdentification := t
    isGS10Identification := hi
    constantIntertwines := terminalMap_intertwines α t
    modelIdentification := (DerivedCategory.Plus.ι (C := Sheaves surface)).mapIso v
    modelIntertwines := hv }⟩
  change (constantDatum (A.action 1 (le_refl 1)) 2).iso.hom = _
  rw [constantDatum_iso, d.constant_normalized]
  exact constantArrowChange _ 2 ha

end RepTheorySurvey.Geometric.TwoStepICNormalization
