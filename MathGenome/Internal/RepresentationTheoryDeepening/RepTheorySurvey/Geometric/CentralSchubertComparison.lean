import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralSchubertComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Geometric.CentralSchubertComparison

open CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open CentralSchubertComparisonSpecs
open scoped MatrixGroups

open private bounded_of_minimal boundedSubspace_injective windowSchemePoint_lattice
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

set_option autoImplicit false

private theorem difference_shift (a : ℤ) (ab : DominantPair) :
    difference (shiftPair a ab) = difference ab := by
  change ((ab.val.1 + a) - (ab.val.2 + a)).toNat = (ab.val.1 - ab.val.2).toNat
  congr 1
  omega

private def WindowPointFormula (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (b : ℤ) (m : ℕ) (d : WindowDimension 2 b m)
    (e : windowStableScheme 2 b m d ⟶ occupiedSchubert ab N hN) : Prop :=
  ∀ (q : Points (windowStableScheme 2 b m d) complexAlgebra) (L : WindowLattice 2 b m),
    windowSchemeSubspace q = latticeSubspace b m L.val →
    schubertPointSubspace (q ≫ e) = latticeSubspace (-(N : ℤ)) (2 * N) L.val

private theorem minimalWindowIso (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (b : ℤ) (m : ℕ) (d : WindowDimension 2 b m)
    (hb : b = ab.val.2) (hm : m = difference ab) (hd : d.val = difference ab) :
    ∃ e : windowStableScheme 2 b m d ≅ occupiedSchubert ab N hN,
      WindowPointFormula ab N hN b m d e.hom := by
  subst b
  subst m
  obtain ⟨d₀, hd₀, e, he⟩ := RankTwoSchubertStrata.minimalWindowComparison ab N hN
  have heq : d₀ = d := Fin.ext (hd₀.trans hd.symm)
  subst d₀
  refine ⟨e, fun q L hq ↦ ?_⟩
  simpa only [schubertPointSubspace, Category.assoc] using he L q hq

private theorem comp_window_isos {C : Type*} [Category C] {T X U V Y : C}
    (p : T ⟶ X) (eN : U ≅ X) (eW : U ≅ V) (eM : V ≅ Y) :
    p ≫ (eN.symm ≪≫ eW ≪≫ eM).hom = ((p ≫ eN.inv) ≫ eW.hom) ≫ eM.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]

section TranslatedWindow

attribute [local irreducible] latticeSubspace translate windowStableScheme schubertScheme

set_option maxHeartbeats 900000 in
private theorem composeWindows_onPoints (a : ℤ) (ab : DominantPair)
    (N M : ℕ) (hN : OrbitBound ab N) (hM : OrbitBound (shiftPair a ab) M)
    {d : WindowDimension 2 ab.val.2 (difference ab)}
    {d' : WindowDimension 2 (ab.val.2 + a) (difference ab)}
    (eN : windowStableScheme 2 ab.val.2 (difference ab) d ≅ occupiedSchubert ab N hN)
    (eM : windowStableScheme 2 (ab.val.2 + a) (difference ab) d' ≅
      occupiedSchubert (shiftPair a ab) M hM)
    (eW : windowStableScheme 2 ab.val.2 (difference ab) d ≅
      windowStableScheme 2 (ab.val.2 + a) (difference ab) d')
    (heN : WindowPointFormula ab N hN ab.val.2 (difference ab) d eN.hom)
    (heM : WindowPointFormula (shiftPair a ab) M hM (ab.val.2 + a) (difference ab) d' eM.hom)
    (hW : ShiftedMinimalWindow a ab)
    (heW : ∀ (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra)
        (L : WindowLattice 2 ab.val.2 (difference ab)),
      windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val →
      windowSchemeSubspace (q ≫ eW.hom) =
        latticeSubspace (ab.val.2 + a) (difference ab) (translate a L.val))
    (p : OccupiedSchubertPoints ab N hN) (L : BoundedLattice 2 N)
    (hp : schubertPointSubspace p = boundedSubspace L) :
    schubertPointSubspace (p ≫ (eN.symm ≪≫ eW ≪≫ eM).hom) =
      latticeSubspace (-(M : ℤ)) (2 * M) (translate a L.val) := by
  let q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra := p ≫ eN.inv
  have hqN : q ≫ eN.hom = p := by
    simp only [q, Category.assoc, eN.inv_hom_id, Category.comp_id]
  obtain ⟨W, hq⟩ := windowSchemePoint_lattice (r := 2) (b := ab.val.2)
    (m := difference ab) (d := d) q
  let B := bounded_of_minimal ab N hN W
  have hNsub : schubertPointSubspace p = boundedSubspace B :=
    (congrArg (schubertPointSubspace (hN := hN)) hqN).symm.trans (heN q W hq)
  have hB : B = L := boundedSubspace_injective N (hNsub.symm.trans hp)
  let W' : WindowLattice 2 (ab.val.2 + a) (difference ab) :=
    ⟨translate a W.val, hW.mapsWindow W⟩
  have hMsub := heM (q ≫ eW.hom) W' (heW q W hq)
  have hL : W'.val = translate a L.val := congrArg (fun B : BoundedLattice 2 N ↦
    translate a B.val) hB
  have hcomp : p ≫ (eN.symm ≪≫ eW ≪≫ eM).hom = (q ≫ eW.hom) ≫ eM.hom :=
    comp_window_isos (C := SchemeOver ℂ) (T := (testSpec ℂ).obj (Opposite.op complexAlgebra))
      (X := occupiedSchubert ab N hN) (Y := occupiedSchubert (shiftPair a ab) M hM)
      (U := windowStableScheme 2 ab.val.2 (difference ab) d)
      (V := windowStableScheme 2 (ab.val.2 + a) (difference ab) d') p eN eW eM
  have hsubcomp := congrArg (schubertPointSubspace (ab := shiftPair a ab) (N := M) (hN := hM))
    hcomp
  have hsubL := congrArg (latticeSubspace (r := 2) (-(M : ℤ)) (2 * M)) hL
  exact hsubcomp.trans (hMsub.trans hsubL)

end TranslatedWindow

set_option maxHeartbeats 700000 in
private theorem translatedSchemeIso (a : ℤ) (ab : DominantPair)
    (hW : ShiftedMinimalWindow a ab) (N M : ℕ) (hN : OrbitBound ab N)
    (hM : OrbitBound (shiftPair a ab) M) :
    ∃ e : occupiedSchubert ab N hN ≅ occupiedSchubert (shiftPair a ab) M hM,
      ∀ (p : OccupiedSchubertPoints ab N hN) (L : BoundedLattice 2 N),
        schubertPointSubspace p = boundedSubspace L →
        schubertPointSubspace (p ≫ e.hom) =
          latticeSubspace (-(M : ℤ)) (2 * M) (translate a L.val) := by
  obtain ⟨d, hd, _, _⟩ := RankTwoSchubertStrata.minimalWindowComparison ab N hN
  obtain ⟨eN, heN⟩ := minimalWindowIso ab N hN ab.val.2 (difference ab) d rfl rfl hd
  obtain ⟨d', hd', eW, heW⟩ := hW.schemeComparison d
  have hm := (difference_shift a ab).symm
  obtain ⟨eM, heM⟩ := minimalWindowIso (shiftPair a ab) M hM (ab.val.2 + a)
    (difference ab) d' rfl hm (hd'.trans (hd.trans hm))
  exact ⟨eN.symm ≪≫ eW ≪≫ eM, composeWindows_onPoints a ab N M hN hM eN eM eW
    heN heM hW heW⟩

section LatticeCoordinates

variable {ab cd : DominantPair} {N M : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound cd M}

/-- A map with the scalar formula on lattice coordinates is continuous in the bounded models. -/
private theorem continuous_of_translation {a : ℤ} (ht : ContinuousBoundedTranslation a)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (F : SchubertSpace cd M hM ≃ₜ schubertLatticeSet cd M)
    (f : SchubertSpace ab N hN → SchubertSpace cd M hM)
    (hf : ∀ p, (F (f p)).val.val = translate a (E p).val.val) :
    Continuous f := by
  have h : Continuous (fun p ↦ (F (f p)).val) :=
    ht N M (fun p ↦ (E p).val) (fun p ↦ (F (f p)).val) E.continuous.subtype_val hf
  have hF : Continuous (fun p ↦ F (f p)) := continuous_induced_rng.mpr h
  have heq : F.symm ∘ (fun p ↦ F (f p)) = f := funext fun p ↦ F.symm_apply_apply (f p)
  exact heq ▸ F.symm.continuous.comp hF

private theorem mem_orbitPoints_iff
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (p : SchubertSpace ab N hN) (j : OrbitIndex ab) :
    p ∈ orbitPoints ab N hN j ↔ (E p).val.val ∈ gl2Orbit (orbitLabel ab j) := by
  constructor
  · rintro ⟨B, hB, hp⟩
    have he : (E p).val = B := boundedSubspace_injective N ((hE p).symm.trans hp)
    rwa [he]
  · intro hp
    exact ⟨(E p).val, hp, hE p⟩

private theorem lattice_under_actual_action
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (J : GL2JetParameters) (A : SchubertJetAction J ab N hN)
    (k : ℕ) (hk : A.action.cutoff ≤ k) (g : GL (Fin 2) O) (p : SchubertSpace ab N hN) :
    (E ((A.action.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p))).val.val =
      positiveGLMap 2 g • (E p).val.val := by
  let p' := (A.action.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)
  let gO : PositiveGL 2 := ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩
  have hmem : gO • (E p).val.val ∈ closureLattices ab :=
    RankTwoSchubertStrata.smul_mem_closureLattices ab gO (E p).property
  obtain ⟨B, hB⟩ := RankTwoSchubertStrata.closureLattices_bounded hN hmem
  have hP : schubertPointSubspace p' = boundedSubspace B := by
    rw [A.actual.2.1 k hk g p (E p).val (hE p)]
    exact congrArg (latticeSubspace (-(N : ℤ)) (2 * N)) hB.symm
  have he : (E p').val = B := boundedSubspace_injective N ((hE p').symm.trans hP)
  exact (congrArg Subtype.val he).trans hB

end LatticeCoordinates

private theorem orbitLabel_shift (a : ℤ) (ab : DominantPair)
    (j : OrbitIndex ab) (j' : OrbitIndex (shiftPair a ab)) (h : j.val = j'.val) :
    orbitLabel (shiftPair a ab) j' = shiftPair a (orbitLabel ab j) := by
  apply Subtype.ext
  apply Prod.ext
  · change ab.val.1 + a - (j'.val : ℤ) = ab.val.1 - (j.val : ℤ) + a
    omega
  · change ab.val.2 + a + (j'.val : ℤ) = ab.val.2 + (j.val : ℤ) + a
    omega

section EquivarianceAndStrata

variable {a : ℤ} {ab : DominantPair} {N M : ℕ}
variable {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
variable (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
variable (F : SchubertSpace (shiftPair a ab) M hM ≃ₜ schubertLatticeSet (shiftPair a ab) M)
variable (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
variable (hF : ∀ p, schubertPointSubspace p = boundedSubspace (F p).val)
variable (f : SchubertSpace ab N hN ⟶ SchubertSpace (shiftPair a ab) M hM)
variable (hf : ∀ p, (F (f p)).val.val = translate a (E p).val.val)
variable (hτ : ScalarTranslationProperties a)

include E F hE hF hf hτ

private theorem translation_sameDepth (j : OrbitIndex ab)
    (j' : OrbitIndex (shiftPair a ab)) (h : j.val = j'.val) :
    f ⁻¹' orbitPoints (shiftPair a ab) M hM j' = orbitPoints ab N hN j ∧
    orbitDimension (shiftPair a ab) j'.val = orbitDimension ab j.val := by
  constructor
  · ext p
    change f p ∈ orbitPoints (shiftPair a ab) M hM j' ↔ p ∈ orbitPoints ab N hN j
    rw [mem_orbitPoints_iff F hF, mem_orbitPoints_iff E hE, hf, orbitLabel_shift a ab j j' h,
      ← hτ.orbitImage (orbitLabel ab j)]
    exact hτ.leftInverse.injective.mem_set_image
  · simp only [orbitDimension, difference_shift, h]

private theorem translation_intertwines (J : GL2JetParameters)
    (A : SchubertJetAction J ab N hN) (B : SchubertJetAction J (shiftPair a ab) M hM) :
    JetMapsCommute A.action B.action f := by
  intro k hk hk'
  refine TopCat.ext fun ⟨u, p⟩ ↦ ?_
  obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) u
  change (B.action.action k hk').act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, f p) =
    f ((A.action.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p))
  apply F.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [lattice_under_actual_action F hF J B, hf, hf, lattice_under_actual_action E hE J A,
    hτ.commutesWithPositiveLoop]

end EquivarianceAndStrata

theorem schubertTranslation : Expected.SchubertTranslation := by
  intro a ab hW hτ N M hN hM
  obtain ⟨e, he⟩ := translatedSchemeIso a ab hW N M hN hM
  obtain ⟨E, hE, _⟩ := RankTwoSchubertStrata.schubertStratification ab N hN
  obtain ⟨F, hF, _⟩ := RankTwoSchubertStrata.schubertStratification (shiftPair a ab) M hM
  let f (p : SchubertSpace ab N hN) : SchubertSpace (shiftPair a ab) M hM := p ≫ e.hom
  let g (p : SchubertSpace (shiftPair a ab) M hM) : SchubertSpace ab N hN := p ≫ e.inv
  have hgf : Function.LeftInverse g f := fun p ↦ by
    simp only [f, g, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hfg : Function.RightInverse g f := fun p ↦ by
    simp only [f, g, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hf (p : SchubertSpace ab N hN) : (F (f p)).val.val = translate a (E p).val.val := by
    have hmem : translate a (E p).val.val ∈ closureLattices (shiftPair a ab) := by
      rw [← hτ.closureImage]
      exact ⟨(E p).val.val, (E p).property, rfl⟩
    obtain ⟨B, hB⟩ := RankTwoSchubertStrata.closureLattices_bounded hM hmem
    have hsub : schubertPointSubspace (f p) = boundedSubspace B := by
      exact (he p (E p).val (hE p)).trans
        (congrArg (latticeSubspace (-(M : ℤ)) (2 * M)) hB.symm)
    have hcoord : (F (f p)).val = B := boundedSubspace_injective M ((hF (f p)).symm.trans hsub)
    exact (congrArg Subtype.val hcoord).trans hB
  have hg (p : SchubertSpace (shiftPair a ab) M hM) :
      (E (g p)).val.val = translate (-a) (F p).val.val := by
    have h := hf (g p)
    rw [hfg p] at h
    exact (hτ.leftInverse _).symm.trans (congrArg (translate (-a)) h.symm)
  let φ : SchubertSpace ab N hN ≃ₜ SchubertSpace (shiftPair a ab) M hM :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg
      continuous_toFun := continuous_of_translation hτ.continuousForward E F f hf
      continuous_invFun := continuous_of_translation hτ.continuousInverse F E g hg }
  let eTop := TopCat.isoOfHomeo φ
  have hDepth := translation_sameDepth E F hE hF eTop.hom hf hτ
  refine ⟨{
    schemeIso := e
    analyticIso := eTop
    onPoints := fun _ ↦ rfl
    onInversePoints := fun _ ↦ rfl
    onLattices := he
    onInverseLattices := ?_
    preservesStrata := ?_
    sameDepth := hDepth
    intertwines := translation_intertwines E F hE hF eTop.hom hf hτ }⟩
  · intro p L hp
    change schubertPointSubspace (g p) = _
    have hL : (F p).val = L := boundedSubspace_injective M ((hF p).symm.trans hp)
    have h := (hg p).trans (congrArg (fun B : BoundedLattice 2 M ↦ translate (-a) B.val) hL)
    exact (hE (g p)).trans (congrArg (latticeSubspace (-(N : ℤ)) (2 * N)) h)
  · let i : OrbitIndex ab ≃ OrbitIndex (shiftPair a ab) :=
      finCongr (congrArg (fun m : ℕ ↦ m / 2 + 1) (difference_shift a ab).symm)
    exact ⟨i, fun j ↦ ⟨rfl, hDepth j (i j) rfl⟩⟩

end RepTheorySurvey.Geometric.CentralSchubertComparison
