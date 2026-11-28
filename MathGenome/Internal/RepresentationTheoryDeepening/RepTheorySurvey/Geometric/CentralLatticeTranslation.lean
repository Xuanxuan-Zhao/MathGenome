import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralLatticeTranslation
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShiftedStableWindows
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralSchubertComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralFrameDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
import Mathlib.Topology.Sheaves.Points

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open scoped Matrix MatrixGroups

namespace RepTheorySurvey.Geometric.CentralLatticeTranslation

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open CentralLatticeTranslationSpecs
open Analytic Analytic.IntersectionComplex LocalSheaf
open EquivariantHomeomorphismDirectImageSpecs (EquivariantDirectImageComparison PullbackIntertwines)
open CentralSchubertComparisonSpecs (ShiftedMinimalWindow ScalarTranslationProperties ContinuousBoundedTranslation)

private theorem scalarLoop_linear (a : ℤ) :
    loopLinearEquiv 2 (scalarLoop a) = diagonalEquiv (fun _ ↦ a) :=
  (loopLinearEquiv 2).apply_symm_apply _

private theorem translate_eq_smul (a : ℤ) (L : GL2Lattice) :
    translate a L = scalarLoop a • L := by
  change mapLattice (diagonalEquiv (fun _ ↦ a)) L =
    mapLattice (loopLinearEquiv 2 (scalarLoop a)) L
  rw [scalarLoop_linear]

private theorem translate_standard (a : ℤ) :
    translate a (standardLattice 2) = scalarLattice 2 a := rfl

private theorem scalarLoop_add (a b : ℤ) :
    scalarLoop a * scalarLoop b = scalarLoop (a + b) := by
  apply (loopLinearEquiv 2).injective
  rw [map_mul, scalarLoop_linear, scalarLoop_linear, scalarLoop_linear]
  apply LinearEquiv.ext
  intro x
  funext i
  change monomial a * (monomial b * x i) = monomial (a + b) * x i
  rw [monomial_add, mul_assoc]

private theorem scalarLoop_zero : scalarLoop 0 = 1 := by
  apply (loopLinearEquiv 2).injective
  rw [map_one, scalarLoop_linear]
  apply LinearEquiv.ext
  intro x
  funext i
  change monomial 0 * x i = x i
  simp [monomial_eq_zpow]

private theorem translate_add (a b : ℤ) (L : GL2Lattice) :
    translate a (translate b L) = translate (a + b) L := by
  simp only [translate_eq_smul, ← mul_smul, scalarLoop_add]

private theorem translate_zero (L : GL2Lattice) : translate 0 L = L := by
  simp only [translate_eq_smul, scalarLoop_zero, one_smul]

private theorem scalarLoop_comm (a : ℤ) (g : Loop) : scalarLoop a * g = g * scalarLoop a := by
  apply (loopLinearEquiv 2).injective
  rw [map_mul, map_mul, scalarLoop_linear]
  apply LinearEquiv.ext
  intro x
  change monomial a • loopLinearEquiv 2 g x = loopLinearEquiv 2 g (monomial a • x)
  rw [map_smul]

private theorem translate_smul (a : ℤ) (g : Loop) (L : GL2Lattice) :
    translate a (g • L) = g • translate a L := by
  simp only [translate_eq_smul, ← mul_smul, scalarLoop_comm a g]

private theorem scalar_fixed (a : ℤ) (h : Positive) :
    (h : Loop) • scalarLattice 2 a = scalarLattice 2 a := by
  obtain ⟨g, hg⟩ := h.property
  rw [← hg]
  exact positiveGL_preserves_scalar g a

private theorem shiftPair_add (a b : ℤ) (ab : DominantPair) :
    shiftPair a (shiftPair b ab) = shiftPair (b + a) ab := by
  apply Subtype.ext
  exact Prod.ext (add_assoc ..) (add_assoc ..)

private theorem shiftPair_zero (ab : DominantPair) : shiftPair 0 ab = ab := by
  apply Subtype.ext
  exact Prod.ext (add_zero _) (add_zero _)

private theorem translate_diagonal (a : ℤ) (ab : DominantPair) :
    translate a (diagonalLattice (pairCoweight ab)) =
      diagonalLattice (pairCoweight (shiftPair a ab)) := by
  rw [← diagonalLoop_smul_standard, ← diagonalLoop_smul_standard, translate_eq_smul, ← mul_smul]
  congr 1
  apply (loopLinearEquiv 2).injective
  rw [map_mul, scalarLoop_linear, diagonalLoop_linear, diagonalLoop_linear]
  apply LinearEquiv.ext
  intro x
  funext i
  change monomial a * (monomial (pairCoweight ab i) * x i) =
    monomial (pairCoweight (shiftPair a ab) i) * x i
  rw [← mul_assoc, ← monomial_add, add_comm a]
  simp [pairCoweight, CentralSchubertComparisonSpecs.shiftPair, apply_ite (· + a)]

private theorem translate_mem_orbit (a : ℤ) {ab : DominantPair} {L : GL2Lattice}
    (h : L ∈ gl2Orbit ab) : translate a L ∈ gl2Orbit (shiftPair a ab) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g, by
    change (g : Loop) • diagonalLattice _ = translate a ((g : Loop) • diagonalLattice _)
    rw [translate_smul, translate_diagonal]⟩

private theorem below_shift (a : ℤ) {ab cd : DominantPair} (h : Below cd ab) :
    Below (shiftPair a cd) (shiftPair a ab) := by
  obtain ⟨j, hj, h₁, h₂⟩ := h
  refine ⟨j, ?_, ?_, ?_⟩
  · change 2 * (j : ℤ) ≤ (ab.val.1 + a) - (ab.val.2 + a)
    omega
  · change cd.val.1 + a = (ab.val.1 + a) - (j : ℤ)
    omega
  · change cd.val.2 + a = (ab.val.2 + a) + (j : ℤ)
    omega

private theorem translate_mem_closure (a : ℤ) {ab : DominantPair} {L : GL2Lattice}
    (h : L ∈ closureLattices ab) : translate a L ∈ closureLattices (shiftPair a ab) := by
  obtain ⟨cd, hcd, hL⟩ := h
  exact ⟨shiftPair a cd, below_shift a hcd, translate_mem_orbit a hL⟩

private theorem translate_images (a : ℤ) (ab : DominantPair) :
    translate a '' gl2Orbit ab = gl2Orbit (shiftPair a ab) ∧
      translate a '' closureLattices ab = closureLattices (shiftPair a ab) := by
  have hp : shiftPair (-a) (shiftPair a ab) = ab := by
    rw [shiftPair_add, add_neg_cancel, shiftPair_zero]
  have hL (L : GL2Lattice) : translate a (translate (-a) L) = L := by
    rw [translate_add, add_neg_cancel, translate_zero]
  constructor
  · ext L
    constructor
    · rintro ⟨L', h, rfl⟩
      exact translate_mem_orbit a h
    · intro h
      exact ⟨translate (-a) L, hp ▸ translate_mem_orbit (-a) h, hL L⟩
  · ext L
    constructor
    · rintro ⟨L', h, rfl⟩
      exact translate_mem_closure a h
    · intro h
      exact ⟨translate (-a) L, hp ▸ translate_mem_closure (-a) h, hL L⟩

private theorem orderedCharts (a : ℤ) (ab : DominantPair) : Nonempty (OrderedCharts a ab) := by
  classical
  let l : LeftOrdered a ab → closureLattices ab := fun q ↦
    ⟨translate (-a) (leftTerminal a ab q), by
      induction q using Quotient.inductionOn with
      | _ p =>
        obtain ⟨⟨g, L⟩, hg, hL⟩ := p
        have he : coset Positive (scalarLoop a) = coset Positive g := hg.symm
        obtain ⟨_, h, rfl⟩ := (LatticeModels.cosetRelation Positive _ _).mp he
        change translate (-a) ((scalarLoop a * (h : Loop)) • L) ∈ closureLattices ab
        rw [mul_smul, ← translate_eq_smul a, translate_add, neg_add_cancel, translate_zero]
        exact schubertStable ab h hL⟩
  have ll (h : Positive) (L : closureLattices ab) :
      (l (Quotient.mk _ (leftRepresentative a ab h L))).val = (h : Loop) • L.val := by
    change translate (-a) ((scalarLoop a * (h : Loop)) • L.val) = _
    rw [mul_smul, ← translate_eq_smul a, translate_add, neg_add_cancel, translate_zero]
  let lInv (L : closureLattices ab) : LeftOrdered a ab :=
    Quotient.mk _ (leftRepresentative a ab 1 L)
  have hli : Function.LeftInverse lInv l := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      obtain ⟨⟨g, L⟩, hg, hL⟩ := p
      have he : coset Positive (scalarLoop a) = coset Positive g := hg.symm
      obtain ⟨_, h, rfl⟩ := (LatticeModels.cosetRelation Positive _ _).mp he
      let U : closureLattices ab := ⟨L, hL⟩
      have hc : l (Quotient.mk _ (leftRepresentative a ab h U)) =
          ⟨(h : Loop) • L, schubertStable ab h hL⟩ := Subtype.ext (ll h U)
      change lInv (l (Quotient.mk _ (leftRepresentative a ab h U))) = _
      rw [hc]
      apply Quotient.sound
      refine ⟨h, ?_, ?_⟩
      · change _ = (scalarLoop a * ((1 : Positive) : Loop)) * _
        simp
      · change L = ((h⁻¹ : Positive) : Loop) • ((h : Loop) • L)
        simp [← mul_smul]
  have hls : Function.RightInverse lInv l := by
    intro L
    exact Subtype.ext ((ll 1 L).trans (by simp))
  let lequiv : LeftOrdered a ab ≃ closureLattices ab := ⟨l, lInv, hli, hls⟩
  obtain ⟨e, he⟩ := BoundedLattices.glCosets 2
  let r : RightOrdered a ab → closureLattices ab := fun q ↦
    ⟨e (firstProjection Positive (centralStable a) q).val, by
      obtain ⟨g, hg, hcos⟩ := (firstProjection Positive (centralStable a) q).property
      rw [← hcos, he]
      exact hg⟩
  have rr (g : Loop) (hg : g • standardLattice 2 ∈ closureLattices ab) :
      (r (Quotient.mk _ (rightRepresentative a ab g hg))).val = g • standardLattice 2 :=
    he g
  have hrinj : Function.Injective r := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        obtain ⟨⟨g, L⟩, hg, hL⟩ := p
        obtain ⟨⟨g', L'⟩, hg', hL'⟩ := q
        have hEq : L = scalarLattice 2 a := hL
        have hEq' : L' = scalarLattice 2 a := hL'
        subst L
        subst L'
        have hc : coset Positive g = coset Positive g' := e.injective (congrArg Subtype.val hpq)
        obtain ⟨_, h, hh⟩ := (LatticeModels.cosetRelation Positive _ _).mp hc
        exact Quotient.sound ⟨h, hh, (scalar_fixed a h⁻¹).symm⟩
  have hrsurj : Function.Surjective r := by
    intro L
    obtain ⟨g, hg⟩ := BoundedLattices.glTransitive 2 L.val
    have hg' : g • standardLattice 2 ∈ closureLattices ab := hg.symm ▸ L.property
    exact ⟨Quotient.mk _ (rightRepresentative a ab g hg'), Subtype.ext ((rr g hg').trans hg)⟩
  let requiv := Equiv.ofBijective r ⟨hrinj, hrsurj⟩
  refine ⟨⟨lequiv, requiv, ll, rr, ?_, ?_⟩⟩
  · intro q
    change _ = translate a (translate (-a) _)
    rw [translate_add, add_neg_cancel, translate_zero]
  · intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      obtain ⟨⟨g, L⟩, hg, hL⟩ := p
      have hEq : L = scalarLattice 2 a := hL
      subst L
      change g • scalarLattice 2 a = translate a (e (coset Positive g))
      rw [he, translate_smul, translate_standard]

theorem orderedCentralProducts :
    OrderedCentralProducts :=
  orderedCharts

theorem windowTranslation : WindowTranslation :=
  ShiftedStableWindows.windowTranslation

private def translateWindow (a : ℤ) {b : ℤ} {m : ℕ} (L : WindowLattice 2 b m) :
    WindowLattice 2 (b + a) m :=
  ⟨translate a L.val, ((windowTranslation a b m).1 L).1⟩

private theorem translate_windowSubspace (a b : ℤ) (m : ℕ) (L : WindowLattice 2 b m) :
    latticeSubspace (b + a) m (translate a L.val) =
      (latticeSubspace b m L.val).map (shiftWindow a b m).toLinearMap :=
  ((windowTranslation a b m).1 L).2

open private stableStageIncidence windowPoint_has_lattice windowStageSubspace_injective
  windowStageInclusion from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

open private stableStagePlane from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

private theorem window_stagePlane_eq (r : ℕ) (b : ℤ) (m : ℕ) (p : WindowStage r b m) :
    stableStagePlane (windowBasis r b m) (windowOperator r b m) p =
      windowStageSubspace p := rfl

section WindowIncidence

attribute [local irreducible] windowBasis windowOperator latticeSubspace

set_option maxHeartbeats 350000 in
/-- On complex points the translated window is a closed analytic embedding. -/
private theorem shiftWindow_embedding (a b : ℤ) (m : ℕ) :
    ∃ f : WindowStage 2 b m → WindowStage 2 (b + a) m, Topology.IsClosedEmbedding f ∧
      ∀ (L : WindowLattice 2 b m) (p : WindowStage 2 b m),
        windowStageSubspace p = latticeSubspace b m L.val →
          windowStageSubspace (f p) = latticeSubspace (b + a) m (translate a L.val) := by
  let Z := Fin 0 → ℂ
  let : Subsingleton Z := ⟨fun _ _ ↦ funext fun i ↦ Fin.elim0 i⟩
  let : Unique (Z × Z) := ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let s : Window 2 (b + a) m ≃ₗ[ℂ] Window 2 b m × (Z × Z) :=
    (shiftWindow a b m).symm ≪≫ₗ LinearEquiv.prodUnique.symm
  have hdim : Module.finrank ℂ Z = 0 := Module.finrank_zero_of_subsingleton
  have hcoord (L : WindowLattice 2 b m) (w : Window 2 (b + a) m) :
      w ∈ latticeSubspace (b + a) m (translate a L.val) ↔
        (s w).1 ∈ latticeSubspace b m L.val ∧ (s w).2.2 = 0 := by
    rw [translate_windowSubspace, Submodule.mem_map]
    have hs : (s w).1 = (shiftWindow a b m).symm w := rfl
    rw [hs]
    simp only [show (s w).2.2 = 0 from Subsingleton.elim _ _, and_true]
    constructor
    · rintro ⟨y, hy, h⟩
      change shiftWindow a b m y = w at h
      rw [← h, LinearEquiv.symm_apply_apply]
      exact hy
    · intro h
      exact ⟨_, h, (shiftWindow a b m).apply_symm_apply w⟩
  have hsource := windowPoint_has_lattice (a := b) (m := m) (r := 2)
  have hl (p : WindowStage 2 b m) : ∃ L : WindowLattice 2 b m,
      stableStagePlane (windowBasis 2 b m) (windowOperator 2 b m) p =
        latticeSubspace b m L.val := by
    rw [window_stagePlane_eq]
    exact hsource p
  have h := stableStageIncidence s (windowBasis 2 b m) (windowBasis 2 (b + a) m)
    (windowOperator 2 b m) (windowOperator 2 (b + a) m)
    (fun L : WindowLattice 2 b m ↦ latticeSubspace b m L.val)
    (fun L ↦ latticeSubspace (b + a) m (translate a L.val)) 0 hdim hcoord
    (fun L ↦ latticeSubspace_stable (b + a) m (translate a L.val)) hl
  obtain ⟨f, hf, hp⟩ := h.2
  refine ⟨f, hf, fun L p hL ↦ ?_⟩
  have h₁ := window_stagePlane_eq 2 b m p
  have h₂ := window_stagePlane_eq 2 (b + a) m (f p)
  have hp₁ : stableStagePlane (windowBasis 2 b m) (windowOperator 2 b m) p =
      latticeSubspace b m L.val := h₁.trans hL
  exact h₂.symm.trans (hp L p hp₁)

end WindowIncidence

private theorem translate_bounded_continuous (a : ℤ) (N M : ℕ)
    (h₁ : -(M : ℤ) ≤ -(N : ℤ) + a)
    (h₂ : -(N : ℤ) + a + ((2 * N : ℕ) : ℤ) ≤ -(M : ℤ) + ((2 * M : ℕ) : ℤ))
    {X : Type} [TopologicalSpace X]
    (e : X → BoundedLattice 2 N) (he : Continuous e)
    (u : X → BoundedLattice 2 M) (hu : ∀ x, (u x).val = translate a (e x).val) :
    Continuous u := by
  let intoWindow (L : BoundedLattice 2 N) : WindowLattice 2 (-(N : ℤ)) (2 * N) :=
    ⟨L.val, by simpa only [boundedExponent] using L.property⟩
  obtain ⟨f, hf, hfp⟩ := shiftWindow_embedding a (-(N : ℤ)) (2 * N)
  obtain ⟨g, hg, hgp⟩ := windowStageInclusion 2 (-(N : ℤ) + a) (-(M : ℤ))
    (2 * N) (2 * M) h₁ h₂
  have hform (x : X) : boundedPoint (u x) = g (f (boundedPoint (e x))) := by
    let L := translateWindow a (intoWindow (e x))
    have h := hgp L
    change g (windowStagePoint (-(N : ℤ) + a) (2 * N) L.val) =
      windowStagePoint (-(M : ℤ)) (2 * M) L.val at h
    change windowStagePoint (-(M : ℤ)) (2 * M) (u x).val = _
    rw [hu x]
    change windowStagePoint (-(M : ℤ)) (2 * M) L.val = _
    rw [← h]
    congr 1
    apply windowStageSubspace_injective 2 (-(N : ℤ) + a) (2 * N)
    exact (BoundedLattices.windowStageComparison 2 (-(N : ℤ) + a) (2 * N)).2 L |>.trans
      (hfp (intoWindow (e x)) _ ((BoundedLattices.boundedStageComparison 2 N).2 (e x))).symm
  apply continuous_induced_rng.mpr
  change Continuous (fun x ↦ boundedPoint (u x))
  simp only [hform]
  have hb : Continuous (boundedPoint (r := 2) (N := N)) := continuous_induced_dom
  exact hg.continuous.comp (hf.continuous.comp (hb.comp he))

private theorem translate_continuous (a : ℤ) : Continuous (translate a) := by
  change @Continuous _ _ (⨆ N : ℕ, TopologicalSpace.coinduced
    (Subtype.val : BoundedLattice 2 N → GL2Lattice) inferInstance) _ _
  apply continuous_iSup_dom.mpr
  intro N
  apply continuous_coinduced_dom.mpr
  let M := N + a.natAbs
  have h₁ : -(M : ℤ) ≤ -(N : ℤ) + a := by
    have ha : -a ≤ ((-a).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at ha
    simp only [M, Nat.cast_add]
    linarith only [ha]
  have h₂ : -(N : ℤ) + a + ((2 * N : ℕ) : ℤ) ≤ -(M : ℤ) + ((2 * M : ℕ) : ℤ) := by
    rw [boundedExponent]
    have ha : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
    simp only [M, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [ha]
  let intoBounded (L : BoundedLattice 2 N) : BoundedLattice 2 M :=
    ⟨translate a L.val, by
      have h := (translateWindow a (⟨L.val, by simpa only [boundedExponent] using L.property⟩ :
        WindowLattice 2 (-(N : ℤ)) (2 * N))).property
      rw [boundedExponent] at h₂
      exact ⟨(diagonalLattice_le fun _ ↦ h₂).trans h.1,
        h.2.trans (diagonalLattice_le fun _ ↦ h₁)⟩⟩
  have hval : Continuous (Subtype.val : BoundedLattice 2 M → GL2Lattice) :=
    continuous_iSup_rng (i := M) continuous_coinduced_rng
  exact hval.comp (translate_bounded_continuous a N M h₁ h₂ id continuous_id intoBounded
    (fun _ ↦ rfl))

theorem scalarTranslation : ScalarTranslation :=
  ⟨translate_standard, translate_add, translate_zero, scalarLoop_comm, scalar_fixed,
    translate_images, fun a ↦ ⟨translate_continuous a, translate_continuous (-a)⟩⟩

private theorem centralPair_difference (a : ℤ) : difference (centralPair a) = 0 := by
  change (a - a).toNat = 0
  simp

private theorem centralPoint_scheme (a : ℤ) (N : ℕ) (hN : OrbitBound (centralPair a) N) :
    Nonempty (occupiedSchubert (centralPair a) N hN ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)) := by
  let ab := centralPair a
  obtain ⟨e⟩ := (RankTwoSchubertStrata.equalPairOrbit ab N hN rfl).2.2
  let j := orbitToSchubert ab N hN
  have htop : orbitOpen ab N hN = ⊤ := by simp [orbitOpen, ab, centralPair_difference]
  have hj : IsIso j.left := by
    change IsIso (orbitOpen ab N hN).ι
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι, htop]
  have : IsIso ((Over.forget _).map j) := hj
  let : IsIso j := isIso_of_reflects_iso _ (Over.forget _)
  exact ⟨(asIso j).symm ≪≫ e⟩

private theorem centralPoint_subspace (a : ℤ) (N : ℕ) (hN : OrbitBound (centralPair a) N)
    (p : SchubertSpace (centralPair a) N hN) :
    schubertPointSubspace p = latticeSubspace (-(N : ℤ)) (2 * N) (scalarLattice 2 a) := by
  obtain ⟨E, hE, _⟩ := RankTwoSchubertStrata.schubertStratification (centralPair a) N hN
  have h := (E p).property
  change (E p).val.val ∈ closureLattices (centralPair a) at h
  rw [(RankTwoSchubertStrata.equalPairOrbit (centralPair a) N hN rfl).1] at h
  have he : (E p).val.val = scalarLattice 2 a := h
  rw [hE p, boundedSubspace, he]

set_option maxHeartbeats 650000 in
/-- Continuity also holds when the image already lies in a smaller target window. -/
private theorem translate_between_continuous (a : ℤ) : ContinuousBoundedTranslation a := by
  intro N M X _ e u he hu
  let P := max M (N + a.natAbs)
  have hP : (N : ℤ) + (a.natAbs : ℤ) ≤ (P : ℤ) := by
    exact_mod_cast (le_max_right M (N + a.natAbs))
  have h₁ : -(P : ℤ) ≤ -(N : ℤ) + a := by
    have h : -a ≤ ((-a).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at h
    linarith only [hP, h]
  have h₂ : -(N : ℤ) + a + ((2 * N : ℕ) : ℤ) ≤ -(P : ℤ) + ((2 * P : ℕ) : ℤ) := by
    rw [boundedExponent]
    have h : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hP, h]
  let hMP : M ≤ P := le_max_left _ _
  have hIncl := BoundedLattices.boundedInclusionTopology 2 M P hMP
  apply hIncl.isEmbedding.continuous_iff.mpr
  exact translate_bounded_continuous a N P h₁ h₂ e he (boundedInclusion hMP ∘ u) hu

private theorem shiftedMinimalWindow (a : ℤ) (ab : DominantPair) : ShiftedMinimalWindow a ab := by
  have hW := windowTranslation a ab.val.2 (difference ab)
  refine ⟨fun L ↦ (hW.1 L).1, ?_⟩
  intro d
  obtain ⟨d', hd', e, he, _⟩ := hW.2.2 d
  refine ⟨d', hd', e, fun q L hL ↦ ?_⟩
  rw [he q, hL]
  exact (translate_windowSubspace a ab.val.2 (difference ab) L).symm

private theorem scalarTranslationProperties (a : ℤ) : ScalarTranslationProperties a :=
  ⟨fun L ↦ by
      change translate (-a) (translate a L) = L
      rw [translate_add, neg_add_cancel, translate_zero],
    fun L ↦ by
      change translate a (translate (-a) L) = L
      rw [translate_add, add_neg_cancel, translate_zero],
    fun ab ↦ (translate_images a ab).1, fun ab ↦ (translate_images a ab).2,
    fun g L ↦ translate_smul a (positiveGLMap 2 g) L,
    translate_between_continuous a, translate_between_continuous (-a)⟩

theorem schubertTranslation : SchubertTranslation :=
  fun a ab ↦ CentralSchubertComparison.schubertTranslation a ab (shiftedMinimalWindow a ab)
    (scalarTranslationProperties a)

open private lattice_under_actual_action difference_shift from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralSchubertComparison

private theorem boundedClosure_bijective (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    Function.Bijective (fun L : schubertLatticeSet ab N ↦
      (⟨L.val.val, L.property⟩ : closureLattices ab)) := by
  constructor
  · intro L U h
    have h₀ : L.val.val = U.val.val := congrArg (fun v : closureLattices ab ↦ v.val) h
    exact Subtype.ext (Subtype.ext h₀)
  · intro L
    obtain ⟨B, hB⟩ := RankTwoSchubertStrata.closureLattices_bounded hN L.property
    have hB' : B.val ∈ closureLattices ab := hB.symm ▸ L.property
    exact ⟨⟨B, hB'⟩, Subtype.ext hB⟩

set_option maxHeartbeats 500000 in
private theorem realizeOrderedSchemes {J : GL2JetParameters} {a : ℤ} {ab : DominantPair}
    {N M C : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C} (A : SchubertJetAction J ab N hN)
    (T : SchubertTranslationData a ab N M hN hM) (W : OrderedCharts a ab)
    (point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)) :
    Nonempty (RealizesOrderedSchemes A T W point) := by
  obtain ⟨E, hE, _⟩ := RankTwoSchubertStrata.schubertStratification ab N hN
  let f := E.toEquiv.trans (Equiv.ofBijective _ (boundedClosure_bijective ab N hN))
  let left := f.trans W.left.symm
  let right := f.trans W.right.symm
  have hl (p : SchubertSpace ab N hN) : (W.left (left p)).val = (E p).val.val := by
    change (W.left (W.left.symm (f p))).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hr (p : SchubertSpace ab N hN) : (W.right (right p)).val = (E p).val.val := by
    change (W.right (W.right.symm (f p))).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨⟨E, hE, left, right, fun p ↦ ⟨hl p, hr p, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · apply Subtype.ext
    exact (firstProjection Positive (schubertStable ab) (left p)).property
  · intro k hk g
    apply W.left.injective
    apply Subtype.ext
    rw [hl, W.leftChart]
    exact lattice_under_actual_action E hE J A k hk g p
  · intro g hg
    have hRight : right p = Quotient.mk _ (rightRepresentative a ab g (hg.symm ▸ (E p).property)) := by
      apply W.right.injective
      apply Subtype.ext
      rw [hr, W.rightChart]
      exact hg.symm
    exact ⟨by rw [hRight]; rfl, hRight⟩
  · exact centralPoint_subspace a C hC _
  · rw [← T.onPoints p, W.leftMap, hl]
    exact T.onLattices p (E p).val (hE p)
  · rw [← T.onPoints p, W.rightMap, hr]
    exact T.onLattices p (E p).val (hE p)

section FrameTopology

open LinearAlgebraicGroups.Specs.GrassmannianCharts
open scoped Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open private scalarLattice_zero from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

private def shiftedFrameMatrix (b : ℤ) (B : Matrix (Fin 2) (Fin 2) O) : Matrix (Fin 2) (Fin 2) K :=
  monomial b • inclusion.mapMatrix B

private theorem det_shiftedFrameMatrix (b : ℤ) (B : Matrix (Fin 2) (Fin 2) O) :
    (shiftedFrameMatrix b B).det = monomial (b + b) * inclusion B.det := by
  rw [shiftedFrameMatrix, Matrix.det_smul, ← inclusion.map_det B]
  simp only [Fintype.card_fin, pow_two, monomial_add]

private theorem det_orbitFrame (ab : DominantPair) (g : GL (Fin 2) O) :
    ((positiveGLMap 2 g * diagonalLoop 2 (pairCoweight ab)).val).det =
      monomial (ab.val.1 + ab.val.2) * inclusion g.val.det := by
  change ((inclusion.mapMatrix g.val) * Matrix.diagonal (fun i ↦ monomial (pairCoweight ab i))).det = _
  rw [Matrix.det_mul, Matrix.det_diagonal, ← inclusion.map_det g.val, Fin.prod_univ_two, ← monomial_add]
  simp [pairCoweight, mul_comm]

private theorem closureFrame_det (ab : DominantPair) (L : GL2Lattice)
    (hL : L ∈ closureLattices ab) :
    ∃ (g : Loop) (u : O), g • standardLattice 2 = L ∧ IsUnit u ∧
      g.val.det = monomial (ab.val.1 + ab.val.2) * inclusion u := by
  obtain ⟨cd, ⟨j, _, h₁, h₂⟩, g, rfl⟩ := hL
  obtain ⟨g', hg'⟩ := g.property
  have hs : cd.val.1 + cd.val.2 = ab.val.1 + ab.val.2 := by omega
  refine ⟨positiveGLMap 2 g' * diagonalLoop 2 (pairCoweight cd), g'.val.det, ?_,
    Matrix.isUnits_det_units g', ?_⟩
  · rw [mul_smul, diagonalLoop_smul_standard, hg']
    rfl
  · rw [det_orbitFrame, hs]

private theorem frameColumn_mem (g : Loop) (j : Fin 2) :
    (fun i ↦ g.val i j) ∈ (g • standardLattice 2).val := by
  change _ ∈ (standardLattice 2).val.map ((loopLinearEquiv 2 g).restrictScalars O).toLinearMap
  refine ⟨coordinateInclusion 2 (Pi.single j 1), ⟨_, rfl⟩, ?_⟩
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, loopLinearEquiv_apply]
  funext i
  change (∑ k : Fin 2, g.val i k * inclusion ((Pi.single j (1 : O) : Fin 2 → O) k)) = g.val i j
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp

private theorem matrix_factors_through_frame (g : Loop) (A : Matrix (Fin 2) (Fin 2) K)
    (hA : ∀ j, (fun i ↦ A i j) ∈ (g • standardLattice 2).val) :
    ∃ B : Matrix (Fin 2) (Fin 2) O, A = g.val * inclusion.mapMatrix B := by
  have h (j : Fin 2) : ∃ x : Fin 2 → O, (loopLinearEquiv 2 g) (coordinateInclusion 2 x) = fun i ↦ A i j := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hA j
    exact ⟨x, hx⟩
  choose x hx using h
  refine ⟨fun i j ↦ x j i, ?_⟩
  apply Matrix.ext
  intro i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, coordinateInclusion, inclusion, LaurentSeries.coe_algebraMap] using (congrFun (hx j) i).symm

private theorem det_shifted_eq_pow {b : ℤ} {n : ℕ} {B : Matrix (Fin 2) (Fin 2) O} {v : O}
    (h : (shiftedFrameMatrix b B).det = monomial (b + b + (n : ℤ)) * inclusion v) :
    B.det = t ^ n * v := by
  rw [det_shiftedFrameMatrix, monomial_add (b + b) (n : ℤ), monomial_nat, mul_assoc, ← map_mul] at h
  exact HahnSeries.ofPowerSeries_injective (mul_left_cancel₀ (monomial_ne_zero _) h)

private theorem frames_from_columns {ab : DominantPair} {L : GL2Lattice} (hL : L ∈ closureLattices ab)
    (b : ℤ) (n : ℕ) (hdegree : ab.val.1 + ab.val.2 = b + b + (n : ℤ))
    (A : Matrix (Fin 2) (Fin 2) O)
    (hA : ∀ j, (fun i ↦ shiftedFrameMatrix b A i j) ∈ L.val)
    (hdet : PowerSeries.coeff n A.det ≠ 0) :
    ∃ g : Loop, g • standardLattice 2 = L ∧ g.val = shiftedFrameMatrix b A := by
  obtain ⟨g, u, hg, _, hdetg⟩ := closureFrame_det ab L hL
  have hcol : ∀ j, (fun i ↦ shiftedFrameMatrix b A i j) ∈ (g • standardLattice 2).val := by
    rw [hg]; exact hA
  obtain ⟨B, hB⟩ := matrix_factors_through_frame g (shiftedFrameMatrix b A) hcol
  have hdetA : A.det = t ^ n * (u * B.det) := by
    apply det_shifted_eq_pow (b := b)
    rw [hB, Matrix.det_mul, ← inclusion.map_det B, hdetg, hdegree, mul_assoc, ← map_mul]
  have huB : IsUnit (PowerSeries.constantCoeff (u * B.det)) := by
    have hcoeff : PowerSeries.coeff n A.det = PowerSeries.constantCoeff (u * B.det) := by
      rw [hdetA]
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using PowerSeries.coeff_X_pow_mul (u * B.det) n 0
    exact isUnit_iff_ne_zero.mpr (hcoeff ▸ hdet)
  have hBunit : IsUnit B.det := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    exact isUnit_of_mul_isUnit_right (by simpa only [map_mul] using huB)
  let h := Matrix.GeneralLinearGroup.mk'' B hBunit
  refine ⟨g * positiveGLMap 2 h, ?_, hB.symm⟩
  rw [mul_smul, ← scalarLattice_zero, positiveGL_preserves_scalar, scalarLattice_zero, hg]

private theorem detCoefficients_continuous {X : Type} [TopologicalSpace X]
    (A : X → Matrix (Fin 2) (Fin 2) O)
    (hA : ∀ i j n, Continuous (fun x ↦ PowerSeries.coeff n (A x i j))) (n : ℕ) :
    Continuous (fun x ↦ PowerSeries.coeff n (A x).det) := by
  simp only [Matrix.det_fin_two, map_sub, PowerSeries.coeff_mul]
  exact (continuous_finsetSum _ (fun i _ ↦ (hA 0 0 i.1).mul (hA 1 1 i.2))).sub
    (continuous_finsetSum _ (fun i _ ↦ (hA 0 1 i.1).mul (hA 1 0 i.2)))

private theorem quotientMap_of_localSections {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (h : ∀ y : Y, ∃ (U : Type) (_ : TopologicalSpace U) (j : U → Y) (s : U → X),
      IsOpenMap j ∧ y ∈ Set.range j ∧ Continuous s ∧ f ∘ s = j) : IsQuotientMap f := by
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun V ↦ ⟨?_, fun hV ↦ hV.preimage hf⟩, ?_⟩
  · intro hV
    apply isOpen_iff_mem_nhds.2
    intro y hy
    obtain ⟨U, _, j, s, hj, ⟨u, rfl⟩, hs, he⟩ := h y
    have hOp : IsOpen (j '' (s ⁻¹' (f ⁻¹' V))) := hj _ (hV.preimage hs)
    have hmem : u ∈ s ⁻¹' (f ⁻¹' V) := by
      change (f ∘ s) u ∈ V
      rw [he]
      exact hy
    exact Filter.mem_of_superset (hOp.mem_nhds ⟨u, hmem, rfl⟩) (by
      rintro _ ⟨v, hv, rfl⟩
      rw [← he]
      exact hv)
  · intro y
    obtain ⟨_, _, j, s, _, ⟨u, rfl⟩, _, he⟩ := h y
    exact ⟨s u, congrFun he u⟩

open private windowProjection windowProjection_range windowInverseImage_latticeSubspace
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

private def windowFrameCoordinates (b : ℤ) (m : ℕ) :
    (Fin 2 → O) →ₗ[ℂ] (Fin 2 × Fin m → ℂ) :=
  (windowCoordinates 2 b m).toLinearMap.comp
    (((windowProjection 2 b m).comp (shiftedCoordinates 2 b).toLinearMap).restrictScalars ℂ)

private theorem windowFrameCoordinates_surjective (b : ℤ) (m : ℕ) :
    Function.Surjective (windowFrameCoordinates b m) :=
  (windowCoordinates 2 b m).surjective.comp
    ((LinearMap.range_eq_top.1 (windowProjection_range 2 b m)).comp
      (shiftedCoordinates 2 b).surjective)

private theorem windowFrameCoordinates_mem {b : ℤ} {m : ℕ} (L : WindowLattice 2 b m)
    (v : Fin 2 → O) :
    windowFrameCoordinates b m v ∈
      (latticeSubspace b m L.val).map (windowCoordinates 2 b m).toLinearMap ↔
    shiftedInclusion 2 b v ∈ L.val.val := by
  have h := windowInverseImage_latticeSubspace L
  let x := shiftedCoordinates 2 b v
  change _ ↔ (x : Coordinates 2) ∈ L.val.val.restrictScalars ℂ
  rw [← h]
  constructor
  · intro hv
    obtain ⟨w, hw, he⟩ := hv
    have he' : w = windowProjection 2 b m x := (windowCoordinates 2 b m).injective he
    refine ⟨x, ?_, rfl⟩
    change windowProjection 2 b m x ∈ latticeSubspace b m L.val
    rwa [← he']
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := Subtype.ext he
    subst y
    exact ⟨windowProjection 2 b m x, hy, rfl⟩

private theorem schubert_local_frame {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (p₀ : SchubertSpace ab N hN) :
    ∃ (U : Type) (_ : TopologicalSpace U) (j : U → SchubertSpace ab N hN) (s : U → RightFrameSpace E),
      IsOpenMap j ∧ p₀ ∈ Set.range j ∧ Continuous s ∧ (rightFrameProjection E) ∘ s = j := by
  classical
  let X := SchubertSpace ab N hN
  let b : ℤ := -(N : ℤ)
  let m := 2 * N
  let d := occupiedDimension ab N hN
  let B := windowBasis 2 b m
  let hd := windowDimension_le d
  let f : X → GrassmannianPoints B hd := fun p ↦ p ≫ schubertToGrassmannian ab N hN d
  have hf : Continuous f := continuous_induced_dom
  obtain ⟨I, A₀, hchart⟩ := grassmannianChartPoint_cover B hd (f p₀)
  let chart := grassmannianChartPoint B hd I
  let hEmb := SchubertAnalyticFlagTransport.graphChartOpenEmbeddings B hd I
  let U : Set X := f ⁻¹' Set.range chart
  have hU : IsOpen U := hEmb.isOpen_range.preimage hf
  have hp₀ : p₀ ∈ U := ⟨A₀, hchart⟩
  let D : U → Matrix (Outside I) (Inside I) ℂ := fun p ↦
    hEmb.isEmbedding.toHomeomorph.symm ⟨f p.val, p.property⟩
  have hD : Continuous D := hEmb.isEmbedding.toHomeomorph.symm.continuous.comp
    ((hf.comp continuous_subtype_val).subtype_mk _)
  have hDpt (p : U) : chart (D p) = f p.val :=
    congrArg Subtype.val (hEmb.isEmbedding.toHomeomorph.apply_symm_apply ⟨f p.val, p.property⟩)
  have hplane (p : U) :
      (boundedSubspace (E p.val).val).map (windowCoordinates 2 b m).toLinearMap =
        (Matrix.toLin' (graphMatrix I (D p))).range := by
    rw [← hE p.val]
    change (grassmannianSubspace B hd (f p.val)).map B.equivFun.toLinearMap = _
    rw [← hDpt p]
    exact grassmannianChartSubspace B hd I (D p)
  obtain ⟨g₀, u, hg₀, hu, hdet₀⟩ := closureFrame_det ab (E p₀).val.val (E p₀).property
  have hcol₀ (j : Fin 2) : (fun i ↦ g₀.val i j) ∈ (scalarLattice 2 b).val :=
    (E p₀).val.property.2 (hg₀ ▸ frameColumn_mem g₀ j)
  simp only [scalarLattice_val, LinearMap.mem_range] at hcol₀
  choose y₀ hy₀ using hcol₀
  let F₀ : Matrix (Fin 2) (Fin 2) O := fun i j ↦ y₀ j i
  have hF₀ : shiftedFrameMatrix b F₀ = g₀.val := by
    apply Matrix.ext
    intro i j
    exact congrFun (hy₀ j) i
  let L (p : X) : WindowLattice 2 b m :=
    ⟨(E p).val.val, by simpa only [b, m, boundedExponent] using (E p).val.property⟩
  have hcols₀ (j : Fin 2) : windowFrameCoordinates b m (y₀ j) ∈
      (Matrix.toLin' (graphMatrix I (D ⟨p₀, hp₀⟩))).range := by
    rw [← hplane ⟨p₀, hp₀⟩]
    exact (windowFrameCoordinates_mem (L p₀) _).2 (hy₀ j ▸ hg₀ ▸ frameColumn_mem g₀ j)
  choose z hz using fun j ↦ LinearMap.mem_range.mp (hcols₀ j)
  let a (p : U) (j : Fin 2) : Fin 2 × Fin m → ℂ := graphMatrix I (D p) *ᵥ z j
  have ha₀ (j : Fin 2) : a ⟨p₀, hp₀⟩ j = windowFrameCoordinates b m (y₀ j) := hz j
  have ha (j : Fin 2) : Continuous (fun p ↦ a p j) := by
    apply continuous_pi
    intro i
    change Continuous (fun p ↦ ∑ k : Inside I, graphMatrix I (D p) i k * z j k)
    apply continuous_finsetSum
    intro k _
    apply Continuous.mul _ continuous_const
    by_cases h : i ∈ I.val
    · simpa [graphMatrix, h] using (continuous_const (y := if i = k.val then (1 : ℂ) else 0) :
        Continuous (fun _ : U ↦ if i = k.val then (1 : ℂ) else 0))
    · change Continuous (fun p : U ↦ graphMatrix I (D p) i k)
      simp only [graphMatrix, Matrix.of_apply, dite_eq_right h]
      exact hD.matrix_elem ⟨i, h⟩ k
  obtain ⟨ℓ, hℓ⟩ := (windowFrameCoordinates b m).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (windowFrameCoordinates_surjective b m))
  have hℓ' (v) : windowFrameCoordinates b m (ℓ v) = v :=
    congrFun (congrArg DFunLike.coe hℓ) v
  let y (p : U) (j : Fin 2) := y₀ j + ℓ (a p j - a ⟨p₀, hp₀⟩ j)
  have hy (p : U) (j : Fin 2) : windowFrameCoordinates b m (y p j) = a p j := by
    simp only [y, map_add, hℓ', ha₀]
    abel
  let F (p : U) : Matrix (Fin 2) (Fin 2) O := fun i j ↦ y p j i
  have hF : F ⟨p₀, hp₀⟩ = F₀ := by
    apply Matrix.ext; intro i j
    change (y₀ j + ℓ (_ - _)) i = _
    simp [F₀]
  have hcolumns (p : U) (j : Fin 2) :
      (fun i ↦ shiftedFrameMatrix b (F p) i j) ∈ (E p.val).val.val.val := by
    apply (windowFrameCoordinates_mem (L p.val) (y p j)).1
    change windowFrameCoordinates b m (y p j) ∈
      (boundedSubspace (E p.val).val).map (windowCoordinates 2 b m).toLinearMap
    rw [hy, hplane p]
    exact ⟨z j, rfl⟩
  have hCoeff (i j : Fin 2) (n : ℕ) : Continuous (fun p ↦ PowerSeries.coeff n (F p i j)) := by
    let v := (PowerSeries.coeff n).comp ((LinearMap.proj i).comp ℓ)
    change Continuous (fun p ↦ PowerSeries.coeff n (y₀ j i) + v (a p j - a ⟨p₀, hp₀⟩ j))
    exact continuous_const.add (v.continuous_of_finiteDimensional.comp ((ha j).sub continuous_const))
  let n := (ab.val.1 + ab.val.2 - (b + b)).toNat
  have hdeg : ab.val.1 + ab.val.2 = b + b + (n : ℤ) := by
    have h1 : b ≤ ab.val.1 := by simpa [b, pairCoweight] using (hN 0).1
    have h2 : b ≤ ab.val.2 := by simpa [b, pairCoweight] using (hN 1).1
    dsimp [n]
    omega
  have hnonzero : PowerSeries.coeff n F₀.det ≠ 0 := by
    have hd₀ : F₀.det = t ^ n * u := by
      apply det_shifted_eq_pow (b := b)
      rw [hF₀, hdet₀, hdeg]
    have hc : PowerSeries.coeff n (t ^ n * u) = PowerSeries.constantCoeff u := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using PowerSeries.coeff_X_pow_mul u n 0
    rw [hd₀, hc]
    exact (hu.map PowerSeries.constantCoeff).ne_zero
  let V : Set U := {p | PowerSeries.coeff n (F p).det ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun (detCoefficients_continuous F hCoeff n) continuous_const
  have h₀ : (⟨p₀, hp₀⟩ : U) ∈ V := by change PowerSeries.coeff n (F _).det ≠ 0; rw [hF]; exact hnonzero
  have hg (p : V) : ∃ g : Loop, g • standardLattice 2 = (E p.val.val).val.val ∧
      g.val = shiftedFrameMatrix b (F p.val) :=
    frames_from_columns (E p.val.val).property b n hdeg (F p.val) (hcolumns p.val) p.property
  choose g hg hgmat using hg
  let s (p : V) : RightFrameSpace E := ⟨(p.val.val, ⟨g p⟩), hg p⟩
  refine ⟨V, inferInstance, fun p ↦ p.val.val, s,
    hU.isOpenMap_subtype_val.comp hV.isOpenMap_subtype_val, ⟨⟨⟨p₀, hp₀⟩, h₀⟩, rfl⟩, ?_, rfl⟩
  apply Continuous.subtype_mk
  apply (continuous_subtype_val.comp continuous_subtype_val).prodMk
  apply continuous_induced_rng.2
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  apply continuous_pi; intro k
  let v := (HahnSeries.coeff.linearMap (R := ℂ) k).comp
    ((LinearMap.proj i).comp (((shiftedInclusion 2 b).restrictScalars ℂ).comp ℓ))
  have hform (p : V) : ((g p).val i j).coeff k =
      (shiftedInclusion 2 b (y₀ j) i).coeff k + v (a p.val j - a ⟨p₀, hp₀⟩ j) := by
    rw [hgmat]
    change (shiftedInclusion 2 b (y p.val j) i).coeff k = _
    simp only [y, map_add, Pi.add_apply, HahnSeries.coeff_add]
    rfl
  change Continuous (fun p : V ↦ ((g p).val i j).coeff k)
  simp_rw [hform]
  exact continuous_const.add (v.continuous_of_finiteDimensional.comp
    (((ha j).comp continuous_subtype_val).sub continuous_const))

private theorem rightFrameProjection_isQuotient {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val) :
    IsQuotientMap (fun r : RightFrameSpace E ↦ rightFrameProjection E r) :=
  quotientMap_of_localSections _ (rightFrameProjection E).hom.continuous (schubert_local_frame E hE)

end FrameTopology

section Descent

variable {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N M C : ℕ}
  {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
  {hC : OrbitBound (centralPair a) C}
  {A : SchubertJetAction J ab N hN} {T : SchubertTranslationData a ab N M hN hM}
  {W : OrderedCharts a ab}
  {point : occupiedSchubert (centralPair a) C hC ≅ (testSpec ℂ).obj (Opposite.op complexAlgebra)}
  (S : RealizesOrderedSchemes A T W point)
  (B : SchubertJetAction J (centralPair a) C hC)
  {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
  (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
  (F G : A.action.Object) (i : G ≅ F)

private theorem rightFrameProjection_surjective :
    Function.Surjective (rightFrameProjection S.E) := by
  intro x
  obtain ⟨g, hg⟩ := BoundedLattices.glTransitive 2 (S.E x).val.val
  exact ⟨⟨(x, ⟨g⟩), hg⟩, rfl⟩

private theorem rightFrameProjection_chart (r : RightFrameSpace S.E) :
    S.right (rightFrameProjection S.E r) = Quotient.mk _ (rightFrameRepresentative a S.E r) := by
  obtain ⟨_, _, _, _, hRight, _, _, _⟩ := S.onRepresentatives (rightFrameProjection S.E r)
  exact (hRight r.val.2.loop r.property).2

open Analytic.DerivedPullbackPasting.Expected (squareValue)

private theorem pointCoefficientOverlap_of_fixed (hc : CentralPointCoefficients B η c)
    (k : ℕ) (hk : B.action.cutoff ≤ k) {R V : TopCat.{0}}
    (x : SchubertSpace (centralPair a) C hC) (s t : V ⟶ R)
    (u : V ⟶ AnalyticAction.Parameters (J.toJetSystem.group k) _)
    (hu : ∀ v : V, (u v).2 = x) : PointCoefficientOverlap B η c k hk x s t u :=
  CentralFrameDescent.rightPointComparison B η c hc k hk x s t u hu

private theorem rightFrameProjection_square
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (k : ℕ) :
    rightFrameSource J E k ≫ rightFrameProjection E =
      rightFrameTarget J E k ≫ rightFrameProjection E :=
  TopCat.ext fun r ↦ r.property.1

private theorem rightFrameJetPoint_snd
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (x : SchubertSpace (centralPair a) C hC)
    (k : ℕ) (r : RightFrameChanges J E k) :
    (rightFrameJetPoint J E x k r).2 = x := rfl

private theorem rightFramePointOverlap
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (x : SchubertSpace (centralPair a) C hC) (hc : CentralPointCoefficients B η c)
    (k : ℕ) (hk : B.action.cutoff ≤ k) :
    PointCoefficientOverlap B η c k hk x (rightFrameSource J E k)
      (rightFrameTarget J E k) (rightFrameJetPoint J E x k) :=
  pointCoefficientOverlap_of_fixed B η c hc k hk x (rightFrameSource J E k)
    (rightFrameTarget J E k) (rightFrameJetPoint J E x k) (rightFrameJetPoint_snd E x k)

private theorem rightFrameOverlap_of_coefficients
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (x : SchubertSpace (centralPair a) C hC) (hc : CentralPointCoefficients B η c)
    {F₀ G₀ : Derived (SchubertSpace ab N hN)}
    {d : (derivedInverseImage (rightFrameProjection E)).obj G₀ ≅
      (derivedInverseImage (rightFrameProjection E)).obj F₀}
    (hoverlap : ∀ {V : TopCat.{0}} (s t : V ⟶ RightFrameSpace E)
      (h : s ≫ rightFrameProjection E = t ≫ rightFrameProjection E),
        (squareValue h).hom.app G₀ ≫ (derivedInverseImage t).map d.hom =
          (derivedInverseImage s).map d.hom ≫ (squareValue h).hom.app F₀) :
    RightFrameOverlap E B x η c F₀ G₀ d := fun k hk ↦
  ⟨⟨rightFrameProjection_square E k, hoverlap _ _ (rightFrameProjection_square E k)⟩,
    rightFramePointOverlap B η c E x hc k hk⟩

private theorem centralRightDescent (hc : CentralPointCoefficients B η c)
    (hUnit : ∀ {R : TopCat.{0}} (z : R ⟶ SchubertSpace (centralPair a) C hC),
      IsIso (centralPointUnitMap z c)) :
    CentralDescent S B η c F F (Iso.refl F) false := by
  let p := rightFrameProjection S.E
  let x : SchubertSpace (centralPair a) C hC := 𝟙 _ ≫ point.inv
  let z : RightFrameSpace S.E ⟶ SchubertSpace (centralPair a) C hC :=
    TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
  let d := Iso.refl ((derivedInverseImage p).obj F.obj)
  have hOverlap : RightFrameOverlap S.E B x η c F.obj F.obj d := by
    apply rightFrameOverlap_of_coefficients B η c S.E x hc
    intro V s t hst
    let K := (derivedInverseImage (rightFrameProjection S.E)).obj F.obj
    change _ ≫ (derivedInverseImage t).map (𝟙 K) =
      (derivedInverseImage s).map (𝟙 K) ≫ _
    rw [(derivedInverseImage t).map_id K, (derivedInverseImage s).map_id K,
      Category.comp_id, Category.id_comp]
  have hd : d.hom = (derivedInverseImage p).map (Iso.refl F).hom.hom :=
    ((derivedInverseImage p).map_id F.obj).symm
  exact ⟨rightFrameProjection_surjective S, rightFrameProjection_chart S, hUnit z, d, hd, hOverlap⟩

set_option maxHeartbeats 500000 in
private theorem centralLeftDescent
    (hUnit : ∀ {R : TopCat.{0}} (z : R ⟶ SchubertSpace (centralPair a) C hC),
      IsIso (centralPointUnitMap z c)) :
    CentralDescent S B η c F G i true := by
  unfold CentralDescent
  dsimp only [↓reduceIte]
  intro k hk
  refine ⟨fun L ↦ ⟨(1, L), (A.action.action k hk).one_act L⟩, ?_, hUnit _, ?_⟩
  · intro g L
    exact (S.onRepresentatives L).2.2.2.1 k hk g
  · exact CentralFrameDescent.leftFrameComparison A.action F G i k hk

end Descent

section OrderedIncidence

set_option backward.isDefEq.respectTransparency false

open private schubertToGrassmannian_closed from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

private theorem schubertPointSubspace_injective {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N} :
    Function.Injective (schubertPointSubspace (hN := hN)) := by
  intro p q h
  let d := occupiedDimension ab N hN
  let j := schubertToGrassmannian ab N hN d
  have := schubertToGrassmannian_closed ab N hN d
  have hpq := grassmannianSubspace_injective (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d) h
  apply Over.OverMorphism.ext
  exact (cancel_mono j.left).mp (congrArg Over.Hom.left hpq)

private def complexBaseTerminal : IsTerminal ((testSpec ℂ).obj (Opposite.op complexAlgebra)) :=
  IsTerminal.ofUniqueHom complexBaseMap (fun X f ↦ by
    apply Over.OverMorphism.ext
    have h := Over.w f
    rw [algSpec_obj_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] at h
    exact (Category.comp_id f.left).symm.trans h)

private def terminalProductIso {D : Type*} [Category* D] {X P Y : D} [HasBinaryProduct P Y]
    (z : X ⟶ P) (hP : IsTerminal P) (e : X ≅ Y) : X ≅ Limits.prod P Y where
  hom := prod.lift z e.hom
  inv := prod.snd ≫ e.inv
  hom_inv_id := by simp
  inv_hom_id := by
    apply prod.hom_ext
    · exact hP.hom_ext _ _
    · simp

private def rightIncidenceHomeomorph {a : ℤ} {ab : DominantPair} {N M : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    (T : SchubertTranslationData a ab N M hN hM)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val) :
    SchubertSpace ab N hN ≃ₜ RightIncidence E a M hM := by
  let e := TopCat.homeoOfIso T.analyticIso
  have hg (p : SchubertSpace ab N hN) : (p, e p) ∈ RightIncidence E a M hM :=
    T.onLattices p (E p).val (hE p)
  refine { toFun := fun p ↦ ⟨(p, e p), hg p⟩
           invFun := fun p ↦ p.val.1
           left_inv := fun _ ↦ rfl
           right_inv := fun p ↦ Subtype.ext (Prod.ext rfl (schubertPointSubspace_injective
             ((hg p.val.1).trans p.property.symm)))
           continuous_toFun := (continuous_id.prodMk e.continuous).subtype_mk _
           continuous_invFun := continuous_fst.comp continuous_subtype_val }

set_option maxHeartbeats 700000 in
private theorem orderedIncidenceComparison {J : GL2JetParameters} {a : ℤ} {ab : DominantPair}
    {N M C : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C} {A : SchubertJetAction J ab N hN}
    {T : SchubertTranslationData a ab N M hN hM} {W : OrderedCharts a ab}
    {point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)}
    (S : RealizesOrderedSchemes A T W point) : Nonempty (OrderedIncidenceComparison S) := by
  have hQ := rightFrameProjection_isQuotient S.E S.onSubspaces
  let X := occupiedSchubert ab N hN
  let P := occupiedSchubert (centralPair a) C hC
  let Y := occupiedSchubert (shiftPair a ab) M hM
  let hP : IsTerminal P := complexBaseTerminal.ofIso point.symm
  let l : X ≅ LeftIncidenceScheme a ab C M hC hM :=
    terminalProductIso (complexBaseMap X ≫ point.inv) hP T.schemeIso
  let r : X ≅ RightIncidenceScheme T := (asIso (pullback.fst T.schemeIso.hom (𝟙 Y))).symm
  have rfst : r.hom ≫ pullback.fst T.schemeIso.hom (𝟙 Y) = 𝟙 X := r.hom_inv_id
  have rsnd : r.hom ≫ pullback.snd T.schemeIso.hom (𝟙 Y) = T.schemeIso.hom := by
    have h := pullback.condition (f := T.schemeIso.hom) (g := 𝟙 Y)
    rw [Category.comp_id] at h
    rw [← h, ← Category.assoc, rfst, Category.id_comp]
  let e := TopCat.homeoOfIso T.analyticIso
  let p₀ : SchubertSpace (centralPair a) C hC := 𝟙 _ ≫ point.inv
  let el : SchubertSpace ab N hN ≃ₜ LeftIncidence a ab C M hC hM :=
    { toFun p := (p₀, e p)
      invFun p := e.symm p.2
      left_inv p := e.symm_apply_apply p
      right_inv p := Prod.ext (hP.hom_ext _ _) (e.apply_symm_apply p.2)
      continuous_toFun := continuous_const.prodMk e.continuous
      continuous_invFun := e.symm.continuous.comp continuous_snd }
  let er := rightIncidenceHomeomorph T S.E S.onSubspaces
  refine ⟨{ leftScheme := l, rightScheme := r
            leftFirst := prod.lift_fst _ _, leftTerminal := prod.lift_snd _ _
            rightFirst := rfst, rightTerminal := rsnd
            leftAnalytic := el, rightAnalytic := er
            leftPoints := ?_, rightPoints := ?_
            rightQuotient := er.isQuotientMap.comp hQ
            rightFrameClasses := ?_ }⟩
  · intro p
    apply Prod.ext
    · apply hP.hom_ext
    · change e p = p ≫ l.hom ≫ prod.snd
      rw [show l.hom ≫ prod.snd = T.schemeIso.hom from prod.lift_snd _ _]
      exact T.onPoints p
  · intro p
    apply Prod.ext
    · change p = p ≫ r.hom ≫ pullback.fst _ _
      rw [rfst, Category.comp_id]
    · change e p = p ≫ r.hom ≫ pullback.snd _ _
      rw [rsnd]
      exact T.onPoints p
  · intro f g
    rw [er.injective.eq_iff, ← S.right.injective.eq_iff,
      rightFrameProjection_chart S f, rightFrameProjection_chart S g]
    exact ⟨Quotient.exact, Quotient.sound⟩

end OrderedIncidence

section TensorCoefficients

open MonoidalCategory Opposite
open scoped TensorProduct
open ConvolutionConstantDescentSpec (scalars tensorPresheaf constantSections shiftedConstantPullback)
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open private square_hom transport from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting

set_option backward.isDefEq.respectTransparency false

private theorem scalarActionLeft_eq (V : Coeff.{0}) :
    scalarActionLeft V = ((ULift.moduleEquiv (R := ℚ) (M := ℚ)).toModuleIso.hom ▷ V) ≫ (λ_ V).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro r v
  rfl

private abbrev constPresheaf (R : TopCat.{0}) : ((Opens R)ᵒᵖ ⥤ Coeff.{0}) :=
  (Functor.const (Opens R)ᵒᵖ).obj scalars

private def constPresheafUnit (R : TopCat.{0}) : constPresheaf R ≅ 𝟙_ (((Opens R)ᵒᵖ ⥤ Coeff.{0})) :=
  (Functor.const (Opens R)ᵒᵖ).mapIso ((ULift.moduleEquiv (R := ℚ) (M := ℚ)).toModuleIso)

private def leftPresheafUnitor {R : TopCat.{0}} (F : ((Opens R)ᵒᵖ ⥤ Coeff.{0})) :
    constPresheaf R ⊗ F ≅ F :=
  (tensorRight F).mapIso (constPresheafUnit R) ≪≫ λ_ F

private def constIntoRational (R : TopCat.{0}) : constPresheaf R ⟶ (rational R).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology R) Coeff.{0}).unit.app _

private theorem leftTensorInclusion_isIso {R : TopCat.{0}} (F : Sheaves R) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).map
      (constIntoRational R ▷ F.obj)) := by
  let J := Opens.grothendieckTopology R
  apply (J.W_iff _).mp
  apply MorphismProperty.whiskerRight_mem
  exact J.W_adj_unit_app (sheafificationAdjunction J Coeff.{0}) _

private def leftTensorUnitApp {R : TopCat.{0}} (F : Sheaves R) :
    (rationalTensor R true).obj F ≅ F := by
  let L := presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}
  letI := leftTensorInclusion_isIso F
  exact (asIso (L.map (constIntoRational R ▷ F.obj))).symm ≪≫
    L.mapIso (leftPresheafUnitor F.obj) ≪≫ asIso ((sheafificationAdjunction
      (Opens.grothendieckTopology R) Coeff.{0}).counit.app F)

private theorem leftTensorInclusion_unit {R : TopCat.{0}} (F : Sheaves R) :
    (presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).map (constIntoRational R ▷ F.obj) ≫
      (leftTensorUnitApp F).hom =
    (presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).map (leftPresheafUnitor F.obj).hom ≫
      (sheafificationAdjunction (Opens.grothendieckTopology R) Coeff.{0}).counit.app F := by
  let adj := sheafificationAdjunction (Opens.grothendieckTopology R) Coeff.{0}
  let L := presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}
  let := leftTensorInclusion_isIso F
  let e := asIso (L.map (constIntoRational R ▷ F.obj))
  change e.hom ≫ (e.inv ≫ L.map (leftPresheafUnitor F.obj).hom ≫ adj.counit.app F) = _
  exact e.hom_inv_id_assoc _

private theorem leftTensorUnit_naturality {R : TopCat.{0}} {F G : Sheaves R} (f : F ⟶ G) :
    (rationalTensor R true).map f ≫ (leftTensorUnitApp G).hom = (leftTensorUnitApp F).hom ≫ f := by
  let J := Opens.grothendieckTopology R
  let L := presheafToSheaf J Coeff.{0}
  let e := constIntoRational R
  let := leftTensorInclusion_isIso F
  have v : (rationalTensor R true).map f = L.map ((rational R).obj ◁ f.hom) := by
    change coefficientTensorMap (𝟙 (rational R)) f = _
    unfold coefficientTensorMap
    congr 1
  have h (X : Sheaves R) := leftTensorInclusion_unit X
  have hw : (constPresheaf R ◁ f.hom) ≫ (leftPresheafUnitor G.obj).hom =
      (leftPresheafUnitor F.obj).hom ≫ f.hom := by
    change _ ≫ ((constPresheafUnit R).hom ▷ G.obj) ≫ (λ_ G.obj).hom =
      (((constPresheafUnit R).hom ▷ F.obj) ≫ (λ_ F.obj).hom) ≫ _
    rw [← Category.assoc, whisker_exchange, Category.assoc, leftUnitor_naturality, Category.assoc]
  apply (cancel_epi (L.map (e ▷ F.obj))).mp
  rw [v, ← Functor.map_comp_assoc, ← whisker_exchange, Functor.map_comp_assoc, h G]
  have hc := (sheafificationAdjunction J Coeff.{0}).counit_naturality f
  change L.map f.hom ≫ _ = _ ≫ f at hc
  rw [← Functor.map_comp_assoc, hw, Functor.map_comp_assoc, hc, ← Category.assoc,
    ← Category.assoc, h F]

private def leftTensorUnit (R : TopCat.{0}) : RationalTensorUnit R true where
  scalar := NatIso.ofComponents leftTensorUnitApp (fun f ↦ leftTensorUnit_naturality f)
  onSections F U := by
    let J := Opens.grothendieckTopology R
    let L := presheafToSheaf J Coeff.{0}
    let η := (sheafificationAdjunction J Coeff.{0}).unit
    let ψ := constIntoRational R ▷ F.obj
    let u := (leftPresheafUnitor F.obj).hom
    have hψ := NatTrans.congr_app (η.naturality ψ) U
    have hu := NatTrans.congr_app (η.naturality u) U
    change ψ.app U ≫ (η.app (tensorPresheaf (rational R) F)).app U =
      (η.app _).app U ≫ (L.map ψ).hom.app U at hψ
    change u.app U ≫ (η.app F.obj).app U = (η.app _).app U ≫ (L.map u).hom.app U at hu
    have hc := NatTrans.congr_app ((sheafificationAdjunction J Coeff.{0}).right_triangle_components F) U
    change (η.app F.obj).app U ≫ ((sheafificationAdjunction J Coeff.{0}).counit.app F).hom.app U =
      𝟙 _ at hc
    change (constantSections R U ⊗ₘ 𝟙 (F.obj.obj U)) ≫ _ ≫ (leftTensorUnitApp F).hom.hom.app U = _
    rw [tensorHom_id]
    change ψ.app U ≫ _ ≫ (leftTensorUnitApp F).hom.hom.app U = _
    rw [← Category.assoc, hψ, Category.assoc]
    change (η.app _).app U ≫ ((L.map ψ) ≫ (leftTensorUnitApp F).hom).hom.app U = _
    rw [leftTensorInclusion_unit]
    change (η.app _).app U ≫ (L.map u).hom.app U ≫ _ = _
    rw [← Category.assoc, ← hu, Category.assoc, hc]
    exact (Category.comp_id (u.app U)).trans (scalarActionLeft_eq _).symm

private def swapTensorApp {R : TopCat.{0}} (F : Sheaves R) :
    (rationalTensor R false).obj F ≅ (rationalTensor R true).obj F :=
  (presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).mapIso (β_ F.obj (rational R).obj)

private def swapTensor (R : TopCat.{0}) : rationalTensor R false ≅ rationalTensor R true :=
  NatIso.ofComponents swapTensorApp (fun {F G} f ↦ by
    let L := presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}
    change L.map (f.hom ⊗ₘ 𝟙 (rational R).obj) ≫ L.map (β_ G.obj (rational R).obj).hom =
      L.map (β_ F.obj (rational R).obj).hom ≫ L.map (𝟙 (rational R).obj ⊗ₘ f.hom)
    rw [← Functor.map_comp, ← Functor.map_comp, BraidedCategory.braiding_naturality])

private def rightTensorUnit (R : TopCat.{0}) : RationalTensorUnit R false where
  scalar := swapTensor R ≪≫ (leftTensorUnit R).scalar
  onSections F U := by
    let J := Opens.grothendieckTopology R
    let L := presheafToSheaf J Coeff.{0}
    let η := (sheafificationAdjunction J Coeff.{0}).unit
    let b := (β_ F.obj (rational R).obj).hom
    have hb := NatTrans.congr_app (η.naturality b) U
    change (b.app U) ≫ (η.app (tensorPresheaf (rational R) F)).app U =
      (η.app (tensorPresheaf F (rational R))).app U ≫ (L.map b).hom.app U at hb
    have h := (leftTensorUnit R).onSections F U
    change (𝟙 (F.obj.obj U) ⊗ₘ constantSections R U) ≫ _ ≫
      ((L.map b).hom.app U ≫ ((leftTensorUnit R).scalar.hom.app F).hom.app U) = _
    rw [← Category.assoc (f := (η.app (tensorPresheaf F (rational R))).app U), ← hb,
      ← Category.assoc (f := (𝟙 (F.obj.obj U) ⊗ₘ constantSections R U)),
      show b.app U = (β_ (F.obj.obj U) ((rational R).obj.obj U)).hom from rfl,
      BraidedCategory.braiding_naturality_assoc, Category.assoc, Category.assoc, h]
    rfl

private def rationalTensorUnit (R : TopCat.{0}) (left : Bool) : RationalTensorUnit R left :=
  Bool.rec (rightTensorUnit R) (leftTensorUnit R) left

private theorem rationalTensorCoefficient_id (R : TopCat.{0}) (l : Bool) :
    rationalTensorCoefficient l (𝟙 (rational R)) = 𝟙 _ := by
  cases l <;> apply NatTrans.ext <;> funext F <;> exact coefficientTensorMap_id _ _

private theorem derivedCoefficient_id {R : TopCat.{0}} {l : Bool} (μ : RationalTensorUnit R l) :
    μ.derivedCoefficient (𝟙 _) = 𝟙 _ := by
  let : PreservesFiniteLimits (rationalTensor R l) := preservesFiniteLimits_of_natIso μ.scalar.symm
  let : PreservesFiniteColimits (rationalTensor R l) := preservesFiniteColimits_of_natIso μ.scalar.symm
  let : (rationalTensor R l).Additive := Functor.additive_of_preserves_binary_products _
  change (rationalTensorCoefficient l (𝟙 (rational R))).mapDerivedCategory = 𝟙 _
  rw [rationalTensorCoefficient_id]
  apply Localization.natTrans_ext (DerivedCategory.Q (C := Sheaves R))
    (HomologicalComplex.quasiIso (Sheaves R) (.up ℤ))
  intro K
  rw [NatTrans.mapDerivedCategory_app_Q_obj, NatTrans.mapHomologicalComplex_id]
  simp

private def representativeTensor {R X Y : TopCat.{0}} (l : Bool) (q p : R ⟶ X) (z : R ⟶ Y)
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj) {F G : Derived X}
    (d : (derivedInverseImage q).obj G ≅ (derivedInverseImage p).obj F) :
    RepresentativeTensor l q p z c F G d.hom where
  pointUnit := inferInstanceAs (IsIso ((derivedInverseImage z).mapIso c ≪≫ shiftedConstantPullback z 0).hom)
  tensor := rationalTensorUnit R l
  comparison := d ≪≫ ((rationalTensorUnit R l).derivedUnit.app ((derivedInverseImage p).obj F)).symm
  multiplication := by simp

private theorem tensorFrameComparison_of {V R X Y : TopCat.{0}} {l : Bool} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F G : Derived X}
    {d : (derivedInverseImage q).obj G ⟶ (derivedInverseImage p).obj F}
    (D : RepresentativeTensor l q p z c F G d) (s t : V ⟶ R)
    (b : (derivedInverseImage s).obj ((derivedInverseImage q).obj G) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage q).obj G))
    (v : (derivedInverseImage s).obj ((derivedInverseImage z).obj P) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage z).obj P))
    (w : (derivedInverseImage s).obj ((derivedInverseImage p).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage p).obj F))
    (hv : v ≫ pointFrameUnit t z c = pointFrameUnit s z c)
    (h : b ≫ (derivedInverseImage t).map d = (derivedInverseImage s).map d ≫ w) :
    TensorFrameComparison D s t b v w := by
  let ν := rationalTensorUnit V l
  refine ⟨ν, 𝟙 _, ?_, ?_⟩
  · have hId : derivedPointMap (𝟙 (rational V)) = 𝟙 (shiftedConstant V 0).obj := by
      unfold derivedPointMap
      rw [(DerivedCategory.singleFunctor (Sheaves V) 0).map_id]
      exact (shiftFunctor (Derived V) (0 : ℤ)).map_id _
    rw [hId, Category.comp_id, hv]
  · rw [derivedCoefficient_id]
    simp only [NatTrans.id_app, Category.id_comp]
    let K := (derivedInverseImage p).obj F
    let a := D.tensor.derivedUnit.app K
    apply (cancel_mono ((derivedInverseImage t).map a.hom)).mp
    simp only [RationalTensorUnit.pullback, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    have hmul : D.comparison.hom ≫ a.hom = d := D.multiplication
    rw [← Functor.map_comp, hmul, h]
    have h₁ : (derivedInverseImage t).map a.inv ≫ (derivedInverseImage t).map a.hom = 𝟙 _ := by
      rw [← (derivedInverseImage t).map_comp, Iso.inv_hom_id]
      exact (derivedInverseImage t).map_id _
    rw [h₁, Category.comp_id]
    have hw := (ν.derivedUnit.hom.naturality w)
    change ν.derived.map w ≫ (ν.derivedUnit.app _).hom = (ν.derivedUnit.app _).hom ≫ w at hw
    rw [hw, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, hmul]

@[reassoc]
private theorem pointFrameUnit_comp {V R Y : TopCat.{0}} (s : V ⟶ R) (z : R ⟶ Y) {P : Derived Y}
    (c : P ≅ (shiftedConstant Y 0).obj) :
    (derivedInverseImageComposition s z).hom.app P ≫ pointFrameUnit s z c =
      centralPointUnitMap (s ≫ z) c := by
  simp only [pointFrameUnit, centralPointUnitMap, CentralFrameDescentSpecs.centralPointUnitMap,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have h := ((derivedInverseImageComposition s z).hom.naturality c.hom).symm
  change (derivedInverseImageComposition s z).hom.app P ≫
      (derivedInverseImage s).map ((derivedInverseImage z).map c.hom) =
    (derivedInverseImage (s ≫ z)).map c.hom ≫
      (derivedInverseImageComposition s z).hom.app (shiftedConstant Y 0).obj at h
  rw [reassoc_of% h, ConvolutionConstantDescent.shiftedPullbackComposition s z 0]

@[reassoc]
private theorem frameSquare_preservesPoint {V R U Y : TopCat.{0}} (s : V ⟶ R) (z : R ⟶ Y)
    (t : V ⟶ U) (p : U ⟶ Y) (h : s ≫ z = t ≫ p) {P : Derived Y}
    (c : P ≅ (shiftedConstant Y 0).obj) :
    (squareValue h).hom.app P ≫ pointFrameUnit t p c = pointFrameUnit s z c := by
  have h₁ {f g : V ⟶ Y} (h' : f = g) :
      transport h' P ≫ centralPointUnitMap g c = centralPointUnitMap f c := by
    subst g
    simp [transport]
  simp only [square_hom, Category.assoc, pointFrameUnit_comp, h₁]
  rw [← pointFrameUnit_comp s z c, Iso.inv_hom_id_app_assoc]

private theorem rebaseFrameArrow_eq {V R U X : TopCat.{0}} (s t : V ⟶ R) (p : R ⟶ X)
    (u : V ⟶ U) {f g : U ⟶ X} (hf : u ≫ f = s ≫ p) (hg : u ≫ g = t ≫ p)
    {F : Derived X} (e : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    rebaseFrameArrow s t p u hf hg e = (squareValue hf.symm).hom.app F ≫
      (derivedInverseImage u).map e ≫ (squareValue hg).hom.app F := by
  simp only [rebaseFrameArrow, pullbackMorphism, square_hom, transport, Category.assoc]

private theorem rebaseFrameArrow_point {V R U Y : TopCat.{0}} (s t : V ⟶ R) (z : R ⟶ Y)
    (u : V ⟶ U) {f g : U ⟶ Y} (hf : u ≫ f = s ≫ z) (hg : u ≫ g = t ≫ z)
    {P : Derived Y} (e : (derivedInverseImage f).obj P ⟶ (derivedInverseImage g).obj P)
    (c : P ≅ (shiftedConstant Y 0).obj)
    (he : e ≫ centralPointUnitMap g c = centralPointUnitMap f c) :
    rebaseFrameArrow s t z u hf hg e ≫ pointFrameUnit t z c = pointFrameUnit s z c := by
  simp only [rebaseFrameArrow_eq, Category.assoc, frameSquare_preservesPoint]
  change (squareValue hf.symm).hom.app P ≫ (derivedInverseImage u).map e ≫ pointFrameUnit u g c = _
  unfold pointFrameUnit at *
  rw [← Functor.map_comp_assoc, he]
  exact frameSquare_preservesPoint s z u f hf.symm c

@[reassoc]
private theorem frameSquare_reverse {V R U X : TopCat.{0}} {s : V ⟶ R} {t : V ⟶ U}
    {p : R ⟶ X} {q : U ⟶ X} (h : s ≫ p = t ≫ q) (F : Derived X) :
    (squareValue h.symm).hom.app F ≫ (squareValue h).hom.app F = 𝟙 _ := by
  have hv : transport h.symm F ≫ transport h F = 𝟙 _ := by
    unfold transport
    rw [eqToHom_trans, eqToHom_refl]
  simp only [square_hom, Category.assoc, Iso.hom_inv_id_app_assoc, reassoc_of% hv,
    Iso.inv_hom_id_app]


private theorem tensorFrameComparison_identity {V R X Y : TopCat.{0}} {q : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F : Derived X}
    (D : RepresentativeTensor false q q z c F F (𝟙 _)) (s t : V ⟶ R)
    (b : (derivedInverseImage s).obj ((derivedInverseImage q).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage q).obj F))
    (v : (derivedInverseImage s).obj ((derivedInverseImage z).obj P) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage z).obj P))
    (hv : v ≫ pointFrameUnit t z c = pointFrameUnit s z c) :
    TensorFrameComparison D s t b v b := by
  apply tensorFrameComparison_of D s t b v b hv
  rw [(derivedInverseImage t).map_id, (derivedInverseImage s).map_id]
  exact (Category.comp_id b).trans (Category.id_comp b).symm

private theorem frameMultiplication {V R X : TopCat.{0}} (s t u : V ⟶ R) (q p : R ⟶ X)
    (hq : s ≫ q = t ≫ q) (hf : s ≫ p = u ≫ q) (hp : u ≫ p = t ≫ p)
    {F : Derived X} (e : (derivedInverseImage q).obj F ⟶ (derivedInverseImage p).obj F)
    (h : pullbackMorphism t rfl rfl e = pullbackMorphism s hq hf e ≫ pullbackMorphism u rfl hp e) :
    (squareValue hq).hom.app F ≫ (derivedInverseImage t).map e =
      (derivedInverseImage s).map e ≫ rebaseFrameArrow s t p u hf.symm hp e := by
  have h₁ := congrArg (fun (v : (derivedInverseImage (t ≫ q)).obj F ⟶
      (derivedInverseImage (t ≫ p)).obj F) ↦
    (derivedInverseImageComposition s q).inv.app F ≫ transport hq F ≫ v ≫
      (derivedInverseImageComposition t p).hom.app F) h
  have hid : (derivedInverseImage t).map e ≫ 𝟙 ((derivedInverseImage p ⋙ derivedInverseImage t).obj F) =
      (derivedInverseImage t).map e := Category.comp_id _
  simpa only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, square_hom, rebaseFrameArrow, transport,
    eqToHom_trans_assoc, hid] using h₁

private theorem inverse_frameSquare {V R U X : TopCat.{0}} {s : V ⟶ R} {t : V ⟶ U}
    {p : R ⟶ X} {q : U ⟶ X} (h : s ≫ p = t ≫ q) (F : Derived X) :
    (squareValue h.symm).hom.app F = (squareValue h).inv.app F := by
  let a := (squareValue h).app F
  change _ = a.inv
  exact (cancel_mono a.hom).mp ((frameSquare_reverse h F).trans a.inv_hom_id.symm)

private theorem moveFrameIsomorphisms {D : Type*} [Category* D] {A B C E : D}
    (a : A ≅ B) (b : C ≅ E) (f : B ⟶ E) (g : A ⟶ C)
    (h : a.hom ≫ f = g ≫ b.hom) : a.inv ≫ g = f ≫ b.inv := by
  calc
    a.inv ≫ g = a.inv ≫ (g ≫ b.hom) ≫ b.inv := by simp [Category.assoc]
    _ = f ≫ b.inv := by rw [← h, ← Category.assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 900000 in
private theorem frameMultiplication_action {V R X : TopCat.{0}} (s t u : V ⟶ R) (q p : R ⟶ X)
    (hq : s ≫ q = t ≫ q) (hf : s ≫ p = u ≫ q) (hp : u ≫ p = t ≫ p)
    {F : Derived X} (e : (derivedInverseImage q).obj F ⟶ (derivedInverseImage p).obj F)
    (h : (squareValue hq).hom.app F ≫ (derivedInverseImage t).map e =
      (derivedInverseImage s).map e ≫ rebaseFrameArrow s t p u hf.symm hp e) :
    rebaseFrameArrow t u q s hq hf e ≫ (derivedInverseImage u).map e =
      (derivedInverseImage t).map e ≫ (squareValue hp.symm).hom.app F := by
  let a := (squareValue hq).app F
  let b := (squareValue hp).app F
  let g := (derivedInverseImage s).map e ≫ (squareValue hf).hom.app F ≫ (derivedInverseImage u).map e
  have hm : a.hom ≫ (derivedInverseImage t).map e = g ≫ b.hom := by
    simpa only [rebaseFrameArrow_eq, g, a, b, Iso.app_hom, Category.assoc] using h
  calc
    rebaseFrameArrow t u q s hq hf e ≫ (derivedInverseImage u).map e = a.inv ≫ g := by
      rw [rebaseFrameArrow_eq, inverse_frameSquare hq]
      simp only [a, g, Iso.app_inv, Category.assoc]
    _ = (derivedInverseImage t).map e ≫ b.inv := moveFrameIsomorphisms a b _ _ hm
    _ = _ := by rw [inverse_frameSquare hp]; rfl

private theorem quotientMap_action {H : AnalyticGroup.{0}} {X : TopCat.{0}} (A : AnalyticAction H X) :
    IsQuotientMap (fun r : AnalyticAction.Parameters H X ↦ A.act r) := by
  let s := AnalyticAction.identitySection H X
  change IsQuotientMap (A.act : AnalyticAction.Parameters H X → X)
  have he : (A.act : AnalyticAction.Parameters H X → X) ∘ s = id := funext A.one_act
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen (fun U ↦ ⟨?_, ?_⟩), ?_⟩
  · intro h
    have hs : IsOpen (((A.act : AnalyticAction.Parameters H X → X) ∘ s) ⁻¹' U) :=
      h.preimage s.hom.continuous
    rwa [he, Set.preimage_id] at hs
  · exact fun h ↦ h.preimage A.act.hom.continuous
  · exact fun x ↦ ⟨s x, A.one_act x⟩

private abbrev constantFrameMap {R Y : TopCat.{0}} (x : Y) : R ⟶ Y :=
  TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩

private theorem fixedPointTensorArrow {V R U X Y : TopCat.{0}} {p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj) {F : Derived X}
    (D : RepresentativeTensor false p p z c F F (𝟙 _))
    (s t : V ⟶ R) (u : V ⟶ U) {act proj : U ⟶ Y}
    (ha : u ≫ act = s ≫ z) (hp : u ≫ proj = t ≫ z)
    (η : (derivedInverseImage act).obj P ⟶ (derivedInverseImage proj).obj P)
    (hη : η ≫ centralPointUnitMap proj c = centralPointUnitMap act c)
    (b : (derivedInverseImage s).obj ((derivedInverseImage p).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage p).obj F)) :
    TensorFrameComparison D s t b (rebaseFrameArrow s t z u ha hp η) b :=
  tensorFrameComparison_identity D s t b _ (rebaseFrameArrow_point s t z u ha hp η c hη)

private theorem constantPointTensorArrow {V R X Y : TopCat.{0}} {p : R ⟶ X} (x : Y)
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj) {F : Derived X}
    (D : RepresentativeTensor false p p (constantFrameMap x) c F F (𝟙 _)) (s t : V ⟶ R)
    (b : (derivedInverseImage s).obj ((derivedInverseImage p).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage p).obj F)) :
    TensorFrameComparison D s t b
      ((squareValue (show s ≫ constantFrameMap x = t ≫ constantFrameMap x from
        TopCat.ext (fun _ ↦ rfl))).hom.app P) b := by
  let z : R ⟶ Y := constantFrameMap x
  have hz : s ≫ z = t ≫ z := TopCat.ext (fun _ ↦ rfl)
  exact tensorFrameComparison_identity D s t b _ (frameSquare_preservesPoint s z t z hz c)

set_option maxHeartbeats 360000 in
private theorem rightTensorBasisChange {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N C : ℕ}
    {hN : OrbitBound ab N} {hC : OrbitBound (centralPair a) C}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (B : SchubertJetAction J (centralPair a) C hC)
    {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
    (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
    (x : SchubertSpace (centralPair a) C hC) (hc : CentralPointCoefficients B η c)
    {F : Derived (SchubertSpace ab N hN)}
    (D : RepresentativeTensor false (rightFrameProjection E) (rightFrameProjection E)
      (constantFrameMap x) c F F (𝟙 _))
    (k : ℕ) (hk : B.action.cutoff ≤ k) :
    let p := rightFrameProjection E
    let z := (constantFrameMap x : RightFrameSpace E ⟶ SchubertSpace (centralPair a) C hC)
    let s := rightFrameSource J E k
    let t := rightFrameTarget J E k
    let u := rightFrameJetPoint J E x k
    let act := (B.action.action k hk).act
    let π := AnalyticAction.projection (J.toJetSystem.group k) (SchubertSpace (centralPair a) C hC)
    ∃ (hp : s ≫ p = t ≫ p) (ha : u ≫ act = s ≫ z) (hπ : u ≫ π = t ≫ z),
      TensorFrameComparison D s t ((squareValue hp).hom.app F)
        (rebaseFrameArrow s t z u ha hπ (η.datum k hk).iso.hom) ((squareValue hp).hom.app F) := by
  intro p z s t u act π
  have hp : s ≫ p = t ≫ p := TopCat.ext (fun r ↦ r.property.1)
  have ha : u ≫ act = s ≫ z := TopCat.ext (fun v ↦ (hc k hk).1 (u v).1 x)
  have hπ : u ≫ π = t ≫ z := TopCat.ext (fun _ ↦ rfl)
  exact ⟨hp, ha, hπ, fixedPointTensorArrow c D s t u ha hπ (η.datum k hk).iso.hom (hc k hk).2
    ((squareValue hp).hom.app F)⟩

private theorem tensorFrameNaturality {R X Y : TopCat.{0}} {left : Bool} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F G : Derived X}
    {d : (derivedInverseImage q).obj G ⟶ (derivedInverseImage p).obj F}
    (D : RepresentativeTensor left q p z c F G d) : TensorFrameNaturality D := by
  intro V s t b v w h
  exact tensorFrameComparison_of D s t b v w h.1 h.2

private theorem tensorFrameMultiplication {R X Y : TopCat.{0}} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F : Derived X}
    {e : (derivedInverseImage q).obj F ⟶ (derivedInverseImage p).obj F}
    (D : RepresentativeTensor true q p z c F F e) : TensorFrameMultiplication D := by
  intro V s t u hq hf hp hz hm
  exact tensorFrameComparison_of D s t ((squareValue hq).hom.app F) ((squareValue hz).hom.app P)
    (rebaseFrameArrow s t p u hf.symm hp e) (frameSquare_preservesPoint s z t z hz c)
    (frameMultiplication s t u q p hq hf hp e hm)

set_option maxHeartbeats 460000 in
private theorem leftTensorAction {H : AnalyticGroup.{0}} {X Y : TopCat.{0}}
    (A : AnalyticAction H X) (B : AnalyticAction H Y) (x : Y) {F : Derived X} (ε : A.Equivariance F)
    {P : Derived Y} (η : B.Equivariance P) (c : P ≅ (shiftedConstant Y 0).obj)
    (hB : ∀ g : H.space, B.act (g, x) = x)
    (hη : η.iso.hom ≫ centralPointUnitMap (AnalyticAction.projection H Y) c = centralPointUnitMap B.act c) :
    let u₀ : AnalyticAction.TwoParameters H X ⟶ AnalyticAction.Parameters H Y :=
      TopCat.ofHom ⟨fun v ↦ (v.1, x), continuous_fst.prodMk continuous_const⟩
    let s := AnalyticAction.firstAfterSecond A
    let t := AnalyticAction.multiplyParameters H X
    let u := AnalyticAction.secondParameter H X
    let z : AnalyticAction.Parameters H X ⟶ Y := constantFrameMap x
    ∃ (ha : u₀ ≫ B.act = t ≫ z) (hπ : u₀ ≫ AnalyticAction.projection H Y = u ≫ z),
      NormalizedFrameComparison c ε.iso.hom t u
        (rebaseFrameArrow t u A.act s (AnalyticAction.multiply_act A) (AnalyticAction.first_projection A) ε.iso.hom)
        (rebaseFrameArrow t u z u₀ ha hπ η.iso.hom)
        ((squareValue (AnalyticAction.multiply_projection (H := H) (X := X)).symm).hom.app F) := by
  intro u₀ s t u z
  let q := A.act
  let p := AnalyticAction.projection H X
  let hq := AnalyticAction.multiply_act A
  let hf := AnalyticAction.first_projection A
  let hp := AnalyticAction.multiply_projection (H := H) (X := X)
  have ha : u₀ ≫ B.act = t ≫ z := TopCat.ext (fun v ↦ hB v.1)
  have hπ : u₀ ≫ AnalyticAction.projection H Y = u ≫ z := TopCat.ext (fun _ ↦ rfl)
  have hm := frameMultiplication s t u q p hq hf hp ε.iso.hom ε.multiplication
  exact ⟨ha, hπ, rebaseFrameArrow_point t u z u₀ ha hπ η.iso.hom c hη,
    frameMultiplication_action s t u q p hq hf hp ε.iso.hom hm⟩

set_option maxHeartbeats 650000 in
private theorem leftTensorDescentAtLevel {H : AnalyticGroup.{0}} {X Y : TopCat.{0}}
    (A : AnalyticAction H X) (x : Y) {F : Derived X} (ε : A.Equivariance F)
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj)
    {pointLevel : Prop} (B : pointLevel → AnalyticAction H Y) (η : ∀ h, (B h).Equivariance P)
    (hc : ∀ h, (∀ g : H.space, (B h).act (g, x) = x) ∧
      (η h).iso.hom ≫ centralPointUnitMap (AnalyticAction.projection H Y) c =
        centralPointUnitMap (B h).act c) :
    LeftTensorDescentAtLevel A x ε c B η := by
  delta LeftTensorDescentAtLevel
  intro R p q z s t u
  let D : RepresentativeTensor true q p z c F F ε.iso.hom :=
    representativeTensor true q p z c ε.iso
  have hz : s ≫ z = t ≫ z := TopCat.ext (fun _ ↦ rfl)
  refine ⟨quotientMap_action A, D, tensorFrameNaturality D, tensorFrameMultiplication D, hz, ?_, ?_⟩
  · exact ε.multiplication
  · intro hkC
    exact leftTensorAction A (B hkC) x ε (η hkC) c (hc hkC).1 (hc hkC).2

section TensorDescent

variable {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N M C : ℕ}
  {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
  {hC : OrbitBound (centralPair a) C}
  {A : SchubertJetAction J ab N hN} {T : SchubertTranslationData a ab N M hN hM}
  {W : OrderedCharts a ab}
  {point : occupiedSchubert (centralPair a) C hC ≅ (testSpec ℂ).obj (op complexAlgebra)}
  (S : RealizesOrderedSchemes A T W point)
  (B : SchubertJetAction J (centralPair a) C hC)
  {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
  (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
  (F : A.action.Object)

set_option maxHeartbeats 250000 in
private theorem centralRightTensorDescent (hc : CentralPointCoefficients B η c) :
    CentralTensorDescent S B η c F false := by
  let Y := SchubertSpace (centralPair a) C hC
  let x : Y := 𝟙 _ ≫ point.inv
  let R := RightFrameSpace S.E
  let p := rightFrameProjection S.E
  let z : R ⟶ Y := constantFrameMap x
  obtain ⟨D⟩ : Nonempty (RepresentativeTensor false p p z c F.obj F.obj (𝟙 _)) :=
    ⟨representativeTensor false p p z c (Iso.refl _)⟩
  refine ⟨D, rightTensorBasisChange S.E B η c x hc D, ?_⟩
  intro k hk V s t u ha hπ
  exact constantPointTensorArrow x c D s t
    (rebaseFrameArrow s t p u ha hπ (F.equivariance.datum k hk).iso.hom)

private theorem centralLeftTensorDescent (hc : CentralPointCoefficients B η c) :
    CentralTensorDescent S B η c F true := by
  delta CentralTensorDescent
  intro X Y x k hk
  exact leftTensorDescentAtLevel (A.action.action k hk) x (F.equivariance.datum k hk) c
    (B.action.action k) (η.datum k) (fun hkC ↦ ⟨fun g ↦ (hc k hkC).1 g x, (hc k hkC).2⟩)

end TensorDescent

end TensorCoefficients

/-- Invert the equivariant pullback comparison, using the full bounded-below
subcategory for the adjoint comparison. -/
private theorem inversePullbackComparison {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {f : X ⟶ Y}
    (h : JetMapsCommute A B f) {F : BoundedBelow X} {G : BoundedBelow Y}
    (α : A.Equivariance F.obj) (β : B.Equivariance G.obj)
    (u : F.obj ≅ (derivedInverseImage f).obj G.obj) (hu : IntertwinesPullback h α β u.hom) :
    ∃ c : (boundedBelowInverseImage f).obj G ≅ F, PullbackIntertwines h α β c := by
  let c : (boundedBelowInverseImage f).obj G ≅ F := ObjectProperty.isoMk _ u.symm
  refine ⟨c, fun k hx hy ↦ ?_⟩
  let uAct := (derivedInverseImage (A.action k hx).act).mapIso u
  let uProj := (derivedInverseImage (AnalyticAction.projection (J.group k) X)).mapIso u
  change uAct.inv ≫ (α.datum k hx).iso.hom = restrictedArrow h β k hx hy ≫ uProj.inv
  apply uProj.eq_comp_inv.mpr
  rw [Category.assoc]
  exact uAct.inv_comp_eq.mpr (hu k hx hy).symm

private theorem closedSupportTransport_of {J : GL2JetParameters} {a : ℤ} {ab : DominantPair}
    {N M : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    (adj : DerivedAdjunctions) (cl : ClosedAdjunctions)
    (hclosed : ClosedExtensionCompatibility J.toJetSystem)
    (A : SchubertJetAction J ab N hN) (B : SchubertJetAction J (shiftPair a ab) M hM)
    (v : SchubertSpace ab N hN ≅ SchubertSpace (shiftPair a ab) M hM)
    (hf : JetMapsCommute A.action B.action v.hom) (hAB : A.action.cutoff ≤ B.action.cutoff)
    (F : BoundedBelow (SchubertSpace ab N hN)) (α : A.action.Equivariance F.obj)
    (G : BoundedBelow (SchubertSpace (shiftPair a ab) M hM)) (β : B.action.Equivariance G.obj)
    (hfg : EquivariantDirectImageComparison adj A.action B.action v.hom hf F α G β) :
    ClosedSupportTransport adj cl A.action B.action v.hom F α G β := by
  intro X Z hZ A_X A_Z w hw hi
  have hBZ : B.action.cutoff ≤ A_Z.cutoff :=
    CentralTranslationBoundedJetSupport.schubertJetCutoffMinimal J _ M hM B _ A_Z w hw
  obtain ⟨G_Z, β_Z, hG⟩ :=
    (EquivariantHomeomorphismDirectImage.equivariantHomeomorphismDirectImage
      w (@adj) B.action A_Z hw).2 hBZ G β
  obtain ⟨c, hc, β_X, hm, hb, hterm⟩ :=
    EquivariantClosedDirectImageComposition.equivariantClosedDirectImageComposition
      (@adj) (@cl) hclosed hZ v w A.action B.action A_Z A_X hAB hBZ hf hw hi F α G β G_Z β_Z hfg hG
  exact ⟨G_Z, β_Z, c, hc, hG, β_X, hm, hb, hterm⟩

private theorem translatedICComparison {J : GL2JetParameters} {a : ℤ} {ab : DominantPair}
    {N M : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    (adj : DerivedAdjunctions) (A : SchubertJetAction J ab N hN)
    (B : SchubertJetAction J (shiftPair a ab) M hM) (T : SchubertTranslationData a ab N M hN hM)
    (h : JetMapsCommute A.action B.action T.analyticIso.hom)
    {s t : ℕ} {P : Stratification (SchubertSpace ab N hN)}
    {Q : Stratification (SchubertSpace (shiftPair a ab) M hM)}
    {D : DimensionFiltration (SchubertSpace ab N hN) s}
    {E : DimensionFiltration (SchubertSpace (shiftPair a ab) M hM) t}
    (hD : IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D)
    (hE : IsNormalizedOrbitIC (shiftPair a ab) M hM (𝟙 _) (difference (shiftPair a ab) / 2) Q E)
    (α : A.action.Equivariance (complex D).obj) (β : B.action.Equivariance (complex E).obj)
    (hα : NormalizedICDatum adj A.action D α)
    (hβ : ∀ (β' : B.action.Equivariance (complex E).obj), NormalizedICDatum adj B.action E β' → β' = β) :
    ∃ c : (boundedBelowInverseImage T.analyticIso.hom).obj (complex E) ≅ complex D,
      PullbackIntertwines h α β c := by
  have he : EquivariantIntersectionComplexes.PreservesOrbitStrata T.analyticIso := by
    obtain ⟨e, he⟩ := T.preservesStrata
    exact ⟨e, fun j ↦ (he j).2⟩
  obtain ⟨β', u, hβ', hu⟩ :=
    EquivariantIntersectionComplexes.normalizedEquivarianceTransportOnOrbits (@adj)
      A.actual B.actual T.analyticIso he h hD hE hα
  rw [hβ β' hβ'] at hu
  exact inversePullbackComparison h α β u hu

open private closedInverseAdjunction from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option maxHeartbeats 700000 in
theorem centralConvolutionTransport : CentralConvolutionTransport := by
  classical
  obtain ⟨_, _, hclosed, J, hExists, hUnique, _⟩ :=
    EquivariantIntersectionComplexes.equivariantIntersectionComplexes
  let adj : DerivedAdjunctions.{0} := fun f ↦ DerivedLocalSheaves.derivedInverseDirectAdjunctionData f
  let cl : ClosedAdjunctions := fun hZ ↦ closedInverseAdjunction hZ
  let A (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) : SchubertJetAction J ab N hN :=
    Classical.choose (hExists (@adj) ab N hN)
  let norm (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
      (P : Stratification (SchubertSpace ab N hN))
      (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2)))
      (hD : IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D) :=
    hUnique (@adj) ab N hN (A ab N hN).action (A ab N hN).actual P D hD
  let ε (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
      (P : Stratification (SchubertSpace ab N hN))
      (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2)))
      (hD : IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D) :
      (A ab N hN).action.Equivariance (complex D).obj :=
    Classical.choose (norm ab N hN P D hD)
  have hClose : ClosedExtensionCompatibility (jetSystem J) := @hclosed (jetSystem J)
  refine ⟨J, @adj, @cl, hClose, A, ?_, ε, ?_, ?_⟩
  · intro ab N hN
    obtain ⟨_, P, D, hD, _⟩ := hExists (@adj) ab N hN
    exact ⟨P, D, hD⟩
  · intro ab N hN P D hD
    exact (Classical.choose_spec (norm ab N hN P D hD)).1
  · intro a ab N M C hN hM hC P D hD Q E hE
    let cd := shiftPair a ab
    let A₁ := A ab N hN
    let A₂ := A cd M hM
    let α := ε ab N hN P D hD
    let β := ε cd M hM Q E hE
    obtain ⟨T⟩ := schubertTranslation a ab N M hN hM
    obtain ⟨W⟩ := orderedCentralProducts a ab
    obtain ⟨point⟩ := centralPoint_scheme a C hC
    let h := T.intertwines J A₁ A₂
    obtain ⟨S⟩ := realizeOrderedSchemes A₁ T W point
    have hBound := CentralTranslationBoundedJetSupport.boundedJetSupport J cd M hM A₂
    have hCut : A₁.action.cutoff ≤ A₂.action.cutoff := by
      rw [A₁.actual.1, A₂.actual.1, difference_shift a ab]
    have hα := (Classical.choose_spec (norm ab N hN P D hD)).1
    have hβ := (Classical.choose_spec (norm cd M hM Q E hE)).2
    obtain ⟨c, hc⟩ := translatedICComparison (@adj) A₁ A₂ T h hD hE α β hα hβ
    obtain ⟨v, _, hImage⟩ :=
      (EquivariantHomeomorphismDirectImage.equivariantHomeomorphismDirectImage
        T.analyticIso (@adj) A₁.action A₂.action h).1 (complex D) (complex E) α β c hc
    have hDirect :
        EquivariantDirectImageComparison adj A₁.action A₂.action T.analyticIso.hom h
          (complex D) α (complex E) β := ⟨v, hImage⟩
    have hExt : ClosedSupportTransport adj cl A₁.action A₂.action T.analyticIso.hom
        (complex D) α (complex E) β :=
      closedSupportTransport_of (@adj) (@cl) hClose A₁ A₂ T.analyticIso h hCut
        (complex D) α (complex E) β hDirect
    refine ⟨T, W, point, h, S, hBound, ⟨c, hc⟩, ?_⟩
    intro P₀ Dp hDp
    let B := A (centralPair a) C hC
    let η := ε (centralPair a) C hC P₀ Dp hDp
    have hη := (Classical.choose_spec (norm (centralPair a) C hC P₀ Dp hDp)).1
    obtain ⟨c₀, hc₀, hUnit⟩ :=
      CentralFrameDescent.centralPointNormalization J a C hC B (@adj) P₀ Dp hDp η hη
    refine ⟨c₀, hc₀, fun left ↦ ?_⟩
    let K : A₁.action.Object := ⟨(complex D).obj, α⟩
    refine ⟨?_, hDirect, hExt⟩
    cases left
    · exact centralRightDescent S B η c₀ K hc₀ (@hUnit)
    · exact centralLeftDescent S B η c₀ K K (Iso.refl K) (@hUnit)

set_option maxHeartbeats 500000 in
theorem centralConvolution : CentralConvolution := by
  refine ⟨centralConvolutionTransport, ?_⟩
  intro J a ab N M C hN hM hC A T W point S
  refine ⟨orderedIncidenceComparison S, ?_⟩
  intro B P η c hc F left
  cases left
  · exact centralRightTensorDescent S B η c F hc
  · exact centralLeftTensorDescent S B η c F hc

end RepTheorySurvey.Geometric.CentralLatticeTranslation
