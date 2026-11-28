import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.PluckerEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagIncidence
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundleBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundleCharts
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionDeterminantDual
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionBundle

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
namespace RepTheorySurvey.Geometric.ConvolutionBundle

noncomputable section

open LinearAlgebraicGroups (TestAlgebra)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs
open scoped Matrix MatrixGroups

private theorem standard_eq_scalar_zero : standardLattice 2 = scalarLattice 2 0 := by
  apply Subtype.ext
  rw [scalarLattice_val]
  change (coordinateInclusion 2).range = (shiftedInclusion 2 0).range
  congr 1
  apply LinearMap.ext
  intro x
  funext i
  change inclusion (x i) = monomial 0 * inclusion (x i)
  have h : monomial 0 = 1 := by simp [monomial_eq_zpow]
  rw [h, one_mul]

private theorem loop_smul_val (g : Loop) (L : GL2Lattice) :
    (g • L).val = L.val.map ((loopLinearEquiv 2 g).restrictScalars O).toLinearMap := rfl

private noncomputable def relativeCongr {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) (P Q : Submodule R M) :
    (P ⧸ Q.comap P.subtype) ≃ₗ[R]
      ((P.map e.toLinearMap : Submodule R M) ⧸
        (Q.map e.toLinearMap).comap (P.map e.toLinearMap).subtype) :=
  let f := P.equivMapOfInjective e.toLinearMap e.injective
  Submodule.Quotient.equiv _ _ f (by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.val, hu, rfl⟩
    · intro hv
      obtain ⟨u, rfl⟩ := f.surjective v
      obtain ⟨w, hw, heq⟩ := (show (f u).val ∈ Q.map e.toLinearMap from hv)
      refine ⟨u, ?_, rfl⟩
      have h : w = u.val := e.injective heq
      change u.val ∈ Q
      exact h ▸ hw)

private def loopRelativeCongr (g : Loop) (L M : GL2Lattice) :
    RelativeQuotient L M ≃ₗ[ℂ] RelativeQuotient (g • L) (g • M) :=
  (relativeCongr ((loopLinearEquiv 2 g).restrictScalars O) L.val M.val).restrictScalars ℂ

private theorem loop_le_iff (g : Loop) (L M : GL2Lattice) :
    (g • L).val ≤ (g • M).val ↔ L.val ≤ M.val := by
  simp only [loop_smul_val]
  exact Submodule.map_le_map_iff_of_injective
    (((loopLinearEquiv 2 g).restrictScalars O).injective) _ _

private theorem relativeColength_smul (g : Loop) (L M : GL2Lattice) (n : ℕ) :
    ((g • M).val ≤ (g • L).val ∧ Module.Finite ℂ (RelativeQuotient (g • L) (g • M)) ∧
      Module.finrank ℂ (RelativeQuotient (g • L) (g • M)) = n) ↔
    (M.val ≤ L.val ∧ Module.Finite ℂ (RelativeQuotient L M) ∧
      Module.finrank ℂ (RelativeQuotient L M) = n) := by
  let e := loopRelativeCongr g L M
  rw [loop_le_iff, ← e.finrank_eq]
  constructor <;> rintro ⟨h1, h2, h3⟩
  · exact ⟨h1, Module.Finite.equiv e.symm, h3⟩
  · exact ⟨h1, Module.Finite.equiv e, h3⟩

private theorem colength_smul_of_fixed (g : Loop) (hg : g • standardLattice 2 = standardLattice 2)
    (L : GL2Lattice) (n : ℕ) : g • L ∈ colength n ↔ L ∈ colength n := by
  rw [standard_eq_scalar_zero] at hg
  have h := relativeColength_smul g (scalarLattice 2 0) L n
  rw [hg] at h
  exact h

private theorem positive_fixed (g : PositiveGL 2) : (g.val : Loop) • standardLattice 2 =
    standardLattice 2 := by
  obtain ⟨h, hh⟩ := g.property
  rw [← hh, standard_eq_scalar_zero]
  exact positiveGL_preserves_scalar h 0

private theorem loop_stabilizer (g : Loop) (hg : g • standardLattice 2 = standardLattice 2) :
    g ∈ PositiveGL 2 := by
  classical
  let f := (loopLinearEquiv 2 g).restrictScalars O
  let P := (scalarLattice 2 0).val
  have hP : P.map f.toLinearMap = P := by
    rw [standard_eq_scalar_zero] at hg
    exact congrArg Subtype.val hg
  let d := shiftedCoordinates 2 0
  let E : (Fin 2 → O) ≃ₗ[O] (Fin 2 → O) :=
    d ≪≫ₗ P.equivMapOfInjective f.toLinearMap f.injective ≪≫ₗ
      LinearEquiv.ofEq _ _ hP ≪≫ₗ d.symm
  let h : Positive := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv O _).symm E)
  have hshift (x : Fin 2 → O) : shiftedInclusion 2 0 x = coordinateInclusion 2 x := by
    funext i
    change monomial 0 * inclusion (x i) = inclusion (x i)
    simp [monomial_eq_zpow]
  have hE (x : Fin 2 → O) : coordinateInclusion 2 (E x) =
      loopLinearEquiv 2 g (coordinateInclusion 2 x) := by
    rw [← hshift, ← hshift, ← shiftedCoordinates_coe, ← shiftedCoordinates_coe]
    change ((d (E x)).val : Coordinates 2) = f (d x).val
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hmul (x : Fin 2 → O) : h.val *ᵥ x = E x := by
    change Matrix.mulVecLin h.val x = E x
    rw [← Matrix.GeneralLinearGroup.toLin_apply]
    simp only [h, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨h, Units.ext (Matrix.ext fun i j ↦ ?_)⟩
  have hx := (positiveGLMap_linear h (Pi.single j 1)).trans
    ((congrArg (coordinateInclusion 2) (hmul (Pi.single j 1))).trans (hE (Pi.single j 1)))
  have hsingle : coordinateInclusion 2 (Pi.single j 1) = Pi.single j 1 := by
    funext k
    by_cases hkj : k = j
    · simp [coordinateInclusion, hkj]
    · simp [coordinateInclusion, hkj]
  rw [hsingle, loopLinearEquiv_apply, loopLinearEquiv_apply, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one] at hx
  exact congrFun hx i

private theorem fixed_of_coset_eq {g k : Loop}
    (h : coset (PositiveGL 2) g = coset (PositiveGL 2) k) :
    g • standardLattice 2 = k • standardLattice 2 := by
  obtain ⟨_, a, rfl⟩ := (LatticeModels.cosetRelation (PositiveGL 2) g k).mp h
  rw [mul_smul, positive_fixed]

private theorem scalarLattice_shift (a : ℤ) :
    (scalarLattice 2 (a + 1)).val =
      (scalarLattice 2 a).val.map (t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2)) := by
  have step (x : Fin 2 → O) : shiftedInclusion 2 (a + 1) x = t • shiftedInclusion 2 a x := by
    simpa using (shiftedInclusion_add_nat 2 a 1 x).trans
      (map_smul (shiftedInclusion 2 a) (t ^ 1) x)
  rw [scalarLattice_val, scalarLattice_val]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨shiftedInclusion 2 a u, ⟨u, rfl⟩, (step u).symm⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, step u⟩

private theorem quotient_add_finrank {R M : Type*} [CommRing R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    (P Q : Submodule R M) (hPQ : P ≤ Q)
    [Module.Finite ℂ (M ⧸ Q)] [Module.Finite ℂ (Q ⧸ P.comap Q.subtype)] :
    Module.Finite ℂ (M ⧸ P) ∧
      Module.finrank ℂ (M ⧸ P) =
        Module.finrank ℂ (M ⧸ Q) + Module.finrank ℂ (Q ⧸ P.comap Q.subtype) := by
  let f := P.mkQ.comp Q.subtype
  have hf : f.ker = P.comap Q.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : f.range = Q.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let e := ((P.comap Q.subtype).quotEquivOfEq _ hf.symm) ≪≫ₗ f.quotKerEquivRange ≪≫ₗ
    LinearEquiv.ofEq _ _ hr
  let E := e.restrictScalars ℂ
  let F := (Submodule.quotientQuotientEquivQuotient P Q hPQ).restrictScalars ℂ
  let Q' := (Q.map P.mkQ).restrictScalars ℂ
  let : Module.Finite ℂ Q' := Module.Finite.equiv E
  let : Module.Finite ℂ ((M ⧸ P) ⧸ Q') := Module.Finite.equiv F.symm
  let : Module.Finite ℂ (M ⧸ P) := Module.Finite.of_submodule_quotient Q'
  exact ⟨inferInstance, by
    rw [F.finrank_eq.symm, E.finrank_eq]
    exact Q'.finrank_quotient_add_finrank.symm⟩

private def quotientInclusionEquiv {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q A : Submodule R M) (h : Q ≤ A) :
    (Q ⧸ P.comap Q.subtype) ≃ₗ[R]
      ((Q.comap A.subtype : Submodule R A) ⧸
        (P.comap A.subtype).comap (Q.comap A.subtype).subtype) := by
  let f : Q →ₗ[R] (Q.comap A.subtype : Submodule R A) :=
    (Submodule.inclusion h).codRestrict _ fun x ↦ x.property
  let e := LinearEquiv.ofBijective f ⟨
    fun x y hxy ↦ Subtype.ext (congrArg (fun z ↦ z.val.val) hxy),
    fun z ↦ ⟨⟨z.val.val, z.property⟩, rfl⟩⟩
  apply Submodule.Quotient.equiv _ _ e
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x.val.val, x.property⟩, hx, rfl⟩

private theorem flags_colength_two (F : Flags) : F.val.2 ∈ colength 2 := by
  let A := (scalarLattice 2 0).val
  let P := F.val.2.val.comap A.subtype
  let Q := F.val.1.val.comap A.subtype
  have h1 : F.val.1 ∈ colength 1 := F.property.1
  obtain ⟨hA, hfin, hdim⟩ := h1
  obtain ⟨_, h21, hfin21, hdim21⟩ := F.property
  have hPQ : P ≤ Q := Submodule.comap_mono h21
  let e := (quotientInclusionEquiv F.val.2.val F.val.1.val A hA).restrictScalars ℂ
  let := hfin
  let := hfin21
  let : Module.Finite ℂ _ := Module.Finite.equiv e
  obtain ⟨hfinite, heq⟩ := @quotient_add_finrank O (A : Type)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    P Q hPQ hfin (Module.Finite.equiv e)
  have hdim21' := e.finrank_eq.symm.trans hdim21
  refine ⟨h21.trans hA, hfinite, ?_⟩
  exact heq.trans (by rw [show Module.finrank ℂ (StandardQuotient F.val.1) = 1 from hdim, hdim21'])

private theorem exists_standard_basis (h₁ : MinusculeOrbit) {L : GL2Lattice}
    (hL : L ∈ colength 1) : ∃ g : Loop, g • standardLattice 2 = L := by
  rw [h₁.1] at hL
  obtain ⟨a, ha⟩ := hL
  refine ⟨a.val * diagonalLoop 2 (pairCoweight minusculePair), ?_⟩
  rw [mul_smul, diagonalLoop_smul_standard]
  exact ha

private theorem std_transport (g : Loop) (x : GL2Lattice) (n : ℕ) :
    ((g • x).val ≤ (g • standardLattice 2).val ∧
      Module.Finite ℂ (RelativeQuotient (g • standardLattice 2) (g • x)) ∧
      Module.finrank ℂ (RelativeQuotient (g • standardLattice 2) (g • x)) = n)
      ↔ x ∈ colength n := by
  rw [relativeColength_smul, standard_eq_scalar_zero]
  rfl

private theorem flags_shift_le (h₁ : MinusculeOrbit) (F : Flags) :
    Submodule.map (t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2))
      F.val.1.val ≤ F.val.2.val := by
  obtain ⟨g, hg⟩ := exists_standard_basis h₁ F.property.1
  let x := g⁻¹ • F.val.2
  have hxg : g • x = F.val.2 := smul_inv_smul g F.val.2
  have hx : x ∈ colength 1 := (std_transport g x 1).mp (by
    rw [hg, hxg]
    exact F.property.2)
  have hscalar := h₁.2 ⟨x, hx⟩
  rw [← hg, ← hxg]
  rw [loop_smul_val, loop_smul_val, ← Submodule.map_comp]
  let E := ((loopLinearEquiv 2 g).restrictScalars O).toLinearMap
  let T := t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2)
  have commute : T.comp E = E.comp T :=
    LinearMap.ext fun v ↦ (E.map_smul t v).symm
  change (standardLattice 2).val.map (T.comp E) ≤ x.val.map E
  rw [commute, Submodule.map_comp, standard_eq_scalar_zero, ← scalarLattice_shift]
  exact Submodule.map_mono hscalar

theorem twistedFlags_conditional (h₁ : MinusculeOrbit) (_ : MinusculeProjective)
    (_ : SmallSchubertSchemes) (h₂ : TwoStepOrbits) (_ : TwoStepStableModel) : TwistedFlags := by
  classical
  let h : StableStage (PositiveGL 2) (colength 1) :=
    fun a x hx ↦ (colength_smul_of_fixed a.val (positive_fixed a) x 1).mpr hx
  let f : Representatives (PositiveGL 2) firstStage (colength 1) → Flags := fun p ↦
    ⟨(p.val.1 • standardLattice 2, p.val.1 • p.val.2), by
      obtain ⟨k, hk, hL⟩ := p.property.1
      refine ⟨?_, (std_transport p.val.1 p.val.2 1).mpr p.property.2⟩
      rwa [← fixed_of_coset_eq hk]⟩
  let m : OrderedProduct h → Flags := Quotient.lift f (by
    rintro p q ⟨a, ha, hx⟩
    apply Subtype.ext
    change (p.val.1 • standardLattice 2, p.val.1 • p.val.2) =
      (q.val.1 • standardLattice 2, q.val.1 • q.val.2)
    rw [ha, hx, mul_smul, positive_fixed, mul_smul]
    simp)
  have hm : Function.Bijective m := by
    constructor
    · intro P Q
      induction P using Quotient.inductionOn with | h p =>
      induction Q using Quotient.inductionOn with | h q =>
      intro he
      have he₁ := congrArg (fun z : Flags ↦ z.val.1) he
      have he₂ := congrArg (fun z : Flags ↦ z.val.2) he
      change p.val.1 • standardLattice 2 = q.val.1 • standardLattice 2 at he₁
      change p.val.1 • p.val.2 = q.val.1 • q.val.2 at he₂
      let a : PositiveGL 2 := ⟨p.val.1⁻¹ * q.val.1,
        loop_stabilizer _ (by rw [mul_smul, ← he₁, inv_smul_smul])⟩
      apply Quotient.sound
      change ∃ a : PositiveGL 2, q.val.1 = p.val.1 * a.val ∧
        q.val.2 = (↑(a⁻¹) : Loop) • p.val.2
      refine ⟨a, ?_, ?_⟩
      · simp [a, ← mul_assoc]
      · change q.val.2 = (p.val.1⁻¹ * q.val.1)⁻¹ • p.val.2
        rw [mul_inv_rev, inv_inv, mul_smul, he₂, inv_smul_smul]
    · intro F
      obtain ⟨g, hg⟩ := exists_standard_basis h₁ F.property.1
      let x := g⁻¹ • F.val.2
      have hxg : g • x = F.val.2 := smul_inv_smul g F.val.2
      have hx : x ∈ colength 1 := (std_transport g x 1).mp (by
        rw [hg, hxg]
        exact F.property.2)
      let p : Representatives (PositiveGL 2) firstStage (colength 1) :=
        ⟨(g, x), ⟨g, rfl, hg.symm ▸ F.property.1⟩, hx⟩
      refine ⟨Quotient.mk _ p, Subtype.ext ?_⟩
      exact Prod.ext hg hxg
  let e := Equiv.ofBijective m hm
  refine ⟨h, e, fun _ ↦ rfl, fun F ↦ ?_⟩
  have hF := flags_colength_two F
  exact ⟨hF, h₂.1 ⟨F.val.2, hF⟩, flags_shift_le h₁ F⟩


private abbrev Std := (scalarLattice 2 0).val

private abbrev stdQ (m : ℕ) : Std →ₗ[O] Window 2 0 m :=
  @Submodule.mkQ O (Std : Type) inferInstance inferInstance inferInstance (windowLower 2 0 m)

private theorem stdQ_surjective (m : ℕ) : Function.Surjective (stdQ m) :=
  @Submodule.mkQ_surjective O (Std : Type) inferInstance inferInstance inferInstance (windowLower 2 0 m)

private theorem stdQ_mem_plane (m : ℕ) (L : GL2Lattice) (w : Window 2 0 m) :
    w ∈ latticeSubspace 0 m L ↔ ∃ x : Std, x.val ∈ L.val ∧ stdQ m x = w := Iff.rfl

private theorem stdQ_eq_zero_iff (m : ℕ) (x : Std) :
    stdQ m x = 0 ↔ x.val ∈ (scalarLattice 2 (m : ℤ)).val := by
  have h := Submodule.Quotient.mk_eq_zero (windowLower 2 0 m) (x := x)
  change stdQ m x = 0 ↔ x.val ∈ (scalarLattice 2 (0 + (m : ℤ))).val at h
  rwa [zero_add] at h

private theorem window_subspace_le_iff {m : ℕ} {L M : GL2Lattice}
    (hL : L.val ≤ Std) (hM : (scalarLattice 2 (m : ℤ)).val ≤ M.val) :
    latticeSubspace 0 m L ≤ latticeSubspace 0 m M ↔ L.val ≤ M.val := by
  constructor
  · intro h v hv
    let x : Std := ⟨v, hL hv⟩
    obtain ⟨y, hy, hyx⟩ := (stdQ_mem_plane m M _).mp
      (h ((stdQ_mem_plane m L _).mpr ⟨x, hv, rfl⟩))
    have hxy : stdQ m (x - y) = 0 := by
      exact ((stdQ m).map_sub x y).trans (by rw [hyx, sub_self])
    have hmem : v - y.val ∈ M.val := hM ((stdQ_eq_zero_iff m _).mp hxy)
    simpa using M.val.add_mem hmem hy
  · intro h w hw
    obtain ⟨x, hx, rfl⟩ := (stdQ_mem_plane m L w).mp hw
    exact (stdQ_mem_plane m M _).mpr ⟨x, h hx, rfl⟩

private theorem shifted_zero_apply (x : Fin 2 → O) :
    shiftedInclusion 2 0 x = coordinateInclusion 2 x := by
  funext i
  change monomial 0 * inclusion (x i) = inclusion (x i)
  simp [monomial_eq_zpow]

private theorem shifted_zero_positive (g : Positive) (x : Fin 2 → O) :
    loopLinearEquiv 2 (positiveGLMap 2 g) (shiftedCoordinates 2 0 x).val =
      (shiftedCoordinates 2 0 (g.val *ᵥ x)).val := by
  simp only [shiftedCoordinates_coe, shifted_zero_apply, positiveGLMap_linear]

private def onStd (g : Positive) (x : Std) : Std :=
  ⟨loopLinearEquiv 2 (positiveGLMap 2 g) x.val, by
    change _ ∈ (scalarLattice 2 0).val
    rw [← positiveGL_preserves_scalar g 0]
    exact ⟨x.val, x.property, rfl⟩⟩

private theorem windowJets_stdQ (m : ℕ) (x : Std) :
    windowJets 2 0 m (stdQ m x) = windowReduction 2 0 m x := rfl

private theorem windowReduction_positive (g : Positive) (m : ℕ) (x : Std) :
    windowReduction 2 0 m (onStd g x) =
      (g.val.map (jetReduction m).toRingHom) *ᵥ (windowReduction 2 0 m x) := by
  obtain ⟨y, rfl⟩ := (shiftedCoordinates 2 0).surjective x
  have he : onStd g (shiftedCoordinates 2 0 y) = shiftedCoordinates 2 0 (g.val *ᵥ y) :=
    Subtype.ext (shifted_zero_positive g y)
  rw [he]
  have hr (z : Fin 2 → O) :
      windowReduction 2 0 m (shiftedCoordinates 2 0 z) = fun i ↦ jetReduction m (z i) := by
    funext i
    change jetReduction m ((shiftedCoordinates 2 0).symm (shiftedCoordinates 2 0 z) i) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hr, hr]
  exact funext ((jetReduction m).toRingHom.map_mulVec g.val y)

private theorem truncateJet_self (m : ℕ) : truncateJet (le_refl m) = RingHom.id (JetRing m) := by
  apply Ideal.Quotient.ringHom_ext
  rfl

private theorem jet_positive_stdQ (g : Positive) (x : Std) :
    windowJetLinear 0 (le_refl 2) (reduceGL 2 2 (by omega) g).val (stdQ 2 x) =
      stdQ 2 (onStd g x) := by
  apply (windowJets 2 0 2).injective
  unfold windowJetLinear
  change (windowJets 2 0 2) ((windowJets 2 0 2).symm
    (((reduceGL 2 2 (by omega) g).val.map (truncateJet (le_refl 2))) *ᵥ
      windowJets 2 0 2 (stdQ 2 x))) = _
  rw [LinearEquiv.apply_symm_apply, windowJets_stdQ, windowJets_stdQ, windowReduction_positive,
    truncateJet_self]
  rfl

private theorem positive_windowSubspace (g : Positive) (L : GL2Lattice) :
    latticeSubspace 0 2 (positiveGLMap 2 g • L) =
      (latticeSubspace 0 2 L).map
        (windowJetLinear 0 (le_refl 2) (reduceGL 2 2 (by omega) g).val) := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, rfl⟩ := (stdQ_mem_plane 2 _ _).mp hw
    obtain ⟨y, hy, he⟩ := hx
    have hxy : (onStd g⁻¹ x).val = y := by
      change loopLinearEquiv 2 (positiveGLMap 2 g⁻¹) x.val = y
      rw [← he]
      change loopLinearEquiv 2 (positiveGLMap 2 g⁻¹)
        (loopLinearEquiv 2 (positiveGLMap 2 g) y) = y
      rw [map_inv, map_inv]
      exact (loopLinearEquiv 2 (positiveGLMap 2 g)).symm_apply_apply y
    refine ⟨stdQ 2 (onStd g⁻¹ x), (stdQ_mem_plane 2 _ _).mpr
      ⟨onStd g⁻¹ x, hxy.symm ▸ hy, rfl⟩, ?_⟩
    rw [jet_positive_stdQ]
    congr 1
    apply Subtype.ext
    change loopLinearEquiv 2 (positiveGLMap 2 g) (onStd g⁻¹ x).val = x.val
    rw [hxy]
    exact he
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (stdQ_mem_plane 2 _ _).mp hq
    rw [jet_positive_stdQ]
    exact (stdQ_mem_plane 2 _ _).mpr ⟨onStd g x, ⟨x.val, hx, rfl⟩, rfl⟩

private theorem reduce_two_surjective : Function.Surjective (reduceGL 2 2 (by omega)) := by
  classical
  intro g
  choose x hx using fun i j : Fin 2 ↦ Ideal.Quotient.mk_surjective (g.val i j)
  let M : Matrix (Fin 2) (Fin 2) O := x
  have hM : M.map (jetReduction 2).toRingHom = g.val := Matrix.ext hx
  have hu : IsUnit (jetReduction 2 M.det) := by
    have hm' : (jetReduction 2).toRingHom.mapMatrix M = g.val := hM
    change IsUnit ((jetReduction 2).toRingHom M.det)
    rw [RingHom.map_det, hm']
    exact Matrix.isUnits_det_units g
  let c : JetRing 2 →+* ℂ :=
    Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
      change jetIdeal 2 ≤ RingHom.ker PowerSeries.constantCoeff
      rw [jetIdeal, Ideal.span_le]
      rintro v (rfl : v = t ^ 2)
      simp [RingHom.mem_ker])
  have hc : IsUnit (PowerSeries.constantCoeff M.det) := hu.map c
  let h : Positive := Matrix.GeneralLinearGroup.mk'' M
    (PowerSeries.isUnit_iff_constantCoeff.mpr hc)
  refine ⟨h, Units.ext ?_⟩
  change (h.val.map (jetReduction 2).toRingHom) = g.val
  exact hM

@[instance_reducible] private def positiveFlagAction : MulAction Positive Flags where
  smul g L := ⟨(positiveGLMap 2 g • L.val.1, positiveGLMap 2 g • L.val.2),
    (colength_smul_of_fixed _ (by
      rw [standard_eq_scalar_zero]
      exact positiveGL_preserves_scalar g 0) _ 1).mpr L.property.1,
    (relativeColength_smul _ L.val.1 L.val.2 1).mpr L.property.2⟩
  one_smul L := Subtype.ext (by
    change (positiveGLMap 2 1 • L.val.1, positiveGLMap 2 1 • L.val.2) = L.val
    rw [map_one, one_smul, one_smul])
  mul_smul g k L := Subtype.ext (by
    change (positiveGLMap 2 (g * k) • L.val.1, positiveGLMap 2 (g * k) • L.val.2) =
      (positiveGLMap 2 g • (positiveGLMap 2 k • L.val.1),
        positiveGLMap 2 g • (positiveGLMap 2 k • L.val.2))
    rw [map_mul, mul_smul, mul_smul])

theorem flagJetAction_conditional (_ : MinusculeOrbit) (_ : MinusculeProjective)
    (_ : SmallSchubertSchemes) (h₂ : TwoStepOrbits) (_ : TwoStepStableModel) : FlagJetAction := by
  classical
  let red := reduceGL 2 2 (by omega)
  let a := positiveFlagAction
  have injectiveWindow {F G : Flags}
      (hfirst : latticeSubspace 0 2 F.val.1 = latticeSubspace 0 2 G.val.1)
      (hsecond : latticeSubspace 0 2 F.val.2 = latticeSubspace 0 2 G.val.2) : F = G := by
    have bounds (L : Flags) :
        (scalarLattice 2 2).val ≤ L.val.2.val ∧
          (scalarLattice 2 2).val ≤ L.val.1.val ∧ L.val.1.val ≤ Std ∧ L.val.2.val ≤ Std := by
      have hl := h₂.1 ⟨_, flags_colength_two L⟩
      exact ⟨hl, hl.trans L.property.2.1, (show L.val.1 ∈ colength 1 from L.property.1).1,
        (flags_colength_two L).1⟩
    have hF := bounds F
    have hG := bounds G
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact le_antisymm ((window_subspace_le_iff hF.2.2.1 hG.2.1).mp hfirst.le)
        ((window_subspace_le_iff hG.2.2.1 hF.2.1).mp hfirst.ge)
    · exact le_antisymm ((window_subspace_le_iff hF.2.2.2 hG.1).mp hsecond.le)
        ((window_subspace_le_iff hG.2.2.2 hF.1).mp hsecond.ge)
  have eqAction (g k : Positive) (h : red g = red k) (L : Flags) :
      a.smul g L = a.smul k L := by
    apply injectiveWindow
    · change latticeSubspace 0 2 (positiveGLMap 2 g • L.val.1) =
        latticeSubspace 0 2 (positiveGLMap 2 k • L.val.1)
      rw [positive_windowSubspace, positive_windowSubspace, show red g = red k from h]
    · change latticeSubspace 0 2 (positiveGLMap 2 g • L.val.2) =
        latticeSubspace 0 2 (positiveGLMap 2 k • L.val.2)
      rw [positive_windowSubspace, positive_windowSubspace, show red g = red k from h]
  choose lift hlift using reduce_two_surjective
  let ρ : MulAction (GLJets 2 2 (by omega)) Flags :=
    { smul := fun g L ↦ a.smul (lift g) L
      one_smul := fun L ↦ (eqAction _ 1 (by simpa [red] using hlift 1) L).trans (a.one_smul L)
      mul_smul := fun g k L ↦
        (eqAction _ (lift g * lift k) (by
          change reduceGL 2 2 _ (lift (g * k)) = reduceGL 2 2 _ (lift g * lift k)
          rw [map_mul, hlift, hlift, hlift]) L).trans (a.mul_smul _ _ L) }
  refine ⟨ρ, ?_, ?_⟩
  · intro g L
    change latticeSubspace 0 2 (positiveGLMap 2 (lift g) • L.val.1) = _ ∧
      latticeSubspace 0 2 (positiveGLMap 2 (lift g) • L.val.2) = _
    rw [positive_windowSubspace, positive_windowSubspace, hlift]
    exact ⟨rfl, rfl⟩
  · intro g L
    exact congrArg Subtype.val (eqAction _ g (hlift (red g)) L)


private def shortCoefficients : Std →ₗ[ℂ] V :=
  constantCoordinates.toLinearMap.comp ((stdQ 1).restrictScalars ℂ)

private def longCoefficients : Std →ₗ[ℂ] (V × V) :=
  twoStepCoordinates.toLinearMap.comp ((stdQ 2).restrictScalars ℂ)

private theorem longCoefficients_fst (x : Std) :
    (longCoefficients x).1 = shortCoefficients x := rfl

private theorem longCoefficients_surjective : Function.Surjective longCoefficients :=
  twoStepCoordinates.surjective.comp (stdQ_surjective 2)

private theorem longCoefficients_shift (h : TwoStepStableModel) (x : Std) :
    longCoefficients (t • x) = (0, shortCoefficients x) := by
  change twoStepCoordinates (stdQ 2 (t • x)) = _
  rw [(stdQ 2).map_smul]
  change twoStepCoordinates (windowOperator 2 0 2 (stdQ 2 x)) = _
  exact h.1 (stdQ 2 x)

private theorem shortCoefficients_zero (x : Std) :
    shortCoefficients x = 0 ↔ x.val ∈ scalarPoint.val := by
  refine Iff.trans ?_ (stdQ_eq_zero_iff 1 x)
  exact ⟨fun h ↦ constantCoordinates.injective (h.trans constantCoordinates.map_zero.symm),
    fun h ↦ (congrArg constantCoordinates h).trans constantCoordinates.map_zero⟩

private theorem longCoefficients_zero (x : Std) :
    longCoefficients x = 0 ↔ x.val ∈ (scalarLattice 2 2).val := by
  refine Iff.trans ?_ (stdQ_eq_zero_iff 2 x)
  exact ⟨fun h ↦ twoStepCoordinates.injective (h.trans twoStepCoordinates.map_zero.symm),
    fun h ↦ (congrArg twoStepCoordinates h).trans twoStepCoordinates.map_zero⟩

private abbrev firstLine (L : GL2Lattice) :=
  (latticeSubspace 0 1 L).map constantCoordinates.toLinearMap

private theorem firstLine_mem (L : GL2Lattice) (v : V) :
    v ∈ firstLine L ↔ ∃ x : Std, x.val ∈ L.val ∧ shortCoefficients x = v := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (stdQ_mem_plane 1 L w).mp hw
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨stdQ 1 x, (stdQ_mem_plane 1 L _).mpr ⟨x, hx, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem mem_of_shortCoefficients {L : GL2Lattice}
    (hl : scalarPoint.val ≤ L.val) (x : Std) :
    shortCoefficients x ∈ firstLine L ↔ x.val ∈ L.val := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := (firstLine_mem L _).mp hx
    have hxy : shortCoefficients (x - y) = 0 := by
      exact (shortCoefficients.map_sub x y).trans (by rw [he, sub_self])
    have hsub := hl ((shortCoefficients_zero (x - y)).mp hxy)
    simpa using L.val.add_mem hsub hy
  · exact fun h ↦ (firstLine_mem L _).mpr ⟨x, h, rfl⟩

private def firstInStandard (L : Colength 1) : L.val.val →ₗ[O] Std :=
  Submodule.inclusion (show L.val.val ≤ Std from L.property.1)

private def splitCoefficients (L : Colength 1) :
    L.val.val →ₗ[ℂ] firstLine L.val × (V ⧸ firstLine L.val) :=
  let i := (firstInStandard L).restrictScalars ℂ
  let cf := shortCoefficients.comp i
  let lf := (LinearMap.snd ℂ V V).comp (longCoefficients.comp i)
  (cf.codRestrict (firstLine L.val) fun x ↦
    (firstLine_mem L.val _).mpr ⟨firstInStandard L x, x.property, rfl⟩).prod
    ((firstLine L.val).mkQ.comp lf)

private theorem splitCoefficients_surjective (h : MinusculeOrbit) (L : Colength 1) :
    Function.Surjective (splitCoefficients L) := by
  rintro ⟨a, b⟩
  obtain ⟨b, rfl⟩ := (firstLine L.val).mkQ_surjective b
  obtain ⟨z, hz⟩ := longCoefficients_surjective (a.val, b)
  have hz₀ : shortCoefficients z = a.val :=
    (longCoefficients_fst z).symm.trans (congrArg Prod.fst hz)
  have hzL : z.val ∈ L.val.val := (mem_of_shortCoefficients (h.2 L) z).mp (hz₀.symm ▸ a.property)
  refine ⟨⟨z.val, hzL⟩, Prod.ext (Subtype.ext ?_) ?_⟩
  · exact hz₀
  · exact congrArg (firstLine L.val).mkQ (congrArg Prod.snd hz)

set_option backward.isDefEq.respectTransparency false in
private theorem splitCoefficients_ker (h : MinusculeOrbit) (h' : TwoStepStableModel)
    (L : Colength 1) :
    (splitCoefficients L).ker = (firstLatticeShift L).restrictScalars ℂ := by
  ext x
  change splitCoefficients L x = 0 ↔ x ∈ firstLatticeShift L
  let A := firstInStandard L
  let S := firstLine L.val
  have zero_iff (v : L.val.val) : splitCoefficients L v = 0 ↔
      shortCoefficients (A v) = 0 ∧ (longCoefficients (A v)).2 ∈ S := by
    constructor
    · intro e
      exact ⟨congrArg (fun z : S × (V ⧸ S) ↦ z.1.val) e,
        (Submodule.Quotient.mk_eq_zero S).mp (congrArg Prod.snd e)⟩
    · rintro ⟨h0, h1⟩
      exact Prod.ext (Subtype.ext h0) ((Submodule.Quotient.mk_eq_zero S).mpr h1)
  rw [zero_iff]
  constructor
  · rintro ⟨hx₀, hx₁⟩
    obtain ⟨z, hz, he⟩ := (firstLine_mem L.val _).mp hx₁
    let y : L.val.val := ⟨z.val, hz⟩
    have hy : longCoefficients (A (t • y)) = (0, (longCoefficients (A x)).2) :=
      ((congrArg longCoefficients (A.map_smul t y)).trans (longCoefficients_shift h' z)).trans
        (congrArg (fun u : V ↦ (0, u)) he)
    have hdiff : longCoefficients (A x - A (t • y)) = 0 := by
      have hp : longCoefficients (A x) = (0, (longCoefficients (A x)).2) :=
        Prod.ext ((longCoefficients_fst (A x)).trans hx₀) rfl
      have hadd := longCoefficients.map_add (A x - A (t • y)) (A (t • y))
      have hcancel : A x - A (t • y) + A (t • y) = A x :=
        sub_add_cancel (A x) (A (t • y))
      apply add_right_cancel (b := longCoefficients (A (t • y)))
      exact hadd.symm.trans ((congrArg longCoefficients hcancel).trans
        ((hp.trans hy.symm).trans (zero_add _).symm))
    have hb := (longCoefficients_zero _).mp hdiff
    change x.val - (t • y).val ∈ (scalarLattice 2 2).val at hb
    have bound : (scalarLattice 2 2).val ≤
        L.val.val.map (t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2)) := by
      have hs := scalarLattice_shift 1
      change (scalarLattice 2 2).val = _ at hs
      rw [hs]
      exact Submodule.map_mono (h.2 L)
    obtain ⟨u, hu, hu'⟩ := bound hb
    refine ⟨y + ⟨u, hu⟩, Subtype.ext ?_⟩
    change t • (y.val + u) = x.val
    rw [smul_add t y.val u]
    change t • u = x.val - t • y.val at hu'
    rw [hu']
    abel
  · rintro ⟨y, rfl⟩
    have hys : longCoefficients (A (t • y)) = (0, shortCoefficients (A y)) :=
      (congrArg longCoefficients (A.map_smul t y)).trans (longCoefficients_shift h' (A y))
    change shortCoefficients (A (t • y)) = 0 ∧ (longCoefficients (A (t • y))).2 ∈ S
    rw [← longCoefficients_fst, hys]
    exact ⟨rfl, (firstLine_mem L.val _).mpr ⟨A y, y.property, rfl⟩⟩

private def quotientEquivOfKernel {R M Y : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    [AddCommGroup Y] [Module ℂ Y] (P : Submodule R M) (f : M →ₗ[ℂ] Y)
    (hker : f.ker = P.restrictScalars ℂ) (hsurj : Function.Surjective f) :
    (M ⧸ P) ≃ₗ[ℂ] Y :=
  (P.restrictScalars ℂ).quotEquivOfEq _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj

theorem firstLatticeQuotient_conditional (h : MinusculeOrbit) (_ : MinusculeProjective)
    (_ : SmallSchubertSchemes) (_ : TwoStepOrbits) (h' : TwoStepStableModel) :
    FirstLatticeQuotient := by
  intro L
  let e := @quotientEquivOfKernel O (L.val.val : Type) _
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (firstLatticeShift L) (splitCoefficients L)
    (splitCoefficients_ker h h' L) (splitCoefficients_surjective h L)
  refine ⟨e, fun x ↦ ?_⟩
  change (shortCoefficients (firstInStandard L x) = (firstLatticeCoefficients L x).1) ∧
    ((firstLine L.val).mkQ (longCoefficients (firstInStandard L x)).2 =
      (firstLine L.val).mkQ (firstLatticeCoefficients L x).2)
  exact ⟨(longCoefficients_fst (firstInStandard L x)).symm, rfl⟩


section FlagCoordinates

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points)

private abbrev secondSubspace (M : GL2Lattice) :=
  (latticeSubspace 0 2 M).map twoStepCoordinates.toLinearMap

private theorem secondSubspace_mem (M : GL2Lattice) (w : V × V) :
    w ∈ secondSubspace M ↔ ∃ x : Std, x.val ∈ M.val ∧ longCoefficients x = w := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (stdQ_mem_plane 2 M v).mp hv
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨stdQ 2 x, (stdQ_mem_plane 2 M _).mpr ⟨x, hx, rfl⟩, rfl⟩

private theorem secondSubspace_first (h : MinusculeOrbit) (L : Colength 1) :
    secondSubspace L.val = (firstLine L.val).prod (⊤ : Submodule ℂ V) := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (secondSubspace_mem L.val v).mp hv
    refine ⟨?_, Submodule.mem_top⟩
    rw [longCoefficients_fst]
    exact (firstLine_mem L.val _).mpr ⟨x, hx, rfl⟩
  · intro hv
    obtain ⟨x, rfl⟩ := longCoefficients_surjective v
    exact (secondSubspace_mem L.val _).mpr ⟨x,
      (mem_of_shortCoefficients (h.2 L) x).mp ((longCoefficients_fst x) ▸ hv.1), rfl⟩

private theorem flag_incidence (h₁ : MinusculeOrbit) (h₂ : TwoStepStableModel) (F : Flags) :
    IncidenceCondition (firstLine F.val.1) (secondSubspace F.val.2) := by
  constructor
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hzero : x = 0 := (Submodule.mem_bot ℂ).mp hx
    subst x
    obtain ⟨z, hz, he⟩ := (firstLine_mem F.val.1 y).mp hy
    exact (secondSubspace_mem F.val.2 _).mpr
      ⟨t • z, flags_shift_le h₁ F ⟨z.val, hz, rfl⟩,
        (longCoefficients_shift h₂ z).trans (congrArg (fun v : V ↦ (0, v)) he)⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := (secondSubspace_mem F.val.2 _).mp hw
    rw [← secondSubspace_first h₁ ⟨F.val.1, F.property.1⟩]
    exact (secondSubspace_mem F.val.1 _).mpr ⟨x, F.property.2.1 hx, rfl⟩

private def relativeQuotient_incl {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) :
    (Q ⧸ P.comap Q.subtype) ≃ₗ[R] (Q.map P.mkQ : Submodule R (M ⧸ P)) := by
  let f := P.mkQ.comp Q.subtype
  have hf : f.ker = P.comap Q.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : f.range = Q.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ((P.comap Q.subtype).quotEquivOfEq _ hf.symm) ≪≫ₗ
    f.quotKerEquivRange ≪≫ₗ LinearEquiv.ofEq _ _ hr

private theorem flags_of_colengths (L : Colength 1) (M : Colength 2) (h : M.val.val ≤ L.val.val) :
    IsFlag (L.val, M.val) := by
  let P := M.val.val.comap Std.subtype
  let Q := L.val.val.comap Std.subtype
  let f := (quotientInclusionEquiv M.val.val L.val.val Std L.property.1).restrictScalars ℂ
  let e₀ := @relativeQuotient_incl O (Std : Type) inferInstance inferInstance inferInstance P Q
  let E := e₀.restrictScalars ℂ
  have hPQ : P ≤ Q := Submodule.comap_mono h
  let : Module.Finite ℂ (StandardQuotient M.val) := M.property.2.1
  let Pq := @Submodule.mkQ O (Std : Type) inferInstance inferInstance inferInstance P
  let Rng := Q.map Pq
  let Q' := Rng.restrictScalars ℂ
  let hQ' : Module.Finite ℂ Q' := inferInstance
  let hQ : Module.Finite ℂ Rng := hQ'
  let hfin := @Module.Finite.equiv ℂ (Rng : Type) _ _ _ _ _ _ hQ (f ≪≫ₗ E).symm
  obtain ⟨_, hr⟩ := @quotient_add_finrank O (Std : Type) inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance P Q hPQ L.property.2.1 (Module.Finite.equiv f)
  have hdim : Module.finrank ℂ (RelativeQuotient L.val M.val) = 1 := by
    have h1 : Module.finrank ℂ (StandardQuotient L.val) = 1 := L.property.2.2
    have h2 : Module.finrank ℂ (StandardQuotient M.val) = 2 := M.property.2.2
    change Module.finrank ℂ (StandardQuotient M.val) =
      Module.finrank ℂ (StandardQuotient L.val) + _ at hr
    have hsum : 2 = 1 + Module.finrank ℂ (RelativeQuotient L.val M.val) :=
      h2.symm.trans (hr.trans (congrArg₂ (· + ·) h1 f.finrank_eq.symm))
    exact Nat.add_left_cancel (hsum.symm.trans (show 2 = 1 + 1 by decide))
  exact ⟨L.property, h, hfin, hdim⟩

private theorem le_of_incidence (h₁ : MinusculeOrbit)
    (L : Colength 1) (M : Colength 2)
    (h : IncidenceCondition (firstLine L.val) (secondSubspace M.val)) :
    M.val.val ≤ L.val.val := by
  have hlower : (scalarLattice 2 2).val ≤ L.val.val := by
    have hl : (scalarLattice 2 2).val ≤ scalarPoint.val :=
      scalarLattice_add_nat_le 2 1 1
    exact hl.trans (h₁.2 L)
  apply (window_subspace_le_iff M.property.1 hlower).mp
  apply (Submodule.map_le_map_iff_of_injective twoStepCoordinates.injective _ _).mp
  change secondSubspace M.val ≤ secondSubspace L.val
  rw [secondSubspace_first h₁ L]
  exact h.2

/-- The flags in the two coefficient Grassmannians with both incidence constraints. -/
abbrev CoefficientFlags :=
  {q : ProjectivePoints × TwoStepPoints //
    IncidenceCondition (firstPlane q.1) (grassmannianSubspace twoStepBasis twoStepRank q.2.val)}

/-- Comparison with the incidence conditions, before imposing the reduced scheme structure. -/
theorem flags_coefficientComparison (h₁ : MinusculeOrbit) (hp : MinusculeProjective)
    (hs : TwoStepStableModel) :
    ∃ e : Flags ≃ₜ CoefficientFlags,
      ∀ L : Flags,
        firstPlane (e L).val.1 = firstLine L.val.1 ∧
        grassmannianSubspace twoStepBasis twoStepRank (e L).val.2.val =
          secondSubspace L.val.2 := by
  obtain ⟨e₁, he₁, _⟩ := hp.1
  obtain ⟨e₂, he₂, _⟩ := hs.2.1
  let encode (L : Flags) : CoefficientFlags :=
    ⟨(e₁ ⟨L.val.1, L.property.1⟩, e₂ ⟨L.val.2, flags_colength_two L⟩), by
      change IncidenceCondition (grassmannianSubspace projectiveBasis projectiveRank
        (e₁ ⟨L.val.1, L.property.1⟩)) (grassmannianSubspace twoStepBasis twoStepRank
        (e₂ ⟨L.val.2, flags_colength_two L⟩).val)
      rw [he₁, he₂]
      exact flag_incidence h₁ hs L⟩
  let decode (q : CoefficientFlags) : Flags := by
    let L := e₁.symm q.val.1
    let M := e₂.symm q.val.2
    have heL := he₁ L
    have heM := he₂ M
    dsimp only [L, M] at heL heM
    rw [e₁.apply_symm_apply] at heL
    rw [e₂.apply_symm_apply] at heM
    have h := q.property
    change IncidenceCondition (grassmannianSubspace projectiveBasis projectiveRank q.val.1)
      (grassmannianSubspace twoStepBasis twoStepRank q.val.2.val) at h
    rw [heL, heM] at h
    exact ⟨(L.val, M.val), flags_of_colengths L M (le_of_incidence h₁ L M h)⟩
  have hf₁ : Continuous (fun L : Flags ↦ (⟨L.val.1, L.property.1⟩ : Colength 1)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hf₂ : Continuous (fun L : Flags ↦ (⟨L.val.2, flags_colength_two L⟩ : Colength 2)) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  let e : Flags ≃ₜ CoefficientFlags := {
    toFun := encode
    invFun := decode
    left_inv := fun L ↦ Subtype.ext (Prod.ext
      (congrArg Subtype.val (e₁.symm_apply_apply _))
      (congrArg Subtype.val (e₂.symm_apply_apply _)))
    right_inv := fun q ↦ Subtype.ext (Prod.ext
      (e₁.apply_symm_apply _) (e₂.apply_symm_apply _))
    continuous_toFun := ((e₁.continuous.comp hf₁).prodMk (e₂.continuous.comp hf₂)).subtype_mk _
    continuous_invFun := ((continuous_subtype_val.comp
      (e₁.symm.continuous.comp (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_subtype_val.comp
        (e₂.symm.continuous.comp (continuous_snd.comp continuous_subtype_val)))).subtype_mk _ }
  exact ⟨e, fun L ↦ ⟨he₁ ⟨L.val.1, L.property.1⟩, he₂ ⟨L.val.2, flags_colength_two L⟩⟩⟩

theorem incidenceReduced : IsReduced incidenceScheme.left :=
  LatticeModels.reducedClosure_reduced IncidenceAmbient incidenceLocus

theorem incidenceInclusion_closed : IsClosedImmersion incidenceInclusion.left :=
  inferInstanceAs (IsClosedImmersion (reducedClosureIdeal IncidenceAmbient incidenceLocus).subschemeι)

private theorem incidenceCoordinates_injective :
    Function.Injective incidenceCoordinates := by
  have := incidenceInclusion_closed
  have : Mono incidenceInclusion := Over.mono_of_mono_left _
  have : IsClosedImmersion twoStepSchemeInGrassmannian.left :=
    inferInstanceAs (IsClosedImmersion
      (reducedClosureIdeal (grassmannianCharts twoStepBasis twoStepRank).scheme
        {p | StablePlane twoStepBasis twoStepRank shift p}).subschemeι)
  have : Mono twoStepSchemeInGrassmannian := Over.mono_of_mono_left _
  intro p q he
  apply (cancel_mono incidenceInclusion).mp
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg Prod.fst he).trans (Category.assoc _ _ _).symm)
  · apply (cancel_mono twoStepSchemeInGrassmannian).mp
    have hh := congrArg Prod.snd he
    change (p ≫ incidenceInclusion ≫ prod.snd) ≫ twoStepSchemeInGrassmannian =
      (q ≫ incidenceInclusion ≫ prod.snd) ≫ twoStepSchemeInGrassmannian at hh
    simpa only [Category.assoc] using hh

/-- Every actual flag determines a complex point of the reduced incidence scheme.
The map is an embedding for the coefficient chart topologies. -/
theorem flags_incidenceEmbedding (h₁ : MinusculeOrbit) (hp : MinusculeProjective)
    (hs : TwoStepStableModel) :
    ∃ f : Flags → Points incidenceScheme complexAlgebra,
      Topology.IsEmbedding f ∧
      ∀ L : Flags,
        firstPlane (f L ≫ ConvolutionBundleSpecs.firstProjection) = firstLine L.val.1 ∧
        secondPlane (f L ≫ terminalProjection) = secondSubspace L.val.2 := by
  classical
  obtain ⟨e, he⟩ := flags_coefficientComparison h₁ hp hs
  obtain ⟨s, hs'⟩ := LatticeModels.stableSchemePointComparison twoStepBasis twoStepRank shift
  let P (q : CoefficientFlags) : Points IncidenceAmbient complexAlgebra :=
    prod.lift q.val.1 (s.symm q.val.2)
  have p₁ (q : CoefficientFlags) : P q ≫ prod.fst = q.val.1 :=
    prod.lift_fst _ _
  have p₂ (q : CoefficientFlags) : P q ≫ prod.snd = s.symm q.val.2 :=
    prod.lift_snd _ _
  have hP (q : CoefficientFlags) : P q ∈ incidenceLocus := by
    have h₂ : (s.symm q.val.2 ≫ twoStepSchemeInGrassmannian) = q.val.2.val :=
      (hs' _).symm.trans (congrArg Subtype.val (s.apply_symm_apply q.val.2))
    change IncidenceCondition (firstPlane (P q ≫ prod.fst)) (secondPlane (P q ≫ prod.snd))
    have e₁ := congrArg firstPlane (p₁ q)
    have e₂ := (congrArg secondPlane (p₂ q)).trans
      (congrArg (grassmannianSubspace twoStepBasis twoStepRank) h₂)
    exact (congrArg₂ IncidenceCondition e₁ e₂).mpr q.property
  have lift_exists (q : CoefficientFlags) :
      ∃ r : Points incidenceScheme complexAlgebra, r ≫ incidenceInclusion = P q :=
    (LatticeModels.pointLocation_in_closure_iff incidenceLocus (P q)).mp
      (subset_closure ⟨P q, hP q, rfl⟩)
  choose lift hlift using lift_exists
  let j (q : CoefficientFlags) : ProjectivePoints × GrassmannianPoints twoStepBasis twoStepRank :=
    (q.val.1, q.val.2.val)
  have hcoords (q : CoefficientFlags) : incidenceCoordinates (lift q) = j q := by
    refine Prod.ext ?_ ?_
    · change lift q ≫ incidenceInclusion ≫ prod.fst = q.val.1
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ prod.fst) (hlift q)).trans (p₁ q))
    · change (lift q ≫ incidenceInclusion ≫ prod.snd) ≫ twoStepSchemeInGrassmannian = q.val.2.val
      rw [← Category.assoc (lift q), hlift q, p₂ q]
      exact (hs' _).symm.trans (congrArg Subtype.val (s.apply_symm_apply q.val.2))
  have hj : Topology.IsEmbedding j :=
    ((Topology.IsEmbedding.id (X := ProjectivePoints)).prodMap
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : TwoStepPoints →
          GrassmannianPoints twoStepBasis twoStepRank))).comp Topology.IsEmbedding.subtypeVal
  have hi : Topology.IsEmbedding incidenceCoordinates := ⟨⟨rfl⟩,
    incidenceCoordinates_injective⟩
  have hemb : Topology.IsEmbedding (lift ∘ e) := hi.of_comp_iff.mp
    (show Topology.IsEmbedding (incidenceCoordinates ∘ (lift ∘ e)) from by
      have hex : incidenceCoordinates ∘ (lift ∘ e) = j ∘ e := funext fun L ↦ hcoords (e L)
      rw [hex]
      exact hj.comp e.isEmbedding)
  refine ⟨lift ∘ e, hemb, fun L ↦ ?_⟩
  exact ⟨(congrArg firstPlane (congrArg Prod.fst (hcoords (e L)))).trans (he L).1,
    (congrArg (grassmannianSubspace twoStepBasis twoStepRank)
      (congrArg Prod.snd (hcoords (e L)))).trans (he L).2⟩

end FlagCoordinates


section Projectivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver pointsFunctor)
open LinearAlgebraicGroups.GrassmannianCharts (affineProbesEquiv hom_ext_on_affines)
open LinearAlgebraicGroups.Specs.ProjectiveSpaces (projectiveSpace coordinateProjectiveSpace tensorSpace)
open LinearAlgebraicGroups.Specs.PluckerEmbedding (Wedge)

open private binaryProduct_proper product_proper from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

private def isoOfAffinePoints {X Y : SchemeOver ℂ} (e : pointsFunctor X ≅ pointsFunctor Y) :
    X ≅ Y where
  hom := (affineProbesEquiv X Y).symm e.hom
  inv := (affineProbesEquiv Y X).symm e.inv
  hom_inv_id := by
    apply hom_ext_on_affines
    intro R p
    have hf (q : Points X R) :
        q ≫ (affineProbesEquiv X Y).symm e.hom = e.hom.app R q :=
      congrArg (fun f ↦ f.app R q) ((affineProbesEquiv X Y).apply_symm_apply e.hom)
    have hg (q : Points Y R) :
        q ≫ (affineProbesEquiv Y X).symm e.inv = e.inv.app R q :=
      congrArg (fun f ↦ f.app R q) ((affineProbesEquiv Y X).apply_symm_apply e.inv)
    rw [← Category.assoc, hf p, hg (e.hom.app R p), Category.comp_id]
    exact (e.app R).toEquiv.symm_apply_apply p
  inv_hom_id := by
    apply hom_ext_on_affines
    intro R p
    have hf (q : Points X R) :
        q ≫ (affineProbesEquiv X Y).symm e.hom = e.hom.app R q :=
      congrArg (fun f ↦ f.app R q) ((affineProbesEquiv X Y).apply_symm_apply e.hom)
    have hg (q : Points Y R) :
        q ≫ (affineProbesEquiv Y X).symm e.inv = e.inv.app R q :=
      congrArg (fun f ↦ f.app R q) ((affineProbesEquiv Y X).apply_symm_apply e.inv)
    rw [← Category.assoc, hg p, hf (e.inv.app R p), Category.comp_id]
    exact (e.app R).toEquiv.apply_symm_apply p

private theorem grassmannianEmbedding {U I : Type} [AddCommGroup U] [Module ℂ U]
    [Module.Finite ℂ U] [Fintype I] [DecidableEq I] (b : Module.Basis I ℂ U)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ U) :
    ∃ j : (grassmannianCharts b hd).scheme ⟶ projectiveSpace ℂ (Wedge ℂ d U),
      IsClosedImmersion j.left := by
  let b' := Module.finBasis ℂ U
  obtain ⟨P, _⟩ := LinearAlgebraicGroups.PluckerEmbedding.pluckerMorphismGeometry ℂ U _ b' d hd
  let e := isoOfAffinePoints ((grassmannianCharts b hd).affinePoints ≪≫ P.charts.affinePoints.symm)
  have : IsClosedImmersion P.morphism.left :=
    LinearAlgebraicGroups.PluckerEmbedding.pluckerClosedImmersion ℂ U _ b' d P
  exact ⟨e.hom ≫ P.morphism, inferInstanceAs (IsClosedImmersion (e.hom.left ≫ P.morphism.left))⟩

private theorem proper_of_embedding {X Y : SchemeOver ℂ} (j : X ⟶ Y)
    (hj : IsClosedImmersion j.left) (hY : IsProper Y.hom) : IsProper X.hom := by
  rw [← Over.w j]
  infer_instance

theorem incidenceTerminalProper : IsProper terminalProjection.left := by
  obtain ⟨j, hj⟩ := grassmannianEmbedding projectiveBasis projectiveRank
  have hp : IsProper projectiveScheme.hom := proper_of_embedding j hj
    (LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper ℂ _)
  have hp' : IsProper (prod.snd (X := projectiveScheme) (Y := twoStepScheme)).left := by
    rw [← Over.prodLeftIsoPullback_hom_snd]
    infer_instance
  have := incidenceInclusion_closed
  exact inferInstanceAs (IsProper
    (incidenceInclusion.left ≫ (prod.snd (X := projectiveScheme) (Y := twoStepScheme)).left))

theorem incidenceProjective :
    ∃ (n : ℕ) (j : incidenceScheme ⟶ coordinateProjectiveSpace ℂ (Fin (n + 1))),
      IsClosedImmersion j.left := by
  classical
  obtain ⟨j₀, hj₀⟩ := grassmannianEmbedding projectiveBasis projectiveRank
  obtain ⟨j₁, hj₁⟩ := grassmannianEmbedding twoStepBasis twoStepRank
  have hi : IsClosedImmersion twoStepSchemeInGrassmannian.left :=
    inferInstanceAs (IsClosedImmersion
      (reducedClosureIdeal (grassmannianCharts twoStepBasis twoStepRank).scheme
        {p | StablePlane twoStepBasis twoStepRank shift p}).subschemeι)
  let j₂ := twoStepSchemeInGrassmannian ≫ j₁
  have hj₂ : IsClosedImmersion j₂.left :=
    inferInstanceAs (IsClosedImmersion (twoStepSchemeInGrassmannian.left ≫ j₁.left))
  let W : Bool → Type
    | false => Wedge ℂ 1 V
    | true => Wedge ℂ 2 (V × V)
  let : ∀ b, AddCommGroup (W b) := fun b ↦ by cases b <;> dsimp [W] <;> infer_instance
  let : ∀ b, Module ℂ (W b) := fun b ↦ by cases b <;> dsimp [W] <;> infer_instance
  let : ∀ b, Module.Finite ℂ (W b) := fun b ↦ by cases b <;> dsimp [W] <;> infer_instance
  let Y (b : Bool) := projectiveSpace ℂ (W b)
  let f (b : Bool) : IncidenceAmbient ⟶ Y b := by
    cases b
    · change IncidenceAmbient ⟶ projectiveSpace ℂ (Wedge ℂ 1 V)
      exact prod.fst ≫ j₀
    · change IncidenceAmbient ⟶ projectiveSpace ℂ (Wedge ℂ 2 (V × V))
      exact prod.snd ≫ j₂
  let j := Pi.lift f
  have hm₀ : Mono j₀ := Over.mono_of_mono_left _
  have hm₂ : Mono j₂ := Over.mono_of_mono_left _
  have : Mono j := by
    constructor
    intro Z a b hab
    apply prod.hom_ext
    · apply (cancel_mono j₀).mp
      have h := congrArg (fun m ↦ m ≫ Pi.π Y false) hab
      change (a ≫ j) ≫ Pi.π Y false = (b ≫ j) ≫ Pi.π Y false at h
      have hj : j ≫ Pi.π Y false = prod.fst ≫ j₀ := Pi.lift_comp_π f false
      rw [Category.assoc, Category.assoc, hj] at h
      exact h
    · apply (cancel_mono j₂).mp
      have h := congrArg (fun m ↦ m ≫ Pi.π Y true) hab
      change (a ≫ j) ≫ Pi.π Y true = (b ≫ j) ≫ Pi.π Y true at h
      have hj : j ≫ Pi.π Y true = prod.snd ≫ j₂ := Pi.lift_comp_π f true
      rw [Category.assoc, Category.assoc, hj] at h
      exact h
  have hBase : IsProper (∏ᶜ Y).hom := product_proper Y (fun _ ↦
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper ℂ _)
  have hAmbient : IsProper IncidenceAmbient.hom := binaryProduct_proper _ _
    (proper_of_embedding j₀ hj₀ (LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper ℂ _))
    (proper_of_embedding j₂ hj₂ (LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper ℂ _))
  have : IsProper (j.left ≫ (∏ᶜ Y).hom) := Over.w j ▸ hAmbient
  have hj : IsClosedImmersion j.left := (IsClosedImmersion.iff_isProper_and_mono (f := j.left)).mpr
    ⟨IsProper.of_comp j.left (∏ᶜ Y).hom, inferInstance⟩
  let σ := LinearAlgebraicGroups.ProjectiveSpaces.segreMorphism (k := ℂ) W
  have hσ : IsClosedImmersion σ.left :=
    LinearAlgebraicGroups.ProjectiveSpaces.segreClosedImmersion W
  let E := tensorSpace (k := ℂ) W
  let d := Module.finrank ℂ E
  obtain ⟨ρ, _, hρ⟩ := LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceLineGeometry ℂ E
  obtain ⟨i, _⟩ := hρ.1 (Fin d) (Module.finBasis ℂ E)
  have hd : 0 < d := by
    have hW (b : Bool) : 0 < Module.finrank ℂ (W b) := by
      cases b
      · change 0 < Module.finrank ℂ (Wedge ℂ 1 V)
        simp [V]
      · change 0 < Module.finrank ℂ (Wedge ℂ 2 (V × V))
        simp [V, Module.finrank_prod]
        decide
    change 0 < Module.finrank ℂ E
    rw [Module.finrank_eq_card_basis (Basis.piTensorProduct fun b ↦ Module.finBasis ℂ (W b))]
    exact Fintype.card_pos_iff.mpr ⟨fun b ↦ ⟨0, hW b⟩⟩
  let n := d - 1
  have hn : n + 1 = d := by omega
  rw [← hn] at i
  have := incidenceInclusion_closed
  exact ⟨n, incidenceInclusion ≫ j ≫ σ ≫ i.inv, inferInstanceAs
    (IsClosedImmersion (incidenceInclusion.left ≫ j.left ≫ σ.left ≫ i.inv.left))⟩

end Projectivity


theorem bundleQuotient_surjective (R : TestAlgebra ℂ)
    (S : Submodule R (Coefficients R)) :
    Function.Surjective (bundleQuotient R S) := by
  rintro ⟨x, y⟩
  obtain ⟨y, rfl⟩ := S.mkQ_surjective y
  exact ⟨⟨(x.val, y), ⟨x.property, Submodule.mem_top⟩⟩, rfl⟩

section AffineIncidence

/-- The inverse-image plane associated to a submodule of S × (V/S). -/
def bundlePreimage (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R))
    (B : Submodule R (BundleFiber R S)) : Submodule R (Coefficients R × Coefficients R) :=
  (B.comap (bundleQuotient R S)).map (S.prod ⊤).subtype

private theorem mem_bundleQuotient_ker (R : TestAlgebra ℂ)
    (S : Submodule R (Coefficients R)) (x : (S.prod ⊤ : Submodule R _)) :
    x ∈ (bundleQuotient R S).ker ↔
      x.val ∈ (⊥ : Submodule R (Coefficients R)).prod S := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨(Submodule.mem_bot R).mpr (congrArg (fun v : BundleFiber R S ↦ v.1.val) h),
      (Submodule.Quotient.mk_eq_zero S).mp (congrArg Prod.snd h)⟩
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext (Subtype.ext ((Submodule.mem_bot R).mp h₁))
      ((Submodule.Quotient.mk_eq_zero S).mpr h₂)

private def submoduleIntervalEquiv {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (U D : Submodule R M) (hDU : D ≤ U) (f : U →ₗ[R] N)
    (hf : Function.Surjective f) (hker : f.ker = D.comap U.subtype) :
    Submodule R N ≃ {P : Submodule R M // D ≤ P ∧ P ≤ U} where
  toFun B := ⟨(B.comap f).map U.subtype, by
    constructor
    · intro x hx
      have hU := hDU hx
      refine ⟨⟨x, hU⟩, ?_, rfl⟩
      have hzero : f ⟨x, hU⟩ = 0 := LinearMap.mem_ker.mp (hker.symm ▸
        (show (⟨x, hU⟩ : U) ∈ D.comap U.subtype from hx))
      exact (show f ⟨x, hU⟩ ∈ B from hzero.symm ▸ B.zero_mem)
    · exact le_trans (Submodule.map_mono le_top) (by simp)⟩
  invFun P := (P.val.comap U.subtype).map f
  left_inv B := by
    change (((B.comap f).map U.subtype).comap U.subtype).map f = B
    rw [Submodule.comap_map_eq_of_injective U.subtype_injective,
      Submodule.map_comap_eq_of_surjective hf]
  right_inv P := by
    apply Subtype.ext
    change (((P.val.comap U.subtype).map f).comap f).map U.subtype = P.val
    have h : f.ker ≤ P.val.comap U.subtype :=
      hker.trans_le (Submodule.comap_mono P.property.1)
    rw [Submodule.comap_map_eq_self h, Submodule.map_comap_subtype,
      inf_eq_right.mpr P.property.2]

/-- Taking an inverse image identifies all submodules of the bundle fibre
with the interval between the shifted and unshifted first lattice. -/
def bundleSubmoduleEquiv (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R)) :
    Submodule R (BundleFiber R S) ≃
      {P : Submodule R (Coefficients R × Coefficients R) //
        (⊥ : Submodule R (Coefficients R)).prod S ≤ P ∧ P ≤ S.prod ⊤} :=
  @submoduleIntervalEquiv R (Coefficients R × Coefficients R) (BundleFiber R S)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (S.prod ⊤) ((⊥ : Submodule R (Coefficients R)).prod S)
    (fun _ hx ↦ ⟨((Submodule.mem_bot R).mp hx.1).symm ▸ S.zero_mem, Submodule.mem_top⟩)
    (bundleQuotient R S) (bundleQuotient_surjective R S)
    (SetLike.ext fun x ↦ mem_bundleQuotient_ker R S x)

open LinearMap in
private def splitSurjection {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    M ≃ₗ[R] f.ker × N := by
  classical
  let hs := f.exists_rightInverse_of_surjective (range_eq_top.mpr hf)
  let s := hs.choose
  have h (y : N) : f (s y) = y := DFunLike.congr_fun hs.choose_spec y
  let r := (LinearMap.id - s.comp f).codRestrict f.ker fun x ↦ by
    change f (x - s (f x)) = 0
    rw [map_sub, h, sub_self]
  refine LinearEquiv.ofLinearMap (f := r.prod f) (g := f.ker.subtype.coprod s) ?_ ?_
  · apply LinearMap.ext
    intro p
    change (⟨p.1.val + s p.2 - s (f (p.1.val + s p.2)), _⟩,
      f (p.1.val + s p.2)) = p
    have hp₁ : f p.1.val = 0 := p.1.property
    have hp : f (p.1.val + s p.2) = p.2 := by rw [map_add, h, hp₁, zero_add]
    have hleft : p.1.val + s p.2 - s (f (p.1.val + s p.2)) = p.1.val := by
      rw [hp, add_sub_cancel_right]
    exact Prod.ext (Subtype.ext hleft) hp
  · apply LinearMap.ext
    intro x
    change x - s (f x) + s (f x) = x
    exact sub_add_cancel _ _

private def nestedQuotientProd {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) (hPQ : P ≤ Q) [Module.Projective R (M ⧸ Q)] :
    (M ⧸ P) ≃ₗ[R] (Q ⧸ P.comap Q.subtype) × (M ⧸ Q) := by
  let f := P.mapQ Q LinearMap.id hPQ
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
    exact ⟨P.mkQ x, rfl⟩
  have hk : f.ker = Q.map P.mkQ := by
    simp [f, Submodule.ker_mapQ]
  exact splitSurjection f hs ≪≫ₗ
    LinearEquiv.prodCongr
      (LinearEquiv.ofEq _ _ hk ≪≫ₗ (relativeQuotient_incl P Q).symm)
      (LinearEquiv.refl _ _)

private def quotientOfComapSurj {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (B : Submodule R N) :
    (M ⧸ B.comap f) ≃ₗ[R] (N ⧸ B) := by
  let F := B.mkQ.comp f
  have hker : F.ker = B.comap f := by rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  exact (B.comap f).quotEquivOfEq _ hker.symm ≪≫ₗ
    F.quotKerEquivOfSurjective (B.mkQ_surjective.comp hf)

private abbrev QuotientBy (R M : Type*)
    [Ring R] [AddCommGroup M] [Module R M] (P : Submodule R M) :=
  @HasQuotient.Quotient _ _ (@Submodule.hasQuotient R M inferInstance inferInstance inferInstance) P

private def quotientProdTop {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (S : Submodule R M) :
    QuotientBy R (M × N) (S.prod (⊤ : Submodule R N)) ≃ₗ[R] QuotientBy R M S :=
  (S.prod (⊤ : Submodule R N)).quotEquivOfEq _ (Submodule.comap_fst (M₂ := N) S).symm ≪≫ₗ
    quotientOfComapSurj (LinearMap.fst R M N) (fun x ↦ ⟨(x, 0), rfl⟩) S

private def upperQuotient (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R)) :
    QuotientBy R (Coefficients R × Coefficients R) (S.prod ⊤) ≃ₗ[R]
      QuotientBy R (Coefficients R) S :=
  @quotientProdTop R (Coefficients R) (Coefficients R)
    inferInstance inferInstance inferInstance inferInstance inferInstance S

set_option backward.isDefEq.respectTransparency false in
/-- The affine quotient of the ambient coefficients by an inverse-image plane
splits as the quotient by the corresponding line and the first quotient. -/
def bundlePreimageQuotient (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R))
    [Module.Projective R (Coefficients R ⧸ S)] (B : Submodule R (BundleFiber R S)) :
    QuotientBy R (Coefficients R × Coefficients R) (bundlePreimage R S B) ≃ₗ[R]
      QuotientBy R (BundleFiber R S) B × QuotientBy R (Coefficients R) S := by
  let U : Submodule R (Coefficients R × Coefficients R) := S.prod ⊤
  let P := bundlePreimage R S B
  have hPU : P ≤ U := ((bundleSubmoduleEquiv R S) B).property.2
  let e := upperQuotient R S
  let : Module.Projective R (QuotientBy R (Coefficients R × Coefficients R) U) :=
    Module.Projective.of_equiv e.symm
  have he : P.comap U.subtype = B.comap (bundleQuotient R S) :=
    Submodule.comap_map_eq_of_injective U.subtype_injective _
  let e' := (P.comap U.subtype).quotEquivOfEq _ he ≪≫ₗ
    @quotientOfComapSurj R (U : Type) (BundleFiber R S)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (bundleQuotient R S) (bundleQuotient_surjective R S) B
  exact nestedQuotientProd P U hPU ≪≫ₗ LinearEquiv.prodCongr e' e

/-- The affine incidence condition using Grassmannian points with locally
free rank-two quotient. -/
abbrev AffineIncidencePlanes (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R)) :=
  {P : Module.Grassmannian R (Coefficients R × Coefficients R) 2 //
    (⊥ : Submodule R (Coefficients R)).prod S ≤ P.toSubmodule ∧ P.toSubmodule ≤ S.prod ⊤}

set_option backward.isDefEq.respectTransparency false in
private def bundlePlane (R : TestAlgebra ℂ)
    (S : Module.Grassmannian R (Coefficients R) 1)
    (B : Module.Grassmannian R (BundleFiber R S.toSubmodule) 1) :
    AffineIncidencePlanes R S.toSubmodule := by
  let e := bundlePreimageQuotient R S.toSubmodule B.toSubmodule
  let P : Module.Grassmannian R (Coefficients R × Coefficients R) 2 :=
    { toSubmodule := bundlePreimage R S.toSubmodule B.toSubmodule
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq := by
        intro p
        have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) p
        rw [Module.rankAtStalk_prod, Pi.add_apply] at hr
        exact hr.trans (congrArg₂ (· + ·) (B.rankAtStalk_eq p) (S.rankAtStalk_eq p)) }
  exact ⟨P, ((bundleSubmoduleEquiv R S.toSubmodule) B.toSubmodule).property⟩

set_option backward.isDefEq.respectTransparency false in
private def incidenceLine (R : TestAlgebra ℂ)
    (S : Module.Grassmannian R (Coefficients R) 1) (P : AffineIncidencePlanes R S.toSubmodule) :
    Module.Grassmannian R (BundleFiber R S.toSubmodule) 1 := by
  let F := bundleSubmoduleEquiv R S.toSubmodule
  let I : {Q : Submodule R (Coefficients R × Coefficients R) //
      (⊥ : Submodule R (Coefficients R)).prod S.toSubmodule ≤ Q ∧ Q ≤ S.toSubmodule.prod ⊤} :=
    ⟨P.val.toSubmodule, P.property⟩
  let B := F.symm I
  have hB : bundlePreimage R S.toSubmodule B = P.val.toSubmodule :=
    congrArg Subtype.val (F.apply_symm_apply I)
  let e := (P.val.toSubmodule.quotEquivOfEq _ hB.symm) ≪≫ₗ
    bundlePreimageQuotient R S.toSubmodule B
  let V₁ := QuotientBy R (BundleFiber R S.toSubmodule) B
  let V₂ := QuotientBy R (Coefficients R) S.toSubmodule
  let : Module.Finite R (QuotientBy R _ P.val.toSubmodule) := P.val.finite_quotient
  let : Module.Projective R (QuotientBy R _ P.val.toSubmodule) := P.val.projective_quotient
  let : Module.Finite R (V₁ × V₂) := Module.Finite.equiv e
  let : Module.Projective R (V₁ × V₂) := Module.Projective.of_equiv e
  let : Module.Finite R V₁ := Module.Finite.of_surjective (LinearMap.fst R V₁ V₂)
    (fun x ↦ ⟨(x, 0), rfl⟩)
  let : Module.Projective R V₁ := Module.Projective.of_split
    (LinearMap.inl R V₁ V₂) (LinearMap.fst R V₁ V₂) (LinearMap.ext fun _ ↦ rfl)
  refine ⟨B, inferInstanceAs (Module.Finite R V₁), inferInstanceAs (Module.Projective R V₁), ?_⟩
  intro p
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  have hprod := congrFun (Module.rankAtStalk_prod (R := R) V₁ V₂) p
  have hP := P.val.rankAtStalk_eq p
  have hS := S.rankAtStalk_eq p
  have hsum : Module.rankAtStalk (R := R) V₁ p + 1 = 1 + 1 :=
    (congrArg₂ (· + ·) rfl hS.symm).trans (hprod.symm.trans (hr.symm.trans hP))
  exact Nat.add_right_cancel hsum

set_option backward.isDefEq.respectTransparency false in
/-- Affine planes satisfying the incidence constraints correspond to the
lines in the coefficient quotient. This holds on arbitrary test rings. -/
def affineBundlePlaneEquiv (R : TestAlgebra ℂ) (S : Module.Grassmannian R (Coefficients R) 1) :
    Module.Grassmannian R (BundleFiber R S.toSubmodule) 1 ≃
      AffineIncidencePlanes R S.toSubmodule where
  toFun := bundlePlane R S
  invFun := incidenceLine R S
  left_inv B := Module.Grassmannian.ext
    ((bundleSubmoduleEquiv R S.toSubmodule).symm_apply_apply B.toSubmodule)
  right_inv P := Subtype.ext (Module.Grassmannian.ext (congrArg Subtype.val
    ((bundleSubmoduleEquiv R S.toSubmodule).apply_symm_apply ⟨P.val.toSubmodule, P.property⟩)))

theorem affineBundlePlaneEquiv_submodule (R : TestAlgebra ℂ)
    (S : Module.Grassmannian R (Coefficients R) 1)
    (B : Module.Grassmannian R (BundleFiber R S.toSubmodule) 1) :
    ((affineBundlePlaneEquiv R S) B).val.toSubmodule =
      bundlePreimage R S.toSubmodule B.toSubmodule := rfl


end AffineIncidence

section SchemeIncidence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver mapPoints pointsFunctor)
open LinearAlgebraicGroups.Specs.GrassmannianCharts (Plane planeFunctor Family ChartSystem)
open LinearAlgebraicGroups.GrassmannianCharts (familyEquiv familyEquiv_apply)
open scoped TensorProduct

open private tensorExtensionOfHom planeMap_eq_span_of_hom from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts

private abbrev ProductCoefficients (R : TestAlgebra ℂ) := Coefficients R × Coefficients R

private abbrev coefficientPairs (R : TestAlgebra ℂ) :
    (R ⊗[ℂ] (V × V)) ≃ₗ[R] ProductCoefficients R :=
  TensorProduct.prodRight ℂ R R V V

private theorem coefficientPairs_extension {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (x : R ⊗[ℂ] (V × V)) :
    coefficientPairs T (tensorExtensionOfHom a x) =
      Prod.map (coefficientChange a) (coefficientChange a) (coefficientPairs R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => simp [tensorExtensionOfHom, coefficientChange]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact Prod.ext ((coefficientChange a).map_add _ _).symm
      ((coefficientChange a).map_add _ _).symm

private theorem plane_pair_baseChange {R T : TestAlgebra ℂ} {d : ℕ} (a : R ⟶ T)
    (P : Plane ℂ (V × V) d R) :
    ((Module.Grassmannian.map a.hom P).toSubmodule).map (coefficientPairs T).toLinearMap =
      Submodule.span T (Prod.map (coefficientChange a) (coefficientChange a) ''
        (P.toSubmodule.map (coefficientPairs R).toLinearMap : Set (ProductCoefficients R))) := by
  rw [planeMap_eq_span_of_hom, Submodule.map_span]
  apply congrArg (Submodule.span T)
  rw [Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  funext x
  exact coefficientPairs_extension a x

private theorem span_pair_prod {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (S P : Submodule R (Coefficients R)) :
    Submodule.span T
      (Prod.map (coefficientChange a) (coefficientChange a) ''
        (S.prod P : Set (ProductCoefficients R))) =
      (Submodule.span T (coefficientChange a '' (S : Set (Coefficients R)))).prod
        (Submodule.span T (coefficientChange a '' (P : Set (Coefficients R)))) := by
  rw [← Submodule.span_prod_eq T
    (show 0 ∈ coefficientChange a '' (S : Set (Coefficients R)) from ⟨0, S.zero_mem, map_zero _⟩)
    (show 0 ∈ coefficientChange a '' (P : Set (Coefficients R)) from ⟨0, P.zero_mem, map_zero _⟩)]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
    exact ⟨⟨x,hx,rfl⟩, ⟨y,hy,rfl⟩⟩
  · rintro ⟨⟨x,hx,hex⟩, ⟨y,hy,hey⟩⟩
    exact ⟨(x,y), ⟨hx,hy⟩, Prod.ext hex hey⟩

private theorem span_coefficient_top {R T : TestAlgebra ℂ} (a : R ⟶ T) :
    Submodule.span T (coefficientChange a '' (⊤ : Submodule R (Coefficients R))) = ⊤ := by
  let S := Submodule.span T (coefficientChange a '' (⊤ : Submodule R (Coefficients R)))
  have hs (x : Coefficients T) : x ∈ S := by
    induction x using TensorProduct.inductionOn with
    | tmul r v =>
      have hv : (1 : T) ⊗ₜ[ℂ] v ∈ S :=
        Submodule.subset_span ⟨(1 : R) ⊗ₜ[ℂ] v, Submodule.mem_top, by
          simp [coefficientChange]⟩
      have hh : r • ((1 : T) ⊗ₜ[ℂ] v) ∈ S := S.smul_mem r hv
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hh
    | add x y hx hy => exact S.add_mem hx hy
  exact top_unique (fun x _ ↦ hs x)

private theorem span_coefficient_bot {R T : TestAlgebra ℂ} (a : R ⟶ T) :
    Submodule.span T (coefficientChange a '' (⊥ : Submodule R (Coefficients R))) = ⊥ := by
  simp

private def planeOfSurjection {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (d : ℕ)
    (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) N p = d) :
    Module.Grassmannian R M d :=
  let e := f.quotKerEquivOfSurjective hf
  { toSubmodule := f.ker
    finite_quotient := Module.Finite.equiv e.symm
    projective_quotient := Module.Projective.of_equiv e.symm
    rankAtStalk_eq := fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans (hd p) }

private def shiftedFirstPlane (R : TestAlgebra ℂ) (S : Plane ℂ V 1 R) :
    Plane ℂ (V × V) 1 R := by
  let A := Coefficients R
  let d := (LinearMap.fst R A A).prod (S.toSubmodule.mkQ.comp (LinearMap.snd R A A))
  have hsur : Function.Surjective d := by
    rintro ⟨u, v⟩
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective v
    exact ⟨(u,v), rfl⟩
  refine planeOfSurjection (d.comp (coefficientPairs R).toLinearMap)
    (hsur.comp (coefficientPairs R).surjective) _ ?_
  intro p
  change Module.rankAtStalk (R := R)
    (A × QuotientBy R A S.toSubmodule) p = _
  have hA : Module.rankAtStalk (R := R) A p = 2 := by
    let : Nontrivial R := p.nontrivial
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis
      ((Pi.basisFun ℂ (Fin 2)).baseChange R)]
    simp
  change Module.rankAtStalk (R := R) (A × QuotientBy R A S.toSubmodule) p =
    Module.finrank ℂ (V × V) - 1
  rw [Module.rankAtStalk_prod, Pi.add_apply, hA, S.rankAtStalk_eq p]
  simp [V, Module.finrank_prod]

private def unshiftedFirstPlane (R : TestAlgebra ℂ) (S : Plane ℂ V 1 R) :
    Plane ℂ (V × V) 3 R := by
  let A := Coefficients R
  let d := S.toSubmodule.mkQ.comp (LinearMap.fst R A A)
  have hsur : Function.Surjective d := S.toSubmodule.mkQ_surjective.comp (fun x ↦ ⟨(x,0), rfl⟩)
  refine planeOfSurjection (d.comp (coefficientPairs R).toLinearMap)
    (hsur.comp (coefficientPairs R).surjective) _ ?_
  intro p
  change Module.rankAtStalk (R := R) (QuotientBy R A S.toSubmodule) p =
    Module.finrank ℂ (V × V) - 3
  rw [S.rankAtStalk_eq p]
  simp [V, Module.finrank_prod]

private theorem shiftedFirst_submodule (R : TestAlgebra ℂ) (S : Plane ℂ V 1 R) :
    (shiftedFirstPlane R S).toSubmodule.map (coefficientPairs R).toLinearMap =
      (⊥ : Submodule R (Coefficients R)).prod S.toSubmodule := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change ((coefficientPairs R u).1, S.toSubmodule.mkQ (coefficientPairs R u).2) = 0 at hu
    exact ⟨(Submodule.mem_bot R).mpr (congrArg Prod.fst hu),
      (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp (congrArg Prod.snd hu)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨(coefficientPairs R).symm x, ?_, (coefficientPairs R).apply_symm_apply x⟩
    change ((coefficientPairs R ((coefficientPairs R).symm x)).1,
      S.toSubmodule.mkQ (coefficientPairs R ((coefficientPairs R).symm x)).2) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext ((Submodule.mem_bot R).mp h₁) ((Submodule.Quotient.mk_eq_zero _).mpr h₂)

private theorem unshiftedFirst_submodule (R : TestAlgebra ℂ) (S : Plane ℂ V 1 R) :
    (unshiftedFirstPlane R S).toSubmodule.map (coefficientPairs R).toLinearMap =
      S.toSubmodule.prod ⊤ := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change S.toSubmodule.mkQ (coefficientPairs R u).1 = 0 at hu
    exact ⟨(Submodule.Quotient.mk_eq_zero _).mp hu, Submodule.mem_top⟩
  · rintro ⟨h₁, _⟩
    refine ⟨(coefficientPairs R).symm x, ?_, (coefficientPairs R).apply_symm_apply x⟩
    change S.toSubmodule.mkQ (coefficientPairs R ((coefficientPairs R).symm x)).1 = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr h₁

private theorem shiftedFirst_natural {R T : TestAlgebra ℂ} (a : R ⟶ T) (S : Plane ℂ V 1 R) :
    Module.Grassmannian.map a.hom (shiftedFirstPlane R S) =
      shiftedFirstPlane T (Module.Grassmannian.map a.hom S) := by
  apply Module.Grassmannian.ext
  apply Submodule.map_injective_of_injective (coefficientPairs T).injective
  rw [plane_pair_baseChange, shiftedFirst_submodule, span_pair_prod, span_coefficient_bot,
    shiftedFirst_submodule, planeMap_eq_span_of_hom]
  rfl

private theorem unshiftedFirst_natural {R T : TestAlgebra ℂ} (a : R ⟶ T) (S : Plane ℂ V 1 R) :
    Module.Grassmannian.map a.hom (unshiftedFirstPlane R S) =
      unshiftedFirstPlane T (Module.Grassmannian.map a.hom S) := by
  apply Module.Grassmannian.ext
  apply Submodule.map_injective_of_injective (coefficientPairs T).injective
  rw [plane_pair_baseChange, unshiftedFirst_submodule, span_pair_prod, span_coefficient_top,
    unshiftedFirst_submodule, planeMap_eq_span_of_hom]
  rfl

private abbrev firstChartSystem := grassmannianCharts projectiveBasis projectiveRank
private abbrev secondChartSystem := grassmannianCharts twoStepBasis twoStepRank

private theorem firstPlane_natural {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (p : Points projectiveScheme R) :
    firstChartSystem.affinePoints.hom.app T (mapPoints a p) =
      Module.Grassmannian.map a.hom (firstChartSystem.affinePoints.hom.app R p) := by
  have h := congrArg (fun f : Points projectiveScheme R ⟶ Plane ℂ V 1 T ↦ f p)
    (firstChartSystem.affinePoints.hom.naturality a)
  exact h

private def firstPlaneMorphism {d : ℕ} (C : ChartSystem (k := ℂ) (V := V × V) twoStepBasis d)
    (f : ∀ R : TestAlgebra ℂ, Plane ℂ V 1 R → Plane ℂ (V × V) d R)
    (hf : ∀ {R T : TestAlgebra ℂ} (a : R ⟶ T) (L : Plane ℂ V 1 R),
      Module.Grassmannian.map a.hom (f R L) = f T (Module.Grassmannian.map a.hom L)) :
    projectiveScheme ⟶ C.scheme :=
  let β : Family ℂ (V × V) d projectiveScheme :=
    { app := fun R ↦ ↾fun p ↦ f R (firstChartSystem.affinePoints.hom.app R p)
      naturality := by
        intro R T a
        apply ConcreteCategory.hom_ext
        intro p
        exact (congrArg (f T) (firstPlane_natural a p)).trans (hf a _).symm }
  (familyEquiv C.affinePoints projectiveScheme).symm β

private theorem firstPlaneMorphism_apply {d : ℕ} (C : ChartSystem (k := ℂ) (V := V × V) twoStepBasis d)
    (f : ∀ R : TestAlgebra ℂ, Plane ℂ V 1 R → Plane ℂ (V × V) d R)
    (hf : ∀ {R T : TestAlgebra ℂ} (a : R ⟶ T) (L : Plane ℂ V 1 R),
      Module.Grassmannian.map a.hom (f R L) = f T (Module.Grassmannian.map a.hom L))
    (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :
    C.affinePoints.hom.app R (p ≫ firstPlaneMorphism C f hf) =
      f R (firstChartSystem.affinePoints.hom.app R p) := by
  unfold firstPlaneMorphism
  rw [← familyEquiv_apply, Equiv.apply_symm_apply]
  rfl

private abbrev flagRanks (i : Fin 3) : ℕ := i.val + 1
private theorem flagRankBound (i : Fin 3) : flagRanks i ≤ Module.finrank ℂ (V × V) := by
  have hi := i.isLt
  simp [V, Module.finrank_prod, flagRanks]
  omega

private abbrev flagCharts (i : Fin 3) : ChartSystem (k := ℂ) (V := V × V) twoStepBasis (flagRanks i) :=
  grassmannianCharts twoStepBasis (flagRankBound i)

private abbrev WGrassmannian := secondChartSystem.scheme
private abbrev PlaneProduct : SchemeOver ℂ := projectiveScheme ⨯ WGrassmannian

private def planeProductMap : IncidenceAmbient ⟶ PlaneProduct :=
  Limits.prod.map (𝟙 projectiveScheme) twoStepSchemeInGrassmannian

private theorem planeProductMap_fst :
    planeProductMap ≫ (prod.fst : PlaneProduct ⟶ projectiveScheme) = prod.fst := by
  simp [planeProductMap]

private theorem planeProductMap_snd :
    planeProductMap ≫ (prod.snd : PlaneProduct ⟶ WGrassmannian) =
      prod.snd ≫ twoStepSchemeInGrassmannian := by
  simp [planeProductMap]

private theorem planeProductMap_closed : IsClosedImmersion planeProductMap.left := by
  have h : IsPullback (prod.snd : IncidenceAmbient ⟶ twoStepScheme) planeProductMap
      twoStepSchemeInGrassmannian (prod.snd : PlaneProduct ⟶ WGrassmannian) := by
    refine IsPullback.mk' planeProductMap_snd.symm ?_ ?_
    · intro T u v hu hv
      apply prod.hom_ext
      · simpa only [Category.assoc, planeProductMap_fst] using
          congrArg (· ≫ (prod.fst : PlaneProduct ⟶ projectiveScheme)) hv
      · exact hu
    · intro T a b hab
      refine ⟨prod.lift (b ≫ prod.fst) a, prod.lift_snd _ _, ?_⟩
      apply prod.hom_ext
      · simp only [Category.assoc, planeProductMap_fst, prod.lift_fst]
      · rw [Category.assoc, planeProductMap_snd, ← Category.assoc, prod.lift_snd]
        exact hab
  exact MorphismProperty.of_isPullback (h.map (Over.forget (Spec (CommRingCat.of ℂ))))
    (inferInstanceAs (IsClosedImmersion
      (reducedClosureIdeal WGrassmannian {p | StablePlane twoStepBasis twoStepRank shift p}).subschemeι))

private def incidenceToProduct : incidenceScheme ⟶ PlaneProduct :=
  incidenceInclusion ≫ planeProductMap

private theorem incidenceToProduct_closed : IsClosedImmersion incidenceToProduct.left := by
  have := incidenceInclusion_closed
  have := planeProductMap_closed
  exact inferInstanceAs (IsClosedImmersion (incidenceInclusion.left ≫ planeProductMap.left))

private theorem incidenceToProduct_fst :
    incidenceToProduct ≫ (prod.fst : PlaneProduct ⟶ projectiveScheme) =
      ConvolutionBundleSpecs.firstProjection := by
  rw [incidenceToProduct, Category.assoc, planeProductMap_fst]
  rfl

private theorem incidenceToProduct_snd :
    incidenceToProduct ≫ (prod.snd : PlaneProduct ⟶ WGrassmannian) =
      terminalProjection ≫ twoStepSchemeInGrassmannian := by
  rw [incidenceToProduct, Category.assoc, planeProductMap_snd, ← Category.assoc]
  rfl

open LinearAlgebraicGroups.Specs.FlagIncidence (GrassmannianProduct productPlanes)
open LinearAlgebraicGroups.FlagIncidence (flagScheme flagInclusion factorsThroughFlag_iff)
open private productPlanes_naturality baseChange_nested from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagIncidence

private abbrev OrdinaryFlags := flagScheme twoStepBasis flagRanks flagCharts
private abbrev ordinaryInclusion := flagInclusion twoStepBasis flagRanks flagCharts

private def incidenceFlagLower : PlaneProduct ⟶ (flagCharts 0).scheme :=
  (prod.fst : PlaneProduct ⟶ projectiveScheme) ≫
    firstPlaneMorphism (flagCharts 0) shiftedFirstPlane shiftedFirst_natural

private def incidenceFlagUpper : PlaneProduct ⟶ (flagCharts 2).scheme :=
  (prod.fst : PlaneProduct ⟶ projectiveScheme) ≫
    firstPlaneMorphism (flagCharts 2) unshiftedFirstPlane unshiftedFirst_natural

private def incidenceFlagComponent : ∀ i : Fin 3, PlaneProduct ⟶ (flagCharts i).scheme :=
  Fin.cases incidenceFlagLower (Fin.cases prod.snd
    (Fin.cases incidenceFlagUpper (fun impossible ↦ Fin.elim0 impossible)))

private def incidenceFlagMap : PlaneProduct ⟶ GrassmannianProduct flagRanks twoStepBasis flagCharts :=
  Pi.lift incidenceFlagComponent

private theorem incidenceFlagComponent_zero :
    incidenceFlagComponent 0 = incidenceFlagLower := Fin.cases_zero

private theorem incidenceFlagComponent_one :
    incidenceFlagComponent 1 = prod.snd := rfl

private theorem incidenceFlagComponent_two :
    incidenceFlagComponent 2 = incidenceFlagUpper := rfl

private theorem incidenceFlagProjection {R : TestAlgebra ℂ} (p : Points PlaneProduct R)
    (i : Fin 3) :
    productPlanes flagRanks twoStepBasis flagCharts (p ≫ incidenceFlagMap) i =
      (flagCharts i).affinePoints.hom.app R (p ≫ incidenceFlagComponent i) :=
  congrArg (fun x : Points (flagCharts i).scheme R ↦ (flagCharts i).affinePoints.hom.app R x)
    ((Category.assoc p incidenceFlagMap (Pi.π (fun j ↦ (flagCharts j).scheme) i)).trans
      (congrArg (p ≫ ·) (Pi.lift_comp_π (f := fun j ↦ (flagCharts j).scheme) incidenceFlagComponent i)))

private def flagSubspace (R : TestAlgebra ℂ) (p : Points PlaneProduct R) (i : Fin 3) :
    Submodule R (ProductCoefficients R) :=
  (productPlanes flagRanks twoStepBasis flagCharts (p ≫ incidenceFlagMap) i).toSubmodule.map
    (coefficientPairs R).toLinearMap

private theorem flagSubspace_eq (R : TestAlgebra ℂ) (p : Points PlaneProduct R) (i : Fin 3) :
    flagSubspace R p i =
      ((flagCharts i).affinePoints.hom.app R (p ≫ incidenceFlagComponent i)).toSubmodule.map
        (coefficientPairs R).toLinearMap :=
  congrArg (fun L : Plane ℂ (V × V) (flagRanks i) R ↦
    L.toSubmodule.map (coefficientPairs R).toLinearMap) (incidenceFlagProjection p i)

private abbrev productFirst (R : TestAlgebra ℂ) (p : Points PlaneProduct R) :
    Plane ℂ V 1 R :=
  firstChartSystem.affinePoints.hom.app R (p ≫ (prod.fst : PlaneProduct ⟶ projectiveScheme))

private theorem flagSubspace_zero (R : TestAlgebra ℂ) (p : Points PlaneProduct R) :
    flagSubspace R p 0 = (⊥ : Submodule R (Coefficients R)).prod (productFirst R p).toSubmodule := by
  rw [flagSubspace_eq R p 0, incidenceFlagComponent_zero, incidenceFlagLower, ← Category.assoc,
    firstPlaneMorphism_apply]
  exact shiftedFirst_submodule R (productFirst R p)

private theorem flagSubspace_one (R : TestAlgebra ℂ) (p : Points PlaneProduct R) :
    flagSubspace R p 1 =
      (secondChartSystem.affinePoints.hom.app R (p ≫ prod.snd)).toSubmodule.map
        (coefficientPairs R).toLinearMap :=
  (flagSubspace_eq R p 1).trans (congrArg (fun x : PlaneProduct ⟶ (flagCharts 1).scheme ↦
      ((flagCharts 1).affinePoints.hom.app R (p ≫ x)).toSubmodule.map
        (coefficientPairs R).toLinearMap) incidenceFlagComponent_one)

private theorem flagSubspace_two (R : TestAlgebra ℂ) (p : Points PlaneProduct R) :
    flagSubspace R p 2 = (productFirst R p).toSubmodule.prod ⊤ := by
  rw [flagSubspace_eq R p 2, incidenceFlagComponent_two, incidenceFlagUpper, ← Category.assoc,
    firstPlaneMorphism_apply]
  exact unshiftedFirst_submodule R (productFirst R p)

private def rawIncidence : SchemeOver ℂ := pullback incidenceFlagMap ordinaryInclusion

private def rawInclusion : rawIncidence ⟶ PlaneProduct :=
  pullback.fst incidenceFlagMap ordinaryInclusion

private theorem rawInclusion_closed : IsClosedImmersion rawInclusion.left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback incidenceFlagMap ordinaryInclusion).map
      (Over.forget (Spec (CommRingCat.of ℂ)))).flip
    (inferInstanceAs (IsClosedImmersion
      (flagInclusion twoStepBasis flagRanks flagCharts).left))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem rawIncidence_affine (R : TestAlgebra ℂ) (p : Points PlaneProduct R) :
    let S := (firstChartSystem.affinePoints.hom.app R (p ≫ prod.fst)).toSubmodule
    let P := (secondChartSystem.affinePoints.hom.app R (p ≫ prod.snd)).toSubmodule.map
      (coefficientPairs R).toLinearMap
    (∃ q : Points rawIncidence R, q ≫ rawInclusion = p) ↔
      (⊥ : Submodule R (Coefficients R)).prod S ≤ P ∧ P ≤ S.prod ⊤ := by
  dsimp only
  let o := p ≫ incidenceFlagMap
  have fac : (∃ q : Points rawIncidence R, q ≫ rawInclusion = p) ↔
      ∃ f : Points OrdinaryFlags R, f ≫ ordinaryInclusion = o := by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q ≫ pullback.snd incidenceFlagMap ordinaryInclusion, ?_⟩
      exact (Category.assoc _ _ _).trans
        ((congrArg (q ≫ ·) (pullback.condition (f := incidenceFlagMap)
          (g := ordinaryInclusion)).symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ incidenceFlagMap) hq)))
    · rintro ⟨f, hf⟩
      exact ⟨pullback.lift p f hf.symm, pullback.lift_fst _ _ _⟩
  rw [fac, factorsThroughFlag_iff]
  have hf : (∀ (A : TestAlgebra ℂ) (a : Points _ A) ⦃i j : Fin 3⦄, i < j →
      (productPlanes flagRanks twoStepBasis flagCharts (a ≫ o) i).toSubmodule ≤
        (productPlanes flagRanks twoStepBasis flagCharts (a ≫ o) j).toSubmodule) ↔
      (∀ ⦃i j : Fin 3⦄, i < j →
        (productPlanes flagRanks twoStepBasis flagCharts o i).toSubmodule ≤
          (productPlanes flagRanks twoStepBasis flagCharts o j).toSubmodule) := by
    constructor
    · intro h i j hij
      simpa only [Category.id_comp] using h R (𝟙 _) hij
    · intro h A a i j hij
      let f := (algSpec.fullyFaithful (R := CommRingCat.of ℂ)).preimage a
      have he : (LinearAlgebraicGroups.testSpec ℂ).map f = a :=
        (algSpec.fullyFaithful (R := CommRingCat.of ℂ)).map_preimage a
      rw [← he]
      change (productPlanes flagRanks twoStepBasis flagCharts (mapPoints f.unop o) i).toSubmodule ≤
        (productPlanes flagRanks twoStepBasis flagCharts (mapPoints f.unop o) j).toSubmodule
      rw [productPlanes_naturality, productPlanes_naturality]
      exact baseChange_nested f.unop _ _ (h hij)
  rw [hf]
  have ha := flagSubspace_zero R p
  have hb := flagSubspace_one R p
  have hc := flagSubspace_two R p
  let E := coefficientPairs R
  have aux (i j : Fin 3) :
      (productPlanes flagRanks twoStepBasis flagCharts o i).toSubmodule ≤
        (productPlanes flagRanks twoStepBasis flagCharts o j).toSubmodule ↔
      ((productPlanes flagRanks twoStepBasis flagCharts o i).toSubmodule.map E.toLinearMap) ≤
        ((productPlanes flagRanks twoStepBasis flagCharts o j).toSubmodule.map E.toLinearMap) :=
    (Submodule.map_le_map_iff_of_injective E.injective _ _).symm
  constructor
  · intro h
    constructor
    · have t := (aux 0 1).mp (h (by decide))
      exact (congrArg₂ (· ≤ ·) ha hb).mp t
    · have t := (aux 1 2).mp (h (by decide))
      exact (congrArg₂ (· ≤ ·) hb hc).mp t
  · intro h i j hij
    apply (aux i j).mpr
    have hCases : ∀ a b : Fin 3, a < b →
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) := by decide
    rcases hCases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (congrArg₂ (· ≤ ·) ha hb).mpr h.1
    · exact (congrArg₂ (· ≤ ·) ha hc).mpr (h.1.trans h.2)
    · exact (congrArg₂ (· ≤ ·) hb hc).mpr h.2


open TopologicalSpace Scheme.IdealSheafData
open private reduced_ker_eq from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels

private theorem liftReducedRange {X Y Z : SchemeOver ℂ} (p : X ⟶ Z) (j : Y ⟶ Z)
    [IsReduced X.left] [IsClosedImmersion j.left] (h : Set.range p.left ⊆ Set.range j.left) :
    ∃ q : X ⟶ Y, q ≫ j = p := by
  have hk : j.left.ker ≤ p.left.ker := by
    rw [reduced_ker_eq p.left, ← le_support_iff_le_vanishingIdeal]
    apply Closeds.closure_le.mpr
    rw [Scheme.Hom.support_ker, j.left.isClosedEmbedding.isClosed_range.closure_eq]
    exact h
  let q := IsClosedImmersion.lift j.left p.left hk
  have hq : q ≫ j.left = p.left := IsClosedImmersion.lift_fac _ _ _
  exact ⟨Over.homMk q (by rw [← Over.w j, ← Category.assoc, hq, Over.w]), Over.OverMorphism.ext hq⟩

private theorem liftPoint_iff_range {X Y : SchemeOver ℂ} (j : X ⟶ Y) [IsClosedImmersion j.left]
    (p : Points Y complexAlgebra) :
    (∃ q : Points X complexAlgebra, q ≫ j = p) ↔ pointLocation p ∈ Set.range j.left := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨pointLocation q, rfl⟩
  · intro h
    have : IsReduced ((LinearAlgebraicGroups.testSpec ℂ).obj (Opposite.op complexAlgebra)).left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of ℂ)))
    apply liftReducedRange p j
    rw [pointLocation_range]
    exact Set.singleton_subset_iff.mpr h

private abbrev coefficientLid : Coefficients complexAlgebra ≃ₗ[ℂ] V := TensorProduct.lid ℂ V

private abbrev coefficientPairLid : ProductCoefficients complexAlgebra ≃ₗ[ℂ] (V × V) :=
  LinearEquiv.prodCongr coefficientLid coefficientLid

private theorem coefficientPairLid_comp :
    coefficientPairLid.toLinearMap.comp (coefficientPairs complexAlgebra).toLinearMap =
      (TensorProduct.lid ℂ (V × V)).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def coefficientIncidence (R : TestAlgebra ℂ)
    (S : Submodule R (Coefficients R)) (P : Submodule R (ProductCoefficients R)) : Prop :=
  (⊥ : Submodule R (Coefficients R)).prod S ≤ P ∧ P ≤ S.prod ⊤

private theorem projectedIncidence_congr (R : TestAlgebra ℂ)
    {x x' : Points projectiveScheme R}
    {y y' : Points WGrassmannian R} (e₁ : x = x') (e₂ : y = y') :
    coefficientIncidence R (tautological R x)
      ((secondChartSystem.affinePoints.hom.app R y).toSubmodule.map (coefficientPairs R).toLinearMap) =
    coefficientIncidence R (tautological R x')
      ((secondChartSystem.affinePoints.hom.app R y').toSubmodule.map (coefficientPairs R).toLinearMap) :=
  by cases e₁; cases e₂; rfl

private theorem complexCoefficientIncidence_iff (x : ProjectivePoints)
    (y : GrassmannianPoints twoStepBasis twoStepRank) :
    let S := tautological complexAlgebra x
    let P := (secondChartSystem.affinePoints.hom.app complexAlgebra y).toSubmodule.map
      (coefficientPairs complexAlgebra).toLinearMap
    coefficientIncidence complexAlgebra S P ↔ IncidenceCondition (firstPlane x)
      (grassmannianSubspace twoStepBasis twoStepRank y) := by
  dsimp only
  let S := tautological complexAlgebra x
  let P := (secondChartSystem.affinePoints.hom.app complexAlgebra y).toSubmodule.map
    (coefficientPairs complexAlgebra).toLinearMap
  change ((⊥ : Submodule ℂ (Coefficients complexAlgebra)).prod S ≤ P ∧ P ≤ S.prod ⊤) ↔ _
  let E := coefficientPairLid.toLinearMap
  have hp : P.map E = grassmannianSubspace twoStepBasis twoStepRank y := by
    unfold P E
    rw [← Submodule.map_comp, coefficientPairLid_comp]
    rfl
  have hlow : ((⊥ : Submodule ℂ (Coefficients complexAlgebra)).prod S).map E =
      (⊥ : Submodule ℂ V).prod (firstPlane x) := by
    change ((⊥ : Submodule ℂ (Coefficients complexAlgebra)).prod S).map
      (coefficientLid.toLinearMap.prodMap coefficientLid.toLinearMap) =
      (⊥ : Submodule ℂ V).prod (S.map coefficientLid.toLinearMap)
    rw [LinearMap.prodMap_map_prod, Submodule.map_bot]
  have hupp : (S.prod (⊤ : Submodule ℂ (Coefficients complexAlgebra))).map E =
      (firstPlane x).prod ⊤ := by
    change (S.prod (⊤ : Submodule ℂ (Coefficients complexAlgebra))).map
      (coefficientLid.toLinearMap.prodMap coefficientLid.toLinearMap) =
      (S.map coefficientLid.toLinearMap).prod ⊤
    rw [LinearMap.prodMap_map_prod, Submodule.map_top,
      LinearMap.range_eq_top.mpr coefficientLid.surjective]
  unfold IncidenceCondition
  rw [← hlow, ← hupp, ← hp]
  rw [Submodule.map_le_map_iff_of_injective coefficientPairLid.injective,
      Submodule.map_le_map_iff_of_injective coefficientPairLid.injective]

private theorem rawComplexPoint (p : Points IncidenceAmbient complexAlgebra) :
    (∃ q : Points rawIncidence complexAlgebra, q ≫ rawInclusion = p ≫ planeProductMap) ↔
      p ∈ incidenceLocus := by
  have hf : (p ≫ planeProductMap) ≫ prod.fst = p ≫ prod.fst := by
    rw [Category.assoc, planeProductMap_fst]
  have hg : (p ≫ planeProductMap) ≫ prod.snd =
      (p ≫ prod.snd) ≫ twoStepSchemeInGrassmannian := by
    rw [Category.assoc, planeProductMap_snd, Category.assoc]
  exact (rawIncidence_affine complexAlgebra (p ≫ planeProductMap)).trans
    ((projectedIncidence_congr complexAlgebra hf hg).to_iff.trans
      (complexCoefficientIncidence_iff (p ≫ prod.fst) ((p ≫ prod.snd) ≫ twoStepSchemeInGrassmannian)))

private theorem incidence_range :
    Set.range (incidenceInclusion ≫ planeProductMap).left ⊆ Set.range rawInclusion.left := by
  have := rawInclusion_closed
  let Z := planeProductMap.left ⁻¹' Set.range rawInclusion.left
  have hZ : IsClosed Z := rawInclusion.left.isClosedEmbedding.isClosed_range.preimage
    planeProductMap.left.continuous
  have hSub : pointLocation '' incidenceLocus ⊆ Z := by
    rintro _ ⟨q, hq, rfl⟩
    exact (liftPoint_iff_range rawInclusion _).mp ((rawComplexPoint q).mpr hq)
  have hClosure := closure_minimal hSub hZ
  rintro _ ⟨x, rfl⟩
  apply hClosure
  have hRange :
      Set.range (reducedClosureIdeal IncidenceAmbient incidenceLocus).subschemeι =
        closure (pointLocation '' incidenceLocus) :=
    (range_subschemeι _).trans (coe_support_vanishingIdeal _)
  exact hRange ▸ Set.mem_range_self x

private theorem incidence_raw_map :
    ∃ i : incidenceScheme ⟶ rawIncidence, i ≫ rawInclusion = incidenceInclusion ≫ planeProductMap := by
  have := incidenceReduced
  have := rawInclusion_closed
  exact liftReducedRange _ _ incidence_range

/-- The incidence equations are closed in the product of the two schemes. -/
theorem incidencePoint_condition (p : Points incidenceScheme complexAlgebra) :
    p ≫ incidenceInclusion ∈ incidenceLocus := by
  obtain ⟨i, hi⟩ := incidence_raw_map
  refine (rawComplexPoint _).mp ⟨p ≫ i, ?_⟩
  rw [Category.assoc, hi, Category.assoc]

theorem incidenceAffine_condition (R : TestAlgebra ℂ) (p : Points incidenceScheme R) :
    let S := tautological R (p ≫ ConvolutionBundleSpecs.firstProjection)
    let P := twoStepAffinePlane R (p ≫ terminalProjection)
    (⊥ : Submodule R (Coefficients R)).prod S ≤ P ∧ P ≤ S.prod ⊤ := by
  obtain ⟨i, hi⟩ := incidence_raw_map
  let a := (p ≫ incidenceInclusion) ≫ planeProductMap
  have h₁ : a ≫ prod.fst = p ≫ ConvolutionBundleSpecs.firstProjection := by
    simp [a, ConvolutionBundleSpecs.firstProjection, planeProductMap, Category.assoc]
  have h₂ : a ≫ prod.snd = (p ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian := by
    simp [a, terminalProjection, planeProductMap, Category.assoc]
  have hh := (rawIncidence_affine R a).mp ⟨p ≫ i, by rw [Category.assoc, hi]; rfl⟩
  exact (projectedIncidence_congr R h₁ h₂).mp hh

private theorem rawIncidence_geometry : Smooth rawIncidence.hom ∧ IsReduced rawIncidence.left := by
  have h : ConvolutionBundleChartsSpecs.AffineIncidence
      firstChartSystem secondChartSystem rawInclusion := rawIncidence_affine
  exact (ConvolutionBundleCharts.bundleCharts projectiveBasis twoStepBasis
    firstChartSystem secondChartSystem rawInclusion rawInclusion_closed h).2

private theorem terminalPlane_stable {S : Submodule ℂ V} {P : Submodule ℂ (V × V)}
    (h : IncidenceCondition S P) : P.map shift ≤ P := by
  rintro _ ⟨x, hx, rfl⟩
  apply h.1
  exact ⟨Submodule.zero_mem _, (h.2 hx).1⟩

private theorem liftRawComplexPoint (p : Points rawIncidence complexAlgebra) :
    ∃ q : Points incidenceScheme complexAlgebra, q ≫ incidenceToProduct = p ≫ rawInclusion := by
  let b := p ≫ rawInclusion
  have h := (rawIncidence_affine complexAlgebra b).mp ⟨p, rfl⟩
  have hc := (complexCoefficientIncidence_iff (b ≫ prod.fst) (b ≫ prod.snd)).mp h
  obtain ⟨e, he⟩ := LatticeModels.stableSchemePointComparison twoStepBasis twoStepRank shift
  let t : TwoStepPoints := ⟨b ≫ prod.snd, terminalPlane_stable hc⟩
  have ht : e.symm t ≫ twoStepSchemeInGrassmannian = b ≫ prod.snd :=
    (he (e.symm t)).symm.trans (congrArg Subtype.val (e.apply_symm_apply t))
  let z : Points IncidenceAmbient complexAlgebra := prod.lift (b ≫ prod.fst) (e.symm t)
  have hz : z ≫ planeProductMap = b := by
    apply prod.hom_ext
    · rw [Category.assoc, planeProductMap_fst]
      exact prod.lift_fst _ _
    · rw [Category.assoc, planeProductMap_snd, ← Category.assoc]
      exact (congrArg (· ≫ twoStepSchemeInGrassmannian) (prod.lift_snd _ _)).trans ht
  have hzLocus : z ∈ incidenceLocus := (rawComplexPoint z).mp ⟨p, hz.symm⟩
  obtain ⟨q, hq⟩ := (LatticeModels.pointLocation_in_closure_iff incidenceLocus z).mp
    (subset_closure ⟨z, hzLocus, rfl⟩)
  exact ⟨q, (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ planeProductMap) hq).trans hz)⟩

private theorem rawIncidence_range :
    Set.range rawInclusion.left ⊆ Set.range incidenceToProduct.left := by
  have := rawIncidence_geometry.1
  have := incidenceToProduct_closed
  have : JacobsonSpace ↥rawIncidence.left := LocallyOfFiniteType.jacobsonSpace rawIncidence.hom
  let Z := rawInclusion.left ⁻¹' Set.range incidenceToProduct.left
  have hZ : IsClosed Z := incidenceToProduct.left.isClosedEmbedding.isClosed_range.preimage
    rawInclusion.left.continuous
  have h : closedPoints rawIncidence.left ⊆ Z := by
    intro x hx
    have hx' : IsClosed ({x} : Set rawIncidence.left) := hx
    have hbase : ((LinearAlgebraicGroups.testSpec ℂ).obj (Opposite.op complexAlgebra)).hom =
        𝟙 (Spec (CommRingCat.of ℂ)) := by
      change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
      simp
    let p : Points rawIncidence complexAlgebra := Over.homMk
      (pointOfClosedPoint rawIncidence.hom x hx')
      ((pointOfClosedPoint_comp rawIncidence.hom x hx').trans hbase.symm)
    have hp : pointLocation p = x := pointOfClosedPoint_apply rawIncidence.hom x hx' _
    obtain ⟨q, hq⟩ := liftRawComplexPoint p
    refine ⟨pointLocation q, ?_⟩
    exact (congrArg pointLocation hq).trans (congrArg rawInclusion.left hp)
  have hh := closure_minimal h hZ
  rw [closure_closedPoints] at hh
  rintro _ ⟨x, rfl⟩
  exact hh (Set.mem_univ x)

private theorem incidenceIsoRaw :
    ∃ e : incidenceScheme ≅ rawIncidence, e.hom ≫ rawInclusion = incidenceToProduct ∧
      e.inv ≫ incidenceToProduct = rawInclusion := by
  have := rawIncidence_geometry.2
  have := rawInclusion_closed
  have := incidenceToProduct_closed
  have : Mono rawInclusion := Over.mono_of_mono_left _
  have : Mono incidenceToProduct := Over.mono_of_mono_left _
  obtain ⟨i, hi⟩ := incidence_raw_map
  have hi' : i ≫ rawInclusion = incidenceToProduct := hi
  obtain ⟨j, hj⟩ := liftReducedRange rawInclusion incidenceToProduct rawIncidence_range
  have h₁ : i ≫ j = 𝟙 _ := by
    apply (cancel_mono incidenceToProduct).mp
    rw [Category.assoc, hj, hi', Category.id_comp]
  have h₂ : j ≫ i = 𝟙 _ := by
    apply (cancel_mono rawInclusion).mp
    rw [Category.assoc, hi', hj, Category.id_comp]
  exact ⟨⟨i, j, h₁, h₂⟩, hi', hj⟩

private theorem incidenceToProduct_affine (R : TestAlgebra ℂ) (p : Points PlaneProduct R) :
    let S := tautological R (p ≫ prod.fst)
    let P := (secondChartSystem.affinePoints.hom.app R (p ≫ prod.snd)).toSubmodule.map
      (coefficientPairs R).toLinearMap
    (∃ q : Points incidenceScheme R, q ≫ incidenceToProduct = p) ↔
      coefficientIncidence R S P := by
  obtain ⟨e, he, he'⟩ := incidenceIsoRaw
  refine Iff.trans ?_ (rawIncidence_affine R p)
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q ≫ e.hom, by rwa [Category.assoc, he]⟩
  · rintro ⟨q, hq⟩
    exact ⟨q ≫ e.inv, by rwa [Category.assoc, he']⟩

theorem surfaceGeometry_conditional (_ : MinusculeOrbit) (_ : MinusculeProjective)
    (_ : SmallSchubertSchemes) (_ : TwoStepOrbits) (_ : TwoStepStableModel) : SurfaceGeometry := by
  refine ⟨?_, incidenceProjective, incidenceTerminalProper⟩
  obtain ⟨e, _⟩ := incidenceIsoRaw
  have := rawIncidence_geometry.1
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

open private reindexRank from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundleCharts

private theorem firstQuotientRank : Module.finrank ℂ V - 1 = 1 := by
  simp [V]

private theorem terminalQuotientRank : Module.finrank ℂ (V × V) - 2 = 2 := by
  simp [V, Module.finrank_prod]

private def firstCoefficientLine (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :
    Module.Grassmannian R (Coefficients R) 1 :=
  reindexRank firstQuotientRank (firstChartSystem.affinePoints.hom.app R p)

private def transportGrassmannian {R M N : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {d : ℕ}
    (e : M ≃ₗ[R] N) (P : Module.Grassmannian R M d) : Module.Grassmannian R N d :=
  let Q := P.toSubmodule.map e.toLinearMap
  let q : (M ⧸ P.toSubmodule) ≃ₗ[R] (N ⧸ Q) := Submodule.Quotient.equiv _ _ e rfl
  ⟨Q, Module.Finite.equiv q, Module.Projective.of_equiv q,
    fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv q) p).symm.trans (P.rankAtStalk_eq p)⟩

private def terminalCoefficientPlane (R : TestAlgebra ℂ) (p : Points WGrassmannian R) :
    Submodule R (ProductCoefficients R) :=
  (secondChartSystem.affinePoints.hom.app R p).toSubmodule.map (coefficientPairs R).toLinearMap

private theorem terminalCoefficientPlane_injective (R : TestAlgebra ℂ) :
    Function.Injective (terminalCoefficientPlane R) := by
  intro p q h
  apply (secondChartSystem.affinePoints.app R).toEquiv.injective
  apply Module.Grassmannian.ext
  exact Submodule.map_injective_of_injective (coefficientPairs R).injective h

private abbrev terminalPoint {R : TestAlgebra ℂ} (q : Points incidenceScheme R) :
    Points WGrassmannian R := (q ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian

private def incidenceTerminalPlane (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    AffineIncidencePlanes R (tautological R (q ≫ ConvolutionBundleSpecs.firstProjection)) :=
  ⟨reindexRank terminalQuotientRank (transportGrassmannian (coefficientPairs R)
      (secondChartSystem.affinePoints.hom.app R (terminalPoint q))),
    incidenceAffine_condition R q⟩

private def affinePointToBundle (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    Σ p : Points projectiveScheme R, BundleLine R p :=
  let p := q ≫ ConvolutionBundleSpecs.firstProjection
  ⟨p, (affineBundlePlaneEquiv R (firstCoefficientLine R p)).symm (incidenceTerminalPlane R q)⟩

private theorem affinePointToBundle_plane (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    let S := tautological R (affinePointToBundle R q).1
    terminalCoefficientPlane R (terminalPoint q) =
      bundlePreimage R S (affinePointToBundle R q).2.toSubmodule := by
  let L := firstCoefficientLine R (q ≫ ConvolutionBundleSpecs.firstProjection)
  let P := incidenceTerminalPlane R q
  let e := affineBundlePlaneEquiv R L
  exact (congrArg (fun P' : AffineIncidencePlanes R L.toSubmodule ↦ P'.val.toSubmodule)
    (e.apply_symm_apply P)).symm.trans (affineBundlePlaneEquiv_submodule R L (e.symm P))

private def bundleCoordinates (R : TestAlgebra ℂ)
    (B : Σ p : Points projectiveScheme R, BundleLine R p) :
    Points projectiveScheme R × Submodule R (ProductCoefficients R) :=
  (B.1, bundlePreimage R (tautological R B.1) B.2.toSubmodule)

private theorem bundleCoordinates_injective (R : TestAlgebra ℂ) :
    Function.Injective (bundleCoordinates R) := by
  rintro ⟨p, L⟩ ⟨q, M⟩ h
  have hpq : p = q := congrArg Prod.fst h
  subst q
  apply congrArg (Sigma.mk p)
  apply Module.Grassmannian.ext
  apply (bundleSubmoduleEquiv R (tautological R p)).injective
  exact Subtype.ext (congrArg Prod.snd h)

private theorem affinePointToBundle_coordinates (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    bundleCoordinates R (affinePointToBundle R q) =
      (q ≫ ConvolutionBundleSpecs.firstProjection, terminalCoefficientPlane R (terminalPoint q)) :=
  Prod.ext rfl (affinePointToBundle_plane R q).symm

private theorem affinePointToBundle_bijective (R : TestAlgebra ℂ) :
    Function.Bijective (affinePointToBundle R) := by
  constructor
  · intro p q h
    have hc := congrArg (bundleCoordinates R) h
    rw [affinePointToBundle_coordinates, affinePointToBundle_coordinates] at hc
    have := incidenceToProduct_closed
    have : Mono incidenceToProduct := Over.mono_of_mono_left _
    apply (cancel_mono incidenceToProduct).mp
    apply prod.hom_ext
    · simpa only [Category.assoc, incidenceToProduct_fst] using congrArg Prod.fst hc
    · rw [Category.assoc, Category.assoc, incidenceToProduct_snd, ← Category.assoc p, ← Category.assoc q]
      exact terminalCoefficientPlane_injective R (congrArg Prod.snd hc)
  · rintro ⟨x, B⟩
    let L := firstCoefficientLine R x
    let P := affineBundlePlaneEquiv R L B
    let G := reindexRank terminalQuotientRank.symm
      (transportGrassmannian (coefficientPairs R).symm P.val)
    let y : Points WGrassmannian R := (secondChartSystem.affinePoints.app R).toEquiv.symm G
    have hy : secondChartSystem.affinePoints.hom.app R y = G :=
      (secondChartSystem.affinePoints.app R).toEquiv.apply_symm_apply G
    have hyP : terminalCoefficientPlane R y = P.val.toSubmodule := by
      unfold terminalCoefficientPlane
      rw [hy]
      exact (Submodule.map_symm_eq_iff (coefficientPairs R)).mp rfl
    let b : Points PlaneProduct R := prod.lift x y
    have hb₁ : b ≫ prod.fst = x := prod.lift_fst _ _
    have hb₂ : b ≫ prod.snd = y := prod.lift_snd _ _
    have hb : coefficientIncidence R (tautological R (b ≫ prod.fst))
        (terminalCoefficientPlane R (b ≫ prod.snd)) := by
      rw [hb₁, hb₂, hyP]
      exact P.property
    obtain ⟨q, hq⟩ := (incidenceToProduct_affine R b).mpr hb
    refine ⟨q, bundleCoordinates_injective R ?_⟩
    rw [affinePointToBundle_coordinates]
    have hq₁ : q ≫ ConvolutionBundleSpecs.firstProjection = x := by
      rw [← incidenceToProduct_fst, ← Category.assoc, hq, hb₁]
    have hq₂ : terminalPoint q = y := by
      change (q ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian = y
      rw [Category.assoc, ← incidenceToProduct_snd, ← Category.assoc, hq, hb₂]
    exact Prod.ext hq₁ ((congrArg (terminalCoefficientPlane R) hq₂).trans
      (hyP.trans (affineBundlePlaneEquiv_submodule R L B)))

private theorem affinePointToBundle_image (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    (affinePointToBundle R q).2.toSubmodule =
      ((terminalCoefficientPlane R (terminalPoint q)).comap
        ((tautological R (affinePointToBundle R q).1).prod ⊤).subtype).map
          (bundleQuotient R (tautological R (affinePointToBundle R q).1)) := rfl

private def coefficientSemilinear {R T : TestAlgebra ℂ} (a : R ⟶ T) :
    Coefficients R →ₛₗ[a.hom.toRingHom] Coefficients T where
  toFun := coefficientChange a
  map_add' := (coefficientChange a).map_add
  map_smul' r x := by
    change coefficientChange a (r • x) = (a.hom r) • coefficientChange a x
    induction x using TensorProduct.inductionOn with
    | tmul s v => simp [coefficientChange, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem tautological_baseChange {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (p : Points projectiveScheme R) :
    tautological T (mapPoints a p) = Submodule.span T
      (coefficientChange a '' (tautological R p : Set (Coefficients R))) := by
  exact (congrArg (fun L : Plane ℂ V 1 T ↦ L.toSubmodule) (firstPlane_natural a p)).trans
    (planeMap_eq_span_of_hom a (firstChartSystem.affinePoints.hom.app R p))

private theorem terminalCoefficientPlane_baseChange {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (p : Points WGrassmannian R) :
    terminalCoefficientPlane T (mapPoints a p) = Submodule.span T
      (Prod.map (coefficientChange a) (coefficientChange a) ''
        (terminalCoefficientPlane R p : Set (ProductCoefficients R))) := by
  have h : secondChartSystem.affinePoints.hom.app T (mapPoints a p) =
      Module.Grassmannian.map a.hom (secondChartSystem.affinePoints.hom.app R p) :=
    congrArg (fun f : Points WGrassmannian R ⟶ Plane ℂ (V × V) 2 T ↦ f p)
      (secondChartSystem.affinePoints.hom.naturality a)
  exact (congrArg (fun P : Plane ℂ (V × V) 2 T ↦
      P.toSubmodule.map (coefficientPairs T).toLinearMap) h).trans
    (plane_pair_baseChange a (secondChartSystem.affinePoints.hom.app R p))

private theorem bundleLine_baseChange_formula {R T : TestAlgebra ℂ} (a : R ⟶ T)
    {p : Points projectiveScheme R} {p' : Points projectiveScheme T}
    (B : BundleLine R p) (B' : BundleLine T p')
    (P : Submodule R (ProductCoefficients R)) (P' : Submodule T (ProductCoefficients T))
    (h : coefficientIncidence R (tautological R p) P)
    (hS : tautological T p' = Submodule.span T
      (coefficientChange a '' (tautological R p : Set (Coefficients R))))
    (hP : P' = Submodule.span T (Prod.map (coefficientChange a) (coefficientChange a) ''
      (P : Set (ProductCoefficients R))))
    (hB : B.toSubmodule = (P.comap ((tautological R p).prod ⊤).subtype).map
      (bundleQuotient R (tautological R p)))
    (hB' : B'.toSubmodule = (P'.comap ((tautological T p').prod ⊤).subtype).map
      (bundleQuotient T (tautological T p'))) :
    B'.toSubmodule = changeBundleLine a (p' := p') B := by
  have hc := (ConvolutionBundleBaseChange.affineBaseChange a.hom.toRingHom (coefficientSemilinear a)
    (tautological R p) P h.1 h.2).2.2
  rw [hB', hP]
  unfold changeBundleLine
  rw [hB]
  generalize tautological T p' = S' at hS ⊢
  subst S'
  exact hc

private theorem affinePointToBundle_natural {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (q : Points incidenceScheme R) :
    (affinePointToBundle T (mapPoints a q)).2.toSubmodule =
      changeBundleLine a (p' := (affinePointToBundle T (mapPoints a q)).1)
        (affinePointToBundle R q).2 := by
  apply bundleLine_baseChange_formula a _ _ (terminalCoefficientPlane R (terminalPoint q))
    (terminalCoefficientPlane T (terminalPoint (mapPoints a q)))
  · exact incidenceAffine_condition R q
  · change tautological T (mapPoints a q ≫ ConvolutionBundleSpecs.firstProjection) = _
    rw [Category.assoc]
    exact tautological_baseChange a _
  · change terminalCoefficientPlane T
      (((mapPoints a q) ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian) = _
    rw [Category.assoc ((LinearAlgebraicGroups.testSpec ℂ).map a.op) q,
      Category.assoc ((LinearAlgebraicGroups.testSpec ℂ).map a.op) (q ≫ terminalProjection)]
    exact terminalCoefficientPlane_baseChange a (terminalPoint q)
  · exact affinePointToBundle_image R q
  · exact affinePointToBundle_image T (mapPoints a q)

theorem projectiveBundle_conditional (_ : MinusculeOrbit) (_ : MinusculeProjective)
    (_ : SmallSchubertSchemes) (_ : TwoStepOrbits) (_ : TwoStepStableModel) : ProjectiveBundle := by
  constructor
  · intro R p
    exact ConvolutionDeterminantDual.determinantDual R (Coefficients R)
      (LinearAlgebraicGroups.Specs.GrassmannianCharts.coordinates (Pi.basisFun ℂ (Fin 2)) R)
      (firstCoefficientLine R p)
  · let e (R : TestAlgebra ℂ) := Equiv.ofBijective (affinePointToBundle R) (affinePointToBundle_bijective R)
    exact ⟨e, fun R q ↦ ⟨rfl, affinePointToBundle_plane R q⟩,
      fun a q ↦ affinePointToBundle_natural a q⟩

theorem latticeIncidence_conditional (h₁ : MinusculeOrbit) (hp : MinusculeProjective)
    (_ : SmallSchubertSchemes) (_ : TwoStepOrbits) (hs : TwoStepStableModel) :
    LatticeIncidence := by
  obtain ⟨f, hf, h⟩ := flags_incidenceEmbedding h₁ hp hs
  obtain ⟨e, he⟩ := flags_coefficientComparison h₁ hp hs
  obtain ⟨s, hs'⟩ := LatticeModels.stableSchemePointComparison twoStepBasis twoStepRank shift
  have hsurj : Function.Surjective f := by
    intro p
    have hc := incidencePoint_condition p
    let p₁ := p ≫ ConvolutionBundleSpecs.firstProjection
    let p₂ := s (p ≫ terminalProjection)
    have h₂ : p₂.val = (p ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian := hs' _
    let q : CoefficientFlags := ⟨(p₁, p₂), by
      change IncidenceCondition (firstPlane p₁) (grassmannianSubspace twoStepBasis twoStepRank p₂.val)
      rw [h₂]
      exact hc⟩
    obtain ⟨L, hL⟩ := e.surjective q
    have hlines := he L
    rw [hL] at hlines
    refine ⟨L, incidenceCoordinates_injective (Prod.ext ?_ ?_)⟩
    · apply grassmannianSubspace_injective projectiveBasis projectiveRank
      exact (h L).1.trans hlines.1.symm
    · apply grassmannianSubspace_injective twoStepBasis twoStepRank
      exact (h L).2.trans (hlines.2.symm.trans
        (congrArg (grassmannianSubspace twoStepBasis twoStepRank) h₂))
  exact ⟨incidenceReduced, incidenceInclusion_closed, hf.toHomeomorphOfSurjective hsurj, h⟩

end SchemeIncidence

end

end RepTheorySurvey.Geometric.ConvolutionBundle

theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«firstLatticeQuotient» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundleSpecs».«FirstLatticeQuotient» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«firstLatticeQuotient_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«flagJetAction» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundleSpecs».«FlagJetAction» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«flagJetAction_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«latticeIncidence» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundleSpecs».«LatticeIncidence» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«latticeIncidence_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«projectiveBundle» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundleSpecs».«ProjectiveBundle» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«projectiveBundle_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«surfaceGeometry» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundleSpecs».«SurfaceGeometry» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«surfaceGeometry_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«twistedFlags» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionBundleSpecs».«TwistedFlags» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«twistedFlags_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel»)
