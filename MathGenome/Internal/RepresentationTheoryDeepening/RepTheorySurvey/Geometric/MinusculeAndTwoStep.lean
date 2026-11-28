import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianCoordinateInclusion
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Pi

namespace RepTheorySurvey.Geometric.MinusculeAndTwoStep

noncomputable section

open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open scoped Matrix MatrixGroups
open LinearAlgebraicGroups.Specs.GrassmannianCharts

private abbrev Upper : Submodule O (Coordinates 2) := (scalarLattice 2 0).val

local instance upperHasQuotient : HasQuotient (Upper : Type) (Submodule O Upper) :=
  @Submodule.hasQuotient O (Upper : Type) inferInstance inferInstance inferInstance

private def inside (L : GL2Lattice) : Submodule O Upper := L.val.comap Upper.subtype

private def complexQuotientOfQuotient {M : Type} [AddCommGroup M] [Module O M]
    [Module ℂ M] [IsScalarTower ℂ O M] (Q P : Submodule O M) (hQP : Q ≤ P) :
    ((M ⧸ Q) ⧸ (P.map Q.mkQ).restrictScalars ℂ) ≃ₗ[ℂ] (M ⧸ P) :=
  (Submodule.quotientQuotientEquivQuotient Q P hQP).restrictScalars ℂ

private theorem complexQuotient_rank {M : Type} [AddCommGroup M] [Module O M]
    [Module ℂ M] [IsScalarTower ℂ O M] (Q P : Submodule O M) (hQP : Q ≤ P)
    [Module.Finite ℂ (M ⧸ Q)] :
    Module.Finite ℂ (M ⧸ P) ∧
      Module.finrank ℂ (M ⧸ P) + Module.finrank ℂ ((P.map Q.mkQ).restrictScalars ℂ) =
        Module.finrank ℂ (M ⧸ Q) := by
  let S := (P.map Q.mkQ).restrictScalars ℂ
  let e := complexQuotientOfQuotient Q P hQP
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    e.finrank_eq ▸ S.finrank_quotient_add_finrank⟩

set_option backward.isDefEq.respectTransparency false in
private theorem colength_iff_window_rank {m : ℕ} (L : WindowLattice 2 0 m) :
    L.val ∈ colength m ↔ Module.finrank ℂ (latticeSubspace 0 m L.val) = m := by
  let Q : Submodule O Upper := windowLower 2 0 m
  let P : Submodule O Upper := inside L.val
  have hQP : Q ≤ P := fun _ hx ↦ L.property.1 hx
  have hd : Module.finrank ℂ (Window 2 0 m) = 2 * m := by
    rw [Module.finrank_eq_card_basis (windowBasis 2 0 m)]
    simp
  let : Module.Finite ℂ (Upper ⧸ Q) := windowFinite 2 0 m
  have hh := complexQuotient_rank (M := Upper) Q P hQP
  have hf : Module.Finite ℂ (StandardQuotient L.val) := hh.1
  have he : Module.finrank ℂ (StandardQuotient L.val) +
    Module.finrank ℂ (latticeSubspace 0 m L.val) = 2 * m := hh.2.trans hd
  constructor
  · intro h
    have hn := h.2.2
    omega
  · intro h
    exact ⟨L.property.2, hf, by omega⟩

private abbrev IntegralCoordinates := Fin 2 → O

private abbrev integralInclusion : IntegralCoordinates →ₗ[O] Coordinates 2 :=
  coordinateInclusion 2

private theorem shifted_zero : shiftedInclusion 2 0 = integralInclusion := by
  apply LinearMap.ext
  intro x
  funext i
  change monomial 0 * inclusion (x i) = inclusion (x i)
  simp [monomial_eq_zpow]

private theorem upper_eq_range : Upper = integralInclusion.range := by
  change (scalarLattice 2 0).val = _
  rw [scalarLattice_val, shifted_zero]

private def integralPart (L : GL2Lattice) : Submodule O IntegralCoordinates :=
  L.val.comap integralInclusion

private theorem integralPart_map {L : GL2Lattice} (h : L.val ≤ Upper) :
    (integralPart L).map integralInclusion = L.val := by
  rw [integralPart, Submodule.map_comap_eq, ← upper_eq_range, inf_eq_right.mpr h]

private def quotientComapEquiv {M M' : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (e : M ≃ₗ[O] M')
    (P : Submodule O M) (Q : Submodule O M')
    (h : Q.comap e.toLinearMap = P) : (M ⧸ P) ≃ₗ[O] (M' ⧸ Q) :=
  Submodule.Quotient.equiv _ _ e
    (by rw [← h, Submodule.map_comap_eq, LinearEquiv.range, top_inf_eq])

set_option backward.isDefEq.respectTransparency false in
private def integralQuotient (L : GL2Lattice) :
    (IntegralCoordinates ⧸ integralPart L) ≃ₗ[O] StandardQuotient L := by
  let e : IntegralCoordinates ≃ₗ[O] Upper := shiftedCoordinates 2 0
  have hc : (inside L).comap e.toLinearMap = integralPart L := by
    unfold inside integralPart
    rw [← Submodule.comap_comp]
    congr 1
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : IntegralCoordinates →ₗ[O] Coordinates 2 ↦ f v) shifted_zero
  let q := quotientComapEquiv (M := IntegralCoordinates) (M' := Upper)
    e (integralPart L) (inside L) hc
  exact q

private def integralAction (g : GL (Fin 2) O) : IntegralCoordinates ≃ₗ[O] IntegralCoordinates :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv O _ (Matrix.GeneralLinearGroup.toLin g)

private theorem integralAction_comm (g : GL (Fin 2) O) (x : IntegralCoordinates) :
    loopLinearEquiv 2 (positiveGLMap 2 g) (integralInclusion x) =
      integralInclusion (integralAction g x) :=
  positiveGLMap_linear g x

private theorem positive_le_upper (g : GL (Fin 2) O) {L : GL2Lattice} (hL : L.val ≤ Upper) :
    (positiveGLMap 2 g • L).val ≤ Upper := by
  let f := ((loopLinearEquiv 2 (positiveGLMap 2 g)).restrictScalars O).toLinearMap
  change L.val.map f ≤ Upper
  have hfix : Upper.map f = Upper :=
    congrArg Subtype.val (positiveGL_preserves_scalar g 0)
  rw [← hfix]
  exact Submodule.map_mono hL

private theorem integralPart_positive (g : GL (Fin 2) O) {L : GL2Lattice}
    (hL : L.val ≤ Upper) :
    integralPart (positiveGLMap 2 g • L) = (integralPart L).map (integralAction g).toLinearMap := by
  let f := ((loopLinearEquiv 2 (positiveGLMap 2 g)).restrictScalars O).toLinearMap
  have hcomp : f.comp integralInclusion = integralInclusion.comp (integralAction g).toLinearMap :=
    LinearMap.ext (integralAction_comm g)
  change (L.val.map f).comap integralInclusion = _
  rw [← integralPart_map hL, ← Submodule.map_comp, hcomp, Submodule.map_comp,
    Submodule.comap_map_eq_of_injective (coordinateInclusion_injective 2)]

private theorem colength_positive (g : GL (Fin 2) O) {m : ℕ} {L : GL2Lattice}
    (hL : L.val ≤ Upper) :
    positiveGLMap 2 g • L ∈ colength m ↔ L ∈ colength m := by
  let L' := positiveGLMap 2 g • L
  let e : StandardQuotient L ≃ₗ[ℂ] StandardQuotient L' :=
    ((integralQuotient L).symm ≪≫ₗ
      Submodule.Quotient.equiv (integralPart L) (integralPart L') (integralAction g)
        (integralPart_positive g hL).symm ≪≫ₗ integralQuotient L').restrictScalars ℂ
  have hf : Module.Finite ℂ (StandardQuotient L') ↔ Module.Finite ℂ (StandardQuotient L) :=
    ⟨fun h ↦ Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
      fun h ↦ Module.Finite.of_surjective e.toLinearMap e.surjective⟩
  change (_ ∧ _ ∧ Module.finrank ℂ (StandardQuotient L') = m) ↔ (_ ∧ _ ∧ _)
  rw [← e.finrank_eq, hf]
  exact and_congr_left fun _ ↦ iff_of_true (positive_le_upper g hL) hL

private def naturalDiagonal (a : Fin 2 → ℕ) : GL2Lattice :=
  diagonalLattice (fun i ↦ (a i : ℤ))

private theorem naturalDiagonal_le_upper (a : Fin 2 → ℕ) :
    (naturalDiagonal a).val ≤ Upper :=
  diagonalLattice_le fun i ↦ Int.natCast_nonneg (a i)

private theorem integralPart_naturalDiagonal (a : Fin 2 → ℕ) :
    integralPart (naturalDiagonal a) = Submodule.pi Set.univ (fun i ↦ jetIdeal (a i)) := by
  have hd (x : IntegralCoordinates) :
      diagonalEquiv (fun i ↦ (a i : ℤ)) (integralInclusion x) =
        integralInclusion (fun i ↦ t ^ a i * x i) := by
    funext i
    change monomial (a i : ℤ) * inclusion (x i) = inclusion (t ^ a i * x i)
    rw [monomial_nat, map_mul]
  ext x
  change integralInclusion x ∈ (naturalDiagonal a).val ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, jetIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, heq⟩
    have h := coordinateInclusion_injective 2 ((hd y).symm.trans heq)
    exact fun i ↦ ⟨y i, (congrFun h i).symm⟩
  · intro h
    choose y hy using h
    refine ⟨integralInclusion y, ⟨y, rfl⟩, (hd y).trans ?_⟩
    exact congrArg integralInclusion (funext fun i ↦ (hy i).symm)

private theorem naturalDiagonal_colength (a : Fin 2 → ℕ) (m : ℕ) :
    naturalDiagonal a ∈ colength m ↔ a 0 + a 1 = m := by
  let e := (((integralQuotient (naturalDiagonal a)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (integralPart_naturalDiagonal a)) ≪≫ₗ
    Submodule.quotientPi (fun i ↦ (jetIdeal (a i) : Submodule O O))).restrictScalars ℂ
  let e' := e ≪≫ₗ LinearEquiv.piCongrRight (fun i ↦ jetCoefficients (a i))
  have hfin : Module.Finite ℂ (StandardQuotient (naturalDiagonal a)) :=
    Module.Finite.of_surjective e'.symm.toLinearMap e'.symm.surjective
  change (_ ∧ _ ∧ Module.finrank ℂ (StandardQuotient (naturalDiagonal a)) = m) ↔ _
  rw [e'.finrank_eq, Module.finrank_pi_fintype]
  have hl : (naturalDiagonal a).val ≤ Upper := naturalDiagonal_le_upper a
  simp [hl, hfin, Fin.sum_univ_two]

private theorem integralPart_eq_iff {L L' : GL2Lattice} (hL : L.val ≤ Upper)
    (hL' : L'.val ≤ Upper) : integralPart L = integralPart L' ↔ L = L' := by
  constructor
  · intro h
    apply Subtype.ext
    rw [← integralPart_map hL, ← integralPart_map hL', h]
  · rintro rfl
    rfl

private theorem diagonalize {L : GL2Lattice} (hL : L.val ≤ Upper) :
    ∃ a : Fin 2 → ℕ, a 1 ≤ a 0 ∧ ∃ g : GL (Fin 2) O,
      positiveGLMap 2 g • naturalDiagonal a = L := by
  classical
  let N := integralPart L
  let b₀ : Module.Basis (Fin 2) O IntegralCoordinates := Pi.basisFun O (Fin 2)
  let eL : N ≃ₗ[O] L.val :=
    Submodule.comap_equiv_self_of_inj_of_le (coordinateInclusion_injective 2)
      (by rwa [← upper_eq_range])
  obtain ⟨bL⟩ := L.property.1
  have hN : Module.finrank O N = Module.finrank O IntegralCoordinates := by
    rw [eL.finrank_eq, Module.finrank_eq_card_basis bL, Module.finrank_eq_card_basis b₀]
  let c := N.smithNormalFormCoeffs b₀ hN
  let k : Fin 2 → ℕ := fun i ↦ (c i).order.toNat
  let s : Fin 2 ≃ Fin 2 := if k 1 ≤ k 0 then Equiv.refl _ else Equiv.swap 0 1
  let a := k ∘ s
  have ha : a 1 ≤ a 0 := by
    by_cases h : k 1 ≤ k 0
    · simp [a, s, h]
    · simpa [a, s, h] using (le_of_lt (Nat.lt_of_not_ge h))
  let b := (N.smithNormalFormTopBasis b₀ hN).reindex s.symm
  let bN := (N.smithNormalFormBotBasis b₀ hN).reindex s.symm
  have hdiag (i : Fin 2) : (bN i : IntegralCoordinates) = c (s i) • b i := by
    simpa only [bN, b, Module.Basis.reindex_apply, Equiv.symm_symm, c] using
      N.smithNormalFormBotBasis_def b₀ hN (s i)
  have hdiv (i : Fin 2) : Associated (t ^ a i) (c (s i)) := by
    have hn : c (s i) ≠ 0 := N.smithNormalFormCoeffs_ne_zero b₀ hN (s i)
    refine ⟨PowerSeries.Unit_of_divided_by_X_pow_order (c (s i)), ?_⟩
    rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hn]
    exact PowerSeries.X_pow_order_mul_divXPowOrder
  have hmem (x : IntegralCoordinates) : x ∈ N ↔ ∀ i, t ^ a i ∣ b.repr x i := by
    simp_rw [(hdiv _).dvd_iff_dvd_left]
    rw [bN.mem_submodule_iff']
    have hsum (v : Fin 2 → O) (i : Fin 2) :
        b.repr (∑ j, v j • (bN j : IntegralCoordinates)) i = c (s i) * v i := by
      simp only [hdiag, ← mul_smul, b.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨v, rfl⟩ i
      exact ⟨v i, hsum v i⟩
    · intro hx
      choose v hv using hx
      exact ⟨v, b.ext_elem fun i ↦ (hv i).trans (hsum v i).symm⟩
  let e := b.equivFun.symm
  let g := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv O IntegralCoordinates).symm e)
  have hg : integralAction g = e := by simp [integralAction, g]
  refine ⟨a, ha, g, (integralPart_eq_iff
    (positive_le_upper g (naturalDiagonal_le_upper a)) hL).mp ?_⟩
  rw [integralPart_positive g (naturalDiagonal_le_upper a), hg,
    integralPart_naturalDiagonal]
  change (Submodule.pi Set.univ (fun i ↦ jetIdeal (a i))).map e.toLinearMap = N
  ext x
  rw [Submodule.mem_map_equiv, hmem]
  simp [e, Submodule.mem_pi, jetIdeal, Ideal.mem_span_singleton]

private theorem orbit_naturalDiagonal_colength {a : Fin 2 → ℕ} {m : ℕ} (h : a 0 + a 1 = m)
    {L : GL2Lattice} (hL : L ∈ MulAction.orbit (PositiveGL 2) (naturalDiagonal a)) :
    L ∈ colength m := by
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩ := hL
  exact (colength_positive g (naturalDiagonal_le_upper a)).mpr
    ((naturalDiagonal_colength a m).mpr h)

private theorem naturalDiagonal_pair (a : Fin 2 → ℕ) (ab : DominantPair)
    (h₀ : (a 0 : ℤ) = ab.val.1) (h₁ : (a 1 : ℤ) = ab.val.2) :
    naturalDiagonal a = diagonalLattice (pairCoweight ab) := by
  apply congrArg (diagonalLattice (r := 2))
  funext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem colength_bound {m : ℕ} {L : GL2Lattice} (hL : L ∈ colength m) :
    (scalarLattice 2 (m : ℤ)).val ≤ L.val := by
  obtain ⟨a, _, g, rfl⟩ := diagonalize hL.1
  have hs := (naturalDiagonal_colength a m).mp
    ((colength_positive g (naturalDiagonal_le_upper a)).mp hL)
  have hle : (scalarLattice 2 (m : ℤ)).val ≤ (naturalDiagonal a).val := by
    apply diagonalLattice_le
    rw [Fin.forall_fin_two]
    constructor <;> omega
  let f := ((loopLinearEquiv 2 (positiveGLMap 2 g)).restrictScalars O).toLinearMap
  have hf : (scalarLattice 2 (m : ℤ)).val.map f = (scalarLattice 2 (m : ℤ)).val :=
    congrArg Subtype.val (positiveGL_preserves_scalar g (m : ℤ))
  change _ ≤ (naturalDiagonal a).val.map f
  rw [← hf]
  exact Submodule.map_mono hle

set_option maxHeartbeats 900000 in
theorem minusculeOrbit : MinusculeOrbit := by
  constructor
  swap
  · intro L
    exact colength_bound (m := 1) (L := L.val) L.property
  apply Set.ext
  intro L
  constructor
  · intro hL
    obtain ⟨a, ha, g, hg⟩ := diagonalize hL.1
    have hs := (naturalDiagonal_colength a 1).mp
      ((colength_positive g (naturalDiagonal_le_upper a)).mp (hg ▸ hL))
    have hd : naturalDiagonal a = diagonalLattice (pairCoweight minusculePair) :=
      naturalDiagonal_pair a _ (by change (a 0 : ℤ) = 1; omega)
        (by change (a 1 : ℤ) = 0; omega)
    exact ⟨⟨positiveGLMap 2 g, g, rfl⟩, by rw [← hd]; exact hg⟩
  · let a : Fin 2 → ℕ := fun i ↦ if i = 0 then 1 else 0
    have hd : naturalDiagonal a = diagonalLattice (pairCoweight minusculePair) :=
      naturalDiagonal_pair a _ rfl rfl
    change L ∈ MulAction.orbit (PositiveGL 2) (diagonalLattice (pairCoweight minusculePair)) → _
    rw [← hd]
    exact orbit_naturalDiagonal_colength (a := a) (by decide)


private theorem scalar_diagonal : diagonalLattice (pairCoweight scalarPair) = scalarPoint := by
  change diagonalLattice _ = diagonalLattice _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem scalar_orbit : gl2Orbit scalarPair = {scalarPoint} := by
  unfold gl2Orbit
  rw [scalar_diagonal]
  apply Set.ext
  intro L
  constructor
  · rintro ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩
    exact positiveGL_preserves_scalar g 1
  · intro h
    have h' : L = scalarPoint := h
    subst L
    exact ⟨1, one_smul (PositiveGL 2) scalarPoint⟩

private theorem scalar_colength : scalarPoint ∈ colength 2 := by
  have h : naturalDiagonal (fun _ ↦ 1) ∈ colength 2 :=
    (naturalDiagonal_colength (fun _ ↦ 1) 2).mpr rfl
  exact h

private def twoStepExponents : Fin 2 → ℕ := fun i ↦ if i = 0 then 2 else 0

private theorem twoStep_diagonal :
    naturalDiagonal twoStepExponents = diagonalLattice (pairCoweight twoStepPair) :=
  naturalDiagonal_pair _ _ rfl rfl

private theorem twoStep_diagonal_ne_scalar : naturalDiagonal twoStepExponents ≠ scalarPoint := by
  intro h
  let x : IntegralCoordinates := Pi.single 1 1
  have hx : x ∈ integralPart (naturalDiagonal twoStepExponents) := by
    rw [integralPart_naturalDiagonal]
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, jetIdeal, Ideal.mem_span_singleton]
    intro i
    fin_cases i <;> simp [x, twoStepExponents]
  have hs : naturalDiagonal (fun _ ↦ 1) = scalarPoint := rfl
  rw [h, ← hs, integralPart_naturalDiagonal] at hx
  have h1 : (t : O) ∣ (1 : O) := by
    have hh := (Submodule.mem_pi.mp hx) (1 : Fin 2) (Set.mem_univ _)
    simpa [x, jetIdeal, Ideal.mem_span_singleton] using hh
  obtain ⟨u, hu⟩ := h1
  have habs := congrArg (PowerSeries.constantCoeff (R := ℂ)) hu
  simp at habs

private theorem twoStep_orbit_set : gl2Orbit twoStepPair = colength 2 \ {scalarPoint} := by
  apply Set.ext
  intro L
  constructor
  · intro hL
    change L ∈ MulAction.orbit (PositiveGL 2) (diagonalLattice (pairCoweight twoStepPair)) at hL
    rw [← twoStep_diagonal] at hL
    refine ⟨orbit_naturalDiagonal_colength (a := twoStepExponents) (by decide) hL, ?_⟩
    obtain ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩ := hL
    intro he
    have hs : positiveGLMap 2 g • naturalDiagonal twoStepExponents =
        positiveGLMap 2 g • scalarPoint :=
      he.trans (positiveGL_preserves_scalar g 1).symm
    exact twoStep_diagonal_ne_scalar ((MulAction.injective _ ) hs)
  · rintro ⟨hL, hne⟩
    obtain ⟨a, ha, g, hg⟩ := diagonalize hL.1
    have hs := (naturalDiagonal_colength a 2).mp
      ((colength_positive g (naturalDiagonal_le_upper a)).mp (hg ▸ hL))
    have hn : a 0 ≠ 1 := by
      intro hn
      have hn' : a 1 = 1 := by omega
      have hscalar : naturalDiagonal a = scalarPoint := by
        change diagonalLattice _ = diagonalLattice _
        congr 1
        funext i
        fin_cases i
        · exact_mod_cast hn
        · exact_mod_cast hn'
      apply hne
      rw [← hg, hscalar]
      exact positiveGL_preserves_scalar g 1
    have hd : naturalDiagonal a = diagonalLattice (pairCoweight twoStepPair) :=
      naturalDiagonal_pair a _ (by change (a 0 : ℤ) = 2; omega)
        (by change (a 1 : ℤ) = 0; omega)
    exact ⟨⟨positiveGLMap 2 g, g, rfl⟩, by rw [← hd]; exact hg⟩

private abbrev windowMk := ShortWindowTopologySpecs.windowQuotient

set_option backward.isDefEq.respectTransparency false in
private theorem windowMk_surjective (a : ℤ) (m : ℕ) :
    Function.Surjective (windowMk a m) :=
  @Submodule.mkQ_surjective O ((scalarLattice 2 a).val : Type)
    inferInstance inferInstance inferInstance (windowLower 2 a m)

set_option backward.isDefEq.respectTransparency false in
private theorem windowCoordinates_mk (a : ℤ) (m : ℕ) (x : IntegralCoordinates)
    (i : Fin 2) (j : Fin m) :
    windowCoordinates 2 a m (windowMk a m (shiftedCoordinates 2 a x)) (i, j) =
      PowerSeries.coeff j.val (x i) := by
  change PowerSeries.coeff j.val (((shiftedCoordinates 2 a).symm (shiftedCoordinates 2 a x)) i) = _
  rw [LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem windowOperator_mk (a : ℤ) (m : ℕ) (x : IntegralCoordinates) :
    windowOperator 2 a m (windowMk a m (shiftedCoordinates 2 a x)) =
      windowMk a m (shiftedCoordinates 2 a (t • x)) := by
  rw [map_smul, map_smul]
  rfl

private theorem one_window_operator : windowOperator 2 0 1 = 0 := by
  apply LinearMap.ext
  intro w
  obtain ⟨z, rfl⟩ := windowMk_surjective 0 1 w
  obtain ⟨x, rfl⟩ := (shiftedCoordinates 2 0).surjective z
  rw [windowOperator_mk, LinearMap.zero_apply]
  apply (windowCoordinates 2 0 1).injective
  ext ⟨i,j⟩
  rw [windowCoordinates_mk, map_zero, Pi.zero_apply]
  have hj : j.val = 0 := by omega
  rw [hj]
  change PowerSeries.coeff 0 (PowerSeries.X * x i) = 0
  rw [← pow_one (PowerSeries.X : O), PowerSeries.coeff_X_pow_mul']; norm_num

private theorem two_window_operator (w : Window 2 0 2) :
    twoStepCoordinates (windowOperator 2 0 2 w) = shift (twoStepCoordinates w) := by
  obtain ⟨z, rfl⟩ := windowMk_surjective 0 2 w
  obtain ⟨x, rfl⟩ := (shiftedCoordinates 2 0).surjective z
  rw [windowOperator_mk]
  apply Prod.ext
  · funext i
    change windowCoordinates 2 0 2
      (windowMk 0 2 (shiftedCoordinates 2 0 (t • x))) (i, 0) = 0
    rw [windowCoordinates_mk]
    change PowerSeries.coeff 0 (PowerSeries.X * x i) = 0
    rw [← pow_one (PowerSeries.X : O), PowerSeries.coeff_X_pow_mul']; norm_num
  · funext i
    change windowCoordinates 2 0 2
      (windowMk 0 2 (shiftedCoordinates 2 0 (t • x))) (i, 1) =
      windowCoordinates 2 0 2 (windowMk 0 2 (shiftedCoordinates 2 0 x)) (i, 0)
    rw [windowCoordinates_mk, windowCoordinates_mk]
    change PowerSeries.coeff 1 (PowerSeries.X * x i) = PowerSeries.coeff 0 (x i)
    rw [← pow_one (PowerSeries.X : O), PowerSeries.coeff_X_pow_mul']; norm_num

private abbrev ShortPoints (m : ℕ) :=
  StablePoints (windowBasis 2 0 m) (shortWindowRank m) (windowOperator 2 0 m)

private def asShortWindow {m : ℕ} (L : Colength m) : WindowLattice 2 0 m :=
  ⟨L.val, by rw [zero_add]; exact colength_bound L.property, L.property.1⟩

private theorem shortPointComparison (m : ℕ) :
    ∃ e : Colength m ≃ ShortPoints m,
      (∀ L, grassmannianSubspace (windowBasis 2 0 m) (shortWindowRank m)
        (e L).val = latticeSubspace 0 m L.val) ∧
      ∀ p, (e.symm p).val.val.restrictScalars ℂ =
        windowInverseImage (grassmannianSubspace (windowBasis 2 0 m)
          (shortWindowRank m) p.val) := by
  classical
  let b := windowBasis 2 0 m
  let hd : m ≤ Module.finrank ℂ (Window 2 0 m) := shortWindowRank m
  obtain ⟨w, hq, hpre⟩ := BoundedLattices.windowLatticeComparison 2 0 m
  let F (L : Colength m) : ShortPoints m := by
    let P := latticeSubspace 0 m L.val
    have hr : Module.finrank ℂ P = m := (colength_iff_window_rank (asShortWindow L)).mp L.property
    refine ⟨subspacePoint b hd P hr, ?_⟩
    change (grassmannianSubspace b hd (subspacePoint b hd P hr)).map (windowOperator 2 0 m) ≤
      grassmannianSubspace b hd (subspacePoint b hd P hr)
    rw [subspacePoint_subspace b hd P hr]
    exact latticeSubspace_stable 0 m L.val
  have hF (L : Colength m) : grassmannianSubspace b hd (F L).val = latticeSubspace 0 m L.val :=
    subspacePoint_subspace b hd (latticeSubspace 0 m L.val)
      ((colength_iff_window_rank (asShortWindow L)).mp L.property)
  have hj : Function.Injective F := by
    intro L L' he
    apply Subtype.ext
    have hL : asShortWindow L = asShortWindow L' := by
      apply w.injective
      apply Subtype.ext
      rw [hq, hq]
      change latticeSubspace 0 m L.val = latticeSubspace 0 m L'.val
      rw [← hF L, ← hF L', he]
    exact congrArg (fun x : WindowLattice 2 0 m ↦ x.val) hL
  have hs : Function.Surjective F := by
    intro p
    let P : StableSubspaces 2 0 m := ⟨grassmannianSubspace b hd p.val, p.property⟩
    let W := w.symm P
    have ht : latticeSubspace 0 m W.val = P.val := by rw [← hq, Equiv.apply_symm_apply]
    have hr : Module.finrank ℂ (latticeSubspace 0 m W.val) = m := by
      rw [ht]
      exact grassmannianSubspace_finrank _ _ _
    let L : Colength m := ⟨W.val, (colength_iff_window_rank W).mpr hr⟩
    refine ⟨L, Subtype.ext (grassmannianSubspace_injective b hd ?_)⟩
    rw [hF]
    exact ht
  let e := Equiv.ofBijective F ⟨hj, hs⟩
  refine ⟨e, hF, fun p ↦ ?_⟩
  have ht : latticeSubspace 0 m (e.symm p).val = grassmannianSubspace b hd p.val := by
    rw [← hF (e.symm p)]
    exact congrArg (fun q : ShortPoints m ↦ grassmannianSubspace b hd q.val) (e.apply_symm_apply p)
  have hh := hpre (w (asShortWindow (e.symm p)))
  rw [Equiv.symm_apply_apply, hq] at hh
  exact hh.trans (congrArg windowInverseImage ht)

open Topology Set
open ShortWindowTopologySpecs
open GrassmannianCoordinateInclusionSpecs (extendCoordinates extendCoordinates_apply
  extendCoordinates_apply_of_notMem_range mapPoint)
open GrassmannianCoordinateInclusion (mapPoint_subspace mapPoint_range mapPoint_isClosedEmbedding)

private def colengthHomeomorphShort (m : ℕ) : Colength m ≃ₜ ShortLattice m where
  toFun L := ⟨L.val, colength_bound L.property, L.property.1,
    (colength_iff_window_rank (asShortWindow L)).mp L.property⟩
  invFun L := ⟨L.val, (colength_iff_window_rank
    ⟨L.val, by rw [zero_add]; exact L.property.1, L.property.2.1⟩).mpr L.property.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private abbrev WidePoints (m : ℕ) :=
  WindowPoints 2 (-(m : ℤ)) (2 * m) (standardBoundDimension m)

private abbrev symmetricPoint (m : ℕ) :=
  mapPoint (windowBasis 2 0 m) (windowBasis 2 (-(m : ℤ)) (2 * m))
    (windowIndexEmbedding m) (shortWindowRank m) (standardBoundRank m)

private abbrev symmetricLinearMap (m : ℕ) : Window 2 0 m →ₗ[ℂ] BoundedWindow 2 m :=
  GrassmannianCoordinateInclusionSpecs.coordinateInclusion (V := Window 2 0 m) (W := BoundedWindow 2 m)
    (windowBasis 2 0 m) (windowBasis 2 (-(m : ℤ)) (2 * m)) (windowIndexEmbedding m)

private theorem symmetricLinearMap_compare {m : ℕ} (hm : m = 1 ∨ m = 2) :
    (symmetricLinearMap m).range = standardSupport m ∧
    ∀ L : WindowLattice 2 0 m, (latticeSubspace 0 m L.val).map (symmetricLinearMap m) =
      latticeSubspace (-(m : ℤ)) (2 * m) L.val := by
  obtain ⟨q, _, _, hrange, _, hL, hzero, hshift⟩ :=
    ShortWindowTopology.windowLinearComparison m hm
  have he : symmetricLinearMap m = q.restrictScalars ℂ := by
    apply LinearMap.ext
    intro w
    apply (windowCoordinates 2 (-(m : ℤ)) (2 * m)).injective
    funext ij
    have hcoord : windowCoordinates 2 (-(m : ℤ)) (2 * m) (symmetricLinearMap m w) =
        extendCoordinates (windowIndexEmbedding m) (windowCoordinates 2 0 m w) := by
      simp only [GrassmannianCoordinateInclusionSpecs.coordinateInclusion, windowBasis,
        Module.Basis.equivFun_ofEquivFun, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
    rw [hcoord]
    by_cases hi : ij ∈ range (windowIndexEmbedding m)
    · obtain ⟨i, rfl⟩ := hi
      rw [extendCoordinates_apply, hshift]
    · rw [extendCoordinates_apply_of_notMem_range _ _ hi]
      symm
      apply hzero
      by_contra! h
      apply hi
      refine ⟨(ij.1, ⟨ij.2.val - m, by have := ij.2.isLt; omega⟩), ?_⟩
      change (ij.1, ⟨m + (ij.2.val - m), _⟩) = ij
      apply Prod.ext
      · rfl
      · exact Fin.ext (Nat.add_sub_of_le h)
  rw [he]
  exact ⟨hrange, hL⟩

private theorem symmetricPoint_isClosedEmbedding (m : ℕ) :
    IsClosedEmbedding (symmetricPoint m) :=
  mapPoint_isClosedEmbedding _ _ _ _ _

private theorem symmetricPoint_subspace {m : ℕ} (hm : m = 1 ∨ m = 2)
    (L : Colength m) (p : ShortPoints m)
    (hp : grassmannianSubspace (windowBasis 2 0 m) (shortWindowRank m) p.val =
      latticeSubspace 0 m L.val) :
    grassmannianSubspace (windowBasis 2 (-(m : ℤ)) (2 * m)) (standardBoundRank m)
      (symmetricPoint m p.val) = latticeSubspace (-(m : ℤ)) (2 * m) L.val := by
  rw [symmetricPoint, mapPoint_subspace, hp]
  exact (symmetricLinearMap_compare hm).2 (asShortWindow L)

private theorem shortPointHomeomorphism {m : ℕ} (hm : m = 1 ∨ m = 2) :
    ∃ e : Colength m ≃ₜ ShortPoints m,
      (∀ L, grassmannianSubspace (windowBasis 2 0 m) (shortWindowRank m) (e L).val =
        latticeSubspace 0 m L.val) ∧
      ∀ p, (e.symm p).val.val.restrictScalars ℂ =
        windowInverseImage (grassmannianSubspace (windowBasis 2 0 m) (shortWindowRank m) p.val) := by
  obtain ⟨e, he, hpre⟩ := shortPointComparison m
  obtain ⟨h, _, hh⟩ := ShortWindowTopology.shortWindowHomeomorphism m hm
  let a := (colengthHomeomorphShort m).trans h
  let k (p : ShortPoints m) := symmetricPoint m p.val
  let j (p : SupportedStablePoints m) : WidePoints m := p.val.val
  have hk : IsEmbedding k :=
    (symmetricPoint_isClosedEmbedding m).isEmbedding.comp IsEmbedding.subtypeVal
  have hstable : IsEmbedding (fun p : SymmetricStablePoints m ↦ (p.val : WidePoints m)) :=
    IsEmbedding.induced Subtype.val_injective
  have hj : IsEmbedding j := hstable.comp IsEmbedding.subtypeVal
  have hcomp : k ∘ e = j ∘ a := by
    funext L
    apply grassmannianSubspace_injective _ (standardBoundRank m)
    exact (symmetricPoint_subspace hm L (e L) (he L)).trans (hh (colengthHomeomorphShort m L)).symm
  have hemb : IsEmbedding e := hk.of_comp_iff.mp (hcomp ▸ hj.comp a.isEmbedding)
  exact ⟨⟨e, hemb.continuous, hemb.continuous_iff.mpr (by
      change Continuous (e ∘ e.symm)
      simpa only [e.self_comp_symm] using continuous_id)⟩, he, hpre⟩


open Topology Set TopologicalSpace
open ShortWindowTopologySpecs
open GrassmannianCoordinateInclusion (mapPoint_range)

open private boundedVal_closedEmbedding boundedPoint_embedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology
open private grassmannianChart_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

private theorem windowOperator_coordinate (a : ℤ) (m : ℕ) (w : Window 2 a m)
    (i : Fin 2) (j : Fin m) :
    windowCoordinates 2 a m (windowOperator 2 a m w) (i, j) =
      if h : 1 ≤ j.val then windowCoordinates 2 a m w (i, ⟨j.val - 1, by omega⟩) else 0 := by
  obtain ⟨z, rfl⟩ := windowMk_surjective a m w
  obtain ⟨x, rfl⟩ := (shiftedCoordinates 2 a).surjective z
  rw [windowOperator_mk, windowCoordinates_mk]
  change PowerSeries.coeff j.val (PowerSeries.X * x i) = _
  rw [← pow_one (PowerSeries.X : O), PowerSeries.coeff_X_pow_mul']
  split <;> simp [*, windowCoordinates_mk]


set_option backward.isDefEq.respectTransparency false in
private theorem scalar_subspace_coefficients (a : ℤ) (m n : ℕ)
    (w : Window 2 a m) :
    w ∈ latticeSubspace a m (scalarLattice 2 (a + (n : ℤ))) ↔
      ∀ (i : Fin 2) (j : Fin m), j.val < n → windowCoordinates 2 a m w (i, j) = 0 := by
  constructor
  · intro hw
    change ∃ y : (scalarLattice 2 a).val,
      y.val ∈ (scalarLattice 2 (a + (n : ℤ))).val ∧ windowMk a m y = w at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [scalarLattice_val] at hy
    obtain ⟨x, hx⟩ := hy
    have hyy : y = shiftedCoordinates 2 a (t ^ n • x) := by
      apply Subtype.ext
      rw [shiftedCoordinates_coe, ← shiftedInclusion_add_nat]
      exact hx.symm
    subst y
    intro i j hj
    rw [windowCoordinates_mk]
    change PowerSeries.coeff j.val (PowerSeries.X ^ n * x i) = 0
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hj)]
  · intro hw
    let x : IntegralCoordinates := fun i ↦
      PowerSeries.mk fun k ↦ if hk : k + n < m then windowCoordinates 2 a m w (i, ⟨k+n, hk⟩)
        else 0
    let y : (scalarLattice 2 a).val := shiftedCoordinates 2 a (t ^ n • x)
    change ∃ z : (scalarLattice 2 a).val, z.val ∈ (scalarLattice 2 (a + (n : ℤ))).val ∧
      windowMk a m z = w
    refine ⟨y, ?_, ?_⟩
    · rw [scalarLattice_val]
      exact ⟨x, shiftedInclusion_add_nat 2 a n x⟩
    · apply (windowCoordinates 2 a m).injective
      funext ij
      obtain ⟨i, j⟩ := ij
      change windowCoordinates 2 a m
        (windowMk a m (shiftedCoordinates 2 a (t ^ n • x))) (i, j) = _
      rw [windowCoordinates_mk]
      change PowerSeries.coeff j.val (PowerSeries.X ^ n * x i) = _
      rw [PowerSeries.coeff_X_pow_mul']
      split
      · simp [x, Nat.sub_add_cancel ‹n ≤ j.val›, j.isLt]
      · symm
        exact hw i j (Nat.lt_of_not_ge ‹¬ n ≤ j.val›)

private def verticalPivot : Pivot (Fin 2 × Fin 2) 2 :=
  ⟨Finset.univ.filter (fun p : Fin 2 × Fin 2 ↦ p.2 = 1), by decide⟩

private theorem mem_verticalPivot (i : Fin 2 × Fin 2) :
    i ∈ verticalPivot.val ↔ i.2 = 1 := by
  simp [verticalPivot]

private def verticalMatrix (s : ℂ) : Matrix (Outside verticalPivot) (Inside verticalPivot) ℂ :=
  Matrix.of fun j i ↦ if j.val = (0, 0) ∧ i.val.1 = 1 then s else 0

private theorem continuous_verticalMatrix : Continuous verticalMatrix := by
  apply continuous_matrix
  intro j i
  by_cases h : j.val = (0, 0) ∧ i.val.1 = 1
  · simp only [verticalMatrix, Matrix.of_apply, ite_eq_left h]
    exact continuous_id
  · simp only [verticalMatrix, Matrix.of_apply, ite_eq_right h]
    exact continuous_const

private def horizontalShift (s : ℂ) (u : Inside verticalPivot → ℂ) :
    Inside verticalPivot → ℂ :=
  fun j ↦ if j.val.1 = 0 then s * u ⟨(1, 1), (mem_verticalPivot _).mpr rfl⟩ else 0

set_option maxHeartbeats 800000 in
private theorem verticalGraph_apply (s : ℂ) (u : Inside verticalPivot → ℂ)
    (j : Fin 2 × Fin 2) :
    (graphMatrix verticalPivot (verticalMatrix s) *ᵥ u) j =
      if h : j.2 = 1 then u ⟨j, (mem_verticalPivot j).mpr h⟩
      else if j = (0, 0) then s * u ⟨(1, 1), (mem_verticalPivot _).mpr rfl⟩ else 0 := by
  by_cases hj : j.2 = 1
  · rw [dite_eq_left hj]
    exact graphMatrix_inside _ _ _ ⟨j, (mem_verticalPivot j).mpr hj⟩
  · let j' : Outside verticalPivot := ⟨j, fun h ↦ hj ((mem_verticalPivot j).mp h)⟩
    have hrow := graphMatrix_outside verticalPivot (verticalMatrix s) u j'
    change (graphMatrix verticalPivot (verticalMatrix s) *ᵥ u) j = _ at hrow
    rw [dite_eq_right hj, hrow]
    by_cases he : j = (0, 0)
    · subst j
      rw [ite_eq_left rfl]
      have hset (i : Inside verticalPivot) : i.val.1 = 1 ↔
          i = ⟨(1, 1), (mem_verticalPivot _).mpr rfl⟩ := by
        constructor
        · intro hi
          apply Subtype.ext
          exact Prod.ext hi ((mem_verticalPivot i.val).mp i.property)
        · intro hi
          rw [hi]
      simp [j', verticalMatrix, Matrix.mulVec, dotProduct, hset, ite_mul]
    · simp [j', verticalMatrix, Matrix.mulVec, dotProduct, he]

private abbrev ShortGrassmannianTwo :=
  GrassmannianPoints (windowBasis 2 0 2) (shortWindowRank 2)

private def deformationPoint (s : ℂ) : ShortGrassmannianTwo :=
  grassmannianChartPoint (windowBasis 2 0 2) (shortWindowRank 2)
    verticalPivot (verticalMatrix s)

private theorem deformationPoint_subspace (s : ℂ) :
    (grassmannianSubspace (windowBasis 2 0 2) (shortWindowRank 2)
      (deformationPoint s)).map (windowCoordinates 2 0 2).toLinearMap =
        (Matrix.toLin' (graphMatrix verticalPivot (verticalMatrix s))).range :=
  grassmannianChartSubspace _ _ _ _

private theorem deformationPoint_stable (s : ℂ) :
    StablePlane (windowBasis 2 0 2) (shortWindowRank 2)
      (windowOperator 2 0 2) (deformationPoint s) := by
  let b := windowCoordinates 2 0 2
  let P := grassmannianSubspace (windowBasis 2 0 2)
    (shortWindowRank 2) (deformationPoint s)
  have hp := deformationPoint_subspace s
  change P.map b.toLinearMap = _ at hp
  change P.map (windowOperator 2 0 2) ≤ P
  apply Submodule.map_le_iff_le_comap.mpr
  intro x hx
  have hbx := Submodule.mem_map_of_mem (f := b.toLinearMap) hx
  rw [hp] at hbx
  obtain ⟨u, hu⟩ := hbx
  have hcoord (j : Fin 2 × Fin 2) :
      b (windowOperator 2 0 2 x) j =
        (graphMatrix verticalPivot (verticalMatrix s) *ᵥ horizontalShift s u) j := by
    obtain ⟨i, j⟩ := j
    change windowCoordinates 2 0 2 (windowOperator 2 0 2 x) (i, j) = _
    rw [windowOperator_coordinate, verticalGraph_apply]
    have hxcoord (j' : Fin 2) :
        windowCoordinates 2 0 2 x (i,j') =
          (graphMatrix verticalPivot (verticalMatrix s) *ᵥ u) (i,j') :=
      (congrFun hu (i,j')).symm
    fin_cases j <;> simp [hxcoord, verticalGraph_apply, horizontalShift]
  have hmem : b (windowOperator 2 0 2 x) ∈ P.map b.toLinearMap := by
    rw [hp]
    exact ⟨horizontalShift s u, funext fun j ↦ (hcoord j).symm⟩
  obtain ⟨y, hy, he⟩ := hmem
  change windowOperator 2 0 2 x ∈ P
  exact (b.injective he) ▸ hy


private theorem continuous_chartPoint {M ι : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ M) (I : Pivot ι d) :
    Continuous (grassmannianChartPoint b hd I) :=
  continuous_iSup_rng (i := I) continuous_coinduced_rng

private theorem change_basis_points {M N ι : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) (f : M ≃ₗ[ℂ] N) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ M) (hd' : d ≤ Module.finrank ℂ N) :
    ∃ e : GrassmannianPoints b hd ≃ₜ GrassmannianPoints (b.map f) hd',
      ∀ p, grassmannianSubspace (b.map f) hd' (e p) =
        (grassmannianSubspace b hd p).map f.toLinearMap := by
  let forward (p : GrassmannianPoints b hd) : GrassmannianPoints (b.map f) hd' :=
    subspacePoint (b.map f) hd' ((grassmannianSubspace b hd p).map f.toLinearMap)
      ((f.finrank_map_eq _).trans (grassmannianSubspace_finrank b hd p))
  let inverse (p : GrassmannianPoints (b.map f) hd') : GrassmannianPoints b hd :=
    subspacePoint b hd ((grassmannianSubspace (b.map f) hd' p).map f.symm.toLinearMap)
      ((f.symm.finrank_map_eq _).trans (grassmannianSubspace_finrank (b.map f) hd' p))
  have hforward (p : GrassmannianPoints b hd) :
      grassmannianSubspace (b.map f) hd' (forward p) =
        (grassmannianSubspace b hd p).map f.toLinearMap :=
    subspacePoint_subspace _ _ _ _
  have hinverse (p : GrassmannianPoints (b.map f) hd') :
      grassmannianSubspace b hd (inverse p) =
        (grassmannianSubspace (b.map f) hd' p).map f.symm.toLinearMap :=
    subspacePoint_subspace _ _ _ _
  let e : GrassmannianPoints b hd ≃ GrassmannianPoints (b.map f) hd' := {
    toFun := forward
    invFun := inverse
    left_inv p := grassmannianSubspace_injective b hd (by
      rw [hinverse, hforward, ← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id])
    right_inv p := grassmannianSubspace_injective (b.map f) hd' (by
      rw [hforward, hinverse, ← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]) }
  have hcoord : (b.map f).equivFun.toLinearMap.comp f.toLinearMap = b.equivFun.toLinearMap := by
    ext x j
    simp [Module.Basis.equivFun_apply]
  have hchart (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) :
      e (grassmannianChartPoint b hd I A) = grassmannianChartPoint (b.map f) hd' I A := by
    apply grassmannianSubspace_injective (b.map f) hd'
    apply Submodule.map_injective_of_injective (b.map f).equivFun.injective
    change (grassmannianSubspace (b.map f) hd' (forward _)).map _ = _
    rw [hforward, ← Submodule.map_comp, hcoord,
      grassmannianChartSubspace, grassmannianChartSubspace]
  have hc : Continuous e := by
    change Continuous[⨆ I : Pivot ι d, TopologicalSpace.coinduced
      (grassmannianChartPoint b hd I) inferInstance, inferInstance] _
    apply continuous_iSup_dom.mpr
    intro I
    apply continuous_coinduced_dom.mpr
    convert continuous_chartPoint (b.map f) hd' I using 1
    funext A
    exact hchart I A
  have hdcont : Continuous e.symm := by
    change Continuous[⨆ I : Pivot ι d, TopologicalSpace.coinduced
      (grassmannianChartPoint (b.map f) hd' I) inferInstance, inferInstance] _
    apply continuous_iSup_dom.mpr
    intro I
    apply continuous_coinduced_dom.mpr
    convert continuous_chartPoint b hd I using 1
    funext A
    rw [Function.comp_apply, ← hchart I A, Equiv.symm_apply_apply]
  exact ⟨⟨e, hc, hdcont⟩, hforward⟩

set_option backward.isDefEq.respectTransparency false in
private theorem colength_inclusion_closed {m : ℕ} (hm : m = 1 ∨ m = 2) :
    IsClosedEmbedding (Subtype.val : Colength m → GL2Lattice) := by
  obtain ⟨h, hh, _⟩ := ShortWindowTopology.shortWindowHomeomorphism m hm
  have hcoincide : Set.range (symmetricPoint m) =
      {p : WidePoints m | grassmannianSubspace (windowBasis 2 (-(m : ℤ)) (2*m))
        (standardBoundRank m) p ≤ standardSupport m} := by
    rw [symmetricPoint, mapPoint_range, (symmetricLinearMap_compare hm).1]
  have hs : IsClosed {p : SymmetricStablePoints m |
      grassmannianSubspace (windowBasis 2 (-(m : ℤ)) (2*m)) (standardBoundRank m)
        p.val ≤ standardSupport m} := by
    change IsClosed ((Subtype.val : SymmetricStablePoints m → WidePoints m) ⁻¹'
      {p : WidePoints m | grassmannianSubspace _ _ p ≤ standardSupport m})
    have hp : IsClosed (Set.range (symmetricPoint m)) :=
      (symmetricPoint_isClosedEmbedding m).isClosed_range
    have hc : Continuous (fun p : SymmetricStablePoints m ↦ (p.val : WidePoints m)) :=
      continuous_induced_dom
    exact (hcoincide ▸ hp).preimage hc
  let j : SupportedStablePoints m → BoundedStage 2 m :=
    fun p ↦ ⟨symmetricDimension m, p.val⟩
  let F (d : WindowDimension 2 (-(m : ℤ)) (2*m)) :=
    StablePoints (windowBasis 2 (-(m : ℤ)) (2*m)) (windowDimension_le d)
      (windowOperator 2 (-(m : ℤ)) (2*m))
  let TF (d : WindowDimension 2 (-(m : ℤ)) (2*m)) : TopologicalSpace (F d) :=
    stablePointsTopology _ _ _
  have hj₀ : @IsClosedEmbedding (F (symmetricDimension m)) (BoundedStage 2 m)
      (TF _) inferInstance (@Sigma.mk _ F (symmetricDimension m)) :=
    @IsClosedEmbedding.sigmaMk _ F TF (symmetricDimension m)
  have hj : IsClosedEmbedding j := hj₀.comp hs.isClosedEmbedding_subtypeVal
  let e := (boundedPoint_embedding m).toHomeomorphOfSurjective
    (BoundedLattices.boundedStageComparison 2 m).1.surjective
  have he (L : BoundedLattice 2 m) : e L = boundedPoint L := rfl
  have hcomp : (Subtype.val : Colength m → GL2Lattice) =
      (Subtype.val : BoundedLattice 2 m → GL2Lattice) ∘ e.symm ∘ j ∘ h ∘ colengthHomeomorphShort m := by
    funext L
    change L.val = (e.symm (j (h (colengthHomeomorphShort m L)))).val
    rw [show j (h (colengthHomeomorphShort m L)) =
      boundedPoint (shortAsBounded (colengthHomeomorphShort m L)) from hh _,
      ← he, e.symm_apply_apply]
    rfl
  rw [hcomp]
  exact (boundedVal_closedEmbedding m).comp
    (e.symm.isClosedEmbedding.comp (hj.comp (h.isClosedEmbedding.comp
      (colengthHomeomorphShort m).isClosedEmbedding)))

private theorem grassmannian_singleton_closed {M ι : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ M) (p : GrassmannianPoints b hd) : IsClosed {p} := by
  change IsClosed[⨆ I : Pivot ι d,
    coinduced (grassmannianChartPoint b hd I) inferInstance] {p}
  rw [isClosed_iSup_iff]
  intro I
  rw [isClosed_coinduced]
  by_cases hp : p ∈ Set.range (grassmannianChartPoint b hd I)
  · obtain ⟨A, rfl⟩ := hp
    rw [← Set.image_singleton, Set.preimage_image_eq _ (grassmannianChart_injective b hd I)]
    exact isClosed_singleton
  · have hh : (grassmannianChartPoint b hd I) ⁻¹' {p} = ∅ := by
      ext A
      exact ⟨fun h ↦ hp ⟨A, h⟩, False.elim⟩
    rw [hh]
    exact isClosed_empty

private theorem scalar_closed : IsClosed ({scalarPoint} : Set GL2Lattice) := by
  obtain ⟨e, _, _⟩ := shortPointHomeomorphism (m := 2) (Or.inr rfl)
  let L : Colength 2 := ⟨scalarPoint, scalar_colength⟩
  let f (L : Colength 2) := (e L).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hc : Continuous f := continuous_subtype_val.comp e.continuous
  have h := (grassmannian_singleton_closed _ _ (f L)).preimage hc
  rw [← Set.image_singleton, Set.preimage_image_eq _ hf] at h
  simpa only [Set.image_singleton] using
    (colength_inclusion_closed (m := 2) (Or.inr rfl)).isClosedMap {L} h

private def deformationStable (s : ℂ) : ShortPoints 2 :=
  ⟨deformationPoint s, deformationPoint_stable s⟩

private theorem continuous_deformationStable : Continuous deformationStable := by
  apply continuous_induced_rng.mpr
  exact (continuous_chartPoint _ _ verticalPivot).comp continuous_verticalMatrix

private theorem deformationStable_zero (e : Colength 2 ≃ₜ ShortPoints 2)
    (he : ∀ L, grassmannianSubspace (windowBasis 2 0 2) (shortWindowRank 2)
      (e L).val = latticeSubspace 0 2 L.val) :
    (e.symm (deformationStable 0)).val = scalarPoint := by
  let L : Colength 2 := ⟨scalarPoint, scalar_colength⟩
  have hp : deformationStable 0 = e L := by
    apply Subtype.ext
    apply grassmannianSubspace_injective _ (shortWindowRank 2)
    rw [he]
    let P := grassmannianSubspace (windowBasis 2 0 2) (shortWindowRank 2) (deformationPoint 0)
    let S := latticeSubspace 0 2 L.val
    change P = S
    have hle : P ≤ S := by
      intro x hx
      apply (scalar_subspace_coefficients 0 2 1 x).mpr
      intro i j hj
      have hm := Submodule.mem_map_of_mem (f := (windowCoordinates 2 0 2).toLinearMap) hx
      change _ ∈ (grassmannianSubspace _ _ (deformationPoint 0)).map _ at hm
      rw [deformationPoint_subspace 0] at hm
      obtain ⟨u, hu⟩ := hm
      have hcoord : windowCoordinates 2 0 2 x (i,j) =
          (graphMatrix verticalPivot (verticalMatrix 0) *ᵥ u) (i,j) :=
        (congrFun hu (i,j)).symm
      rw [hcoord, verticalGraph_apply]
      have hj' : j ≠ 1 := by intro hh; subst j; norm_num at hj
      simp [hj']
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [grassmannianSubspace_finrank]
    exact ((colength_iff_window_rank (asShortWindow L)).mp L.property).le
  rw [hp, e.symm_apply_apply]

private theorem deformationStable_ne_scalar (e : Colength 2 ≃ₜ ShortPoints 2)
    (he : ∀ L, grassmannianSubspace (windowBasis 2 0 2) (shortWindowRank 2)
      (e L).val = latticeSubspace 0 2 L.val) {s : ℂ} (hs : s ≠ 0) :
    (e.symm (deformationStable s)).val ≠ scalarPoint := by
  intro h
  let u : Inside verticalPivot → ℂ := fun _ ↦ 1
  have hm : graphMatrix verticalPivot (verticalMatrix s) *ᵥ u ∈
      (grassmannianSubspace (windowBasis 2 0 2) (shortWindowRank 2)
        (deformationPoint s)).map (windowCoordinates 2 0 2).toLinearMap := by
    rw [deformationPoint_subspace]
    exact ⟨u, rfl⟩
  obtain ⟨x, hx, hv⟩ := hm
  have hp := he (e.symm (deformationStable s))
  rw [e.apply_symm_apply, h] at hp
  change x ∈ grassmannianSubspace _ _ (deformationStable s).val at hx
  rw [hp] at hx
  have h0 := (scalar_subspace_coefficients 0 2 1 x).mp hx 0 0 (by decide)
  have heval : windowCoordinates 2 0 2 x (0,0) =
      (graphMatrix verticalPivot (verticalMatrix s) *ᵥ u) (0,0) := congrFun hv (0,0)
  rw [h0, verticalGraph_apply] at heval
  exact hs (by simpa [u] using heval.symm)

theorem twoStepOrbits : TwoStepOrbits := by
  obtain ⟨e, he, _⟩ := shortPointHomeomorphism (m := 2) (Or.inr rfl)
  let f (s : ℂ) := (e.symm (deformationStable s)).val
  have hf : Continuous f :=
    continuous_subtype_val.comp (e.symm.continuous.comp continuous_deformationStable)
  have hscalar := scalar_closed
  have hclosed : IsClosed (colength 2) := by
    simpa only [Subtype.range_val] using
      (colength_inclusion_closed (m := 2) (Or.inr rfl)).isClosed_range
  refine ⟨fun L ↦ colength_bound L.property, scalar_orbit, twoStep_orbit_set,
    scalar_colength, scalar_orbit.symm ▸ hscalar, ?_, ?_⟩
  · rw [twoStep_orbit_set, Set.preimage_sdiff]
    have hfull : (Subtype.val : Colength 2 → GL2Lattice) ⁻¹' colength 2 = Set.univ := by
      ext L
      simp
    rw [hfull, ← Set.compl_eq_univ_sdiff]
    exact (hscalar.preimage continuous_subtype_val).isOpen_compl
  · apply le_antisymm
    · apply closure_minimal _ hclosed
      rw [twoStep_orbit_set]
      exact Set.sdiff_subset
    · intro L hL
      by_cases hx : L = scalarPoint
      · subst L
        have h0 : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) := (dense_compl_singleton 0) 0
        have hc := mem_closure_image hf.continuousAt h0
        change f 0 ∈ _ at hc
        rw [show f 0 = scalarPoint from deformationStable_zero e he] at hc
        apply closure_mono _ hc
        rintro _ ⟨s, hs, rfl⟩
        rw [twoStep_orbit_set]
        exact ⟨(e.symm (deformationStable s)).property, deformationStable_ne_scalar e he hs⟩
      · apply subset_closure
        rw [twoStep_orbit_set]
        exact ⟨hL, hx⟩


open AlgebraicGeometry CategoryTheory Topology TopologicalSpace Set
open LinearAlgebraicGroups (Points SchemeOver)
open Scheme.IdealSheafData
open GrassmannianIncidenceSpecs (incidenceDimension_le)

open private reduced_ker_eq from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels
open LinearAlgebraicGroups.GrassmannianCharts (chartMatrixEquiv chartMatrixEquiv_apply)

/-- Both reduced immersions induce the reduced scheme structure on their common image. -/
private theorem closed_image_iso {X Y Z : SchemeOver ℂ} (i : X ⟶ Z) (j : Y ⟶ Z)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left] [IsReduced X.left] [IsReduced Y.left]
    (h : Set.range i.left = Set.range j.left) :
    ∃ e : X ≅ Y, e.hom ≫ j = i := by
  have h' : i.left.ker = j.left.ker := by rw [reduced_ker_eq, reduced_ker_eq, h]
  let u := IsClosedImmersion.lift j.left i.left h'.ge
  have hu : u ≫ j.left = i.left := IsClosedImmersion.lift_fac j.left i.left h'.ge
  have : IsIso u := IsClosedImmersion.isIso_of_ker_eq _ _ _ hu h'
  let E := Over.isoMk (asIso u) (by
    change u ≫ Y.hom = X.hom
    rw [← Over.w j, ← Category.assoc, hu, Over.w])
  exact ⟨E, Over.OverMorphism.ext hu⟩

private theorem continuous_pointLocation {M ι : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ M) :
    Continuous (pointLocation : GrassmannianPoints b hd → (grassmannianCharts b hd).scheme.left) := by
  classical
  change Continuous[⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance, inferInstance] _
  apply continuous_iSup_dom.mpr
  intro I
  apply continuous_coinduced_dom.mpr
  let f := chartInclusion b hd I
  have hf : Continuous f := f.continuous
  have hc : Continuous (fun A : Matrix (Outside I) (Inside I) ℂ ↦
      MvPolynomial.pointToPoint (k := ℂ) (chartVariables I A)) := by
    apply continuous_iff_isClosed.mpr
    intro S hS
    obtain ⟨U, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus S).mp hS
    have hset : (fun A : Matrix (Outside I) (Inside I) ℂ ↦
        MvPolynomial.pointToPoint (k := ℂ) (chartVariables I A)) ⁻¹' PrimeSpectrum.zeroLocus U =
        ⋂ P : U, {A | MvPolynomial.eval (chartVariables I A) P.val = 0} := by
      ext A
      simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, MvPolynomial.pointToPoint,
        Set.subset_def, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h P
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff (chartVariables I A) P.val).mp
          (h P.val P.property)
      · intro h P hP
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff (chartVariables I A) P).mpr (h ⟨P, hP⟩)
    rw [hset]
    apply isClosed_iInter
    intro P
    apply isClosed_eq _ continuous_const
    exact (MvPolynomial.continuous_eval _).comp
      (continuous_pi fun ji ↦ (continuous_id : Continuous
        (id : Matrix (Outside I) (Inside I) ℂ → _)).matrix_elem ji.1 ji.2)
  convert hf.comp hc using 1
  funext A
  change pointLocation (((chartMatrixEquiv I complexAlgebra).symm A) ≫
    (grassmannianCharts b hd).chart I) = _
  rw [pointLocation_comp, chart_location]
  rfl

private theorem closure_range_locations (Z : SchemeOver ℂ)
    (S : Set (Points Z complexAlgebra)) :
    closure (Set.range (pointLocation (X := reducedClosureScheme Z S))) = Set.univ := by
  let X := reducedClosureScheme Z S
  let i := reducedClosureInclusion Z S
  have hi : IsClosedImmersion i.left := by
    change IsClosedImmersion (reducedClosureIdeal Z S).subschemeι
    infer_instance
  have hbase : Set.range i.left = closure (pointLocation '' S) := by
    change Set.range (reducedClosureIdeal Z S).subschemeι = _
    rw [range_subschemeι]
    exact coe_support_vanishingIdeal _
  have hmem : pointLocation '' S ⊆ i.left '' Set.range (pointLocation (X := X)) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq⟩ := (LatticeModels.pointLocation_in_closure_iff S p).mp
      (subset_closure (Set.mem_image_of_mem _ hp))
    exact ⟨pointLocation q, Set.mem_range_self _, (pointLocation_comp q i).symm.trans
      (congrArg pointLocation hq)⟩
  have hf := hi.isClosedEmbedding
  have h : Set.range i.left ⊆ i.left '' closure (Set.range (pointLocation (X := X))) := by
    rw [hbase, ← hf.closure_image_eq]
    exact closure_mono hmem
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hy, he⟩ := h (Set.mem_range_self x)
  exact hf.injective he ▸ hy

private theorem range_reducedClosureImage {Z Y : SchemeOver ℂ}
    (S : Set (Points Z complexAlgebra)) (j : reducedClosureScheme Z S ⟶ Y)
    [IsClosedImmersion j.left] :
    Set.range j.left =
      closure (pointLocation '' Set.range (fun p : Points (reducedClosureScheme Z S)
        complexAlgebra ↦ p ≫ j)) := by
  rw [← Set.image_univ, ← closure_range_locations Z S,
    ← (IsClosedImmersion.isClosedEmbedding j.left).closure_image_eq]
  congr 1
  rw [← Set.range_comp, ← Set.range_comp]
  rfl


private theorem grassmannian_reduced {M ι : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ M) : IsReduced (grassmannianCharts b hd).scheme.left := by
  let C := grassmannianCharts b hd
  let 𝒰 : C.scheme.left.OpenCover := {
    I₀ := Pivot ι d
    X := fun I ↦ (chartScheme (k := ℂ) I).left
    f := fun I ↦ (C.chart I).left
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨C.cover, C.openChart⟩ }
  apply (IsReduced.iff_of_openCover _ 𝒰).mpr
  intro I
  change IsReduced (Spec (CommRingCat.of (chartAlgebra (k := ℂ) I)))
  infer_instance

private theorem zero_stable_scheme_iso {M ι : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ M) :
    ∃ e : stableScheme b hd 0 ≅ (grassmannianCharts b hd).scheme,
      e.hom = reducedClosureInclusion _ {p | StablePlane b hd 0 p} := by
  let C := grassmannianCharts b hd
  let S : Set (GrassmannianPoints b hd) := {p | StablePlane b hd 0 p}
  let J := reducedClosureIdeal C.scheme S
  let i := reducedClosureInclusion C.scheme S
  have hi : IsClosedImmersion i.left := by
    change IsClosedImmersion J.subschemeι
    infer_instance
  have hre : IsReduced (reducedClosureScheme C.scheme S).left :=
    LatticeModels.reducedClosure_reduced _ _
  have hX : IsReduced C.scheme.left := grassmannian_reduced b hd
  let idG : C.scheme ⟶ C.scheme := 𝟙 _
  have hid : IsClosedImmersion idG.left := by change IsClosedImmersion (𝟙 C.scheme.left); infer_instance
  have hfull : Set.range i.left = Set.range idG.left := by
    change Set.range J.subschemeι = Set.range (𝟙 C.scheme.left)
    rw [range_subschemeι]
    apply le_antisymm
    · intro x _
      exact ⟨x, rfl⟩
    · intro x _
      obtain ⟨I, y, rfl⟩ := C.cover x
      change y ∈ (chartInclusion b hd I) ⁻¹' (J.support : Set C.scheme.left)
      have hz : stabilityIdeal I (operatorInCoordinates b (0 : M →ₗ[ℂ] M)) = ⊥ := by
        apply bot_unique
        rw [stabilityIdeal, Ideal.span_le]
        rintro _ ⟨⟨j, i⟩, rfl⟩
        simp [operatorInCoordinates, graphPolynomial, graphResidual]
      rw [LatticeModels.stable_chart_support b hd 0 I, hz]
      change (y : PrimeSpectrum (chartAlgebra (k := ℂ) I)) ∈
        PrimeSpectrum.zeroLocus (↑(⊥ : Ideal (chartAlgebra (k := ℂ) I)) : Set (chartAlgebra (k := ℂ) I))
      rw [PrimeSpectrum.zeroLocus_bot]
      exact Set.mem_univ _
  obtain ⟨e, he⟩ := closed_image_iso i idG hfull
  refine ⟨e, ?_⟩
  change e.hom = i
  simpa [idG] using he

set_option maxHeartbeats 600000 in
/-- Use the incidence morphism with zero lower summand and zero complement. -/
private theorem grassmannian_basis_immersion {M N ι : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) (f : M ≃ₗ[ℂ] N) {d : ℕ} (hd : d ≤ Module.finrank ℂ M)
    (hd' : d ≤ Module.finrank ℂ N) :
    ∃ a : (grassmannianCharts b hd).scheme ⟶ (grassmannianCharts (b.map f) hd').scheme,
      IsClosedImmersion a.left ∧
      ∀ p, grassmannianSubspace (b.map f) hd' (p ≫ a) =
        (grassmannianSubspace b hd p).map f.toLinearMap := by
  let Z := Fin 0 → ℂ
  let : Subsingleton Z := ⟨fun _ _ ↦ funext fun i ↦ Fin.elim0 i⟩
  let : Unique (Z × Z) := ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let e : N ≃ₗ[ℂ] M × (Z × Z) :=
    f.symm ≪≫ₗ (LinearEquiv.prodUnique (R := ℂ) (M := M) (M₂ := Z × Z)).symm
  let : Module.Finite ℂ M := Module.Finite.of_basis b
  let hz : Module.finrank ℂ Z = 0 := by simp [Z]
  obtain ⟨a, ha, hpoint⟩ := GrassmannianIncidenceSchemes.grassmannianIncidence e b (b.map f) hd
  suffices transport : ∀ (n : ℕ) (hn : n ≤ Module.finrank ℂ N), n = d →
      (∃ g : (grassmannianCharts b hd).scheme ⟶ (grassmannianCharts (b.map f) hn).scheme,
        IsClosedImmersion g.left ∧
        ∀ p, grassmannianSubspace (b.map f) hn (p ≫ g) =
          (grassmannianSubspace b hd p).map f.toLinearMap) →
      ∃ g : (grassmannianCharts b hd).scheme ⟶ (grassmannianCharts (b.map f) hd').scheme,
        IsClosedImmersion g.left ∧
        ∀ p, grassmannianSubspace (b.map f) hd' (p ≫ g) =
          (grassmannianSubspace b hd p).map f.toLinearMap by
    refine transport _ (incidenceDimension_le e hd) (by simp [hz]) ⟨a, ha, ?_⟩
    intro p
    ext w
    rw [hpoint p w, Submodule.mem_map_equiv]
    change (f.symm w ∈ grassmannianSubspace b hd p ∧ (e w).2.2 = 0) ↔ _
    exact and_iff_left (Subsingleton.elim _ _)
  intro n hn heq H
  subst n
  exact H

private theorem grassmannian_point_surjective {M N ι : Type}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) (f : M ≃ₗ[ℂ] N) {d : ℕ} (hd : d ≤ Module.finrank ℂ M)
    (hd' : d ≤ Module.finrank ℂ N)
    (a : (grassmannianCharts b hd).scheme ⟶ (grassmannianCharts (b.map f) hd').scheme)
    (ha : ∀ p, grassmannianSubspace (b.map f) hd' (p ≫ a) =
      (grassmannianSubspace b hd p).map f.toLinearMap) :
    Function.Surjective (fun p : GrassmannianPoints b hd ↦ p ≫ a) := by
  intro p
  let P := grassmannianSubspace (b.map f) hd' p
  let Q := P.map f.symm.toLinearMap
  have hr : Module.finrank ℂ Q = d :=
    (f.symm.finrank_map_eq _).trans (grassmannianSubspace_finrank _ _ _)
  refine ⟨subspacePoint b hd Q hr, grassmannianSubspace_injective _ hd' ?_⟩
  rw [ha, subspacePoint_subspace]
  change (P.map f.symm.toLinearMap).map f.toLinearMap = P
  rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]

private theorem stable_basis_iso {M N ι : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) (f : M ≃ₗ[ℂ] N) {d : ℕ} (hd : d ≤ Module.finrank ℂ M)
    (hd' : d ≤ Module.finrank ℂ N) (T : M →ₗ[ℂ] M) (T' : N →ₗ[ℂ] N)
    (hT : ∀ x, f (T x) = T' (f x)) :
    ∃ e : stableScheme b hd T ≅ stableScheme (b.map f) hd' T',
      ∀ p : Points (stableScheme b hd T) complexAlgebra,
        grassmannianSubspace (b.map f) hd'
          (p ≫ e.hom ≫ reducedClosureInclusion _ {q | StablePlane (b.map f) hd' T' q}) =
          (grassmannianSubspace b hd
            (p ≫ reducedClosureInclusion _ {q | StablePlane b hd T q})).map f.toLinearMap := by
  let b' := b.map f
  let G := (grassmannianCharts b hd).scheme
  let G' := (grassmannianCharts b' hd').scheme
  let S : Set (GrassmannianPoints b hd) := {p | StablePlane b hd T p}
  let S' : Set (GrassmannianPoints b' hd') := {p | StablePlane b' hd' T' p}
  let X := stableScheme b hd T
  let Y := stableScheme b' hd' T'
  let i : X ⟶ G := reducedClosureInclusion G S
  let j : Y ⟶ G' := reducedClosureInclusion G' S'
  obtain ⟨a, haClose, ha⟩ := grassmannian_basis_immersion b f hd hd'
  have ht : T'.comp f.toLinearMap = f.toLinearMap.comp T :=
    LinearMap.ext (fun x ↦ (hT x).symm)
  have hstable (p : GrassmannianPoints b hd) :
      StablePlane b' hd' T' (p ≫ a) ↔ StablePlane b hd T p := by
    unfold StablePlane
    rw [ha p, ← Submodule.map_comp, ht, Submodule.map_comp,
      Submodule.map_le_map_iff_of_injective f.injective]
  have hi : IsClosedImmersion i.left := by
    change IsClosedImmersion (reducedClosureIdeal G S).subschemeι
    infer_instance
  have hj : IsClosedImmersion j.left := by
    change IsClosedImmersion (reducedClosureIdeal G' S').subschemeι
    infer_instance
  let i' := i ≫ a
  have hi' : IsClosedImmersion i'.left := by
    change IsClosedImmersion (i.left ≫ a.left)
    exact IsClosedImmersion.comp i.left a.left
  have hx : IsReduced X.left := LatticeModels.reducedClosure_reduced G S
  have hy : IsReduced Y.left := LatticeModels.reducedClosure_reduced G' S'
  obtain ⟨L, hL⟩ := LatticeModels.stableSchemePointComparison b hd T
  obtain ⟨R, hR⟩ := LatticeModels.stableSchemePointComparison b' hd' T'
  have hRimage : Set.range (fun q : Points Y complexAlgebra ↦ q ≫ j) = S' := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      change StablePlane b' hd' T' (q ≫ j)
      rw [show q ≫ j = (R q).val from (hR q).symm]
      exact (R q).property
    · intro hp
      let x : StablePoints b' hd' T' := ⟨p, hp⟩
      exact ⟨R.symm x, (hR (R.symm x)).symm.trans (congrArg Subtype.val (R.apply_symm_apply x))⟩
  have hLimage : Set.range (fun q : Points X complexAlgebra ↦ q ≫ i') = S' := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      change StablePlane b' hd' T' (q ≫ i ≫ a)
      rw [← Category.assoc, hstable, ← hL]
      exact (L q).property
    · intro hp
      obtain ⟨p₀, he⟩ := grassmannian_point_surjective b f hd hd' a ha p
      change p₀ ≫ a = p at he
      have hh : StablePlane b hd T p₀ := (hstable p₀).mp (he.symm ▸ hp)
      let x : StablePoints b hd T := ⟨p₀, hh⟩
      refine ⟨L.symm x, ?_⟩
      have hz : L.symm x ≫ i = p₀ :=
        (hL (L.symm x)).symm.trans (congrArg Subtype.val (L.apply_symm_apply x))
      change L.symm x ≫ i ≫ a = p
      rw [← Category.assoc, hz, he]
  have hIL : Set.range i'.left =
      closure (pointLocation '' Set.range (fun q : Points X complexAlgebra ↦ q ≫ i')) :=
    @range_reducedClosureImage G G' S i' hi'
  have hJR : Set.range j.left =
      closure (pointLocation '' Set.range (fun q : Points Y complexAlgebra ↦ q ≫ j)) :=
    @range_reducedClosureImage G' G' S' j hj
  have hrange : Set.range i'.left = Set.range j.left := by
    rw [hIL, hJR, hLimage, hRimage]
  obtain ⟨E, hE⟩ := closed_image_iso i' j hrange
  refine ⟨E, fun p ↦ ?_⟩
  change grassmannianSubspace b' hd' (p ≫ E.hom ≫ j) = _
  rw [hE]
  exact Category.assoc p i a ▸ ha (p ≫ i)


private theorem minuscule_scheme :
    ∃ e : windowStableScheme 2 0 1 (shortDimension 1) ≅ projectiveScheme,
      ∀ q : Points (windowStableScheme 2 0 1 (shortDimension 1)) complexAlgebra,
        grassmannianSubspace projectiveBasis projectiveRank (q ≫ e.hom) =
          (windowSchemeSubspace q).map constantCoordinates.toLinearMap := by
  let b := windowBasis 2 0 1
  let hd := shortWindowRank 1
  have hz (w : Window 2 0 1) : constantCoordinates (windowOperator 2 0 1 w) =
      (0 : V →ₗ[ℂ] V) (constantCoordinates w) := by rw [one_window_operator]; simp
  obtain ⟨a, ha⟩ := stable_basis_iso b constantCoordinates hd projectiveRank _ 0 hz
  obtain ⟨i, hi⟩ := zero_stable_scheme_iso projectiveBasis projectiveRank
  refine ⟨a ≪≫ i, fun q ↦ ?_⟩
  change grassmannianSubspace projectiveBasis projectiveRank (q ≫ a.hom ≫ i.hom) = _
  rw [hi]
  exact ha q

private theorem twoStep_scheme :
    ∃ e : windowStableScheme 2 0 2 (shortDimension 2) ≅ twoStepScheme,
      ∀ q : Points (windowStableScheme 2 0 2 (shortDimension 2)) complexAlgebra,
        grassmannianSubspace twoStepBasis twoStepRank (q ≫ e.hom ≫ twoStepSchemeInGrassmannian) =
          (windowSchemeSubspace q).map twoStepCoordinates.toLinearMap :=
  stable_basis_iso (windowBasis 2 0 2) twoStepCoordinates (shortWindowRank 2) twoStepRank
    (windowOperator 2 0 2) shift two_window_operator


open Topology Set TopologicalSpace
open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver)
open Scheme.IdealSheafData
open ShortWindowTopologySpecs
open private boundedSubspace_finrank from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology

theorem minusculeProjective : MinusculeProjective := by
  refine ⟨?_, minuscule_scheme⟩
  let b := windowBasis 2 0 1
  let hd := shortWindowRank 1
  obtain ⟨e, he, hpre⟩ := shortPointHomeomorphism (m := 1) (Or.inl rfl)
  obtain ⟨a, ha⟩ := change_basis_points b constantCoordinates hd projectiveRank
  have hval : IsEmbedding (fun p : ShortPoints 1 ↦ (p.val : GrassmannianPoints b hd)) :=
    IsEmbedding.induced Subtype.val_injective
  have hs : Function.Surjective (fun p : ShortPoints 1 ↦ (p.val : GrassmannianPoints b hd)) := by
    intro p
    refine ⟨⟨p, ?_⟩, rfl⟩
    change (grassmannianSubspace b hd p).map (windowOperator 2 0 1) ≤ _
    rw [one_window_operator, Submodule.map_zero]
    exact bot_le
  let forget := hval.toHomeomorphOfSurjective hs
  let E : Colength 1 ≃ₜ ProjectivePoints := (e.trans forget).trans a
  have hE (L : Colength 1) : grassmannianSubspace projectiveBasis projectiveRank (E L) =
      (latticeSubspace 0 1 L.val).map constantCoordinates.toLinearMap := by
    change grassmannianSubspace (b.map constantCoordinates) projectiveRank (a (e L).val) = _
    rw [ha, he]
  refine ⟨E, hE, fun p ↦ ?_⟩
  have h := hE (E.symm p)
  rw [E.apply_symm_apply] at h
  rw [h, ← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
  have hh := hpre (e (E.symm p))
  rwa [e.symm_apply_apply, he] at hh

theorem twoStepStableModel : TwoStepStableModel := by
  let b := windowBasis 2 0 2
  let hd := shortWindowRank 2
  let f := twoStepCoordinates
  refine ⟨two_window_operator, ?_, LatticeModels.reducedClosure_reduced _ _, ?_, twoStep_scheme⟩
  · obtain ⟨e, he, hpre⟩ := shortPointHomeomorphism (m := 2) (Or.inr rfl)
    obtain ⟨a, ha⟩ := change_basis_points b f hd twoStepRank
    have ht : shift.comp f.toLinearMap = f.toLinearMap.comp (windowOperator 2 0 2) :=
      LinearMap.ext (fun x ↦ (two_window_operator x).symm)
    have hiff (p : GrassmannianPoints b hd) : StablePlane b hd (windowOperator 2 0 2) p ↔
        StablePlane (b.map f) twoStepRank shift (a p) := by
      unfold StablePlane
      rw [ha p, ← Submodule.map_comp, ht, Submodule.map_comp,
        Submodule.map_le_map_iff_of_injective f.injective]
    let j : ShortPoints 2 ≃ₜ TwoStepPoints := a.subtype hiff
    let E := e.trans j
    have hE (L : Colength 2) : grassmannianSubspace twoStepBasis twoStepRank (E L).val =
        (latticeSubspace 0 2 L.val).map f.toLinearMap := by
      change grassmannianSubspace (b.map f) twoStepRank (a (e L).val) = _
      rw [ha, he]
    refine ⟨E, hE, fun p ↦ ?_⟩
    have h := hE (E.symm p)
    rw [E.apply_symm_apply] at h
    rw [h, ← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
    have hh := hpre (e (E.symm p))
    rwa [e.symm_apply_apply, he] at hh
  · change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance

private abbrev asBounded {m : ℕ} (L : Colength m) :=
  shortAsBounded (colengthHomeomorphShort m L)

private def boundedColengthPoint {m : ℕ} (L : Colength m) : WidePoints m :=
  subspacePoint (windowBasis 2 (-(m : ℤ)) (2*m)) (standardBoundRank m)
    (boundedSubspace (asBounded L))
    ((boundedSubspace_finrank (L := asBounded L) L.property.1).trans
      ((colength_iff_window_rank (asShortWindow L)).mp L.property))

private theorem boundedColengthPoint_subspace {m : ℕ} (L : Colength m) :
    grassmannianSubspace (windowBasis 2 (-(m : ℤ)) (2*m)) (standardBoundRank m)
      (boundedColengthPoint L) = latticeSubspace (-(m : ℤ)) (2*m) L.val :=
  subspacePoint_subspace _ _ _ _

private theorem continuous_boundedColengthPoint {m : ℕ} (hm : m = 1 ∨ m = 2) :
    Continuous (@boundedColengthPoint m) := by
  obtain ⟨e, he, _⟩ := shortPointHomeomorphism hm
  have hf (L : Colength m) : boundedColengthPoint L = symmetricPoint m (e L).val :=
    grassmannianSubspace_injective _ (standardBoundRank m)
      ((boundedColengthPoint_subspace L).trans (symmetricPoint_subspace hm L (e L) (he L)).symm)
  simp_rw [show @boundedColengthPoint m = fun L ↦ symmetricPoint m (e L).val from funext hf]
  exact (symmetricPoint_isClosedEmbedding m).continuous.comp
    (continuous_subtype_val.comp e.continuous)

private theorem orbitPoints_eq_image {m : ℕ} {ab : DominantPair} (h : OrbitBound ab m)
    (hsub : gl2Orbit ab ⊆ colength m) :
    schubertOrbitPoints ab m h (standardBoundDimension m) =
      boundedColengthPoint '' ((Subtype.val : Colength m → GL2Lattice) ⁻¹' gl2Orbit ab) := by
  ext p
  constructor
  · rintro ⟨L, hL, hP⟩
    let Q : Colength m := ⟨L, hsub hL⟩
    refine ⟨Q, hL, grassmannianSubspace_injective _ (standardBoundRank m) ?_⟩
    rw [boundedColengthPoint_subspace]
    exact hP.symm
  · rintro ⟨L, hL, rfl⟩
    exact ⟨L.val, hL, boundedColengthPoint_subspace L⟩

private theorem orbitZariskiClosure_eq {m : ℕ} {ab : DominantPair} (hm : m = 1 ∨ m = 2)
    (hsub : gl2Orbit ab ⊆ colength m) (hdense : colength m ⊆ closure (gl2Orbit ab))
    (h : OrbitBound ab m) :
    closure (pointLocation '' schubertOrbitPoints ab m h (standardBoundDimension m)) =
      closure (pointLocation '' Set.range (@boundedColengthPoint m)) := by
  let S := (Subtype.val : Colength m → GL2Lattice) ⁻¹' gl2Orbit ab
  have hS : Dense S := by
    intro L
    apply closure_subtype.mpr
    rw [Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_val] using hsub)]
    exact hdense L.property
  let g (L : Colength m) := pointLocation (boundedColengthPoint L)
  have hc : Continuous g := (continuous_pointLocation _ (standardBoundRank m)).comp
    (continuous_boundedColengthPoint hm)
  rw [orbitPoints_eq_image h hsub, Set.image_image, ← Set.range_comp]
  change closure (g '' S) = closure (Set.range g)
  apply le_antisymm (closure_mono (Set.image_subset_range _ _))
  apply closure_minimal _ isClosed_closure
  rintro _ ⟨L, rfl⟩
  exact mem_closure_image hc.continuousAt (hS L)

private abbrev ShortScheme (m : ℕ) := windowStableScheme 2 0 m (shortDimension m)

private abbrev SymmetricScheme (m : ℕ) :=
  windowStableScheme 2 (-(m : ℤ)) (2 * m) (standardBoundDimension m)

private abbrev SymmetricGrassmannian (m : ℕ) :=
  (grassmannianCharts (windowBasis 2 (-(m : ℤ)) (2 * m)) (standardBoundRank m)).scheme

set_option backward.isDefEq.respectTransparency false in
private theorem shortScheme_inclusion (m : ℕ) :
    ∃ i : ShortScheme m ⟶ SymmetricScheme m,
      IsClosedImmersion i.left ∧
      ∀ (L : WindowLattice 2 0 m) (q : Points (ShortScheme m) complexAlgebra),
        windowSchemeSubspace q = latticeSubspace 0 m L.val →
        windowSchemeSubspace (q ≫ i) = latticeSubspace (-(m : ℤ)) (2 * m) L.val := by
  obtain ⟨d, hd, i, hi, hq⟩ := BoundedLattices.windowInclusions
     2 0 (-(m : ℤ)) m (2*m) (by omega) (by rw [boundedExponent, zero_add]) (shortDimension m)
  have h : d = standardBoundDimension m := by
    apply Fin.ext
    rw [hd, boundedExponent, zero_add, sub_self]
    simp [shortDimension, standardBoundDimension]
  subst d
  exact ⟨i, hi, hq⟩

private theorem shortScheme_colengthPoints (m : ℕ) :
    ∃ c : Points (ShortScheme m) complexAlgebra ≃ Colength m,
      ∀ q, windowSchemeSubspace q = latticeSubspace 0 m (c q).val := by
  obtain ⟨eL, hE⟩ := (BoundedLattices.windowSchemeComparison 2 0 m (shortDimension m)).2.2
  let eW : {L : WindowLattice 2 0 m // Module.finrank ℂ (latticeSubspace 0 m L.val) = m} ≃
      Colength m :=
    { toFun := fun L ↦ ⟨L.val.val, (colength_iff_window_rank L.val).mpr L.property⟩
      invFun := fun L ↦ ⟨asShortWindow L, (colength_iff_window_rank (asShortWindow L)).mp L.property⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl }
  exact ⟨eL.trans eW, hE⟩

set_option backward.isDefEq.respectTransparency false in
private theorem shortScheme_ambient (m : ℕ) :
    ∃ (i : ShortScheme m ⟶ SymmetricGrassmannian m)
      (c : Points (ShortScheme m) complexAlgebra ≃ Colength m),
      IsClosedImmersion i.left ∧
      (∀ q, windowSchemeSubspace q = latticeSubspace 0 m (c q).val) ∧
      ∀ q, q ≫ i = boundedColengthPoint (c q) := by
  obtain ⟨f, hf, hq⟩ := shortScheme_inclusion m
  obtain ⟨c, hc⟩ := shortScheme_colengthPoints m
  let j : SymmetricScheme m ⟶ SymmetricGrassmannian m :=
    windowSchemeInGrassmannian 2 (-(m : ℤ)) (2*m) (standardBoundDimension m)
  have hj : IsClosedImmersion j.left :=
    (BoundedLattices.windowSchemeComparison 2 (-(m : ℤ)) (2*m) (standardBoundDimension m)).2.1
  refine ⟨f ≫ j, c, IsClosedImmersion.comp f.left j.left, hc, fun q ↦ ?_⟩
  apply grassmannianSubspace_injective _ (standardBoundRank m)
  rw [boundedColengthPoint_subspace]
  rw [← Category.assoc]
  change windowSchemeSubspace (q ≫ f) = _
  exact hq (asShortWindow (c q)) q (hc q)

set_option backward.isDefEq.respectTransparency false in
private theorem shortScheme_ambient_range {m : ℕ}
    (i : ShortScheme m ⟶ SymmetricGrassmannian m) (hi : IsClosedImmersion i.left)
    (c : Points (ShortScheme m) complexAlgebra ≃ Colength m)
    (h : ∀ q, q ≫ i = boundedColengthPoint (c q)) :
    Set.range i.left = closure (pointLocation '' Set.range (@boundedColengthPoint m)) := by
  rw [show Set.range i.left =
      closure (pointLocation '' Set.range (fun q : Points (ShortScheme m) complexAlgebra ↦ q ≫ i)) from
    range_reducedClosureImage _ i]
  rw [show (fun q : Points (ShortScheme m) complexAlgebra ↦ q ≫ i) = @boundedColengthPoint m ∘ c
    from funext h, c.surjective.range_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem shortScheme_realization (m : ℕ) (ab : DominantPair)
    (hclosure : ∀ h : OrbitBound ab m,
      closure (pointLocation '' schubertOrbitPoints ab m h (standardBoundDimension m)) =
        closure (pointLocation '' Set.range (@boundedColengthPoint m))) :
    SchubertRealization m ab := by
  intro h
  let G := SymmetricGrassmannian m
  let S := schubertOrbitPoints ab m h (standardBoundDimension m)
  let X := schubertScheme ab m h (standardBoundDimension m)
  let j : X ⟶ G := reducedClosureInclusion G S
  have hX : IsReduced X.left := LatticeModels.reducedClosure_reduced G S
  have hj : IsClosedImmersion j.left := by
    change IsClosedImmersion (reducedClosureIdeal G S).subschemeι
    infer_instance
  obtain ⟨i, c, hi, hc, hq⟩ := shortScheme_ambient m
  have hP : IsReduced (ShortScheme m).left :=
    (BoundedLattices.windowSchemeComparison 2 0 m (shortDimension m)).1
  have hrange : Set.range i.left = Set.range j.left := by
    rw [shortScheme_ambient_range i hi c hq, ← hclosure h]
    change _ = Set.range (reducedClosureIdeal G S).subschemeι
    rw [range_subschemeι]
    exact (coe_support_vanishingIdeal (Closeds.closure (pointLocation '' S))).symm
  obtain ⟨e, he⟩ := @closed_image_iso (ShortScheme m) X G i j hi hj hP hX hrange
  refine ⟨hX, hj, e, c, fun q ↦ ⟨hc q, ?_⟩⟩
  change grassmannianSubspace _ (standardBoundRank m) (q ≫ e.hom ≫ j) = _
  rw [he, hq, boundedColengthPoint_subspace]

private theorem minusculeBound : OrbitBound minusculePair 1 := by
  intro i
  fin_cases i <;> decide

private theorem twoStepBound : OrbitBound twoStepPair 2 := by
  intro i
  fin_cases i <;> decide

theorem smallSchubertSchemes : SmallSchubertSchemes := by
  have h₁ := minusculeOrbit.1
  have h₂ := twoStep_orbit_set
  have hc := twoStepOrbits.2.2.2.2.2.2
  refine ⟨⟨minusculeBound, shortScheme_realization 1 minusculePair ?_⟩,
    ⟨twoStepBound, shortScheme_realization 2 twoStepPair ?_⟩⟩
  · exact orbitZariskiClosure_eq (Or.inl rfl) h₁.ge (h₁.le.trans subset_closure)
  · exact orbitZariskiClosure_eq (Or.inr rfl) (h₂.le.trans Set.sdiff_subset) hc.ge


end

end RepTheorySurvey.Geometric.MinusculeAndTwoStep
