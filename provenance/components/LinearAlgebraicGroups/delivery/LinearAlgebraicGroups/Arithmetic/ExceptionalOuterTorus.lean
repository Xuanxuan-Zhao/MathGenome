import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Determinant
import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus
import LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
import LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates
import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactCentralizer
import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterAlgebraicBorelPair
import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactPinning
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

noncomputable section

open Topology
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn asMatrix)
open LinearAlgebraicGroups.Specs.ExceptionalOuterTorus

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus

variable {H : Type*} [Group H] [TopologicalSpace H]

private theorem compactTorus_map (T : Subgroup H) (hT : IsCompactTorus T)
    (e : H ≃* H) (he : Continuous e) (he' : Continuous e.symm) :
    IsCompactTorus (T.map e.toMonoidHom) := by
  obtain ⟨n, f, hf, hf'⟩ := hT
  have heT : Continuous (e.subgroupMap T) := by
    apply continuous_induced_rng.mpr
    exact he.comp continuous_subtype_val
  have heT' : Continuous (e.subgroupMap T).symm := by
    apply continuous_induced_rng.mpr
    exact he'.comp continuous_subtype_val
  exact ⟨n, f.trans (e.subgroupMap T), heT.comp hf, hf'.comp heT'⟩

private theorem maximalCompactTorus_map (C : Set H) (T : Subgroup H)
    (hT : IsMaximalCompactTorus C T) (e : H ≃* H)
    (he : Continuous e) (he' : Continuous e.symm)
    (hC : Set.MapsTo e C C) (hC' : Set.MapsTo e.symm C C) :
    IsMaximalCompactTorus C (T.map e.toMonoidHom) := by
  refine ⟨compactTorus_map T hT.1 e he he', ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hC (hT.2.1 hx)
  · intro V hV hVC hle
    let V' := V.map e.symm.toMonoidHom
    have hV' : (V' : Set H) ⊆ C := by
      rintro _ ⟨x, hx, rfl⟩
      exact hC' (hVC hx)
    have hTV' : T ≤ V' := by
      intro x hx
      exact ⟨e x, hle ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have hEq : V' = T := hT.2.2 V' (compactTorus_map V hV e.symm he' he) hV' hTV'
    ext x
    rw [Subgroup.mem_map_equiv, ← hEq, Subgroup.mem_map_equiv,
      MulEquiv.symm_symm, e.apply_symm_apply]

variable [IsTopologicalGroup H]

private theorem conj_mapsTo_identityComponent {J : Subgroup H} {g : H} (hg : g ∈ J) :
    Set.MapsTo (MulAut.conj g) (identityComponent J) (identityComponent J) := by
  rintro _ ⟨x, hx, rfl⟩
  let gJ : J := ⟨g, hg⟩
  have hcont : Continuous (MulAut.conj gJ) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hx' : MulAut.conj gJ x ∈ connectedComponent (1 : J) := by
    simpa only [map_one] using hcont.mapsTo_connectedComponent (1 : J) hx
  exact ⟨MulAut.conj gJ x, hx', rfl⟩

/-- Conjugacy of the maximal tori in the identity component gives a normalizer
representative in every component. -/
theorem normalizerRepresentative {J S : Subgroup H}
    (hS : IsMaximalCompactTorus (identityComponent J) S)
    (hconj : ∀ U : Subgroup H,
      IsMaximalCompactTorus (identityComponent J) U →
      ∃ u ∈ identityComponent J, Conjugates u U S)
    {g : H} (hg : g ∈ J) :
    ∃ n ∈ J, n ∈ Subgroup.normalizer (S : Set H) ∧ g * n⁻¹ ∈ identityComponent J := by
  let e : H ≃* H := MulAut.conj g
  have he : Continuous e := (continuous_const.mul continuous_id).mul continuous_const
  have he' : Continuous e.symm := (continuous_const.mul continuous_id).mul continuous_const
  have he'J : Set.MapsTo e.symm (identityComponent J) (identityComponent J) := by
    intro x hx
    simpa only [e, MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv] using
      conj_mapsTo_identityComponent (J := J) (J.inv_mem hg) hx
  let U := S.map e.toMonoidHom
  have hU : IsMaximalCompactTorus (identityComponent J) U :=
    maximalCompactTorus_map _ S hS e he he' (conj_mapsTo_identityComponent hg) he'J
  obtain ⟨u, hu, huS⟩ := hconj U hU
  obtain ⟨uJ, huJ, rfl⟩ := hu
  refine ⟨(uJ : H) * g, J.mul_mem uJ.property hg, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    change (MulAut.conj (uJ : H)) '' ((MulAut.conj g) '' (S : Set H)) = (S : Set H) at huS
    have hcomp : (MulAut.conj (uJ : H)) ∘ (MulAut.conj g) =
        (MulAut.conj ((uJ : H) * g) : H → H) := by
      funext x
      simp only [Function.comp_apply, MulAut.conj_apply, mul_inv_rev, mul_assoc]
    rw [Set.image_image] at huS
    change Set.image ((MulAut.conj (uJ : H)) ∘ (MulAut.conj g)) (S : Set H) = (S : Set H) at huS
    rwa [hcomp] at huS
  · have huInv := inv_mem_connectedComponent_one huJ
    exact ⟨uJ⁻¹, huInv, by simp [mul_inv_rev, ← mul_assoc]⟩

theorem fixedNormalizerRepresentatives_of_conjugacy (hconj : FixedTorusConjugacy) :
    FixedNormalizerRepresentatives := by
  intro G i hG hsc htype ω θ houter S hS g hg
  let : IsTopologicalGroup (PointsIn i ℂ) :=
    IsInducing.isTopologicalGroup (asMatrix i ℂ) (.induced _)
  exact normalizerRepresentative hS
    (fun U hU => hconj G i hG hsc htype ω θ houter U S hU hS) hg


section MaximalTorusExistence

open Filter
open Specs.ArchimedeanLieChart (ClosedSubgroupChart expUnit exponentialLines)
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
open scoped Matrix.Norms.Operator

variable {P R : Type*} [Group P] [TopologicalSpace P]
  [NormedRing R]

private theorem bot_isCompactTorus : IsCompactTorus (⊥ : Subgroup P) := by
  let e : (Fin 0 → Circle) ≃* (⊥ : Subgroup P) :=
    { Equiv.ofUnique _ _ with map_mul' := fun _ _ => Subsingleton.elim _ _ }
  refine ⟨0, e, ?_, ?_⟩
  · rw [show (⇑e : (Fin 0 → Circle) → (⊥ : Subgroup P)) = fun _ => 1 from
      Subsingleton.elim _ _]
    exact continuous_const
  · rw [show (⇑e.symm : (⊥ : Subgroup P) → Fin 0 → Circle) = fun _ => 1 from
      Subsingleton.elim _ _]
    exact continuous_const

private theorem compact_image_of_torus {T : Subgroup P} (hT : IsCompactTorus T)
    (m : P →* Rˣ) (hm : Continuous m) : IsCompact (T.map m : Set Rˣ) := by
  obtain ⟨n, e, he, _⟩ := hT
  have hcont : Continuous (fun x => m ((e x : T) : P)) :=
    hm.comp (continuous_subtype_val.comp he)
  have hRange : Set.range (fun x => m ((e x : T) : P)) = (T.map m : Set Rˣ) := by
    ext g
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, (e x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm ⟨x, hx⟩, congrArg (fun y : T => m y) (e.apply_symm_apply _)⟩
  rw [← hRange]
  exact isCompact_range hcont

private theorem connectedSpace_image_of_torus {T : Subgroup P} (hT : IsCompactTorus T)
    (m : P →* Rˣ) (hm : Continuous m) : ConnectedSpace (T.map m) := by
  obtain ⟨n, e, he, _⟩ := hT
  let f := (m.subgroupMap T).comp e.toMonoidHom
  have hf : Continuous f := continuous_induced_rng.mpr
    (hm.comp (continuous_subtype_val.comp he))
  have hsurj : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    refine ⟨e.symm ⟨x, hx⟩, Subtype.ext ?_⟩
    exact congrArg (fun y : T => m y) (e.apply_symm_apply _)
  exact hsurj.connectedSpace hf

variable [NormedAlgebra ℝ R] [CompleteSpace R]

private theorem chart_tangent_mono {U V : Subgroup Rˣ} (h : U ≤ V)
    (cU : ClosedSubgroupChart U) (cV : ClosedSubgroupChart V) :
    cU.tangent ≤ cV.tangent := by
  intro x hx
  exact (cV.mem_tangent x).2 fun t => h ((cU.mem_tangent x).1 hx t)

private theorem le_of_expLines {J U : Subgroup Rˣ} (C : ClosedSubgroupChart U)
    [ConnectedSpace U] (h : ∀ x : R, x ∈ C.tangent → x ∈ exponentialLines J) :
    U ≤ J := by
  let U₀ := J.subgroupOf U
  have hOne : (1 : U) ∈ C.expOpen.target := by
    have h0 := C.expOpen.map_source C.zero_mem
    have he : C.expOpen 0 = (1 : U) := Subtype.ext (by simpa using C.exp_chart 0 C.zero_mem)
    simpa only [he] using h0
  have hOpen : IsOpen (U₀ : Set U) := by
    apply U₀.isOpen_of_mem_nhds (g := 1)
    refine mem_of_superset (C.expOpen.open_target.mem_nhds hOne) ?_
    intro g hg
    let x := C.expOpen.symm g
    have he := C.exp_chart x (C.expOpen.map_target hg)
    rw [C.expOpen.right_inv hg] at he
    change (g : Rˣ) ∈ J
    rw [he]
    simpa only [one_smul] using h x x.property 1
  have hEq : (U₀ : Set U) = Set.univ :=
    (show IsClopen (U₀ : Set U) from ⟨U₀.isClosed_of_isOpen hOpen, hOpen⟩).eq_univ ⟨1, U₀.one_mem⟩
  intro g hg
  have hx : (⟨g, hg⟩ : U) ∈ (U₀ : Set U) := hEq.symm ▸ Set.mem_univ _
  exact hx

private theorem eq_of_le_of_chart_tangent_eq {U V : Subgroup Rˣ} (h : U ≤ V)
    [ConnectedSpace V] (cU : ClosedSubgroupChart U) (cV : ClosedSubgroupChart V)
    (hUV : cU.tangent = cV.tangent) : U = V :=
  le_antisymm h (le_of_expLines cV fun x hx => (cU.mem_tangent x).mp (hUV.symm ▸ hx))

variable [FiniteDimensional ℝ R]

/-- In a finite-dimensional faithful matrix realization, the dimensions of
the tangent spaces of compact tori are bounded. A torus of largest dimension
inside a set containing the identity is maximal there. -/
theorem exists_maximalCompactTorus_of_embedding
    (m : P →* Rˣ) (hm : IsEmbedding m) (C : Set P) (hC : 1 ∈ C) :
    ∃ T : Subgroup P, IsMaximalCompactTorus C T := by
  classical
  let X := {T : Subgroup P // IsCompactTorus T ∧ (T : Set P) ⊆ C}
  let chart (T : X) : ClosedSubgroupChart (T.val.map m) :=
    (closedSubgroupExponential R (T.val.map m)
      (compact_image_of_torus T.property.1 m hm.continuous).isClosed).some
  let d (T : X) := Module.finrank ℝ (chart T).tangent
  have hBound (T : X) : d T ≤ Module.finrank ℝ R := (chart T).tangent.finrank_le
  have hX : Nonempty X :=
    ⟨⟨⊥, bot_isCompactTorus, fun x hx => (Subgroup.mem_bot.mp hx).symm ▸ hC⟩⟩
  have hFinite : (Set.range d).Finite := (Set.finite_Iic _).subset (by
    rintro _ ⟨T, rfl⟩
    exact hBound T)
  obtain ⟨_, ⟨T, rfl⟩, hMax⟩ := hFinite.exists_maximal (Set.range_nonempty d)
  refine ⟨T, T.property.1, T.property.2, ?_⟩
  intro V hV hVC hTV
  let V' : X := ⟨V, hV, hVC⟩
  have hTV' : T.val.map m ≤ V'.val.map m := Subgroup.map_mono hTV
  have hdim : d V' ≤ d T := by
    by_contra! hn
    exact (not_le_of_gt hn) (hMax (Set.mem_range_self V') hn.le)
  have hEq := Submodule.eq_of_le_of_finrank_le (chart_tangent_mono hTV' (chart T) (chart V')) hdim
  let : ConnectedSpace (V'.val.map m) := connectedSpace_image_of_torus hV m hm.continuous
  exact (Subgroup.map_injective hm.injective
    (eq_of_le_of_chart_tangent_eq hTV' (chart T) (chart V') hEq)).symm

open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups

theorem maximalFixedTorusExistence : MaximalFixedTorusExistence := by
  intro G i _ _ _ ω θ _
  exact exists_maximalCompactTorus_of_embedding (asMatrix i ℂ)
    (asMatrix_isClosedEmbedding i ℂ).isEmbedding _ ⟨1, mem_connectedComponent, rfl⟩

end MaximalTorusExistence


section FixedCoordinates

variable {M : Type*} [Group M]

/-- The fixed points of the diagram permutation on the torus are the image of
the fixed real space. The full integral lattice lets the chosen real lifts
have equal coordinates on each orbit. -/
theorem diagramFixed_eq_image (f : E6Space →+ Additive M) (δ : MulAut M)
    (hker : ∀ x, f x = 0 ↔ x ∈ e6Lattice)
    (hδ : ∀ x, f (e6Diagram x) = Additive.ofMul (δ (f x).toMul)) :
    {t ∈ Set.range (fun x => (f x).toMul) | δ t = t} =
      (fun x => (f x).toMul) '' foldedSpace := by
  ext t
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    have hdiff : e6Diagram x - x ∈ e6Lattice := (hker _).mp (by
      rw [map_sub, hδ, hx]
      exact sub_self _)
    obtain ⟨a, ha⟩ := hdiff
    let y : E6Space := fun j => Int.fract (x j)
    have hy : y ∈ foldedSpace := by
      change e6Diagram y = y
      funext j
      apply Int.fract_eq_fract.mpr
      exact ⟨a j, (congrFun ha j).symm⟩
    have hyx : y - x ∈ e6Lattice := by
      refine ⟨fun j => -⌊x j⌋, ?_⟩
      funext j
      change ((-⌊x j⌋ : ℤ) : ℝ) = x j - (⌊x j⌋ : ℝ) - x j
      push_cast
      ring
    have hzero := (hker _).mpr hyx
    rw [map_sub, sub_eq_zero] at hzero
    exact ⟨y, hy, congrArg Additive.toMul hzero⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change e6Diagram x = x at hx
    simpa only [hx, toMul_ofMul] using (congrArg Additive.toMul (hδ x)).symm

end FixedCoordinates


section CorootCoordinates

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators Matrix
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing characterValue)
open Specs.IntegralModels (MatrixRealization)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private unitPointHom unitPointHom_apply pointHom_injective
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private characterUnit characterUnitOnPoints characterUnit_cocharacter characterValue_eq_unit
  from LinearAlgebraicGroups.RootData.RootGroups

variable {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G} {A : AdditiveLine ℂ}
variable (M : MarkedPair G A)

private def pointMap {Q : GroupScheme ℂ} (f : Q ⟶ M.P.pair.G.val) :
    GroupPoints Q complexTest →* PointsIn i ℂ :=
  (LinearAlgebraicGroups.baseChangePointGroupEquiv ℂ G.val complexTest).toMonoidHom.comp
    (((groupPointsFunctor ℂ).map (f ≫ M.comparison.hom)).app complexTest).hom

private theorem pointMap_apply {Q : GroupScheme ℂ} (f : Q ⟶ M.P.pair.G.val)
    (x : GroupPoints Q complexTest) :
    pointMap (i := i) M f x = M.onPoints (i := i) f x := rfl

private abbrev TorusPoints := GroupPoints M.P.pair.T.group complexTest

private def cocharacterEvaluation {Q : GroupScheme ℂ} (c : Cocharacter Q) :
    ℂˣ →* GroupPoints Q complexTest :=
  (((groupPointsFunctor ℂ).map c).app complexTest).hom.comp (unitPointHom complexTest)

private theorem cocharacterEvaluation_apply {Q : GroupScheme ℂ} (c : Cocharacter Q) (z : ℂˣ) :
    cocharacterEvaluation c z = cocharacterPoint c complexTest z := by
  simp only [cocharacterEvaluation, MonoidHom.comp_apply, unitPointHom_apply]
  rfl

theorem torusPoint_add (x y : E6Space) :
    M.torusPoint (x + y) = M.torusPoint x * M.torusPoint y := by
  letI := M.datum.comm
  letI : IsMulCommutative (TorusPoints M) :=
    (isCommMonObj_iff_isMulCommutative _).mp M.datum.comm _
  letI : CommGroup (TorusPoints M) :=
    { (inferInstance : Group (TorusPoints M)) with mul_comm := mul_comm' }
  change (List.ofFn _).prod = (List.ofFn _).prod * (List.ofFn _).prod
  simp only [List.prod_ofFn, Pi.add_apply, mul_add, Circle.exp_add,
    ← cocharacterEvaluation_apply, map_mul, Finset.prod_mul_distrib]

theorem markedExp_add (x y : E6Space) :
    M.exp (i := i) (x + y) = M.exp (i := i) x * M.exp (i := i) y := by
  simp only [MarkedPair.exp, ← pointMap_apply, torusPoint_add, map_mul]

private theorem characterUnit_torusPoint (χ : Character M.P.pair.T.group) (x : E6Space) :
    characterUnit χ complexTest (M.torusPoint x) =
      Circle.toUnits (Circle.exp
        (2 * Real.pi * ∑ j, (pairing M.P.pair.T.group χ (M.coroot j) : ℝ) * x j)) := by
  let f := characterUnitOnPoints χ complexTest
  change f (M.torusPoint x) = _
  unfold MarkedPair.torusPoint
  rw [map_list_prod, List.map_ofFn, List.prod_ofFn, Finset.mul_sum]
  have hCircle (v : Fin 6 → ℝ) :
      Circle.exp (∑ j, v j) = ∏ j, Circle.exp (v j) :=
    (map_sum Circle.expHom _ _)
  rw [hCircle, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change characterUnit χ complexTest _ = _
  rw [characterUnit_cocharacter, ← map_zpow, ← Circle.exp_intCast_mul]
  congr 2
  ring

/-- Evaluation of the actual root character on the marked coroot circles. -/
theorem markedRootValue (α : Root M.P.pair.T) (x : E6Space) :
    characterValue α.val complexTest (M.torusPoint x) =
      (Circle.exp (2 * Real.pi * ∑ j, M.rootValues α j * x j) : ℂ) := by
  rw [characterValue_eq_unit, characterUnit_torusPoint]
  rfl

open Specs.AbsoluteDynkinTypes (CartanRoots PreservesCartan reflectCoordinates simpleCharacter)

private lemma e6Cartan_symm (j k : Fin 6) :
    CartanMatrix.E 6 j k = CartanMatrix.E 6 k j := by
  simp [CartanMatrix.E, eq_comm, or_comm, or_left_comm, or_assoc]

private lemma e6CartanRoots_first {p : (Fin 6 → ℤ) × (Fin 6 → ℤ)}
    (hp : CartanRoots (CartanMatrix.E 6) p) :
    p.1 = (CartanMatrix.E 6) *ᵥ p.2 := by
  let L : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) := Matrix.mulVecLin (CartanMatrix.E 6)
  change p.1 = L p.2
  have hs (j : Fin 6) : L (Pi.single j 1) = simpleCharacter (CartanMatrix.E 6) j := by
    ext i
    change (∑ k, CartanMatrix.E 6 i k * (Pi.single j 1 : Fin 6 → ℤ) k) = CartanMatrix.E 6 i j
    simp [Pi.single_apply, mul_ite]
  induction hp with
  | simple j => exact (hs j).symm
  | neg _ h => simpa only [map_neg] using congrArg Neg.neg h
  | @reflect j p _ h =>
    have hpj : p.1 j = ∑ k, p.2 k * CartanMatrix.E 6 k j := by
      rw [h]
      change (∑ k, CartanMatrix.E 6 j k * p.2 k) = _
      apply Finset.sum_congr rfl
      intro k _
      rw [e6Cartan_symm j k, mul_comm]
    change p.1 - p.1 j • simpleCharacter (CartanMatrix.E 6) j =
      L (p.2 - (∑ k, p.2 k * CartanMatrix.E 6 k j) • Pi.single j 1)
    rw [map_sub, map_smul, hs, ← hpj, ← h]

private lemma e6RootValue_of_pair {p : (Fin 6 → ℤ) × (Fin 6 → ℤ)}
    (hp : CartanRoots (CartanMatrix.E 6) p) (j : Fin 6) :
    (p.1 j : ℝ) = e6Inner (Pi.single j 1) (fun k => (p.2 k : ℝ)) := by
  rw [e6CartanRoots_first hp]
  change ((∑ k, CartanMatrix.E 6 j k * p.2 k : ℤ) : ℝ) = _
  push_cast
  simp [e6Inner, Pi.single_apply, ite_mul]

theorem markedCoordinates
    (hL : Specs.SimplyConnectedLattice.corootLattice M.datum = ⊤)
    (hC : letI := M.datum.comm
      PreservesCartan (RootData.integralCartan M.datum.datum.rootDatum M.datum.base)
        (CartanMatrix.E 6) M.numbering) :
    letI := M.datum.comm
    (∃ b : Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)),
      ∀ j, b j = Additive.ofMul (M.coroot j)) ∧
    Set.range M.rootValues = (fun α j => e6Inner (Pi.single j 1) α) '' e6Roots := by
  letI := M.datum.comm
  let D := M.datum.datum
  letI := D.finiteRoots
  letI := D.reduced
  obtain ⟨b, e, hb, he, _, hr⟩ :=
    LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes.cartanCoordinates
      D.rootDatum M.datum.base hL (CartanMatrix.E 6) M.numbering hC
  have hb' (j : Fin 6) : b j = Additive.ofMul (M.coroot j) := hb j
  have hx (α : Root M.P.pair.T) (j : Fin 6) :
      e (D.rootDatum.root α) j = pairing M.P.pair.T.group α.val (M.coroot j) := by
    have hp := he (D.rootDatum.root α) (b j)
    have hsum : (∑ k, b.equivFun (b j) k * e (D.rootDatum.root α) k) =
        e (D.rootDatum.root α) j := by
      simp [Module.Basis.equivFun_self, Pi.single_apply, ite_mul]
    have hpair : D.rootDatum.toLinearMap (D.rootDatum.root α) (b j) =
        pairing M.P.pair.T.group α.val (M.coroot j) := by
      rw [D.root_eq, hb' j, D.pairing_eq]
    exact hsum.symm.trans (hp.symm.trans hpair)
  refine ⟨⟨b, hb'⟩, ?_⟩
  ext y
  constructor
  · rintro ⟨α, rfl⟩
    let p := (e (D.rootDatum.root α), b.equivFun (D.rootDatum.coroot α))
    have hp : CartanRoots (CartanMatrix.E 6) p := by
      change p ∈ {p | CartanRoots (CartanMatrix.E 6) p}
      rw [← hr]
      exact ⟨α, rfl⟩
    refine ⟨(fun j => (p.2 j : ℝ)), ⟨p, hp, rfl⟩, ?_⟩
    funext j
    exact (e6RootValue_of_pair hp j).symm.trans (congrArg Int.cast (hx α j))
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    have hp' : p ∈ Set.range (fun α => (e (D.rootDatum.root α), b.equivFun (D.rootDatum.coroot α))) :=
      hr.symm ▸ hp
    obtain ⟨α, rfl⟩ := hp'
    refine ⟨α, ?_⟩
    funext j
    exact (congrArg Int.cast (hx α j).symm).trans (e6RootValue_of_pair hp j)


private theorem torusInclusion_injective :
    Function.Injective (pointMap (i := i) M M.P.pair.T.inclusion) := by
  intro x y h
  apply pointHom_injective M.P.pair.T complexTest
  let e := (Grp.forget (SchemeOver ℂ)).mapIso M.comparison
  apply (cancel_mono e.hom).mp
  have h' := (LinearAlgebraicGroups.baseChangePointGroupEquiv ℂ G.val complexTest).injective h
  change x ≫ (M.P.pair.T.inclusion ≫ M.comparison.hom).hom.hom =
    y ≫ (M.P.pair.T.inclusion ≫ M.comparison.hom).hom.hom at h'
  change (x ≫ M.P.pair.T.inclusion.hom.hom) ≫ M.comparison.hom.hom.hom =
    (y ≫ M.P.pair.T.inclusion.hom.hom) ≫ M.comparison.hom.hom.hom
  exact (Category.assoc _ _ _).trans (h'.trans (Category.assoc _ _ _).symm)

private theorem corootCircle_eq_one (r : ℝ) :
    Circle.exp (2 * Real.pi * r) = 1 ↔ ∃ n : ℤ, r = n := by
  rw [Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0)
      (hn.trans (mul_comm _ _))⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, mul_comm _ _⟩

/-- The kernel of the marked coroot exponential is the full integral
coroot lattice when the indexed coroots are a basis. -/
theorem markedExp_eq_one
    (b : letI := M.datum.comm; Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j)) (x : E6Space) :
    M.exp (i := i) x = 1 ↔ x ∈ e6Lattice := by
  letI := M.datum.comm
  let D := M.datum.datum
  constructor
  · intro hx
    have ht : M.torusPoint x = 1 := by
      apply torusInclusion_injective (i := i) M
      simpa only [map_one, pointMap_apply, MarkedPair.exp] using hx
    have h (j : Fin 6) : Circle.exp (2 * Real.pi * x j) = 1 := by
      let l := (LinearMap.proj j).comp b.equivFun.toLinearMap
      let χ := Additive.toMul (D.rootDatum.toLinearMap.toPerfPair.symm l)
      have hχ (k : Fin 6) : pairing M.P.pair.T.group χ (M.coroot k) =
          (Pi.single j 1 : Fin 6 → ℤ) k := by
        rw [← D.pairing_eq, ← hb k]
        change (D.rootDatum.toLinearMap.toPerfPair (D.rootDatum.toLinearMap.toPerfPair.symm l))
          (b k) = _
        rw [LinearEquiv.apply_symm_apply]
        simp [l, Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
      have hv := characterUnit_torusPoint M χ x
      change characterUnitOnPoints χ complexTest (M.torusPoint x) = _ at hv
      rw [ht, map_one] at hv
      simp only [hχ, Int.cast_ite, Int.cast_one, Int.cast_zero, Pi.single_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hv
      apply Subtype.ext
      exact congrArg (Units.val : ℂˣ → ℂ) hv.symm
    choose z hz using fun j => (corootCircle_eq_one (x j)).mp (h j)
    exact ⟨z, (funext hz).symm⟩
  · rintro ⟨z, rfl⟩
    change pointMap (i := i) M M.P.pair.T.inclusion (M.torusPoint _) = 1
    suffices h : M.torusPoint (fun j => (z j : ℝ)) = 1 by rw [h, map_one]
    have h (j : Fin 6) : Circle.exp (2 * Real.pi * (z j : ℝ)) = 1 :=
      (corootCircle_eq_one _).mpr ⟨z j, rfl⟩
    simp only [MarkedPair.torusPoint, h, map_one, ← cocharacterEvaluation_apply, map_one,
      List.ofFn_const, List.prod_replicate, one_pow]



open Specs.AbsoluteDynkinTypes (E6Reflection)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints)
open Specs.Pinning (PinnedIso)

private theorem reflection_involutive : Function.Involutive E6Reflection := by
  change ∀ j : Fin 6, E6Reflection (E6Reflection j) = j
  decide

/-- The diagram lift acts on the marked exponential by permuting the
simple-coroot coordinates. -/
theorem markedExp_diagram (d : PinnedIso M.P M.P) (δ : MulAut (PointsIn i ℂ))
    (hδ : ActsOnComplexPoints (i := i)
      (Aut.of (M.comparison.symm ≪≫ d.group ≪≫ M.comparison)) δ)
    (hd : ∀ j, M.coroot j ≫ d.torus.hom = M.coroot (E6Reflection j)) (x : E6Space) :
    δ (M.exp (i := i) x) = M.exp (i := i) (e6Diagram x) := by
  letI := M.datum.comm
  letI : IsMulCommutative (TorusPoints M) :=
    (isCommMonObj_iff_isMulCommutative _).mp M.datum.comm _
  letI : CommGroup (TorusPoints M) :=
    { (inferInstance : Group (TorusPoints M)) with mul_comm := mul_comm' }
  let dT := (((groupPointsFunctor ℂ).map d.torus.hom).app complexTest).hom
  have hCoroot (j : Fin 6) (u : ℂˣ) :
      dT (cocharacterPoint (M.coroot j) complexTest u) =
        cocharacterPoint (M.coroot (E6Reflection j)) complexTest u := by
    rw [← hd j]
    simp only [dT, cocharacterPoint, Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  have htorus : dT (M.torusPoint x) = M.torusPoint (e6Diagram x) := by
    simp only [MarkedPair.torusPoint, List.prod_ofFn, map_prod, hCoroot]
    apply Fintype.prod_equiv E6Reflection
    intro j
    rw [show e6Diagram x (E6Reflection j) = x j from congrArg x (reflection_involutive j)]
  change δ (M.onPoints (i := i) M.P.pair.T.inclusion (M.torusPoint x)) = _
  rw [show M.exp (i := i) (e6Diagram x) =
      M.onPoints (i := i) M.P.pair.T.inclusion (dT (M.torusPoint x)) from
    congrArg (M.onPoints M.P.pair.T.inclusion) htorus.symm]
  unfold MarkedPair.onPoints
  rw [hδ]
  have hmap :
      (M.P.pair.T.inclusion ≫ M.comparison.hom) ≫
          (M.comparison.symm ≪≫ d.group ≪≫ M.comparison).hom =
        d.torus.hom ≫ (M.P.pair.T.inclusion ≫ M.comparison.hom) := by
    change (M.P.pair.T.inclusion ≫ M.comparison.hom) ≫
          ((M.comparison.inv ≫ d.group.hom) ≫ M.comparison.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using congrArg (· ≫ M.comparison.hom) d.torus_comm
  have h := congrArg (fun f : M.P.pair.T.group ⟶ complexGroup G =>
    ((groupPointsFunctor ℂ).map f).app complexTest (M.torusPoint x)) hmap
  exact congrArg (baseChangePoint ℝ ℂ G.val.X complexTest) (by
    simp only [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply] at h
    exact h)

open private continuous_of_coordinates from
  LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
open private coordinateMap from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private coordinateMap_of_map from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open LinearAlgebraicGroups.CocharacterDynamics (unitCoordinates unitPoint)
open Specs.DiagonalizableGroups (IntegerCharacters)

private theorem continuous_coroot_evaluation {Q : GroupScheme ℂ}
    (f : Q ⟶ M.P.pair.G.val) (c : Cocharacter Q) :
    Continuous (fun z : ℂˣ => M.onPoints (i := i) f (cocharacterPoint c complexTest z)) := by
  obtain ⟨_, iC, _, e, he, _⟩ :=
    LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G i
  let B := CommAlgCat.of ℂ (MonoidAlgebra ℂ IntegerCharacters)
  let fC := (c ≫ f ≫ M.comparison.hom).hom.hom
  have h := continuous_of_coordinates iC B fC (unitPoint complexTest) (by
    intro a
    change Continuous (fun z : ℂˣ => (coordinateMap (k := ℂ) (A := complexTest) (B := B)
      ((testSpec ℂ).map (CommAlgCat.ofHom (unitCoordinates complexTest z)).op)).hom a)
    simp_rw [coordinateMap_of_map]
    change Continuous (fun z : ℂˣ => unitCoordinates complexTest z a)
    simp only [unitCoordinates, MonoidAlgebra.lift_apply', RingHom.id_apply,
      Algebra.algebraMap_self]
    apply continuous_finsetSum
    intro m _
    apply continuous_const.mul
    exact Units.continuous_val.comp (continuous_id.zpow _))
  refine (e.continuous.comp h).congr fun z => ?_
  apply Over.OverMorphism.ext
  refine (he (unitPoint complexTest z ≫ fC)).trans ?_
  have hmap :
      (((groupPointsFunctor ℂ).map (c ≫ f ≫ M.comparison.hom)).app complexTest)
          (unitPoint complexTest z) =
        (((groupPointsFunctor ℂ).map (f ≫ M.comparison.hom)).app complexTest)
          (cocharacterPoint c complexTest z) := by
    simp only [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply, cocharacterPoint]
  exact congrArg (fun p => (baseChangePoint ℝ ℂ G.val.X complexTest p).left) hmap

private theorem continuous_circleToUnits : Continuous Circle.toUnits := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  simp only [← map_inv]
  exact continuous_subtype_val.comp continuous_inv

/-- The marked exponential is continuous in the given complex-point topology. -/
theorem markedExp_continuous : Continuous (M.exp (i := i)) := by
  let : IsTopologicalGroup (PointsIn i ℂ) :=
    IsInducing.isTopologicalGroup (asMatrix i ℂ) (.induced _)
  let f := pointMap (i := i) M M.P.pair.T.inclusion
  unfold MarkedPair.exp MarkedPair.torusPoint
  simp only [← pointMap_apply, map_list_prod, List.map_ofFn]
  let a (j : Fin 6) (x : E6Space) := f (cocharacterPoint (M.coroot j) complexTest
    (Circle.toUnits (Circle.exp (2 * Real.pi * x j))))
  have h (j : Fin 6) : Continuous (a j) :=
    (continuous_coroot_evaluation (i := i) M M.P.pair.T.inclusion (M.coroot j)).comp
      (continuous_circleToUnits.comp
        (Circle.exp.continuous.comp (continuous_const.mul (continuous_apply j))))
  change Continuous (fun x : E6Space => (List.ofFn (fun j : Fin 6 => a j x)).prod)
  have hList (l : List (Fin 6)) : Continuous (fun x : E6Space => (l.map (fun j => a j x)).prod) := by
    induction l with
    | nil => exact continuous_const
    | cons j l ih => exact (h j).mul ih
  simpa only [← List.ofFn_eq_map] using hList (List.finRange 6)


open private splitTorus_points_ext from LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates
open private characterEvaluation from LinearAlgebraicGroups.RootData.RootGroups

/-- The product of the marked coroots on arbitrary complex torus coordinates. -/
def torusFromUnits (z : Fin 6 → ℂˣ) : TorusPoints M :=
  (List.ofFn (fun j => cocharacterPoint (M.coroot j) complexTest (z j))).prod

private theorem characterUnit_torusFromUnits (χ : Character M.P.pair.T.group) (z : Fin 6 → ℂˣ) :
    characterUnit χ complexTest (torusFromUnits M z) =
      ∏ j, z j ^ pairing M.P.pair.T.group χ (M.coroot j) := by
  change characterUnitOnPoints χ complexTest (torusFromUnits M z) = _
  simp only [torusFromUnits, map_list_prod, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  exact characterUnit_cocharacter χ (M.coroot j) complexTest (z j)

/-- A marked basis of the cocharacter lattice parametrizes the entire
complex split torus, using the actual product of the coroot morphisms. -/
theorem torusFromUnits_bijective
    (b : letI := M.datum.comm; Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j)) :
    Function.Bijective (torusFromUnits M) := by
  letI := M.datum.comm
  let D := M.datum.datum
  let a := b.dualBasis.map D.rootDatum.toLinearMap.toPerfPair.symm
  have ha (j k : Fin 6) :
      pairing M.P.pair.T.group (a j).toMul (M.coroot k) = (Pi.single j 1 : Fin 6 → ℤ) k := by
    rw [← D.pairing_eq, ← hb k]
    change D.rootDatum.toLinearMap.toPerfPair
      (D.rootDatum.toLinearMap.toPerfPair.symm (b.dualBasis j)) (b k) = _
    rw [LinearEquiv.apply_symm_apply]
    simp [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hcoord (z : Fin 6 → ℂˣ) (j : Fin 6) :
      characterUnit (a j).toMul complexTest (torusFromUnits M z) = z j := by
    rw [characterUnit_torusFromUnits, Finset.prod_eq_single j]
    · rw [ha, Pi.single_eq_same, zpow_one]
    · intro k _ hk
      simp only [ha, Pi.single_eq_of_ne hk, zpow_zero]
    · simp
  constructor
  · intro u v huv
    funext j
    rw [← hcoord u j, ← hcoord v j, huv]
  · intro p
    let z (j : Fin 6) := characterUnit (a j).toMul complexTest p
    use z
    apply splitTorus_points_ext M.P.pair.split complexTest
    let F (q : TorusPoints M) :=
      (characterEvaluation complexTest q).toAdditive.toIntLinearMap
    have heq : F (torusFromUnits M z) = F p := by
      apply a.ext
      intro j
      exact hcoord z j
    intro χ
    exact congrArg Additive.toMul (LinearMap.congr_fun heq (Additive.ofMul χ))


private def conjugateInverseUnit (z : ℂˣ) : ℂˣ :=
  (Units.map Complex.conjAe.toMonoidHom z)⁻¹

private theorem conjugateInverseUnit_eq_self (z : ℂˣ) :
    conjugateInverseUnit z = z ↔ ‖(z : ℂ)‖ = 1 := by
  let w := Units.map Complex.conjAe.toMonoidHom z
  have hn : w * z = 1 ↔ ‖(z : ℂ)‖ = 1 := by
    have hc : (w * z : ℂˣ).val = (‖(z : ℂ)‖ ^ 2 : ℝ) := by
      change Complex.conjAe (z : ℂ) * (z : ℂ) = _
      rw [mul_comm, Complex.conjAe_coe]
      simpa only [Complex.ofReal_pow] using Complex.mul_conj' (z : ℂ)
    constructor
    · intro h
      rw [h, Units.val_one] at hc
      have hs : (1 : ℝ) = ‖(z : ℂ)‖ ^ 2 := by exact_mod_cast hc
      nlinarith [norm_nonneg (z : ℂ)]
    · intro h
      apply Units.ext
      rw [hc, h]
      norm_num
  change w⁻¹ = z ↔ _
  rw [← hn]
  constructor
  · intro h
    rw [← h, mul_inv_cancel]
  · intro h
    calc
      w⁻¹ = w⁻¹ * 1 := (mul_one _).symm
      _ = w⁻¹ * (w * z) := by rw [h]
      _ = z := by simp

private theorem exists_coroot_angle (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ x : ℝ, Circle.toUnits (Circle.exp (2 * Real.pi * x)) = z := by
  let c : Circle := ⟨(z : ℂ), mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨y, hy⟩ := Circle.exp_surjective c
  refine ⟨y / (2 * Real.pi), ?_⟩
  rw [mul_div_cancel₀ _ (by positivity), hy]
  exact Units.ext rfl

/-- Compact conjugation acting by coordinatewise conjugate inversion makes
the marked coroot circles surjective onto the compact part of the torus. -/
theorem markedExp_range_of_conjugateInversion
    (b : letI := M.datum.comm; Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (ω : MulAut (PointsIn i ℂ))
    (hω : ∀ u : Fin 6 → ℂˣ,
      ω (M.onPoints (i := i) M.P.pair.T.inclusion (torusFromUnits M u)) =
        M.onPoints (i := i) M.P.pair.T.inclusion (torusFromUnits M (conjugateInverseUnit ∘ u))) :
    Set.range (M.exp (i := i)) =
      (Specs.ExceptionalCompactInner.fixedSubgroup ω : Set (PointsIn i ℂ)) ∩
        Set.range (M.onPoints (i := i) M.P.pair.T.inclusion) := by
  let p := M.onPoints (i := i) M.P.pair.T.inclusion
  let w (x : E6Space) (j : Fin 6) := Circle.toUnits (Circle.exp (2 * Real.pi * x j))
  have hExp (x : E6Space) : M.exp (i := i) x = p (torusFromUnits M (w x)) := rfl
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    have he : conjugateInverseUnit ∘ w x = w x := by
      funext j
      apply (conjugateInverseUnit_eq_self _).mpr
      exact (Circle.exp _).norm_coe
    refine ⟨?_, ⟨torusFromUnits M (w x), (hExp x).symm⟩⟩
    change ω (M.exp (i := i) x) = M.exp (i := i) x
    rw [hExp, hω, he]
  · rintro ⟨hfix, y, rfl⟩
    obtain ⟨u, rfl⟩ := (torusFromUnits_bijective M b hb).2 y
    have hfix' : ω (p (torusFromUnits M u)) = p (torusFromUnits M u) := hfix
    rw [hω] at hfix'
    have he : conjugateInverseUnit ∘ u = u := (torusFromUnits_bijective M b hb).1
      (torusInclusion_injective (i := i) M hfix')
    have hn (j : Fin 6) : ‖((u j : ℂˣ) : ℂ)‖ = 1 :=
      (conjugateInverseUnit_eq_self _).mp (congrFun he j)
    choose x hx using fun j => exists_coroot_angle (u j) (hn j)
    exact ⟨x, (hExp x).trans (congrArg (p ∘ torusFromUnits M) (funext hx))⟩


end CorootCoordinates


section CompactLieCentralizers

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- An involution with central fixed subalgebra forces a compact Lie algebra
to be abelian. The invariant positive form may be the restriction of the
negative Killing form of a larger compact Lie algebra. -/
theorem lie_eq_zero_of_central_fixed (θ : L ≃ₗ⁅ℝ⁆ L)
    (hθ : Function.Involutive θ) (B : L →ₗ[ℝ] L →ₗ[ℝ] ℝ)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆)
    (hcentral : ∀ x : L, θ x = x → ∀ y : L, ⁅x, y⁆ = 0)
    (x y : L) : ⁅x, y⁆ = 0 := by
  have hLeft (a b : L) : ⁅θ a, b⁆ = -⁅a, b⁆ := by
    have h : θ (a + θ a) = a + θ a := by rw [map_add, hθ, add_comm]
    have hz := hcentral (a + θ a) h b
    rw [add_lie, add_comm, add_eq_zero_iff_eq_neg] at hz
    exact hz
  have hRight (a b : L) : ⁅a, θ b⁆ = -⁅a, b⁆ := by
    calc
      ⁅a, θ b⁆ = -⁅θ b, a⁆ := (lie_skew a (θ b)).symm
      _ = ⁅b, a⁆ := by rw [hLeft, neg_neg]
      _ = -⁅a, b⁆ := (lie_skew b a).symm
  have hFixed : θ ⁅x, y⁆ = ⁅x, y⁆ := by
    rw [LieEquiv.map_lie, hLeft, hRight, neg_neg]
  by_contra hNonzero
  have h := hpos ⁅x, y⁆ hNonzero
  have hz : ⁅y, ⁅x, y⁆⁆ = 0 := by
    rw [← lie_skew y ⁅x, y⁆, hcentral _ hFixed, neg_zero]
  rw [hInv, hz, map_zero] at h
  exact (lt_irrefl _) h

end CompactLieCentralizers

section CompactAbelianQuotients

open Filter Module

variable {V D : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup D] [TopologicalSpace D] [CompactSpace D]

private theorem span_ker_eq_top (f : V →+ D) (hf : IsQuotientMap f) :
    Submodule.span ℝ (f.ker : Set V) = ⊤ := by
  by_contra h
  obtain ⟨l, hl, hlker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr h) inferInstance
  have hle : f.ker ≤ l.toAddMonoidHom.ker := by
    intro x hx
    have hx' := Submodule.mem_map_of_mem (f := l) (Submodule.subset_span hx)
    rwa [hlker, Submodule.mem_bot] at hx'
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f hf.surjective
  let q : D → ℝ := QuotientAddGroup.lift f.ker l.toAddMonoidHom hle ∘ e.symm
  have hq (x : V) : q (f x) = l x := by
    change QuotientAddGroup.lift f.ker l.toAddMonoidHom hle (e.symm (e (x : V ⧸ f.ker))) = l x
    rw [e.symm_apply_apply]
    rfl
  have hc : Continuous q := hf.continuous_iff.mpr (by
    simpa only [Function.comp_def, hq] using l.continuous_of_finiteDimensional)
  have hsurj : Function.Surjective l := by
    obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
      by_contra! hz
      exact hl (LinearMap.ext fun x => hz x)
    intro y
    refine ⟨(y / l x) • x, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨f x, hq x⟩
  exact (not_compactSpace_iff.mpr inferInstance) (hqs.compactSpace hc)

/-- The compact quotient of a finite-dimensional real vector space by a
discrete additive kernel is a product of unit circles. -/
private theorem compactQuotient_circleProduct (f : V →+ D) (hf : IsQuotientMap f)
    [DiscreteTopology f.ker] :
    ∃ (n : ℕ) (e : Additive (Fin n → Circle) ≃+ D), Continuous e ∧ Continuous e.symm := by
  let L : Submodule ℤ V := f.ker.toIntSubmodule
  let : DiscreteTopology L := inferInstanceAs (DiscreteTopology f.ker)
  let : IsZLattice ℝ L := ⟨span_ker_eq_top f hf⟩
  let n := finrank ℤ L
  let b : Basis (Fin n) ℤ L := Module.finBasis ℤ L
  let c := b.ofZLatticeBasis ℝ L
  let T := Additive (Fin n → Circle)
  let q : V →+ T :=
    { toFun := fun x j => Circle.exp (2 * Real.pi * c.equivFun x j)
      map_zero' := funext fun j => by
        change Circle.exp (2 * Real.pi * c.equivFun (0 : V) j) = 1
        simp
      map_add' := fun x y => funext fun j => by
        change Circle.exp (2 * Real.pi * c.equivFun (x + y) j) = _
        simp only [map_add, Pi.add_apply, mul_add, Circle.exp_add]
        rfl }
  have hq (x : V) (j : Fin n) :
      (q x).toMul j = Circle.exp (2 * Real.pi * c.equivFun x j) := rfl
  have hqC : Continuous q := continuous_pi fun j =>
    Circle.exp.continuous.comp (continuous_const.mul
      ((continuous_apply j).comp c.equivFun.toLinearMap.continuous_of_finiteDimensional))
  have hqS : Function.Surjective q := by
    intro y
    refine ⟨c.equivFun.symm (fun j => (Complex.arg (y.toMul j)) / (2 * Real.pi)), funext fun j => ?_⟩
    change (q (c.equivFun.symm (fun j => (Complex.arg (y.toMul j)) / (2 * Real.pi)))).toMul j =
      y.toMul j
    rw [hq, LinearEquiv.apply_symm_apply]
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hπ, Circle.exp_arg]
  have hqK : q.ker = f.ker := by
    ext x
    have hL : x ∈ f.ker ↔ x ∈ Submodule.span ℤ (Set.range c) := by
      change x ∈ L ↔ _
      rw [b.ofZLatticeBasis_span ℝ L]
    rw [hL, c.mem_span_iff_repr_mem ℤ]
    constructor
    · intro hx j
      have h : (q x).toMul j = 1 :=
        congrArg (fun y : T => y.toMul j) (AddMonoidHom.mem_ker.mp hx)
      rw [hq, corootCircle_eq_one] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨z, hz.symm⟩
    · intro hx
      apply AddMonoidHom.mem_ker.mpr
      funext j
      change (q x).toMul j = 1
      rw [hq, corootCircle_eq_one]
      obtain ⟨z, hz⟩ := hx j
      exact ⟨z, hz.symm⟩
  have hqQ : IsQuotientMap q :=
    (AddMonoidHom.isOpenMap_of_sigmaCompact q hqS hqC).isQuotientMap hqC hqS
  let eF := QuotientAddGroup.liftEquiv f.ker hf.surjective rfl
  let eQ := QuotientAddGroup.liftEquiv f.ker hqS hqK.symm
  let e := eQ.symm.trans eF
  have hc (x : V) : e (q x) = f x := by
    change eF (eQ.symm (eQ (x : V ⧸ f.ker))) = _
    rw [eQ.symm_apply_apply]
    rfl
  have hc' (x : V) : e.symm (f x) = q x := e.symm_apply_eq.mpr (hc x).symm
  exact ⟨n, e, hqQ.continuous_iff.mpr (by
    simpa only [Function.comp_def, hc] using hf.continuous),
    hf.continuous_iff.mpr (by simpa only [Function.comp_def, hc'] using hqC)⟩

end CompactAbelianQuotients

section AbelianMatrixSubgroups

open Filter NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
variable {U : Subgroup Rˣ} (C : ClosedSubgroupChart U)

private theorem tangent_commute (hU : ∀ g h : U, Commute g h) (x y : C.tangent) :
    Commute (x : R) (y : R) := by
  have hx := (C.mem_tangent x).mp x.property
  have hy := (C.mem_tangent y).mp y.property
  have hY : HasDerivAt (fun s : ℝ => (expUnit (s • (y : R))).val) (y : R) 0 := by
    simpa using hasDerivAt_exp_smul_const (y : R) (0 : ℝ)
  have hConst (t : ℝ) : conjugate (expUnit (t • (x : R))) (y : R) = y := by
    let g := expUnit (t • (x : R))
    have hD := (hY.const_mul (g : R)).mul_const (g⁻¹ : Rˣ).val
    have hfun (s : ℝ) : (g : R) * (expUnit (s • (y : R))).val * (g⁻¹ : Rˣ).val =
        (expUnit (s • (y : R))).val := by
      let z := expUnit (s • (y : R))
      have hu : Commute g z := (hU ⟨g, hx t⟩ ⟨z, hy s⟩).map U.subtype
      change (g * z * g⁻¹).val = z.val
      rw [hu.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact (hD.congr_of_eventuallyEq (Eventually.of_forall fun s => (hfun s).symm)).unique hY
  have hD := (conjugation_derivative (x : R) (y : R)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => (hConst t).symm)
  exact sub_eq_zero.mp (hD.unique (hasDerivAt_const _ _))

private def abelianExponential [CommGroup U] (hU : ∀ g h : U, Commute g h) :
    C.tangent →+ Additive U where
  toFun x := Additive.ofMul ⟨expUnit (x : R), by
    simpa only [one_smul] using (C.mem_tangent x).mp x.property 1⟩
  map_zero' := by
    change (⟨expUnit ((0 : C.tangent) : R), _⟩ : U) = 1
    exact Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by
    apply Units.ext
    simp only [Submodule.coe_add]
    apply exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (tangent_commute C hU x y) <;>
      rw [expSeries_radius_eq_top] <;> exact edist_lt_top _ _)

private theorem abelianExponential_surjective [CommGroup U] [ConnectedSpace U]
    (hU : ∀ g h : U, Commute g h) : Function.Surjective (abelianExponential C hU) := by
  let f := abelianExponential C hU
  have hchart (x : C.tangent) (hx : x ∈ C.expOpen.source) :
      f x = Additive.ofMul (C.expOpen x) := Subtype.ext (C.exp_chart x hx).symm
  have hOne : (0 : Additive U) ∈ C.expOpen.target := by
    change (1 : U) ∈ C.expOpen.target
    have h0 := C.expOpen.map_source C.zero_mem
    have he : C.expOpen 0 = (1 : U) := Subtype.ext (by simpa using C.exp_chart 0 C.zero_mem)
    simpa only [he] using h0
  have hOpen : IsOpen (f.range : Set (Additive U)) := by
    apply f.range.isOpen_of_mem_nhds (g := 0)
    refine mem_of_superset (C.expOpen.open_target.mem_nhds hOne) ?_
    intro g hg
    refine ⟨C.expOpen.symm g, ?_⟩
    rw [hchart _ (C.expOpen.map_target hg), C.expOpen.right_inv hg]
    rfl
  let : ConnectedSpace (Additive U) := inferInstanceAs (ConnectedSpace U)
  have hAll : (f.range : Set (Additive U)) = Set.univ :=
    (show IsClopen (f.range : Set (Additive U)) from ⟨f.range.isClosed_of_isOpen hOpen, hOpen⟩).eq_univ
      ⟨0, f.range.zero_mem⟩
  intro g
  have : g ∈ (f.range : Set (Additive U)) := hAll.symm ▸ Set.mem_univ _
  exact this

private theorem abelianExponential_discreteKer [CommGroup U] (hU : ∀ g h : U, Commute g h) :
    DiscreteTopology (abelianExponential C hU).ker := by
  let f := abelianExponential C hU
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have hEq : (Subtype.val : f.ker → C.tangent) ⁻¹' C.expOpen.source = {0} := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · change (x : C.tangent) ∈ C.expOpen.source at hx
      have he : C.expOpen (x : C.tangent) = C.expOpen 0 := by
        apply Subtype.ext
        rw [C.exp_chart _ hx, C.exp_chart _ C.zero_mem]
        exact congrArg (fun t : Additive U => (t.toMul : Rˣ))
          ((AddMonoidHom.mem_ker.mp x.property).trans f.map_zero.symm)
      exact Set.mem_singleton_iff.mpr (Subtype.ext (C.expOpen.injOn hx C.zero_mem he))
    · rw [Set.mem_singleton_iff.mp hx]
      exact C.zero_mem
  rw [← hEq]
  exact C.expOpen.open_source.preimage continuous_subtype_val

/-- A compact connected abelian matrix subgroup is a compact torus in
the induced topology. -/
theorem compactTorus_of_abelianMatrixSubgroup
    [FiniteDimensional ℝ R] [ConnectedSpace U] [CompactSpace U]
    (C : ClosedSubgroupChart U) (hU : ∀ g h : U, Commute g h) : IsCompactTorus U := by
  letI : CommGroup U := { (inferInstance : Group U) with mul_comm := fun x y => (hU x y).eq }
  let f := abelianExponential C hU
  have hc : Continuous f := continuous_induced_rng.mpr
    (continuous_expUnit.comp continuous_subtype_val)
  have hs := abelianExponential_surjective C hU
  let : DiscreteTopology f.ker := abelianExponential_discreteKer C hU
  let : CompactSpace (Additive U) := inferInstanceAs (CompactSpace U)
  let : T2Space (Additive U) := inferInstanceAs (T2Space U)
  have hq : IsQuotientMap f := (AddMonoidHom.isOpenMap_of_sigmaCompact f hs hc).isQuotientMap hc hs
  obtain ⟨n, e, he, he'⟩ := compactQuotient_circleProduct f hq
  let e' : (Fin n → Circle) ≃* U :=
    { toEquiv := e.toEquiv
      map_mul' := fun x y => e.map_add (Additive.ofMul x) (Additive.ofMul y) }
  exact ⟨n, e', he, he'⟩

end AbelianMatrixSubgroups


section MaximalTorusTangent

open Filter NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
open private exp_add_commuting from LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private theorem expUnit_add_of_commute {x y : R} (h : Commute x y) :
    expUnit (x + y) = expUnit x * expUnit y := by
  apply Units.ext
  simp only [expUnit_val, Units.val_mul]
  exact exp_add_commuting h

private theorem expUnit_commute {x y : R} (h : Commute x y) :
    Commute (expUnit x) (expUnit y) := by
  change expUnit x * expUnit y = expUnit y * expUnit x
  rw [← expUnit_add_of_commute h, add_comm, expUnit_add_of_commute h.symm]

private def expLine (x : R) : Multiplicative ℝ →* Rˣ where
  toFun t := expUnit (t.toAdd • x)
  map_one' := by change expUnit ((0 : ℝ) • x) = 1; simp
  map_mul' t s := by
    change expUnit ((t.toAdd + s.toAdd) • x) = _
    rw [add_smul, expUnit_add_of_commute (((Commute.refl x).smul_left t.toAdd).smul_right s.toAdd)]

/-- The tangent of a maximal compact torus contains every direction of the
ambient compact matrix subgroup commuting with its tangent. -/
theorem maximalTorus_tangent_centralizer [FiniteDimensional ℝ R]
    {J S : Subgroup Rˣ} (hJ : IsCompact (J : Set Rˣ))
    (hS : IsMaximalCompactTorus (J : Set Rˣ) S) (C : ClosedSubgroupChart S)
    {x : R} (hx : x ∈ exponentialLines J) (hcomm : ∀ y : C.tangent, Commute x (y : R)) :
    x ∈ C.tangent := by
  obtain ⟨n, e, he, _⟩ := hS.1
  letI : CommGroup S := {
    (inferInstance : Group S) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [← map_mul, mul_comm, map_mul] }
  let : ConnectedSpace S := e.surjective.connectedSpace he
  have hSexp : Function.Surjective (abelianExponential C (fun a b => mul_comm a b)) :=
    abelianExponential_surjective C _
  have hcross (a : S) (t : Multiplicative ℝ) : Commute (a : Rˣ) (expLine x t) := by
    obtain ⟨y, hy⟩ := hSexp (Additive.ofMul a)
    have hy' : expUnit (y : R) = (a : Rˣ) :=
      congrArg (fun v : Additive S => (v.toMul : Rˣ)) hy
    rw [← hy']
    exact expUnit_commute ((hcomm y).smul_left t.toAdd).symm
  let f := S.subtype.noncommCoprod (expLine x) hcross
  let L := f.range.topologicalClosure
  have hle : f.range ≤ J := by
    rintro _ ⟨⟨a, t⟩, rfl⟩
    exact J.mul_mem (hS.2.1 a.property) (hx t.toAdd)
  have hLJ : L ≤ J := f.range.topologicalClosure_minimal hle hJ.isClosed
  have hLclosed : IsClosed (L : Set Rˣ) := f.range.isClosed_topologicalClosure
  let : CompactSpace L :=
    isCompact_iff_compactSpace.mp (hJ.of_isClosed_subset hLclosed hLJ)
  let : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have hLcon : IsConnected (L : Set Rˣ) := by
    have ht : Continuous (fun a : S × Multiplicative ℝ => a.2.toAdd • x) :=
      (show Continuous (fun a : S × Multiplicative ℝ => a.2.toAdd) from
        continuous_snd).smul continuous_const
    have hf : Continuous f := continuous_fst.subtype_val.mul (continuous_expUnit.comp ht)
    exact (isConnected_range hf).closure
  let : ConnectedSpace L := isConnected_iff_connectedSpace.mp hLcon
  have hLt : IsCompactTorus L := compactTorus_of_abelianMatrixSubgroup
    (closedSubgroupExponential R L hLclosed).some (fun a b => mul_comm' a b)
  have hSL : S ≤ L := by
    intro a ha
    apply f.range.le_topologicalClosure
    refine ⟨(⟨a, ha⟩, 1), ?_⟩
    change a * expLine x 1 = a
    rw [map_one, mul_one]
  have hLS : L = S := hS.2.2 L hLt hLJ hSL
  apply (C.mem_tangent x).mpr
  intro t
  rw [← hLS]
  apply f.range.le_topologicalClosure
  refine ⟨(1, Multiplicative.ofAdd t), ?_⟩
  change 1 * expUnit (t • x) = expUnit (t • x)
  exact one_mul _

end MaximalTorusTangent

section HaarAverage
open Topology MeasureTheory Module

variable {P V : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Averaging a positive symmetric form gives an invariant form for a
continuous finite-dimensional real representation of a compact group. -/
theorem invariantBilinear_of_compact (ρ : P →* (V ≃ₗ[ℝ] V))
    (hρ : ∀ x : V, Continuous (fun g : P => ρ g x)) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = B y x) ∧
      (∀ x, x ≠ 0 → 0 < B x x) ∧
      ∀ g x y, B (ρ g x) (ρ g y) = B x y := by
  letI : MeasurableSpace P := borel P
  letI : BorelSpace P := ⟨rfl⟩
  let μ : Measure P := Measure.haar
  let b := Module.finBasis ℝ V
  let B₀ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    ∑ j, (b.coord j).smulRight (b.coord j)
  have hB₀ (x y : V) : B₀ x y = ∑ j, b.coord j x * b.coord j y := by
    simp [B₀, LinearMap.smulRight_apply, smul_eq_mul]
  have hSymm (x y : V) : B₀ x y = B₀ y x := by simp [hB₀, mul_comm]
  have hPos (x : V) (hx : x ≠ 0) : 0 < B₀ x x := by
    rw [hB₀]
    have hj : ∃ j, b.coord j x ≠ 0 := by
      by_contra! h
      apply hx
      apply b.repr.injective
      ext j
      simpa using h j
    obtain ⟨j, hj⟩ := hj
    apply Finset.sum_pos' (fun k _ => mul_self_nonneg _) ⟨j, Finset.mem_univ _, ?_⟩
    exact mul_self_pos.mpr hj
  let F (x y : V) (g : P) := B₀ (ρ g⁻¹ x) (ρ g⁻¹ y)
  have hF (x y : V) : Continuous (F x y) := by
    simp only [F, hB₀]
    apply continuous_finsetSum
    intro j _
    have hc := (b.coord j).continuous_of_finiteDimensional
    exact (hc.comp ((hρ x).comp continuous_inv)).mul (hc.comp ((hρ y).comp continuous_inv))
  have hInt (x y : V) : Integrable (F x y) μ :=
    (hF x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let b₁ (x : V) : V →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∫ g, F x y g ∂μ
      map_add' := fun y z => by
        simpa only [F, map_add] using integral_add (hInt x y) (hInt x z)
      map_smul' := fun t y => by
        simp only [F, map_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul] }
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := b₁
      map_add' := fun x y => LinearMap.ext fun z => by
        simpa only [b₁, F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]
          using integral_add (hInt x z) (hInt y z)
      map_smul' := fun t x => LinearMap.ext fun z => by
        simp only [b₁, F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          map_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul] }
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x y
    change (∫ g, F x y g ∂μ) = ∫ g, F y x g ∂μ
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => hSymm _ _)
  · intro x hx
    change 0 < ∫ g, F x x g ∂μ
    have h (g : P) : 0 < F x x g := hPos _ (fun h =>
      hx ((ρ g⁻¹).injective (h.trans (map_zero (ρ g⁻¹)).symm)))
    exact (hF x x).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun g => (h g).le) (h 1).ne'
  · intro k x y
    change (∫ g, F (ρ k x) (ρ k y) g ∂μ) = ∫ g, F x y g ∂μ
    have h (g : P) : F (ρ k x) (ρ k y) g = F x y (k⁻¹ * g) := by
      simp only [F, mul_inv_rev, inv_inv, map_mul, LinearEquiv.mul_apply]
    simpa only [h] using integral_mul_left_eq_self (μ := μ) (F x y) k⁻¹

end HaarAverage

section RegularKernel
open Filter Topology Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- If A and B commute and A has no nonzero vector in the intersection of
its image and kernel, a suitable perturbation has kernel the common kernel. -/
theorem exists_ker_add_smul_eq_inf (A B : V →ₗ[ℝ] V) (hc : Commute A B)
    (hd : Disjoint A.ker A.range) :
    ∃ t : ℝ, (A + t • B).ker = A.ker ⊓ B.ker := by
  have hTop : A.ker ⊔ A.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq A.ker A.range
    rw [hd.eq_bot, finrank_bot, add_zero, add_comm, A.finrank_range_add_finrank_ker] at h
    exact h
  have hh (v : V) : A (B v) = B (A v) := DFunLike.congr_fun hc.eq v
  have hBrange : ∀ v ∈ A.range, B v ∈ A.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨B v, hh v⟩
  let a := (A.restrict (p := A.range) fun v _ => A.mem_range_self v).toContinuousLinearMap
  let b := (B.restrict (p := A.range) hBrange).toContinuousLinearMap
  have ha : LinearMap.ker a.toLinearMap = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hAv : A (v : V) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hv)
    exact Subtype.ext (Submodule.disjoint_def.mp hd _ (LinearMap.mem_ker.mpr hAv) v.property)
  have hcDet : Continuous (fun t : ℝ => (a + t • b).det) :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hD0 : (a + (0 : ℝ) • b).det ≠ 0 := by
    simpa only [zero_smul, add_zero, ContinuousLinearMap.det] using
      (LinearMap.det_eq_zero_iff_ker_ne_bot.not.mpr (not_not_intro ha) :
        a.toLinearMap.det ≠ 0)
  have hD : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, (a + t • b).det ≠ 0 :=
    mem_nhdsWithin_of_mem_nhds (((show IsOpen {r : ℝ | r ≠ 0} from isOpen_ne).preimage
      hcDet).mem_nhds hD0)
  obtain ⟨t, ht, hpositive⟩ := (hD.and self_mem_nhdsWithin).exists
  have ht0 : t ≠ 0 := ne_of_gt hpositive
  let e := a + t • b
  have he : Function.Injective e := by
    change Function.Injective e.toLinearMap
    apply LinearMap.ker_eq_bot.mp
    by_contra hn
    exact ht (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  refine ⟨t, le_antisymm ?_ ?_⟩
  · intro z hz
    have hz' := LinearMap.mem_ker.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp
      (show z ∈ A.ker ⊔ A.range by rw [hTop]; trivial)
    have hu0 := LinearMap.mem_ker.mp hu
    have hBker : B u ∈ A.ker := LinearMap.mem_ker.mpr (by rw [hh, hu0, map_zero])
    have hrange : A v + t • B v ∈ A.range :=
      A.range.add_mem (A.mem_range_self v) (A.range.smul_mem t (hBrange v hv))
    have hsum : t • B u + (A v + t • B v) = 0 := by
      simpa only [LinearMap.add_apply, LinearMap.smul_apply, map_add, smul_add, hu0, zero_add,
        add_left_comm] using hz'
    have hRker : A v + t • B v ∈ A.ker := by
      have hsum' := hsum
      rw [add_comm, add_eq_zero_iff_eq_neg] at hsum'
      rw [hsum']
      exact A.ker.neg_mem (A.ker.smul_mem t hBker)
    have hr0 := Submodule.disjoint_def.mp hd _ hRker hrange
    have hEv : e ⟨v, hv⟩ = 0 := Subtype.ext hr0
    have hv0 : v = 0 := congrArg Subtype.val (he (hEv.trans e.map_zero.symm))
    have huB : B u = 0 := by
      rw [hr0, add_zero, smul_eq_zero] at hsum
      exact hsum.resolve_left ht0
    simpa only [hv0, add_zero] using
      (show u ∈ A.ker ⊓ B.ker from ⟨hu, LinearMap.mem_ker.mpr huB⟩)
  · rintro z ⟨hzA, hzB⟩
    apply LinearMap.mem_ker.mpr
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.mem_ker.mp hzA,
      LinearMap.mem_ker.mp hzB, smul_zero, add_zero]

end RegularKernel

section MatrixTorusConjugacy

open Filter NormedSpace Module Algebra
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
  [FiniteDimensional ℝ R]

private def conjugationRepresentation : Rˣ →* (R ≃ₗ[ℝ] R) where
  toFun g :=
    { toFun := conjugate g
      invFun := conjugate g⁻¹
      left_inv := fun x => by simp [conjugate, mul_assoc]
      right_inv := fun x => by simp [conjugate, mul_assoc]
      map_add' := fun x y => by simp [conjugate, mul_add, add_mul]
      map_smul' := fun t x => by simp [conjugate, mul_smul_comm, smul_mul_assoc] }
  map_one' := by
    ext x
    change conjugate 1 x = x
    simp [conjugate]
  map_mul' g h := by
    ext x
    change conjugate (g * h) x = conjugate g (conjugate h x)
    simp [conjugate, mul_inv_rev, mul_assoc]

private theorem expUnit_conjugate (g : Rˣ) (x : R) :
    expUnit (conjugate g x) = g * expUnit x * g⁻¹ := by
  apply Units.ext
  simp only [expUnit_val, Units.val_mul, conjugate]
  symm
  apply map_exp_of_mem_ball (𝕂 := ℝ)
    (MulSemiringAction.toRingHom (ConjAct Rˣ) R (ConjAct.toConjAct g))
    (continuous_const_smul (ConjAct.toConjAct g))
  rw [expSeries_radius_eq_top]
  exact edist_lt_top _ _

private def commutatorMap (x : R) : R →ₗ[ℝ] R :=
  LinearMap.mulLeft ℝ x - LinearMap.mulRight ℝ x

private theorem commutatorMap_commute {x y : R} (h : Commute x y) :
    Commute (commutatorMap x) (commutatorMap y) := by
  ext z
  change x * (y * z - z * y) - (y * z - z * y) * x =
    y * (x * z - z * x) - (x * z - z * x) * y
  simp only [mul_sub, sub_mul, ← mul_assoc]
  rw [h.eq]
  rw [mul_assoc z y x, ← h.eq, ← mul_assoc]
  abel

private theorem commutatorMap_add_smul (x y : R) (t : ℝ) :
    commutatorMap (x + t • y) = commutatorMap x + t • commutatorMap y := by
  ext z
  change (x + t • y) * z - z * (x + t • y) = x * z - z * x + t • (y * z - z * y)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

private theorem commutatorMap_skew {J : Subgroup Rˣ}
    (B : R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (hInv : ∀ g ∈ J, ∀ x y : R, B (conjugate g x) (conjugate g y) = B x y)
    {a : R} (ha : a ∈ exponentialLines J) (x y : R) :
    B (commutatorMap a x) y = -B x (commutatorMap a y) := by
  let l := (B.flip y).toContinuousLinearMap
  let r := (B x).toContinuousLinearMap
  have hl := l.hasFDerivAt.comp_hasDerivAt 0 (conjugation_derivative a x)
  have hr := r.hasFDerivAt.comp_hasDerivAt 0 (conjugation_derivative (-a) y)
  have hEq (t : ℝ) :
      l (conjugate (expUnit (t • a)) x) = r (conjugate (expUnit (t • -a)) y) := by
    let g := expUnit (t • a)
    have h := hInv g (ha t) x (conjugate g⁻¹ y)
    change B (conjugate g x) y = B x (conjugate (expUnit (t • -a)) y)
    rw [smul_neg, expUnit_neg]
    change B (conjugate g x) y = B x (conjugate g⁻¹ y)
    simpa [conjugate, mul_assoc] using h
  have hval := (hl.congr_of_eventuallyEq
    (Eventually.of_forall fun t => (hEq t).symm)).unique hr
  change B (a * x - x * a) y = B x ((-a) * y - y * (-a)) at hval
  change B (a * x - x * a) y = -B x (a * y - y * a)
  have harg : (-a) * y - y * (-a) = -(a * y - y * a) := by
    rw [neg_mul, mul_neg]
    abel
  rw [harg, map_neg] at hval
  exact hval

private theorem exists_regular_in_commuting_submodule (S : Submodule ℝ R)
    (hComm : ∀ x y : S, Commute (x : R) (y : R))
    (hDisjoint : ∀ x : S, Disjoint (commutatorMap (x : R)).ker (commutatorMap (x : R)).range) :
    ∃ x : S, ∀ (z : R), Commute (x : R) z → ∀ y : S, Commute (y : R) z := by
  classical
  let d (x : S) := Module.finrank ℝ (commutatorMap (x : R)).ker
  have hEx : ∃ n : ℕ, ∃ x : S, d x = n := ⟨d 0, 0, rfl⟩
  obtain ⟨a, ha⟩ := Nat.find_spec hEx
  refine ⟨a, ?_⟩
  intro z hz y
  obtain ⟨t, ht⟩ := exists_ker_add_smul_eq_inf (commutatorMap (a : R)) (commutatorMap (y : R))
    (commutatorMap_commute (hComm a y)) (hDisjoint a)
  let c : S := a + t • y
  have hC : (commutatorMap (c : R)).ker =
      (commutatorMap (a : R)).ker ⊓ (commutatorMap (y : R)).ker := by
    change (commutatorMap ((a : R) + t • (y : R))).ker = _
    rw [commutatorMap_add_smul, ht]
  have hle : (commutatorMap (c : R)).ker ≤ (commutatorMap (a : R)).ker := by
    rw [hC]
    exact inf_le_left
  have hdim : d a ≤ d c := ha ▸ Nat.find_min' hEx ⟨c, rfl⟩
  have hEq := Submodule.eq_of_le_of_finrank_le hle hdim
  have hz' : z ∈ (commutatorMap (a : R)).ker :=
    LinearMap.mem_ker.mpr (sub_eq_zero.mpr hz.eq)
  rw [← hEq, hC] at hz'
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp hz'.2)

/-- Maximal compact tori in a compact matrix group are conjugate. -/
theorem maximalCompactTori_conjugate {J S U : Subgroup Rˣ} (hJ : IsCompact (J : Set Rˣ))
    (hS : IsMaximalCompactTorus (J : Set Rˣ) S)
    (hU : IsMaximalCompactTorus (J : Set Rˣ) U) :
    ∃ g ∈ J, Conjugates g S U := by
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  have hclosed (T : Subgroup Rˣ) (hT : IsCompactTorus T) : IsClosed (T : Set Rˣ) := by
    have h := compact_image_of_torus hT (MonoidHom.id (Rˣ)) continuous_id
    simpa only [Subgroup.map_id] using h.isClosed
  let CJ := (closedSubgroupExponential R J hJ.isClosed).some
  let CS := (closedSubgroupExponential R S (hclosed S hS.1)).some
  let CU := (closedSubgroupExponential R U (hclosed U hU.1)).some
  let ρ := conjugationRepresentation.comp J.subtype
  obtain ⟨B, hSymm, hPos, hB⟩ := invariantBilinear_of_compact ρ (fun x => by
    change Continuous (fun g : J => (g : Rˣ).val * x * ((g : Rˣ)⁻¹ : Rˣ).val)
    fun_prop)
  have hInv (g : Rˣ) (hg : g ∈ J) (x y : R) :
      B (conjugate g x) (conjugate g y) = B x y := hB ⟨g, hg⟩ x y
  have hDisjoint (a : R) (ha : a ∈ exponentialLines J) :
      Disjoint (commutatorMap a).ker (commutatorMap a).range := by
    refine Submodule.disjoint_def.mpr fun z hz hz' => ?_
    obtain ⟨v, rfl⟩ := hz'
    have h0 := LinearMap.mem_ker.mp hz
    by_contra! hne
    have hp := hPos _ hne
    rw [commutatorMap_skew B hInv ha, h0, map_zero, neg_zero] at hp
    exact (lt_irrefl _) hp
  have hab (T : Subgroup Rˣ) (hT : IsCompactTorus T) (C : ClosedSubgroupChart T)
      (a b : C.tangent) : Commute (a : R) (b : R) := by
    obtain ⟨n, e, _, _⟩ := hT
    apply tangent_commute C _ a b
    intro g h
    have hComm : Commute (e.symm g) (e.symm h) := mul_comm _ _
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hComm.map e.toMonoidHom
  obtain ⟨x, hx⟩ := exists_regular_in_commuting_submodule CS.tangent (hab S hS.1 CS)
    (fun a => hDisjoint a fun t => hS.2.1 ((CS.mem_tangent a).mp a.property t))
  obtain ⟨y, hy⟩ := exists_regular_in_commuting_submodule CU.tangent (hab U hU.1 CU)
    (fun a => hDisjoint a fun t => hU.2.1 ((CU.mem_tangent a).mp a.property t))
  let f (g : J) := B (conjugate (g : Rˣ) (x : R)) (y : R)
  have hf : Continuous f := by
    change Continuous (fun g : J => B.flip (y : R) (conjugate (g : Rˣ) (x : R)))
    apply (B.flip (y : R)).continuous_of_finiteDimensional.comp
    unfold conjugate
    fun_prop
  obtain ⟨g, _, hg⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  let z := conjugate (g : Rˣ) (x : R)
  have hz : z ∈ CJ.tangent := CJ.conjugation g
    ⟨(x : R), chart_tangent_mono hS.2.1 CS CJ x.property⟩
  have hyJ : (y : R) ∈ CJ.tangent := chart_tangent_mono hU.2.1 CU CJ y.property
  have hZY : Commute z (y : R) := by
    let a := commutatorMap z (y : R)
    have hay : a ∈ CJ.tangent := CJ.bracket_mem ⟨z, hz⟩ ⟨y, hyJ⟩
    have ha := (CJ.mem_tangent a).mp hay
    let φ (t : ℝ) := B (conjugate (expUnit (t • a)) z) (y : R)
    have hφ (t : ℝ) : φ t = f (⟨expUnit (t • a), ha t⟩ * g) := by
      change B (ρ ⟨expUnit (t • a), ha t⟩ (ρ g (x : R))) _ = B (ρ (_ * _ : J) (x : R)) _
      rw [map_mul]
      rfl
    have hgo (t : ℝ) : φ t ≤ φ 0 := by
      rw [hφ t, hφ 0]
      have h1 : (⟨expUnit ((0 : ℝ) • a), ha 0⟩ : J) = 1 := Subtype.ext (by simp)
      rw [h1, one_mul]
      exact hg (Set.mem_univ (⟨expUnit (t • a), ha t⟩ * g : J))
    have hmax : IsLocalMax φ 0 :=
      (show IsMaxOn φ Set.univ 0 from fun t _ => hgo t).isLocalMax Filter.univ_mem
    have hder := (B.flip (y : R)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
      (conjugation_derivative a z)
    have hzero : B (commutatorMap a z) (y : R) = 0 := hmax.hasDerivAt_eq_zero hder
    have hsk := commutatorMap_skew B hInv ((CJ.mem_tangent z).mp hz) a (y : R)
    have hanti : commutatorMap a z = -commutatorMap z a := by
      change a * z - z * a = -(z * a - a * z)
      abel
    rw [hanti, map_neg, LinearMap.neg_apply, hsk, neg_neg] at hzero
    have ha0 : a = 0 := by
      by_contra hn
      exact (hPos a hn).ne' hzero
    exact sub_eq_zero.mp ha0
  let m := MulAut.conj (g : Rˣ)
  have hM : S.map m.toMonoidHom ≤ J := by
    rintro _ ⟨s, hs, rfl⟩
    exact J.mul_mem (J.mul_mem g.property (hS.2.1 hs)) (J.inv_mem g.property)
  let : ConnectedSpace U := by
    obtain ⟨_, e, he, _⟩ := hU.1
    exact e.surjective.connectedSpace he
  have hUS : U ≤ S.map m.toMonoidHom := by
    apply le_of_expLines CU
    intro u hu
    have hzu := (hy z hZY.symm ⟨u, hu⟩).symm
    let v := conjugate (g : Rˣ)⁻¹ u
    have hv : v ∈ exponentialLines J := conjugate_mem_exponentialLines (J.inv_mem g.property)
      ((CJ.mem_tangent u).mp (chart_tangent_mono hU.2.1 CU CJ hu))
    have hxv : Commute (x : R) v := by
      have h := hzu.map (MulSemiringAction.toRingHom (ConjAct Rˣ) R (ConjAct.toConjAct (g : Rˣ)⁻¹))
      change Commute (conjugate (g : Rˣ)⁻¹ z) (conjugate (g : Rˣ)⁻¹ u) at h
      simpa [z, v, conjugate, mul_assoc] using h
    have hvS : v ∈ CS.tangent :=
      maximalTorus_tangent_centralizer hJ hS CS hv (fun b => (hx v hxv b).symm)
    intro t
    refine ⟨expUnit (t • v), (CS.mem_tangent v).mp hvS t, ?_⟩
    change (g : Rˣ) * expUnit (t • conjugate (g : Rˣ)⁻¹ u) * (g : Rˣ)⁻¹ = expUnit (t • u)
    rw [← expUnit_conjugate]
    congr 1
    simp [conjugate, mul_smul_comm, smul_mul_assoc, mul_assoc]
  have hMC : Continuous m := (continuous_const.mul continuous_id).mul continuous_const
  have hMC' : Continuous m.symm := (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨g, g.property, ?_⟩
  exact congrArg (fun T : Subgroup Rˣ => (T : Set Rˣ))
    (hU.2.2 _ (compactTorus_map S hS.1 m hMC hMC') hM hUS)

end MatrixTorusConjugacy


section TransportCompactConjugacy

open Specs.ExceptionalCompactInner (fixedSubgroup)
open scoped Matrix.Norms.Operator

variable {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]

private theorem isCompactTorus_map_iff (f : P →* Q) (hf : IsEmbedding f) (T : Subgroup P) :
    IsCompactTorus (T.map f) ↔ IsCompactTorus T := by
  let e := T.equivMapOfInjective f hf.injective
  have hI : IsInducing e := by
    apply (IsInducing.of_comp_iff (g := (Subtype.val : T.map f → Q))
      IsInducing.subtypeVal).mp
    exact hf.isInducing.comp IsInducing.subtypeVal
  let E := e.toEquiv.toHomeomorphOfIsInducing hI
  have he : Continuous e := E.continuous
  have he' : Continuous e.symm := E.symm.continuous
  constructor
  · rintro ⟨n, a, ha, ha'⟩
    exact ⟨n, a.trans e.symm, he'.comp ha, ha'.comp he⟩
  · rintro ⟨n, a, ha, ha'⟩
    exact ⟨n, a.trans e, he.comp ha, ha'.comp he'⟩

private theorem IsMaximalCompactTorus.map_embedding {f : P →* Q} (hf : IsEmbedding f)
    {C T : Subgroup P} (hT : IsMaximalCompactTorus (C : Set P) T) :
    IsMaximalCompactTorus (C.map f : Set Q) (T.map f) := by
  refine ⟨(isCompactTorus_map_iff f hf T).mpr hT.1, Subgroup.map_mono hT.2.1, ?_⟩
  intro V hV hVC hTV
  let U := V.comap f
  have hUV : U.map f = V := Subgroup.map_comap_eq_self (hVC.trans (C.map_le_range f))
  have hU : IsCompactTorus U := (isCompactTorus_map_iff f hf U).mp (hUV.symm ▸ hV)
  have hUC : U ≤ C := by
    intro u hu
    obtain ⟨c, hc, heq⟩ := hVC (show f u ∈ V from hu)
    exact hf.injective heq ▸ hc
  have hTU : T ≤ U := fun t ht => hTV ⟨t, ht, rfl⟩
  exact hUV.symm.trans (congrArg (Subgroup.map f) (hT.2.2 U hU hUC hTU))

private theorem conjugates_of_map_embedding {f : P →* Q} (hf : Function.Injective f)
    (g : P) (T U : Subgroup P) (h : Conjugates (f g) (T.map f) (U.map f)) :
    Conjugates g T U := by
  apply hf.image_injective
  rw [Set.image_image]
  change (MulAut.conj (f g)) '' (f '' (T : Set P)) = f '' (U : Set P) at h
  rw [Set.image_image] at h
  convert h using 2
  simp only [MulAut.conj_apply, map_mul, map_inv]

open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups

theorem fixedTorusConjugacy : FixedTorusConjugacy := by
  intro G i _ _ _ ω θ h S U hS hU
  let f := asMatrix i ℂ
  have hf := (asMatrix_isClosedEmbedding i ℂ).isEmbedding
  let : IsTopologicalGroup (PointsIn i ℂ) :=
    IsInducing.isTopologicalGroup f (.induced _)
  let : T2Space (PointsIn i ℂ) := hf.t2Space
  let J := fixedCompact ω θ
  have hK : IsCompact (fixedSubgroup ω : Set (PointsIn i ℂ)) :=
    isCompact_iff_compactSpace.mpr h.compact_fixed
  have hJ : IsClosed (J : Set (PointsIn i ℂ)) :=
    (isClosed_eq h.continuous_compact continuous_id).inter
      (isClosed_eq h.continuous_outer continuous_id)
  let : CompactSpace J := isCompact_iff_compactSpace.mp (hK.of_isClosed_subset hJ inf_le_left)
  let C := (Subgroup.connectedComponentOfOne J).map J.subtype
  have hC : IsCompact (C : Set (PointsIn i ℂ)) :=
    isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hMapped : IsCompact (C.map f : Set (Matrix.GeneralLinearGroup (Specs.Unipotent.Index.{0} i.size) ℂ)) :=
    hC.image hf.continuous
  obtain ⟨_, ⟨g, hg, rfl⟩, hconj⟩ := maximalCompactTori_conjugate hMapped
    (IsMaximalCompactTorus.map_embedding hf (show IsMaximalCompactTorus (C : Set _) S from hS))
    (IsMaximalCompactTorus.map_embedding hf (show IsMaximalCompactTorus (C : Set _) U from hU))
  exact ⟨g, hg, conjugates_of_map_embedding hf.injective g S U hconj⟩

theorem fixedNormalizerRepresentatives : FixedNormalizerRepresentatives :=
  fixedNormalizerRepresentatives_of_conjugacy fixedTorusConjugacy

end TransportCompactConjugacy


section FixedSubtorus

open Specs.ExceptionalCompactInner (fixedSubgroup)
open Specs.ArchimedeanLieChart (ClosedSubgroupChart)
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {P R : Type*} [Group P] [TopologicalSpace P]
  [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] [FiniteDimensional ℝ R]

private theorem compactTorus_of_compact_connected (m : P →* Rˣ) (hm : IsEmbedding m)
    (V : Subgroup P) (hC : IsCompact (V : Set P)) (hV : IsConnected (V : Set P))
    (hAb : ∀ x y : V, Commute x y) : IsCompactTorus V := by
  have hC' : IsCompact (V.map m : Set Rˣ) := hC.image hm.continuous
  have hV' : IsConnected (V.map m : Set Rˣ) := hV.image m hm.continuous.continuousOn
  let : CompactSpace (V.map m) := isCompact_iff_compactSpace.mp hC'
  let : ConnectedSpace (V.map m) := isConnected_iff_connectedSpace.mp hV'
  let e := V.equivMapOfInjective m hm.injective
  have hA (a b : V.map m) : Commute a b := by
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    exact (hAb a b).map e.toMonoidHom
  exact (isCompactTorus_map_iff m hm V).mp
    (compactTorus_of_abelianMatrixSubgroup (closedSubgroupExponential R _ hC'.isClosed).some hA)

private theorem foldedSpace_isConnected : IsConnected foldedSpace := by
  let W : Submodule ℝ E6Space :=
    { carrier := foldedSpace
      zero_mem' := rfl
      add_mem' := by
        intro x y hx hy
        change e6Diagram x = x at hx
        change e6Diagram y = y at hy
        change e6Diagram x + e6Diagram y = x + y
        rw [hx, hy]
      smul_mem' := by
        intro a x hx
        change e6Diagram x = x at hx
        change a • e6Diagram x = a • x
        rw [hx] }
  exact W.convex.isConnected ⟨0, W.zero_mem⟩

/-- If the action on the compact torus is the coroot permutation, the given
maximal fixed torus is exactly the fixed-subspace image. -/
theorem maximalFixedTorus_eq_diagramFixed (m : P →* Rˣ) (hm : IsEmbedding m)
    (ω θ δ : MulAut P) (hδC : Continuous δ) (S T : Subgroup P)
    (hS : IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S)
    (hST : S ≤ T) (hTK : T ≤ fixedSubgroup ω)
    (hT : IsCompactTorus T) (hθδ : ∀ t ∈ T, θ t = δ t)
    (f : E6Space →+ Additive P) (hf : Continuous (fun x => (f x).toMul))
    (hRange : (T : Set P) = Set.range (fun x => (f x).toMul))
    (hKer : ∀ x, f x = 0 ↔ x ∈ e6Lattice)
    (hδ : ∀ x, f (e6Diagram x) = Additive.ofMul (δ (f x).toMul)) :
    S = T ⊓ fixedSubgroup δ ∧
      (S : Set P) = (fun x => (f x).toMul) '' foldedSpace := by
  let : T2Space P := hm.t2Space
  let V := T ⊓ fixedSubgroup δ
  let J := fixedCompact ω θ
  have hV : (V : Set P) = (fun x => (f x).toMul) '' foldedSpace := by
    have he : (V : Set P) = {t ∈ Set.range (fun x => (f x).toMul) | δ t = t} := by
      ext t
      change (t ∈ T ∧ δ t = t) ↔ (t ∈ Set.range (fun x => (f x).toMul) ∧ δ t = t)
      rw [← hRange]
      rfl
    exact he.trans (diagramFixed_eq_image f δ hKer hδ)
  have hConn : IsConnected (V : Set P) := hV.symm ▸
    foldedSpace_isConnected.image _ hf.continuousOn
  obtain ⟨n, e, he, _⟩ := hT
  have hTc : IsCompact (T : Set P) := by
    let : CompactSpace T := e.surjective.compactSpace he
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hVc : IsCompact (V : Set P) := hTc.inter_right (isClosed_eq hδC continuous_id)
  have hAb (a b : V) : Commute a b := by
    let φ : V →* T := Subgroup.inclusion inf_le_left
    apply Commute.of_map (f := φ) (Subgroup.inclusion_injective _)
    have h : Commute (e.symm (φ a)) (e.symm (φ b)) := mul_comm _ _
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using h.map e.toMonoidHom
  have hVT : IsCompactTorus V :=
    compactTorus_of_compact_connected m hm V hVc hConn hAb
  have hVJ : V ≤ J := fun t ht => ⟨hTK ht.1, (hθδ t ht.1).trans ht.2⟩
  have hVJ₀ : (V : Set P) ⊆ identityComponent J := by
    intro t ht
    let ι : V → J := fun a => ⟨a, hVJ a.property⟩
    have hι : Continuous ι := continuous_induced_rng.mpr continuous_subtype_val
    let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hConn
    have hcJ : IsConnected (Set.range ι) := isConnected_range hι
    have hOne : (1 : J) ∈ Set.range ι := ⟨1, rfl⟩
    have hh := hcJ.isPreconnected.subset_connectedComponent hOne (Set.mem_range_self (⟨t, ht⟩ : V))
    exact ⟨ι ⟨t, ht⟩, hh, rfl⟩
  have hSV : S ≤ V := by
    intro t ht
    have htT := hST ht
    obtain ⟨q, _, rfl⟩ := hS.2.1 ht
    exact ⟨htT, (hθδ _ htT).symm.trans q.property.2⟩
  have hEq := hS.2.2 V hVT hVJ₀ hSV
  exact ⟨hEq.symm, (congrArg (fun U : Subgroup P => (U : Set P)) hEq.symm).trans hV⟩

end FixedSubtorus

section OuterComparison

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix.Norms.Operator
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AbsoluteDynkinTypes (E6Reflection)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints fixedSubgroup)
open Specs.IntegralModels (MatrixRealization)
open Specs.Pinning (SplitBorelPair)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups

private def cocharacterPostcompose {Q : GroupScheme ℂ} [IsCommMonObj Q.X] (s : Q ⟶ Q) :
    Additive (Cocharacter Q) →ₗ[ℤ] Additive (Cocharacter Q) :=
  ({ toFun := fun c => Additive.ofMul (c.toMul ≫ s)
     map_zero' := by
       apply Additive.toMul.injective
       apply Grp.hom_ext
       exact MonObj.one_comp s.hom.hom
     map_add' := by
       intro c c'
       apply Additive.toMul.injective
       apply Grp.hom_ext
       exact MonObj.mul_comp c.toMul.hom.hom c'.toMul.hom.hom s.hom.hom } : _ →+ _).toIntLinearMap

variable {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
variable {A : AdditiveLine ℂ}

private theorem markedChamber (M : MarkedPair G A)
    (b : letI := M.datum.comm; Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (s : M.P.pair.T.group ⟶ M.P.pair.T.group)
    (hs : ∀ j, M.coroot j ≫ s = M.coroot (E6Reflection j))
    (c : Cocharacter M.P.pair.T.group) (hc : c ≫ s = c)
    (hReg : IsRegular M.P.pair.T c)
    (hPos : subgroupRoots M.P.pair.T M.P.pair.B = positiveRoots M.P.pair.T c) :
    ∃ z ∈ foldedSpace, M.IsRegularChamber z := by
  let := M.datum.comm
  let L := cocharacterPostcompose s
  let y := Additive.ofMul c
  let z : E6Space := fun j => (b.equivFun y j : ℝ)
  have hL (j : Fin 6) : L (b j) = b (E6Reflection j) := by
    rw [hb j, hb (E6Reflection j)]
    exact congrArg Additive.ofMul (hs j)
  have hLy : L y = y := congrArg Additive.ofMul hc
  refine ⟨z, ?_, ?_⟩
  · change e6Diagram z = z
    funext j
    have hCoeff : ((LinearMap.proj j).comp b.equivFun.toLinearMap).comp L =
        (LinearMap.proj (E6Reflection j)).comp b.equivFun.toLinearMap := by
      apply b.ext
      intro k
      change b.equivFun (L (b k)) j = b.equivFun (b k) (E6Reflection j)
      rw [hL]
      have he : E6Reflection k = j ↔ k = E6Reflection j := by
        constructor
        · intro h
          rw [← h, reflection_involutive k]
        · intro h
          rw [h, reflection_involutive j]
      simp only [Module.Basis.equivFun_self, he]
    have hh := LinearMap.congr_fun hCoeff y
    change b.equivFun (L y) j = b.equivFun y (E6Reflection j) at hh
    rw [hLy] at hh
    exact congrArg Int.cast hh.symm
  · intro α
    let D := M.datum.datum
    let F := D.rootDatum.toLinearMap (Additive.ofMul α.val)
    have hEvaluation : (∑ j, M.rootValues α j * z j) =
        (pairing M.P.pair.T.group α.val c : ℝ) := by
      have hInt : (∑ j, pairing M.P.pair.T.group α.val (M.coroot j) *
          b.equivFun y j) = pairing M.P.pair.T.group α.val c := by
        calc
          _ = F (∑ j, b.repr y j • b j) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [map_smul, hb j]
            change _ = b.repr y j * F (Additive.ofMul (M.coroot j))
            rw [show F (Additive.ofMul (M.coroot j)) = _ from D.pairing_eq α.val (M.coroot j)]
            rw [Module.Basis.equivFun_apply, mul_comm]
          _ = F y := congrArg F (b.sum_repr y)
          _ = _ := D.pairing_eq α.val c
      change (∑ j, (pairing M.P.pair.T.group α.val (M.coroot j) : ℝ) * (b.equivFun y j : ℝ)) = _
      exact_mod_cast hInt
    change (∑ j, M.rootValues α j * z j) ≠ 0 ∧
      (0 < ∑ j, M.rootValues α j * z j ↔ α ∈ subgroupRoots M.P.pair.T M.P.pair.B)
    rw [hEvaluation, hPos]
    exact ⟨by exact_mod_cast hReg α, by exact_mod_cast (Iff.rfl :
      0 < pairing M.P.pair.T.group α.val c ↔ α ∈ positiveRoots M.P.pair.T c)⟩

private theorem markedExp_range (M : MarkedPair G A)
    (b : letI := M.datum.comm; Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (ω : MulAut (PointsIn i ℂ))
    (hω : ∀ (c : Cocharacter M.P.pair.T.group) (u : ℂˣ),
      ω (M.onPoints (i := i) M.P.pair.T.inclusion (cocharacterPoint c complexTest u)) =
      M.onPoints (i := i) M.P.pair.T.inclusion
        (cocharacterPoint c complexTest (conjugateInverseUnit u))) :
    Set.range (M.exp (i := i)) =
      (fixedSubgroup ω : Set (PointsIn i ℂ)) ∩
        Set.range (M.onPoints (i := i) M.P.pair.T.inclusion) := by
  apply markedExp_range_of_conjugateInversion M b hb ω
  intro u
  simp only [torusFromUnits, ← pointMap_apply, map_list_prod, List.map_ofFn, Function.comp_apply]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact hω (M.coroot j) (u j)

private def transportPairAction {P : SplitBorelPair ℂ}
    (e : P.G.val ≅ complexGroup G) (a : Aut (complexGroup G))
    (aT : Aut P.T.group) (aB : Aut P.B.group)
    (hT : P.T.inclusion ≫ e.hom ≫ a.asIso.hom = aT.asIso.hom ≫ P.T.inclusion ≫ e.hom)
    (hB : P.B.inclusion ≫ e.hom ≫ a.asIso.hom = aB.asIso.hom ≫ P.B.inclusion ≫ e.hom) :
    Specs.ExceptionalOuterCompactPinning.PairAction P where
  group := Aut.of (e ≪≫ a.asIso ≪≫ e.symm)
  torus := aT
  borel := aB
  torus_comm := by
    change P.T.inclusion ≫ (e.hom ≫ a.asIso.hom) ≫ e.inv = _
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using congrArg (· ≫ e.inv) hT
  borel_comm := by
    change P.B.inclusion ≫ (e.hom ≫ a.asIso.hom) ≫ e.inv = _
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using congrArg (· ≫ e.inv) hB

private theorem acts_transportPairAction {P : SplitBorelPair ℂ}
    (e : P.G.val ≅ complexGroup G) (a : Aut (complexGroup G))
    (aT : Aut P.T.group) (aB : Aut P.B.group)
    (hT : P.T.inclusion ≫ e.hom ≫ a.asIso.hom = aT.asIso.hom ≫ P.T.inclusion ≫ e.hom)
    (hB : P.B.inclusion ≫ e.hom ≫ a.asIso.hom = aB.asIso.hom ≫ P.B.inclusion ≫ e.hom)
    (θ : MulAut (PointsIn i ℂ)) (ha : ActsOnComplexPoints (i := i) a θ) :
    ActsOnComplexPoints (i := i)
      (Aut.of (e.symm ≪≫ (transportPairAction e a aT aB hT hB).group.asIso ≪≫ e)) θ := by
  have he : e.symm ≪≫ (transportPairAction e a aT aB hT hB).group.asIso ≪≫ e = a.asIso := by
    apply Iso.ext
    change (e.inv ≫ (e.hom ≫ a.asIso.hom) ≫ e.inv) ≫ e.hom = a.asIso.hom
    simp
  rw [he]
  exact ha

set_option maxHeartbeats 1200000 in
/-- The stable pinned comparison and the exponential of the folded cocharacter space
for every maximal torus of the connected compact fixed group. -/
theorem outerTorusComparison : OuterTorusComparison := by
  intro G i hSimple hSC hExc ω θ hOut S hS
  obtain ⟨T, hTComp, hST, _, hT⟩ :=
    ExceptionalOuterCompactCentralizer.compactCentralizer G i hSimple hSC hExc ω θ
      hOut.continuous_compact hOut.continuous_outer hOut.compact_involutive hOut.outer_involutive
      hOut.commute hOut.compact_fixed hOut.connected_fixed S hS
  obtain ⟨P, hP, hTCentral, hTIntersect, _, hInv, hChamber⟩ :=
    ExceptionalOuterAlgebraicBorelPair.algebraicBorelPair G i hSimple hSC hExc ω θ
      hOut.continuous_compact hOut.continuous_outer hOut.compact_differential hOut.algebraic_outer
      hOut.compact_involutive hOut.outer_involutive hOut.commute
      hOut.compact_fixed hOut.connected_fixed S T hS hTComp hST hT
  let e := Specs.ExceptionalOuterCompactPinning.comparison (G := G) (P := P) hP
  obtain ⟨a, aT, aB, c, ha, haT, haB, hc, hReg, hPos⟩ := hChamber
  let aPair := transportPairAction e a aT aB haT haB
  have hAct : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ aPair.group.asIso ≪≫ e)) θ :=
    acts_transportPairAction e a aT aB haT haB θ ha
  have hPinOut : Specs.ExceptionalOuterCompactPinning.OuterInvolutions (i := i) ω θ :=
    ⟨hOut.continuous_compact, hOut.continuous_outer, hOut.compact_differential,
      hOut.algebraic_outer, hOut.compact_involutive, hOut.outer_involutive, hOut.commute,
      hOut.compact_fixed, hOut.connected_fixed, hOut.outer⟩
  have hPinInv : Specs.ExceptionalOuterCompactPinning.ConjugateInversion (i := i) e ω := by
    intro c' u
    have hu : Specs.ExceptionalOuterAlgebraicBorelPair.conjugateInverse u =
        Specs.ExceptionalOuterCompactPinning.conjugateInverseUnit u :=
      map_inv (Units.map Complex.conjAe.toMonoidHom) u
    rw [← hu]
    exact hInv c' u
  obtain ⟨A, U, p, d, hCompact, hδω, t, htFix, hθ⟩ :=
    ExceptionalOuterCompactPinning.compactPinning G i hSimple hSC hExc ω θ hPinOut P hP aPair
      hAct hPinInv
  let M : MarkedPair G A := ⟨⟨P, U, p⟩, e, d.datum, d.numbering⟩
  have hStable : M.IsStable (i := i) θ := ⟨a, aT, aB, ha, haT, haB⟩
  have hCompatible : M.IsCompactCompatible (i := i) ω := by
    intro j
    obtain ⟨β, x, _, r, hr, hω⟩ := hCompact (M.simple j)
    exact ⟨x.val.hom ≫ (M.P.roots β).val.inclusion, r, x.property, hr, hω⟩
  obtain ⟨⟨b, hb⟩, hRoots⟩ := markedCoordinates M d.full_coroot_lattice d.cartan
  have hdCoroot (j : Fin 6) : M.coroot j ≫ d.diagram.torus.hom = M.coroot (E6Reflection j) :=
    d.permutes_coroots j
  have hc' : c ≫ d.diagram.torus.hom = c := by
    rw [← d.torus_eq]
    exact hc
  have hMarkedChamber := markedChamber M b hb d.diagram.torus.hom hdCoroot c hc' hReg hPos
  have hTIntersect' : (T : Set (PointsIn i ℂ)) =
      (fixedSubgroup ω : Set _) ∩ Set.range (M.onPoints (i := i) M.P.pair.T.inclusion) := hTIntersect
  have hRange : (T : Set (PointsIn i ℂ)) = Set.range (M.exp (i := i)) :=
    hTIntersect'.trans (markedExp_range M b hb ω hPinInv).symm
  have htT : M.onPoints (i := i) M.P.pair.T.inclusion t ∈ T := by
    change M.onPoints (i := i) M.P.pair.T.inclusion t ∈ (T : Set (PointsIn i ℂ))
    rw [hTIntersect']
    exact ⟨htFix, Set.mem_range_self t⟩
  let t₀ : T := ⟨M.onPoints (i := i) M.P.pair.T.inclusion t, htT⟩
  have hθ' : θ = MulAut.conj t₀.val * d.pointDiagram := hθ
  have hDiag := markedExp_diagram M d.diagram d.pointDiagram d.acts hdCoroot
  have hθδ (q : PointsIn i ℂ) (hq : q ∈ T) : θ q = d.pointDiagram q := by
    have hδq : d.pointDiagram q ∈ T := by
      obtain ⟨x, rfl⟩ : q ∈ Set.range (M.exp (i := i)) := hRange ▸ hq
      change d.pointDiagram (M.exp x) ∈ (T : Set (PointsIn i ℂ))
      rw [hDiag, hRange]
      exact Set.mem_range_self _
    obtain ⟨n, ψ, _, _⟩ := hT.1
    let w : T := ⟨d.pointDiagram q, hδq⟩
    have hCom : Commute t₀.val (d.pointDiagram q) := by
      have h : Commute (ψ.symm t₀) (ψ.symm w) := mul_comm _ _
      have h' : Commute t₀ w := by
        simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using h.map ψ.toMonoidHom
      exact h'.map T.subtype
    calc
      θ q = (MulAut.conj t₀.val * d.pointDiagram) q :=
        congrArg (fun a : MulAut (PointsIn i ℂ) => a q) hθ'
      _ = d.pointDiagram q := by
        rw [MulAut.mul_apply, MulAut.conj_apply, hCom.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hKer := markedExp_eq_one (i := i) M b hb
  let f : E6Space →+ Additive (PointsIn i ℂ) :=
    { toFun := fun x => Additive.ofMul (M.exp (i := i) x)
      map_zero' := (hKer 0).mpr ⟨0, by funext j; norm_num⟩
      map_add' := markedExp_add (i := i) M }
  obtain ⟨hFixed, hFold⟩ := maximalFixedTorus_eq_diagramFixed
    (asMatrix i ℂ) (asMatrix_isClosedEmbedding i ℂ).isEmbedding ω θ d.pointDiagram d.continuous
    S T hS hST hT.2.1 hT.1 hθδ f (markedExp_continuous (i := i) M) hRange hKer
    (fun x => congrArg Additive.ofMul (hDiag x).symm)
  exact ⟨T, A, M, d.diagram, d.pointDiagram, hTComp, hTCentral, hT, hTIntersect', hStable,
    hCompatible, d.cartan, ⟨b, hb⟩, hRoots, markedRootValue M, hMarkedChamber,
    markedExp_continuous (i := i) M, markedExp_add (i := i) M, hRange, hKer,
    d.permutes_coordinates, hdCoroot, d.acts, d.involutive, d.continuous, hδω, hDiag,
    ⟨t₀, hθ'⟩, hFixed, hFold⟩

end OuterComparison

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus
