import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterAlgebraicBorelPair
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalTorsionCentralizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Topology.Algebra.Order.Archimedean

noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Topology
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterAlgebraicBorelPair

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.ExceptionalOuterAlgebraicBorelPair
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)

open private exists_avoiding_zero_forms precomp_pairing map_parabolic_of_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private characterUnit characterUnitOnPoints characterEvaluation characterValue_eq_unit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem circleProduct_squares {n : ℕ} (x : Fin n → Circle) :
    ∃ y : Fin n → Circle, y * y = x := by
  choose a ha using fun j : Fin n => Circle.exp_surjective (x j)
  refine ⟨fun j => Circle.exp (a j / 2), funext fun j => ?_⟩
  change Circle.exp (a j / 2) * Circle.exp (a j / 2) = x j
  rw [← Circle.exp_add, ← ha j]
  congr 1
  ring

private theorem subgroup_squares {X : Type*} [Group X] [TopologicalSpace X]
    {S : Subgroup X} (hS : IsCompactTorus S) (s : S) : ∃ y : S, y * y = s := by
  obtain ⟨n, e, _, _⟩ := hS
  obtain ⟨y, hy⟩ := circleProduct_squares (e.symm s)
  exact ⟨e y, (map_mul e y y).symm.trans ((congrArg e hy).trans (e.apply_symm_apply s))⟩

private theorem character_comp_value {Q : GroupScheme ℂ} (a : Q ⟶ Q)
    (χ : Character Q) (t : GroupPoints Q complexTest) :
    characterValue (a ≫ χ) complexTest t = characterValue χ complexTest (t ≫ a.hom.hom) := by
  have he : t ≫ (a ≫ χ).hom.hom = (t ≫ a.hom.hom) ≫ χ.hom.hom :=
    (Category.assoc (show Points Q.X complexTest from t) a.hom.hom χ.hom.hom).symm
  simp only [characterValue, he]

/-- Nontriviality on the pointwise fixed torus makes each root nonzero on
the invariant cocharacter lattice. The sum of a cocharacter and its image
provides an integral invariant direction. -/
theorem fixedRegularCocharacter
    (H : AffineAlgebraicGroup ℂ) (Q : ClosedSubgroup H.val) (hsplit : IsSplitTorus Q.group)
    (a : Q.group ≅ Q.group) (ha : a.hom ≫ a.hom = 𝟙 _)
    {X : Type*} [Group X] [TopologicalSpace X] (S : Subgroup X) (hS : IsCompactTorus S)
    (j : GroupPoints Q.group complexTest →* X) (hj : Function.Injective j)
    (hSrange : (S : Set X) ⊆ Set.range j)
    (hSfix : ∀ t : GroupPoints Q.group complexTest, j t ∈ S → t ≫ a.hom.hom.hom = t)
    (hroots : ∀ α : ↥(absoluteRoots Q), ∃ t : GroupPoints Q.group complexTest,
      j t ∈ S ∧ characterValue α.val complexTest t ≠ 1) :
    ∃ c : Cocharacter Q.group, c ≫ a.hom = c ∧ IsRegular Q c := by
  obtain ⟨hComm, _, _, _, _, p, hperf, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing Q.group hsplit
  letI := hComm
  letI := hperf
  letI : Finite ↥(absoluteRoots Q) := RootData.CharacterPairing.finiteAbsoluteRoots H Q hsplit
  have hχ (α : ↥(absoluteRoots Q)) : α.val * (a.hom ≫ α.val) ≠ 1 := by
    intro he
    obtain ⟨t, ht, hval⟩ := hroots α
    obtain ⟨s, hs⟩ := subgroup_squares hS ⟨j t, ht⟩
    obtain ⟨v, hv⟩ := hSrange s.prop
    have hvS : j v ∈ S := hv.symm ▸ s.prop
    have hvv : v * v = t := hj (by
      rw [map_mul, hv]
      exact congrArg Subtype.val hs)
    let ev := characterEvaluation (T := Q.group) complexTest v
    have hfix : ev (a.hom ≫ α.val) = ev α.val := by
      apply Units.ext
      change (characterUnit (a.hom ≫ α.val) complexTest v : ℂ) =
        (characterUnit α.val complexTest v : ℂ)
      rw [← characterValue_eq_unit, ← characterValue_eq_unit, character_comp_value, hSfix v hvS]
    have h := congrArg ev he
    rw [map_mul, map_one, hfix] at h
    apply hval
    rw [characterValue_eq_unit, ← hvv]
    change (characterUnitOnPoints α.val complexTest (v * v) : ℂ) = 1
    rw [map_mul]
    exact congrArg Units.val h
  obtain ⟨y, hy⟩ := exists_avoiding_zero_forms
    (fun α : ↥(absoluteRoots Q) => p (Additive.ofMul (α.val * (a.hom ≫ α.val))))
    (by
      intro α
      by_contra! hz
      apply hχ α
      have hpz : p (Additive.ofMul (α.val * (a.hom ≫ α.val))) = 0 := LinearMap.ext hz
      have hzero := p.toPerfPair.injective (hpz.trans p.toPerfPair.map_zero.symm)
      exact congrArg Additive.toMul hzero)
  let d : Cocharacter Q.group := y.toMul
  let c := d * (d ≫ a.hom)
  refine ⟨c, ?_, fun α => ?_⟩
  · have hmul : c ≫ a.hom = (d ≫ a.hom) * ((d ≫ a.hom) ≫ a.hom) :=
      Grp.hom_ext _ _ (MonObj.mul_comp _ _ _)
    rw [hmul, Category.assoc, ha, Category.comp_id, mul_comm]
  · rw [← hpair]
    have hsum :
        Additive.ofMul c = Additive.ofMul d + Additive.ofMul (d ≫ a.hom) := rfl
    rw [hsum, map_add, hpair, hpair, precomp_pairing, ← hpair, ← hpair]
    change p (Additive.ofMul α.val) y + p (Additive.ofMul (a.hom ≫ α.val)) y ≠ 0
    have h := hy α
    change p (Additive.ofMul α.val + Additive.ofMul (a.hom ≫ α.val)) y ≠ 0 at h
    simpa only [map_add, LinearMap.add_apply] using h

/-- A regular invariant cocharacter defines an invariant Borel by the
limit construction. The restriction isomorphism acts on the same subgroup. -/
theorem stableBorelOfFixedCocharacter
    (H : AffineAlgebraicGroup ℂ) (hH : IsReductive H)
    (Q : ClosedSubgroup H.val) (hsplit : IsSplitTorus Q.group) (hmax : IsGeometricallyMaximal Q)
    (a : H.val ≅ H.val) (aQ : Q.group ≅ Q.group)
    (haQ : Q.inclusion ≫ a.hom = aQ.hom ≫ Q.inclusion)
    (c : Cocharacter Q.group) (hfix : c ≫ aQ.hom = c) (hreg : IsRegular Q c) :
    ∃ (B : ClosedSubgroup H.val) (aB : B.group ≅ B.group),
      IsKBorel B ∧ IsSubgroupOf Q B ∧ subgroupRoots Q B = positiveRoots Q c ∧
      B.inclusion ≫ a.hom = aB.hom ≫ B.inclusion := by
  let d := c ≫ Q.inclusion
  have hd : d ≫ a.hom = d := by
    dsimp only [d]
    rw [Category.assoc, haQ, ← Category.assoc, hfix]
  have hd' : d ≫ a.inv = d := by
    calc
      d ≫ a.inv = (d ≫ a.hom) ≫ a.inv := congrArg (· ≫ a.inv) hd.symm
      _ = d := by rw [Category.assoc, a.hom_inv_id, Category.comp_id]
  obtain ⟨D⟩ := existsLimitDecomposition H d
  let B := D.parabolic
  obtain ⟨_, hB, hQB, hroots, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel H hH Q hsplit hmax c hreg D
  obtain ⟨f, hf⟩ := map_parabolic_of_comp H.property.1 a.hom hd D D
  obtain ⟨g, hg⟩ := map_parabolic_of_comp H.property.1 a.inv hd' D D
  letI := inclusion_mono B
  refine ⟨B, ⟨f, g, ?_, ?_⟩, hB, hQB, hroots, hf.symm⟩
  · apply (cancel_mono B.inclusion).mp
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, a.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono B.inclusion).mp
    rw [Category.assoc, hf, ← Category.assoc, hg, Category.assoc, a.inv_hom_id,
      Category.comp_id, Category.id_comp]


section Torsion

open Filter

private def circleRoot (p n : ℕ) : Circle :=
  Circle.exp (2 * Real.pi / (p : ℝ) ^ n)

private theorem circleRoot_pow (p : ℕ) (hp : 0 < p) (n : ℕ) :
    circleRoot p n ^ (p ^ n) = 1 := by
  rw [circleRoot, ← Circle.exp_natCast_mul, Nat.cast_pow]
  have h : (p : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  rw [show (p : ℝ) ^ n * (2 * Real.pi / (p : ℝ) ^ n) = 2 * Real.pi by field_simp]
  exact Circle.exp_two_pi

private theorem circleRoot_succ (p : ℕ) (hp : 0 < p) (n : ℕ) :
    circleRoot p (n + 1) ^ p = circleRoot p n := by
  rw [circleRoot, circleRoot, ← Circle.exp_natCast_mul, pow_succ]
  have h : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  congr 1
  field_simp

private theorem circleRoot_generates_dense (p : ℕ) (hp : 1 < p) (N : ℕ)
    (J : Subgroup Circle) (hJ : IsClosed (J : Set Circle))
    (hroot : ∀ n ≥ N, circleRoot p n ∈ J) : J = ⊤ := by
  let D : AddSubgroup ℝ := J.toAddSubgroup.comap Circle.expHom
  have hD : IsClosed (D : Set ℝ) := hJ.preimage Circle.exp.continuous
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have ht : Tendsto (fun n : ℕ => 2 * Real.pi / (p : ℝ) ^ n) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    simpa only [mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hpR)).const_mul
        (2 * Real.pi)
  have hdense := D.dense_of_not_isolated_zero (by
    intro ε hε
    obtain ⟨n, hn, hlt⟩ := ((eventually_ge_atTop N).and ((tendsto_order.mp ht).2 ε hε)).exists
    refine ⟨2 * Real.pi / (p : ℝ) ^ n, hroot n hn, ?_, hlt⟩
    positivity)
  rw [Subgroup.eq_top_iff']
  intro z
  obtain ⟨x, rfl⟩ := Circle.exp_surjective z
  have hx : x ∈ closure (D : Set ℝ) := by rw [hdense.closure_eq]; exact Set.mem_univ x
  rwa [hD.closure_eq] at hx

variable {k E X : Type*} [Field k] [AddCommGroup E] [Module k E] [Group X]

/-- The subgroup fixing a vector in a linear action. -/
private def vectorStabilizer (ρ : X →* (E ≃ₗ[k] E)) (v : E) : Subgroup X where
  carrier := {x | ρ x v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ g v = v at hg
    change ρ h v = v at hh
    change ρ (g * h) v = v
    rw [map_mul, LinearEquiv.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g v = v at hg
    change ρ g⁻¹ v = v
    rw [map_inv]
    exact (LinearEquiv.symm_apply_eq _).mpr hg.symm

private theorem circleRoot_detects_fixed [FiniteDimensional k E] [TopologicalSpace E] [T2Space E]
    (ρ : Circle →* (E ≃ₗ[k] E)) (hρ : ∀ v, Continuous (fun z : Circle => ρ z v))
    (p : ℕ) (hp : 1 < p) :
    ∃ n : ℕ, ∀ v : E, ρ (circleRoot p n) v = v → ∀ z, ρ z v = v := by
  classical
  let W (n : ℕ) := ((ρ (circleRoot p n)).toLinearMap - LinearMap.id).ker
  have hm (n : ℕ) (v : E) : v ∈ W n ↔ ρ (circleRoot p n) v = v := by
    change ρ (circleRoot p n) v - v = 0 ↔ _
    exact sub_eq_zero
  have hmono : Antitone W := antitone_nat_of_succ_le fun n v hv => by
    apply (hm n v).mpr
    rw [← circleRoot_succ p (by omega) n]
    exact (vectorStabilizer ρ v).pow_mem ((hm _ _).mp hv) p
  let d (n : ℕ) := Module.finrank k (W n)
  have hex : ∃ m : ℕ, ∃ n : ℕ, d n = m := ⟨d 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  refine ⟨N, fun v hv z => ?_⟩
  let J := vectorStabilizer ρ v
  have hJ : IsClosed (J : Set Circle) := isClosed_eq (hρ v) continuous_const
  have hr (n : ℕ) (hn : N ≤ n) : circleRoot p n ∈ J := by
    have hdim : d N ≤ d n := hN ▸ Nat.find_min' hex ⟨n, rfl⟩
    have he : W n = W N := Submodule.eq_of_le_of_finrank_le (hmono hn) hdim
    exact (hm n v).mp (he.symm ▸ (hm N v).mpr hv)
  have he := circleRoot_generates_dense p hp N J hJ hr
  exact show z ∈ J from he.symm ▸ Subgroup.mem_top z

private theorem circleProduct_torsion_detects_fixed {m : ℕ}
    [FiniteDimensional k E] [TopologicalSpace E] [T2Space E]
    (ρ : (Fin m → Circle) →* (E ≃ₗ[k] E))
    (hρ : ∀ v, Continuous (fun x : Fin m → Circle => ρ x v)) :
    ∃ t : Fin m → Circle, IsOfFinOrder t ∧
      ∀ v : E, ρ t v = v → ∀ z, ρ z v = v := by
  classical
  let p : Fin m ↪ Nat.Primes := Fin.valEmbedding.trans (Infinite.natEmbedding Nat.Primes)
  let coord (j : Fin m) := MonoidHom.mulSingle (fun _ : Fin m => Circle) j
  have hcoordCont (j : Fin m) : Continuous (coord j) := by
    apply continuous_pi
    intro l
    by_cases h : l = j
    · subst l
      simpa [coord, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] using
        (show Continuous (fun x : Circle => x) from continuous_id)
    · simpa [coord, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h] using
        (continuous_const : Continuous (fun _ : Circle => (1 : Circle)))
  choose n hn using fun j : Fin m =>
    circleRoot_detects_fixed (ρ.comp (coord j)) (fun v => (hρ v).comp (hcoordCont j))
      (p j).val (p j).prop.one_lt
  let e (j : Fin m) := (p j).val ^ n j
  let t (j : Fin m) := circleRoot (p j).val (n j)
  have he (j : Fin m) : t j ^ e j = 1 := circleRoot_pow _ (p j).prop.pos _
  have ht : IsOfFinOrder t := by
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨∏ j, e j, ?_, funext fun j => ?_⟩
    · exact Finset.prod_pos fun j _ => pow_pos (p j).prop.pos _
    · change t j ^ (∏ l, e l) = 1
      apply (orderOf_dvd_iff_pow_eq_one).mp
      exact ((orderOf_dvd_iff_pow_eq_one).mpr (he j)).trans
        (Finset.dvd_prod_of_mem e (Finset.mem_univ j))
  refine ⟨t, ht, fun v hv z => ?_⟩
  let J := vectorStabilizer ρ v
  have hj (j : Fin m) : coord j (t j) ∈ J := by
    let q := ∏ l ∈ Finset.univ.erase j, e l
    have hpower : t ^ q = coord j (t j ^ q) := by
      funext l
      change t l ^ q = Pi.mulSingle (M := fun _ : Fin m => Circle) j (t j ^ q) l
      by_cases h : l = j
      · subst l
        rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        apply (orderOf_dvd_iff_pow_eq_one).mp
        exact ((orderOf_dvd_iff_pow_eq_one).mpr (he l)).trans
          (Finset.dvd_prod_of_mem e (Finset.mem_erase.mpr ⟨h, Finset.mem_univ l⟩))
    have hc : q.Coprime (orderOf (t j)) := by
      refine Nat.Coprime.coprime_dvd_right ((orderOf_dvd_iff_pow_eq_one).mpr (he j)) ?_
      apply Nat.coprime_prod_left_iff.mpr
      intro l hl
      have hne : (p l).val ≠ (p j).val := fun hh =>
        (Finset.mem_erase.mp hl).1 (p.injective (Subtype.ext hh))
      exact ((Nat.coprime_primes (p l).prop (p j).prop).mpr hne).pow _ _
    obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hc
    have hv' : coord j (t j ^ q) ∈ J := hpower ▸ J.pow_mem hv q
    have h := J.pow_mem hv' a
    rwa [← map_pow, ha] at h
  have hcoord (j : Fin m) : coord j (z j) ∈ J := hn j v (hj j) (z j)
  have hprod : (∏ j, coord j (z j)) = z := by
    funext l
    rw [Finset.prod_apply]
    simp only [coord, MonoidHom.mulSingle_apply]
    rw [Finset.prod_eq_single l (fun j _ h => Pi.mulSingle_eq_of_ne h.symm _) (by simp),
      Pi.mulSingle_eq_same]
  exact show z ∈ J from hprod ▸ J.prod_mem (fun j _ => hcoord j)

end Torsion


section MatrixCentralizers

open Arithmetic.AdelicGroups (PointsIn asMatrix)
open Specs.IntegralModels (MatrixRealization)
open Specs.ArchimedeanLieChart (conjugate)
open scoped Matrix.Norms.Operator

open private asMatrix_isClosedEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

private def unitConjugation (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    Aˣ →* (A ≃ₗ[ℝ] A) where
  toFun g :=
    { toFun := conjugate g
      invFun := conjugate g⁻¹
      left_inv := fun x => by simp [conjugate, mul_assoc]
      right_inv := fun x => by simp [conjugate, mul_assoc]
      map_add' := fun x y => by simp [conjugate, mul_add, add_mul]
      map_smul' := fun t x => by simp [conjugate] }
  map_one' := by
    ext x
    change conjugate 1 x = x
    simp [conjugate]
  map_mul' g h := by
    ext x
    change conjugate (g * h) x = conjugate g (conjugate h x)
    simp [conjugate, mul_assoc]

private theorem conjugate_eq_self_iff {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (u : Aˣ) (x : A) :
    conjugate u x = x ↔ Commute (u : A) x := by
  change (u : A) * x * ↑u⁻¹ = x ↔ (u : A) * x = x * (u : A)
  constructor
  · intro h
    simpa [mul_assoc] using congrArg (· * (u : A)) h
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

/-- A single finite-order point of a compact torus detects commutation with
the whole torus, in the given closed matrix realization. -/
theorem exists_torsion_with_same_centralizer {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    (S : Subgroup (PointsIn i ℂ)) (hS : IsCompactTorus S) :
    ∃ s : S, IsOfFinOrder s.val ∧
      Subgroup.centralizer ({s.val} : Set (PointsIn i ℂ)) =
        Subgroup.centralizer (S : Set (PointsIn i ℂ)) := by
  obtain ⟨m, e, he, _⟩ := hS
  let A := Matrix (Specs.Unipotent.Index i.size) (Specs.Unipotent.Index i.size) ℂ
  let σ : (Fin m → Circle) →* Aˣ :=
    (asMatrix i ℂ).comp (S.subtype.comp e.toMonoidHom)
  let ρ := (unitConjugation A).comp σ
  have hσ : Continuous σ :=
    (asMatrix_isClosedEmbedding i ℂ).continuous.comp (continuous_subtype_val.comp he)
  have hρ (x : A) : Continuous (fun z => ρ z x) := by
    change Continuous (fun z => (σ z : A) * x * ((σ z)⁻¹ : Aˣ).val)
    exact ((Units.continuous_val.comp hσ).mul continuous_const).mul
      (Units.continuous_val.comp hσ.inv)
  obtain ⟨t, ht, hfix⟩ := circleProduct_torsion_detects_fixed ρ hρ
  let s := e t
  refine ⟨s, (S.subtype.comp e.toMonoidHom).isOfFinOrder ht, ?_⟩
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨z, hz⟩ := e.surjective (⟨h, hh⟩ : S)
    have hcomm : Commute (asMatrix i ℂ s.val) (asMatrix i ℂ g) :=
      (show Commute s.val g from hg.symm).map (asMatrix i ℂ)
    have htfix : ρ t (asMatrix i ℂ g).val = (asMatrix i ℂ g).val :=
      (conjugate_eq_self_iff _ _).mpr hcomm.units_val
    have hzfix : Commute (σ z).val (asMatrix i ℂ g).val :=
      (conjugate_eq_self_iff _ _).mp (hfix _ htfix z)
    have hmat : σ z = asMatrix i ℂ h :=
      congrArg (fun x : S => asMatrix i ℂ x.val) hz
    rw [hmat] at hzfix
    exact (asMatrix_isClosedEmbedding i ℂ).injective (by
      rw [map_mul, map_mul]
      exact Units.ext hzfix.eq)
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hg) s.val s.prop).symm

end MatrixCentralizers


section AlgebraicTorus

open Arithmetic.AdelicGroups (PointsIn)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.ExceptionalCompactInner (HasExceptionalType)
open Specs.ExceptionalTorsionCentralizers (ExceptionalAlcoveInputs ComplexPoints RootGenerators torusPoint)
open Specs.IntegralModels (MatrixRealization)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.Pinning (SplitBorelPair)
open Specs.RootGroups (rootPoint)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

open private rootPoint_injective_of_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private transportComplexPoints transportComplexPoints_apply transportComplexPoints_comp
  torsionCentralizer_pathConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner

private theorem roots_nontrivial_at_abelian_centralizer
    (P : SplitBorelPair ℂ) (s : ComplexPoints P.T.group) (U : RootSubgroupFamily P.T)
    (hgen : Subgroup.centralizer ({torusPoint s} : Set (ComplexPoints P.G.val)) =
      Subgroup.closure (Set.range (torusPoint (P := P)) ∪ RootGenerators U s))
    (hab : ∀ x y : Subgroup.centralizer ({torusPoint s} : Set (ComplexPoints P.G.val)),
      Commute x.val y.val) :
    ∀ α : ↥(absoluteRoots P.T), characterValue α.val complexTest s ≠ 1 := by
  intro α hα
  obtain ⟨_, _, hV⟩ :=
    (RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 α.val α.prop
  obtain ⟨V, _, _, _, ⟨A, r, hr⟩, huniq⟩ := hV
  obtain ⟨j, hj⟩ := (huniq (U α).val (U α).prop).1
  let x := r.hom ≫ V.inclusion
  let z : ComplexPoints P.G.val := rootPoint x complexTest 1
  have hz : z ∈ Subgroup.centralizer ({torusPoint s} : Set (ComplexPoints P.G.val)) := by
    rw [hgen]
    apply Subgroup.subset_closure
    apply Or.inr
    refine ⟨α, hα, (rootPoint r.hom complexTest 1) ≫ j.hom.hom, ?_⟩
    have h := congrArg (fun a : V.group ⟶ P.G.val => a.hom.hom) hj
    change (rootPoint r.hom complexTest 1 ≫ j.hom.hom) ≫ (U α).val.inclusion.hom.hom = z
    rw [Category.assoc]
    change rootPoint r.hom complexTest 1 ≫ (j ≫ (U α).val.inclusion).hom.hom = z
    rw [hj]
    exact Category.assoc _ _ _
  obtain ⟨c, hc⟩ := LinearAlgebraicGroups.RankOneFlag.exists_positive_cocharacter P.split α.prop.1
  let b : ℂˣ := Units.mk0 2 (by norm_num)
  let v := cocharacterPoint c complexTest b
  let g := torusPoint (P := P) v
  have hg : g ∈ Subgroup.centralizer ({torusPoint s} : Set (ComplexPoints P.G.val)) := by
    rw [hgen]
    exact Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)
  have he := hr complexTest v 1
  change g * z * g⁻¹ = rootPoint x complexTest (characterValue α.val complexTest v * 1) at he
  have heq : g * z = z * g := (hab ⟨g, hg⟩ ⟨z, hz⟩).eq
  rw [heq, mul_assoc, mul_inv_cancel, mul_one, mul_one] at he
  letI := inclusion_mono V
  letI : Mono x := mono_comp _ _
  letI : Mono x.hom.hom := Functor.map_mono (Grp.forget (SchemeOver ℂ)) x
  have heval : characterValue α.val complexTest v = 1 :=
    (rootPoint_injective_of_mono x complexTest he).symm
  rw [(RootData.CharacterPairing.characterPairingComposition P.T.group α.val c).2 complexTest b] at heval
  have heval' : (2 : ℂ) ^ pairing P.T.group α.val c = 1 := by
    simpa only [Units.val_zpow_eq_zpow_val, b, Units.val_mk0] using heval
  have hevalR : (2 : ℝ) ^ pairing P.T.group α.val c = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_zpow, Complex.ofReal_ofNat, Complex.ofReal_one]
    exact heval'
  exact (ne_of_gt (one_lt_zpow₀ (by norm_num) hc)) hevalR

private theorem onPoints_transport {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    {P : SplitBorelPair ℂ} (hP : P.G = baseChangedAlgebraicGroup ℂ G)
    {Q : GroupScheme ℂ} (f : Q ⟶ P.G.val) (z : GroupPoints Q complexTest) :
    onPoints (i := i) hP f z =
      (baseChangePointGroupEquiv ℂ G.val complexTest)
        (transportComplexPoints hP (z ≫ f.hom.hom)) := by
  rw [transportComplexPoints_comp]
  rfl

/-- An abelian complex centralizer of a compact torus is the point group of
an actual split maximal algebraic torus, and that compact torus meets the
nontrivial locus of every root. -/
theorem algebraicTorusOfAbelianCentralizer (G : AffineAlgebraicGroup ℝ)
    (i : MatrixRealization G) (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (htype : HasExceptionalType G) (S : Subgroup (PointsIn i ℂ)) (hS : IsCompactTorus S)
    (hab : ∀ x y : Subgroup.centralizer (S : Set (PointsIn i ℂ)), Commute x.val y.val) :
    ∃ (P : SplitBorelPair ℂ) (hP : P.G = baseChangedAlgebraicGroup ℂ G),
      (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) =
        Set.range (onPoints (i := i) hP P.T.inclusion) ∧
      ∀ α : ↥(absoluteRoots P.T), ∃ p : GroupPoints P.T.group complexTest,
        onPoints (i := i) hP P.T.inclusion p ∈ S ∧ characterValue α.val complexTest p ≠ 1 := by
  obtain ⟨s, hs, hsC⟩ := exists_torsion_with_same_centralizer i S hS
  let eC : ComplexPoints (baseChangedAlgebraicGroup ℂ G).val ≃* PointsIn i ℂ :=
    baseChangePointGroupEquiv ℂ G.val complexTest
  have hAlcove := ExceptionalCompactInner.exceptionalAlcove
  obtain ⟨P, hP, t, _, U, ht, _, hgen⟩ :=
    ExceptionalTorsionCentralizers.torsionCentralizer
      ⟨hAlcove.1, hAlcove.2.1, hAlcove.2.2.1⟩ G hG hsc htype
      (eC.symm s.val) (eC.symm.toMonoidHom.isOfFinOrder hs)
  let e : ComplexPoints P.G.val ≃* PointsIn i ℂ := (transportComplexPoints hP).trans eC
  have he : e (torusPoint t) = s.val := by
    change eC (transportComplexPoints hP (torusPoint t)) = s.val
    rw [transportComplexPoints_apply, ht, eC.apply_symm_apply]
  have hmem (x : ComplexPoints P.G.val) :
      e x ∈ Subgroup.centralizer (S : Set (PointsIn i ℂ)) ↔
        x ∈ Subgroup.centralizer ({torusPoint t} : Set (ComplexPoints P.G.val)) := by
    rw [← hsC, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← he, ← map_mul, ← map_mul, e.injective.eq_iff]
  have hAb (x y : Subgroup.centralizer ({torusPoint t} : Set (ComplexPoints P.G.val))) :
      Commute x.val y.val := by
    apply e.injective
    rw [map_mul, map_mul]
    exact (hab ⟨e x.val, (hmem _).mpr x.prop⟩ ⟨e y.val, (hmem _).mpr y.prop⟩).eq
  have hroot := roots_nontrivial_at_abelian_centralizer P t U hgen hAb
  have hnone : RootGenerators U t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨α, hα, _⟩
    exact hroot α hα
  let f : ComplexPoints P.T.group →* ComplexPoints P.G.val :=
    (((groupPointsFunctor ℂ).map P.T.inclusion).app complexTest).hom
  change Subgroup.centralizer _ = Subgroup.closure ((f.range : Set _) ∪ RootGenerators U t) at hgen
  rw [hnone, Set.union_empty, Subgroup.closure_eq] at hgen
  have hcomp (z : ComplexPoints P.T.group) :
      onPoints (i := i) hP P.T.inclusion z = e (f z) :=
    onPoints_transport i hP P.T.inclusion z
  refine ⟨P, hP, ?_, fun α => ⟨t, ?_, hroot α⟩⟩
  · ext x
    constructor
    · intro hx
      have hx' : e.symm x ∈ Subgroup.centralizer ({torusPoint t} : Set (ComplexPoints P.G.val)) :=
        (hmem _).mp (by rwa [e.apply_symm_apply])
      rw [hgen] at hx'
      obtain ⟨p, hp⟩ := hx'
      exact ⟨p, (hcomp p).trans ((congrArg e hp).trans (e.apply_symm_apply x))⟩
    · rintro ⟨p, rfl⟩
      rw [hcomp]
      exact (hmem _).mpr (hgen.symm ▸ ⟨p, rfl⟩)
  · rw [hcomp, show f t = torusPoint t from rfl, he]
    exact s.prop

end AlgebraicTorus


section Restrictions

open CategoryTheory.Limits Opposite
open Specs.Pinning (SplitBorelPair)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization)
open Arithmetic.AdelicGroups (PointsIn)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints fixedSubgroup)

private theorem factor_group_of_complexPoints {A G : GroupScheme ℂ}
    [IsReduced A.X.left] [LocallyOfFiniteType A.X.hom]
    (Q : ClosedSubgroup G) (f : A ⟶ G)
    (hf : ∀ x : GroupPoints A complexTest, ∃ y : GroupPoints Q.group complexTest,
      y ≫ Q.inclusion.hom.hom = x ≫ f.hom.hom) :
    ∃ g : A ⟶ Q.group, g ≫ Q.inclusion = f := by
  let p := pullback.fst f Q.inclusion
  let F := Grp.forget (SchemeOver ℂ) ⋙ Over.forget _
  let hp := (IsPullback.of_hasPullback f Q.inclusion).map F
  haveI : IsClosedImmersion p.hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip Q.isClosedImmersion
  have hc : IsClosed (Set.range p.hom.hom.left) :=
    (IsClosedImmersion.isClosedEmbedding p.hom.hom.left).isClosed_range
  have hj : closedPoints A.X.left ⊆ Set.range p.hom.hom.left := by
    intro a ha
    let z := pointOfClosedPoint A.X.hom a ha
    let x : GroupPoints A complexTest := Over.homMk z (by
      rw [pointOfClosedPoint_comp]
      change (𝟙 _) = Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))
      rw [show algebraMap ℂ ℂ = RingHom.id ℂ from rfl, CommRingCat.ofHom_id, Spec.map_id])
    obtain ⟨y, he⟩ := hf x
    have hw : x.left ≫ (F.map f) = y.left ≫ (F.map Q.inclusion) :=
      congrArg Over.Hom.left he.symm
    let v := hp.lift x.left y.left hw
    have hv : v ≫ p.hom.hom.left = x.left := hp.lift_fst _ _ _
    refine ⟨v (IsLocalRing.closedPoint ℂ), ?_⟩
    exact (congrArg (fun f : (Spec (CommRingCat.of ℂ)) ⟶ A.X.left =>
      f (IsLocalRing.closedPoint ℂ)) hv).trans (pointOfClosedPoint_apply _ _ _ _)
  letI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  haveI : Surjective p.hom.hom.left := ⟨by
    intro a
    apply closure_minimal hj hc
    rw [closure_closedPoints]
    trivial⟩
  haveI : IsIso p.hom.hom.left := isIso_of_isClosedImmersion_of_surjective p.hom.hom.left
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of ℂ))).map p.hom.hom) :=
    inferInstanceAs (IsIso p.hom.hom.left)
  haveI : IsIso p.hom.hom := isIso_of_reflects_iso p.hom.hom (Over.forget _)
  let e := Grp.mkIso' (asIso p.hom.hom)
  have he : e.hom = p := Grp.hom_ext _ _ rfl
  haveI : IsIso p := he ▸ (inferInstance : IsIso e.hom)
  refine ⟨inv p ≫ pullback.snd f Q.inclusion, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

private theorem restrict_involutive_group_iso {G : GroupScheme ℂ} (Q : ClosedSubgroup G)
    [IsReduced Q.group.X.left] [LocallyOfFiniteType Q.group.X.hom]
    (a : G ≅ G) (haSq : a.hom ≫ a.hom = 𝟙 _)
    (h : ∀ x : GroupPoints Q.group complexTest, ∃ y : GroupPoints Q.group complexTest,
      y ≫ Q.inclusion.hom.hom = (x ≫ Q.inclusion.hom.hom) ≫ a.hom.hom.hom) :
    ∃ b : Q.group ≅ Q.group, Q.inclusion ≫ a.hom = b.hom ≫ Q.inclusion ∧
      b.hom ≫ b.hom = 𝟙 _ := by
  obtain ⟨b, hb⟩ := factor_group_of_complexPoints Q (Q.inclusion ≫ a.hom)
    (fun x => by
      obtain ⟨y, hy⟩ := h x
      exact ⟨y, hy.trans (Category.assoc (show Points Q.group.X complexTest from x) _ _)⟩)
  letI := inclusion_mono Q
  have hbSq : b ≫ b = 𝟙 _ := by
    apply (cancel_mono Q.inclusion).mp
    rw [Category.assoc, hb, ← Category.assoc, hb, Category.assoc, haSq,
      Category.comp_id, Category.id_comp]
  exact ⟨⟨b, b, hbSq, hbSq⟩, hb.symm, hbSq⟩

end Restrictions


section CompactCentralizer

open Filter NormedSpace
open Specs.ArchimedeanLieChart (ClosedSubgroupChart expUnit exponentialLines)
open ArchimedeanLieChart (closedSubgroupExponential continuous_expUnit expUnit_val expUnit_zero)
open Specs.ExceptionalCompactInner (fixedSubgroup)
open scoped unitInterval

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [Algebra ℂ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]

omit [Algebra ℂ A] in
private theorem expUnit_map (κ : A ≃ₐ[ℝ] A) (x : A) :
    Units.map κ.toMonoidHom (expUnit x) = expUnit (κ x) := by
  apply Units.ext
  change κ (expUnit x).val = (expUnit (κ x)).val
  simp only [expUnit_val]
  apply map_exp_of_mem_ball (𝕂 := ℝ) κ.toRingHom κ.toLinearMap.continuous_of_finiteDimensional
  rw [expSeries_radius_eq_top]
  exact edist_lt_top _ _

omit [Algebra ℂ A] [FiniteDimensional ℝ A] in
private theorem commute_of_exp_commute (x y : A)
    (h : ∀ t : ℝ, Commute x (expUnit (t • y)).val) : Commute x y := by
  have hd : HasDerivAt (fun t : ℝ => (expUnit (t • y)).val) y 0 := by
    simpa only [expUnit_val, zero_smul, exp_zero, one_mul] using
      hasDerivAt_exp_smul_const y (0 : ℝ)
  exact ((hd.const_mul x).congr_of_eventuallyEq
    (Eventually.of_forall fun t => (h t).eq.symm)).unique (hd.mul_const x)

omit [Algebra ℂ A] [FiniteDimensional ℝ A] in
private theorem expUnit_of_commute {x y : A} (h : Commute x y) :
    Commute (expUnit x) (expUnit y) := by
  exact Units.ext h.exp.eq

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
private theorem abelian_of_fixed_tangent (W : Submodule ℝ A)
    (κ : A ≃ₐ[ℝ] A) (hκ : Function.Involutive κ)
    (hanti : ∀ c : ℂ, ∀ x : A, κ (c • x) = Complex.conjAe c • κ x)
    (hW : ∀ x ∈ W, κ x ∈ W) (hComplex : ∀ (c : ℂ) (x : A), x ∈ W → c • x ∈ W)
    (hfix : ∀ x ∈ W, ∀ y ∈ W, κ x = x → κ y = y → Commute x y) :
    ∀ x ∈ W, ∀ y ∈ W, Commute x y := by
  have htwo : Complex.conjAe (2 : ℂ) = 2 := map_ofNat _ _
  have hi : Complex.conjAe Complex.I = -Complex.I := Complex.conj_I
  have decompose (z : A) (hz : z ∈ W) :
      ∃ u ∈ W, ∃ v ∈ W, κ u = u ∧ κ v = v ∧ z = u + Complex.I • v := by
    let u := (2 : ℂ)⁻¹ • (z + κ z)
    let v := (-Complex.I / 2) • (z - κ z)
    refine ⟨u, hComplex _ _ (W.add_mem hz (hW z hz)),
      v, hComplex _ _ (W.sub_mem hz (hW z hz)), ?_, ?_, ?_⟩
    · dsimp only [u]
      rw [hanti, map_add, hκ, add_comm z (κ z), map_inv₀, htwo]
    · dsimp only [v]
      rw [hanti, map_sub, hκ]
      rw [map_div₀, map_neg, hi, neg_neg, htwo, ← neg_sub z (κ z),
        smul_neg, ← neg_smul, neg_div]
    · have hI : Complex.I * (-Complex.I / 2) = (2 : ℂ)⁻¹ := by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_div]
      dsimp only [u, v]
      rw [smul_smul, hI, ← smul_add, show z + κ z + (z - κ z) = z + z by abel,
        ← two_smul ℂ z, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  intro x hx y hy
  obtain ⟨u, hu, v, hv, hu', hv', rfl⟩ := decompose x hx
  obtain ⟨p, hp, q, hq, hp', hq', rfl⟩ := decompose y hy
  exact ((hfix u hu p hp hu' hp').add_right
    ((hfix u hu q hq hu' hq').smul_right _)).add_left
    (((hfix v hv p hp hv' hp').add_right
      ((hfix v hv q hq hv' hq').smul_right _)).smul_left _)

private theorem isClosed_centralizer {Q : Type*} [Group Q] [TopologicalSpace Q]
    [ContinuousMul Q] [T2Space Q] (S : Set Q) :
    IsClosed (Subgroup.centralizer S : Set Q) := by
  have he : (Subgroup.centralizer S : Set Q) = ⋂ s : S, {x | s.val * x = x * s.val} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq, Subgroup.mem_centralizer_iff,
      Subtype.forall]
  rw [he]
  exact isClosed_iInter fun _ => isClosed_eq (continuous_const.mul continuous_id)
    (continuous_id.mul continuous_const)

private theorem compactTorus_commute {P : Type*} [Group P] [TopologicalSpace P]
    (T : Subgroup P) (hT : IsCompactTorus T) (x y : T) : Commute x.val y.val := by
  obtain ⟨n, e, _, _⟩ := hT
  have h : Commute (e.symm x) (e.symm y) := mul_comm _ _
  have h' := h.map (T.subtype.comp e.toMonoidHom)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    Subgroup.subtype_apply] using h' 

/-- A semilinear matrix action on a covered complex group lets the exponential
lines of its compact centralizer span the complex centralizer tangent. -/
theorem centralizer_commute_of_covered_compact_component
    {P Q : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q]
    (q : P →* Q) (hq : IsCoveringMap q) (hqSurj : Function.Surjective q)
    (m : Q →* Aˣ) (hm : IsClosedEmbedding m)
    (hComplex : ∀ (c : ℂ) (x : A), x ∈ exponentialLines m.range →
      c • x ∈ exponentialLines m.range)
    (ω : MulAut P) (hωc : Continuous ω)
    (κ : A ≃ₐ[ℝ] A) (hκ : Function.Involutive κ)
    (hanti : ∀ (c : ℂ) (x : A), κ (c • x) = Complex.conjAe c • κ x)
    (hω : ∀ x : P, m (q (ω x)) = Units.map κ.toMonoidHom (m (q x)))
    (S T : Subgroup P) (hS : S ≤ fixedSubgroup ω) (hT : IsCompactTorus T)
    (hTC : (T : Set P) = identityComponent (fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set P)))
    [ConnectedSpace (Subgroup.centralizer (S : Set P))] :
    ∀ x y : Subgroup.centralizer (S : Set P), Commute x.val y.val := by
  let j := m.comp q
  let S' := j '' (S : Set P)
  let J := m.range ⊓ Subgroup.centralizer S'
  have hJ : IsClosed (J : Set Aˣ) := hm.isClosed_range.inter (isClosed_centralizer S')
  let C := (closedSubgroupExponential A J hJ).some
  have hκJ (u : Aˣ) (hu : u ∈ J) : Units.map κ.toMonoidHom u ∈ J := by
    obtain ⟨v, hv⟩ := hu.1
    obtain ⟨w, rfl⟩ := hqSurj v
    have hpre : Units.map κ.toMonoidHom u = j (ω w) := by
      change Units.map κ.toMonoidHom u = m (q (ω w))
      rw [← hv, hω]
    refine ⟨⟨q (ω w), hpre.symm⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs' : Units.map κ.toMonoidHom (j s) = j s := by
      change Units.map κ.toMonoidHom (m (q s)) = m (q s)
      rw [← hω, (hS hs : ω s = s)]
    have hc := Subgroup.mem_centralizer_iff.mp hu.2 (j s) ⟨s, hs, rfl⟩
    simpa only [map_mul, hs'] using congrArg (Units.map κ.toMonoidHom) hc
  have hsmul (t : ℝ) (x : A) : κ (t • x) = t • κ x :=
    κ.toLinearMap.map_smul t x
  have hκW (x : A) (hx : x ∈ C.tangent) : κ x ∈ C.tangent := by
    apply (C.mem_tangent _).mpr
    intro t
    rw [← hsmul, ← expUnit_map]
    exact hκJ _ ((C.mem_tangent _).mp hx t)
  have hcW (c : ℂ) (x : A) (hx : x ∈ C.tangent) : c • x ∈ C.tangent := by
    have hl := (C.mem_tangent x).mp hx
    apply (C.mem_tangent _).mpr
    intro t
    refine ⟨hComplex c x (fun a => (hl a).1) t, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro u hu
    have hu' : Commute (u : A) x := commute_of_exp_commute _ _ fun a =>
      (show Commute u (expUnit (a • x)) from
        Subgroup.mem_centralizer_iff.mp ((hl a).2) u hu).units_val
    have he : Commute (u : A) (expUnit (t • (c • x))).val := by
      rw [expUnit_val]
      apply Commute.exp_right
      exact (hu'.smul_right c).smul_right t
    exact Units.ext he.eq
  have hline (x : A) (hx : x ∈ C.tangent) (hfix : κ x = x) (t : ℝ) :
      ∃ u : T, j u.val = expUnit (t • x) := by
    let E : Q ≃ₜ m.range := hm.isEmbedding.toHomeomorph
    let F : ContinuousMap unitInterval m.range :=
      ⟨fun r => ⟨expUnit (((r : ℝ) * t) • x), ((C.mem_tangent _).mp hx _).1⟩,
        (continuous_expUnit.comp ((continuous_subtype_val.mul continuous_const).smul
          continuous_const)).subtype_mk _⟩
    let PathQ : ContinuousMap unitInterval Q :=
      ⟨fun t => E.symm (F t), E.symm.continuous.comp F.continuous⟩
    have hPathQ (r : unitInterval) : m (PathQ r) = expUnit (((r : ℝ) * t) • x) := by
      exact congrArg Subtype.val (E.apply_symm_apply (F r))
    have h0 : PathQ 0 = q (1 : P) := hm.injective (by rw [hPathQ, map_one, map_one]; simp)
    obtain ⟨lifted, hlifted, hlifted0⟩ := hq.exists_path_lifts PathQ 1 h0
    have hliftedPathQ (r : unitInterval) : q (lifted r) = PathQ r := congr_fun hlifted r
    have hliftedj (r : unitInterval) : j (lifted r) = expUnit (((r : ℝ) * t) • x) := by
      change m (q (lifted r)) = _
      rw [hliftedPathQ, hPathQ]
    have hliftedω : (fun r : unitInterval => ω (lifted r)) = lifted := by
      apply hq.eq_of_comp_eq (hωc.comp lifted.continuous) lifted.continuous _ 0
      · change ω (lifted 0) = lifted 0
        rw [hlifted0, map_one]
      · funext r
        apply hm.injective
        change j (ω (lifted r)) = j (lifted r)
        rw [show j (ω (lifted r)) = Units.map κ.toMonoidHom (j (lifted r)) from hω _,
          hliftedj, expUnit_map, hsmul, hfix]
    have hliftedC (r : unitInterval) : lifted r ∈ Subgroup.centralizer (S : Set P) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro s hs
      have hh : (fun r : unitInterval => s * lifted r) = fun r => lifted r * s := by
        apply hq.eq_of_comp_eq (continuous_const.mul lifted.continuous)
          (lifted.continuous.mul continuous_const) _ 0
        · change s * lifted 0 = lifted 0 * s
          rw [hlifted0, mul_one, one_mul]
        · funext r
          apply hm.injective
          change j (s * lifted r) = j (lifted r * s)
          rw [map_mul, map_mul, hliftedj]
          exact Subgroup.mem_centralizer_iff.mp
            (((C.mem_tangent _).mp hx ((r : ℝ) * t)).2) _ ⟨s, hs, rfl⟩
      exact congr_fun hh r
    let K := fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set P)
    let liftedK : ContinuousMap unitInterval K := ⟨fun r => ⟨lifted r, congr_fun hliftedω r, hliftedC r⟩,
      lifted.continuous.subtype_mk _⟩
    have hliftedK0 : liftedK 0 = 1 := Subtype.ext hlifted0
    have hliftedK1 : liftedK 1 ∈ connectedComponent (1 : K) := by
      rw [← hliftedK0]
      exact liftedK.continuous.mapsTo_connectedComponent 0 (isConnected_univ.subset_connectedComponent
        (Set.mem_univ 0) (Set.mem_univ 1))
    have ht : lifted 1 ∈ (T : Set P) := hTC.symm ▸ ⟨liftedK 1, hliftedK1, rfl⟩
    refine ⟨⟨lifted 1, ht⟩, ?_⟩
    simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul] using hliftedj 1
  have hcomm (x : A) (hx : x ∈ C.tangent) (y : A) (hy : y ∈ C.tangent)
      (hfx : κ x = x) (hfy : κ y = y) : Commute x y := by
    apply commute_of_exp_commute
    intro t
    apply Commute.symm
    apply commute_of_exp_commute
    intro u
    obtain ⟨a, ha⟩ := hline x hx hfx u
    obtain ⟨b, hb⟩ := hline y hy hfy t
    exact (hb ▸ ha ▸ ((compactTorus_commute T hT b a).map j)).units_val
  have hW := abelian_of_fixed_tangent C.tangent κ hκ hanti hκW hcW hcomm
  let V : Set J := Set.range fun x : C.tangent =>
    ⟨expUnit (x : A), by simpa only [one_smul] using (C.mem_tangent _).mp x.prop 1⟩
  let U := Subgroup.closure V
  have hV : V.Pairwise Commute := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact Subtype.ext (expUnit_of_commute (hW x x.prop y y.prop))
  letI : IsMulCommutative U := Subgroup.isMulCommutative_closure hV
  have hOne : (1 : J) ∈ C.expOpen.target := by
    have h0 := C.expOpen.map_source C.zero_mem
    have he : C.expOpen 0 = (1 : J) := Subtype.ext (by simpa using C.exp_chart 0 C.zero_mem)
    rwa [he] at h0
  have hOpen : IsOpen (U : Set J) := by
    apply U.isOpen_of_mem_nhds (g := 1)
    refine mem_of_superset (C.expOpen.open_target.mem_nhds hOne) ?_
    intro g hg
    let x := C.expOpen.symm g
    have he := C.exp_chart x (C.expOpen.map_target hg)
    rw [C.expOpen.right_inv hg] at he
    exact Subgroup.subset_closure ⟨x, Subtype.ext he.symm⟩
  let F : Subgroup.centralizer (S : Set P) → J :=
    fun a => ⟨j a.val, ⟨⟨q a.val, rfl⟩, Subgroup.mem_centralizer_iff.mpr (by
      rintro _ ⟨s, hs, rfl⟩
      exact ((show Commute s a.val from Subgroup.mem_centralizer_iff.mp a.prop s hs).map j).eq)⟩⟩
  have hF : Continuous F :=
    (hm.continuous.comp (hq.continuous.comp continuous_subtype_val)).subtype_mk _
  have hFU : ∀ a : Subgroup.centralizer (S : Set P), F a ∈ U := by
    have hclopen := (show IsClopen (U : Set J) from ⟨U.isClosed_of_isOpen hOpen, hOpen⟩).preimage hF
    have h := hclopen.eq_univ ⟨1, by
      change F 1 ∈ U
      have h1 : F 1 = 1 := Subtype.ext (map_one j)
      exact h1.symm ▸ U.one_mem⟩
    intro a
    have ha : a ∈ F ⁻¹' (U : Set J) := h.symm ▸ Set.mem_univ a
    exact ha
  intro x y
  have he (a : Subgroup.centralizer (S : Set P)) : Commute (q x.val) (q a.val) := by
    apply hm.injective
    rw [map_mul, map_mul]
    exact congrArg (fun b : U => b.val.val)
      (mul_comm' (⟨F x, hFU x⟩ : U) ⟨F a, hFU a⟩)
  have H := hq.eq_of_comp_eq
    (g₁ := fun a : Subgroup.centralizer (S : Set P) => x.val * a.val)
    (g₂ := fun a : Subgroup.centralizer (S : Set P) => a.val * x.val)
    (continuous_const.mul continuous_subtype_val) (continuous_subtype_val.mul continuous_const)
    (funext fun a => by
      change q (x.val * a.val) = q (a.val * x.val)
      rw [map_mul, map_mul]
      exact (he a).eq)
    1 (by simp)
  exact congr_fun H y

end CompactCentralizer


section AdjointMatrixAction

open Arithmetic.AdelicGroups (PointsIn asMatrix)
open Specs.ArchimedeanLieChart (exponentialLines tangentMatrix)
open ArchimedeanLieChart (baseChangeMatrixComparison)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints HasCompactDifferential HasExceptionalType
  fixedSubgroup realConjugation)
open Specs.IntegralModels (MatrixRealization)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.ExceptionalLieAutomorphismTransport (ActsByAdjoint matrixPoint matrixPointValue)
open LieAlgebrasAndRepresentations.RealForms (Conjugation)
open scoped Matrix Matrix.Norms.Operator
open Specs.ExceptionalComplexPointGeometry (pointMap)
open private asMatrix_isClosedEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private torsionCentralizer_pathConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner

open private adjoint_intertwines_groundField adjoint_intertwines_algebraic matrixAction
  realConjugation_involutive from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private tangentMatrix_linear_laws exponentialLines_matrix_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

private theorem complexTangent_of_matrixRange_eq {H : AffineAlgebraicGroup ℂ}
    (i : MatrixRealization H) (d : ℕ) (hd : i.size = d)
    (J : Subgroup (Matrix (Specs.Unipotent.Index d) (Specs.Unipotent.Index d) ℂ)ˣ)
    (hJ : (J : Set _) =
      cast (congrArg (fun n => Matrix.GeneralLinearGroup (Specs.Unipotent.Index n) ℂ) hd) ''
        ((asMatrix i ℂ).range : Set _)) :
    ∀ (c : ℂ) (x : Matrix (Specs.Unipotent.Index d) (Specs.Unipotent.Index d) ℂ),
      x ∈ exponentialLines J → c • x ∈ exponentialLines J := by
  subst d
  have he : J = (asMatrix i ℂ).range := SetLike.coe_injective (by simpa using hJ)
  rw [he]
  intro c x hx
  obtain ⟨v, hv⟩ := (exponentialLines_matrix_iff i x).mp hx
  refine (exponentialLines_matrix_iff i _).mpr
    ⟨scalePointKernel H.val c v, ?_⟩
  rw [(tangentMatrix_linear_laws i).2, hv]

private theorem complexTangent_of_real_matrixRange {Q : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization Q) :
    ∀ (c : ℂ) (x : Matrix (Specs.Unipotent.Index i.size) (Specs.Unipotent.Index i.size) ℂ),
      x ∈ exponentialLines (asMatrix i ℂ).range →
        c • x ∈ exponentialLines (asMatrix i ℂ).range := by
  obtain ⟨_, j, hj, e, _, hmat⟩ := baseChangeMatrixComparison ℝ ℂ Q i
  apply complexTangent_of_matrixRange_eq j i.size hj
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨asMatrix j ℂ (e.symm u), ⟨e.symm u, rfl⟩, ?_⟩
    rw [hmat, e.apply_symm_apply]
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨e u, (hmat u).symm⟩

private def conjugationEnd {L : Type} [LieRing L] [LieAlgebra ℂ L]
    (τ : Conjugation L) : Module.End ℂ L ≃ₐ[ℝ] Module.End ℂ L := by
  let F (M : Module.End ℂ L) : Module.End ℂ L :=
    { toFun := fun x => τ.map (M (τ.map x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change τ.map (M (τ.map (c • x))) = c • τ.map (M (τ.map x))
        rw [τ.antilinear, map_smul, τ.antilinear, star_star] }
  have hF (M : Module.End ℂ L) (x : L) : F M x = τ.map (M (τ.map x)) := rfl
  have hFF (M : Module.End ℂ L) : F (F M) = M := by
    ext x
    rw [hF, hF, τ.involutive, τ.involutive]
  exact {
    toFun := F
    invFun := F
    left_inv := hFF
    right_inv := hFF
    map_mul' := fun M N => by
      ext x
      change τ.map (M (N (τ.map x))) = τ.map (M (τ.map (τ.map (N (τ.map x)))))
      rw [τ.involutive]
    map_add' := fun M N => by
      ext x
      change τ.map (M (τ.map x) + N (τ.map x)) =
        τ.map (M (τ.map x)) + τ.map (N (τ.map x))
      exact map_add _ _ _
    commutes' := fun r => by
      ext x
      rw [Algebra.algebraMap_eq_smul_one]
      change τ.map ((r : ℝ) • τ.map x) = (r : ℝ) • x
      rw [map_smul, τ.involutive] }

private theorem conjugationEnd_apply {L : Type} [LieRing L] [LieAlgebra ℂ L]
    (τ : Conjugation L) (M : Module.End ℂ L) (x : L) :
    conjugationEnd τ M x = τ.map (M (τ.map x)) := rfl

private theorem toLinAlgEquiv_val {L I : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup L] [Module ℂ L] (b : Module.Basis I ℂ L)
    (M : Matrix.GeneralLinearGroup I ℂ) (x : L) :
    Matrix.toLinAlgEquiv b M.val x = matrixAction b M x := by
  rw [Matrix.toLinAlgEquiv_apply]
  change (∑ j, (M.val *ᵥ b.equivFun x) j • b j) =
    b.equivFun.symm (M.val *ᵥ b.equivFun x)
  rw [Module.Basis.equivFun_symm_apply]

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The adjoint representation realizes the given compact involution as
coefficient conjugation in the Lie space, including its precise real action
on matrices and the complex linearity of exponential directions. -/
private theorem compactAction_on_covered_matrices (G : AffineAlgebraicGroup ℝ)
    (i : MatrixRealization G) (hG : IsAbsolutelyAlmostSimple G)
    (ω : MulAut (PointsIn i ℂ)) (a : Aut (complexGroup G))
    (ha : ActsOnComplexPoints (i := i) a (fun x => ω (realConjugation G i x)))
    (hd : HasCompactDifferential a) :
    ∃ (Q : AffineAlgebraicGroup ℝ) (j : MatrixRealization Q)
      (p : PointsIn i ℂ →* PointsIn j ℂ)
      (κ : Matrix (Specs.Unipotent.Index j.size) (Specs.Unipotent.Index j.size) ℂ ≃ₐ[ℝ]
        Matrix (Specs.Unipotent.Index j.size) (Specs.Unipotent.Index j.size) ℂ),
      IsCoveringMap p ∧ Function.Surjective p ∧ Function.Involutive κ ∧
      (∀ (c : ℂ) x, κ (c • x) = Complex.conjAe c • κ x) ∧
      (∀ x : PointsIn i ℂ, asMatrix j ℂ (p (ω x)) =
        Units.map κ.toMonoidHom (asMatrix j ℂ (p x))) := by
  obtain ⟨s, τ, _, hτ⟩ := hd
  let L := Specs.Lie ℂ (Specs.ExceptionalLieAutomorphismTransport.complexGroup G)
  letI : LieRing L := s.lieRing
  letI : AddCommGroup L := s.lieRing.toAddCommGroup
  letI : LieAlgebra ℂ L := s.lieAlgebra
  letI : Module ℂ L := s.lieAlgebra.toModule
  obtain ⟨σL, hσL⟩ := ExceptionalLieAutomorphismTransport.groundFieldConjugation G s
  obtain ⟨Z, Q, q, d, N, U, jQ, jU, l, b, hquot, hcentral, hfin, hclosed, hU, hsurj,
     hgeom, hAdj, hbracket, hfull⟩ :=
    ExceptionalLieAutomorphismTransport.complexAdjointComparison G hG.1 s
  let j : MatrixRealization Q := ⟨d, N, l, jQ ≫ jU, hclosed⟩
  let p := pointMap i j q
  obtain ⟨_, hp, _, hcover⟩ := ExceptionalComplexPointGeometry.centralIsogenyCovering i j q hcentral
  let B : Module.Basis (Specs.Unipotent.Index d) ℂ L := b
  let τ' : Conjugation L := τ
  let E := (Matrix.toLinAlgEquiv B).restrictScalars ℝ
  let κ := E.trans ((conjugationEnd τ').trans E.symm)
  have hκ (M : Matrix (Specs.Unipotent.Index j.size) (Specs.Unipotent.Index j.size) ℂ) :
      E (κ M) = conjugationEnd τ' (E M) := E.apply_symm_apply _
  refine ⟨Q, j, p, κ, hcover, hp, ?_, ?_, ?_⟩
  · intro M
    apply E.injective
    rw [hκ, hκ]
    ext x
    rw [conjugationEnd_apply, conjugationEnd_apply, τ.involutive, τ.involutive]
  · intro c M
    apply E.injective
    have hE (r : ℂ) (m : Matrix (Specs.Unipotent.Index j.size) (Specs.Unipotent.Index j.size) ℂ) :
        E (r • m) = r • E m := (Matrix.toLinAlgEquiv B).toLinearMap.map_smul r m
    rw [hκ, hE, hE, hκ]
    apply LinearMap.ext
    intro x
    simp only [conjugationEnd_apply, LinearMap.smul_apply, τ'.antilinear]
    rfl
  · intro x
    have hD (v : Specs.Lie ℂ (complexGroup G)) :
        τ.map v = mapPointKernel a.asIso.hom (σL.map v) := by
      obtain ⟨w, hw, htw⟩ := hτ v
      have hinj : Function.Injective (Specs.ExceptionalLieAutomorphismTransport.onDual G) :=
        (baseChangePointGroupEquiv ℂ G.val (CommAlgCat.of ℂ (DualNumber ℂ))).injective
      have he : w = σL.map v :=
        Subtype.ext (hinj (hw.trans (hσL v).symm))
      rw [← he]
      exact htw
    have hσAdj := adjoint_intertwines_groundField q (jQ ≫ jU) l s b hAdj σL hσL
    have hh (v : Specs.Lie ℂ (complexGroup G)) :
        matrixAction b (asMatrix j ℂ (p (ω x))) (τ.map v) =
          τ.map (matrixAction b (asMatrix j ℂ (p x)) v) := by
      let gconj := Specs.ExceptionalLieAutomorphismTransport.realConjugation G
      have ha' : Specs.ExceptionalLieAutomorphismTransport.ActsOnComplexPoints G a
          (fun y => ω (gconj y)) := ha
      have h := adjoint_intertwines_algebraic q (jQ ≫ jU) l s b hAdj a _ ha'
        (gconj x) (σL.map v)
      have hi : gconj (gconj x) = x := realConjugation_involutive G x
      rw [hi, ← hD v, hσAdj x v, ← hD] at h
      exact h
    apply Units.ext
    change (asMatrix j ℂ (p (ω x))).val = κ (asMatrix j ℂ (p x)).val
    apply E.injective
    rw [hκ]
    apply LinearMap.ext
    intro v
    rw [conjugationEnd_apply]
    change Matrix.toLinAlgEquiv B (asMatrix j ℂ (p (ω x))).val v =
      τ'.map (Matrix.toLinAlgEquiv B (asMatrix j ℂ (p x)).val (τ'.map v))
    rw [toLinAlgEquiv_val, toLinAlgEquiv_val]
    have h := hh (τ'.map v)
    change matrixAction B (asMatrix j ℂ (p (ω x))) (τ'.map (τ'.map v)) = _ at h
    rw [τ'.involutive] at h
    exact h

/-- The complex point centralizer of the specified compact torus is abelian
once its compact centralizer has toral identity component. -/
theorem complexCentralizer_isAbelian (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G) (htype : HasExceptionalType G)
    (ω : MulAut (PointsIn i ℂ)) (hω : Continuous ω)
    (a : Aut (complexGroup G))
    (ha : ActsOnComplexPoints (i := i) a (fun x => ω (realConjugation G i x)))
    (hd : HasCompactDifferential a)
    (S T : Subgroup (PointsIn i ℂ)) (hS : IsCompactTorus S) (hSω : S ≤ fixedSubgroup ω)
    (hT : IsCompactTorus T)
    (hTC : (T : Set (PointsIn i ℂ)) =
      identityComponent (fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _))) :
    ∀ x y : Subgroup.centralizer (S : Set (PointsIn i ℂ)), Commute x.val y.val := by
  obtain ⟨t, ht, hC⟩ := exists_torsion_with_same_centralizer i S hS
  have hAlcove := ExceptionalCompactInner.exceptionalAlcove
  letI : PathConnectedSpace (Subgroup.centralizer (S : Set (PointsIn i ℂ))) :=
    hC ▸ torsionCentralizer_pathConnected
      ⟨hAlcove.1, hAlcove.2.1, hAlcove.2.2.1⟩ G i hG hsc htype t.val ht
  letI : IsTopologicalGroup (PointsIn i ℂ) :=
    (asMatrix_isClosedEmbedding i ℂ).isEmbedding.isTopologicalGroup (asMatrix i ℂ)
  obtain ⟨Q, j, p, κ, hp, hsurj, hκ, hanti, hcompat⟩ :=
    compactAction_on_covered_matrices G i hG ω a ha hd
  exact centralizer_commute_of_covered_compact_component p hp hsurj (asMatrix j ℂ)
    (asMatrix_isClosedEmbedding j ℂ) (complexTangent_of_real_matrixRange j) ω hω κ hκ hanti hcompat
    S T hSω hT hTC

end AdjointMatrixAction


section TorusActions

open Arithmetic.AdelicGroups (PointsIn)
open Specs.Pinning (SplitBorelPair)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints fixedSubgroup)
open private eq_of_complexPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open LinearAlgebraicGroups.EquivariantUnipotentSeries (split_torus_smooth_connected)

private def pointMapToReal {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    {Q : GroupScheme ℂ} (f : Q ⟶ complexGroup G) :
    GroupPoints Q complexTest →* PointsIn i ℂ :=
  (baseChangePointGroupEquiv ℂ G.val complexTest).toMonoidHom.comp
    (((groupPointsFunctor ℂ).map f).app complexTest).hom

private theorem pointMapToReal_apply {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    {Q : GroupScheme ℂ} (f : Q ⟶ complexGroup G) (z : GroupPoints Q complexTest) :
    pointMapToReal i f z = baseChangePoint ℝ ℂ G.val.X complexTest (z ≫ f.hom.hom) := rfl

private theorem pointMapToReal_injective {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    {Q : GroupScheme ℂ} (f : Q ⟶ complexGroup G) [Mono f.hom.hom] :
    Function.Injective (pointMapToReal i f) := by
  intro x y h
  apply (cancel_mono f.hom.hom).mp
  exact (baseChangePointGroupEquiv ℂ G.val complexTest).injective h

private theorem reduced_of_smooth_group (H : AffineAlgebraicGroup ℂ)
    (hsm : Smooth H.val.X.hom) : IsReduced H.val.X.left := by
  letI := hsm
  letI : GeometricallyReduced H.val.X.hom := ((affineGroupSmoothnessCriteria ℂ H).1).mp hsm
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.val.X.hom

private theorem algebraic_point_action_involutive {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G)
    (θ : MulAut (PointsIn i ℂ)) (hθ : Function.Involutive θ)
    (hsm : Smooth (complexGroup G).X.hom) (a : Aut (complexGroup G))
    (ha : ActsOnComplexPoints (i := i) a θ) :
    a.asIso.hom ≫ a.asIso.hom = 𝟙 _ := by
  let H := baseChangedAlgebraicGroup ℂ G
  letI : IsReduced (complexGroup G).X.left := reduced_of_smooth_group H hsm
  letI : IsAffine (complexGroup G).X.left := H.property.1
  letI : LocallyOfFiniteType (complexGroup G).X.hom := H.property.2.1
  let e := baseChangePointGroupEquiv ℂ G.val complexTest
  apply Grp.hom_ext
  apply eq_of_complexPoints
  intro z
  apply e.injective
  change e (z ≫ a.asIso.hom.hom.hom ≫ a.asIso.hom.hom.hom) = e (z ≫ 𝟙 _)
  have hact (x : GroupPoints (complexGroup G) complexTest) :
      θ (e x) = e (x ≫ a.asIso.hom.hom.hom) := ha x
  calc
    e (z ≫ a.asIso.hom.hom.hom ≫ a.asIso.hom.hom.hom) =
        e ((z ≫ a.asIso.hom.hom.hom) ≫ a.asIso.hom.hom.hom) :=
      congrArg e (Category.assoc z _ _).symm
    _ = θ (e (z ≫ a.asIso.hom.hom.hom)) := (hact _).symm
    _ = θ (θ (e z)) := congrArg θ (hact z).symm
    _ = e (z ≫ 𝟙 _) := by rw [hθ, Category.comp_id]

set_option maxHeartbeats 1200000 in
private theorem stable_chamber_of_point_centralizer (G : AffineAlgebraicGroup ℝ)
    (i : MatrixRealization G) (θ : MulAut (PointsIn i ℂ))
    (hθ : Function.Involutive θ)
    (a : Aut (complexGroup G)) (ha : ActsOnComplexPoints (i := i) a θ)
    (S : Subgroup (PointsIn i ℂ)) (hS : IsCompactTorus S) (hSθ : S ≤ fixedSubgroup θ)
    (P : SplitBorelPair ℂ) (hP : P.G = baseChangedAlgebraicGroup ℂ G)
    (hC : (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) =
      Set.range (onPoints (i := i) hP P.T.inclusion))
    (hroots : ∀ α : ↥(absoluteRoots P.T), ∃ t : GroupPoints P.T.group complexTest,
      onPoints (i := i) hP P.T.inclusion t ∈ S ∧ characterValue α.val complexTest t ≠ 1) :
    ∃ (B : ClosedSubgroup P.G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf P.T B),
      StableChamber (P := { P with B := B, borel := hB, containsTorus := hTB }) (i := i) hP θ := by
  let e : P.G.val ≅ complexGroup G := eqToIso (congrArg Subtype.val hP)
  let aP := e ≪≫ a.asIso ≪≫ e.symm
  have hreductive : IsReductive (baseChangedAlgebraicGroup ℂ G) := hP ▸ P.reductive
  have hasq := algebraic_point_action_involutive i θ hθ hreductive.1 a ha
  have haPsq : aP.hom ≫ aP.hom = 𝟙 _ := by
    simp only [aP, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      reassoc_of% hasq, Iso.hom_inv_id]
  have hae : aP.hom ≫ e.hom = e.hom ≫ a.asIso.hom := by
    simp [aP]
  let j := pointMapToReal i (P.T.inclusion ≫ e.hom)
  have hCj : (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) =
      Set.range j := by
    exact hC
  letI := inclusion_mono P.T
  letI : Mono ((P.T.inclusion ≫ e.hom).hom.hom) :=
    show Mono ((Grp.forget (SchemeOver ℂ)).map (P.T.inclusion ≫ e.hom)) from
      Functor.map_mono (Grp.forget (SchemeOver ℂ)) _
  have hj := pointMapToReal_injective i (P.T.inclusion ≫ e.hom)
  have hθact (x : GroupPoints P.G.val complexTest) :
      θ (pointMapToReal i e.hom x) =
        pointMapToReal i e.hom (x ≫ aP.hom.hom.hom) := by
    rw [pointMapToReal_apply, pointMapToReal_apply, ha]
    have h := congrArg (fun f : P.G.val ⟶ complexGroup G => f.hom.hom) hae
    apply congrArg (baseChangePoint ℝ ℂ G.val.X complexTest)
    change (x ≫ e.hom.hom.hom) ≫ a.asIso.hom.hom.hom =
      (x ≫ aP.hom.hom.hom) ≫ e.hom.hom.hom
    simp only [Category.assoc]
    exact congrArg (fun f => (show Points P.G.val.X complexTest from x) ≫ f) h.symm
  have hCm (x : PointsIn i ℂ) (hx : x ∈ Subgroup.centralizer (S : Set _)) :
      θ x ∈ Subgroup.centralizer (S : Set _) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have h := ((show Commute s x from Subgroup.mem_centralizer_iff.mp hx s hs).map
      θ.toMonoidHom).eq
    rwa [show θ.toMonoidHom s = s from hSθ hs] at h
  let R := closedSubgroupAlgebraicGroup (G := P.G) P.T
  letI : LocallyOfFiniteType P.T.group.X.hom := R.property.2.1
  letI : IsReduced P.T.group.X.left :=
    reduced_of_smooth_group R (split_torus_smooth_connected R P.split).1
  obtain ⟨b, hb, hbsq⟩ := restrict_involutive_group_iso P.T aP haPsq (by
    intro x
    have hx : j x ∈ (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) := by
      rw [hCj]
      exact Set.mem_range_self x
    have hy := hCm _ hx
    have hy' : θ (j x) ∈ Set.range j := hCj ▸ hy
    obtain ⟨y, hy⟩ := hy'
    refine ⟨y, ?_⟩
    have he : j y = pointMapToReal i e.hom ((x ≫ P.T.inclusion.hom.hom) ≫ aP.hom.hom.hom) := by
      exact hy.trans (hθact (x ≫ P.T.inclusion.hom.hom))
    have hE : Function.Injective (pointMapToReal i e.hom) :=
      pointMapToReal_injective i e.hom
    exact hE he)
  have hj_apply (t : GroupPoints P.T.group complexTest) :
      j t = pointMapToReal i e.hom (t ≫ P.T.inclusion.hom.hom) :=
    congrArg (baseChangePoint ℝ ℂ G.val.X complexTest) (Category.assoc
      (show Points P.T.group.X complexTest from t) P.T.inclusion.hom.hom e.hom.hom.hom).symm
  have hfix (t : GroupPoints P.T.group complexTest) (ht : j t ∈ S) :
      t ≫ b.hom.hom.hom = t := by
    apply hj
    have h := congrArg (fun f : P.T.group ⟶ P.G.val => f.hom.hom) hb
    calc
      j (t ≫ b.hom.hom.hom) = pointMapToReal i e.hom ((t ≫ P.T.inclusion.hom.hom) ≫
          aP.hom.hom.hom) := by
        rw [hj_apply]
        apply congrArg (pointMapToReal i e.hom)
        rw [Category.assoc (show Points P.T.group.X complexTest from t),
          Category.assoc (show Points P.T.group.X complexTest from t)]
        exact congrArg (fun f => (show Points P.T.group.X complexTest from t) ≫ f) h.symm
      _ = θ (j t) := (hθact (t ≫ P.T.inclusion.hom.hom)).symm.trans
        (congrArg θ (hj_apply t).symm)
      _ = j t := hSθ ht
  have hrange : (S : Set _) ⊆ Set.range j := by
    intro x hx
    rw [← hCj]
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact (compactTorus_commute S hS ⟨y, hy⟩ ⟨x, hx⟩).eq
  obtain ⟨c, hc, hreg⟩ := fixedRegularCocharacter P.G P.T P.split b hbsq S hS j hj hrange hfix hroots
  obtain ⟨B, d, hdB, hTB, hsign, hd⟩ :=
    stableBorelOfFixedCocharacter P.G P.reductive P.T P.split P.maximal aP b hb c hc hreg
  refine ⟨B, hdB, hTB, a, Aut.of b, Aut.of d, c, ha, ?_, ?_, hc, hreg, hsign⟩
  · change P.T.inclusion ≫ e.hom ≫ a.asIso.hom = b.hom ≫ P.T.inclusion ≫ e.hom
    rw [← hae, ← Category.assoc P.T.inclusion, hb, Category.assoc]
  · change B.inclusion ≫ e.hom ≫ a.asIso.hom = d.hom ≫ B.inclusion ≫ e.hom
    rw [← hae, ← Category.assoc B.inclusion, hd, Category.assoc]

end TorusActions


section ConjugatedCocharacters

open CategoryTheory.Limits Opposite
open Arithmetic.AdelicGroups (PointsIn)
open Specs.IntegralModels (MatrixRealization)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints fixedSubgroup realConjugation)
open Specs.ExceptionalLieAutomorphismTransport (coefficientConjugation)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open CocharacterDynamics (unitPoint cocharacterPoint mapPoints_unitPoint)
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private conjugateTestPoint conjugateTestPoint_left coefficientSchemeMap_involutive
  realConjugation_involutive from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private fieldAutomorphismSpec twist twistGroupBaseChangeIso twistBaseChangeIso scalarSchemeMap
  scalarSchemeMap_fst scalarSchemeMap_snd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

private def conjugateUnit (z : ℂˣ) : ℂˣ :=
  Units.map Complex.conjAe.toRingHom.toMonoidHom z

private theorem conjugateUnit_involutive (z : ℂˣ) : conjugateUnit (conjugateUnit z) = z :=
  Units.ext (star_star _)

private theorem scalar_conjugated_cocharacter {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) (c : Cocharacter (complexGroup G)) :
    ∃ c' : Cocharacter (complexGroup G), ∀ z : ℂˣ,
      pointMapToReal i c' (unitPoint complexTest z) =
        realConjugation G i (pointMapToReal i c (unitPoint complexTest (conjugateUnit z))) := by
  let M := specGroup (groupAlgebra ℝ IntegerCharacters)
  let F := groupBaseChange ℝ ℂ
  let s := Complex.conjAe
  obtain ⟨e, he⟩ := gm_baseChange ℝ ℂ
  let d : F.obj M ⟶ complexGroup G := e.inv ≫ c
  let bM := (twistGroupBaseChangeIso s).app M
  let bG := (twistGroupBaseChangeIso s).app G.val
  let d' := bM.inv ≫ ((twist s).mapGrp.map d) ≫ bG.hom
  let c' := e.hom ≫ d'
  refine ⟨c', fun z => ?_⟩
  let u (w : ℂˣ) : GroupPoints (F.obj M) complexTest :=
    unitPoint complexTest w ≫ e.hom.hom.hom
  let a := coefficientConjugation
  let j := (fieldAutomorphismSpec s).hom
  let SM := scalarSchemeMap s M.X
  let SG := scalarSchemeMap s G.val.X
  have hj : j ≫ j = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom Complex.conjAe.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Complex.conjAe.toRingHom) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
    congr 2
    ext x
    exact star_star x
  have hunit :
      j ≫ (u (conjugateUnit z)).left ≫ SM = (u z).left := by
    apply pullback.hom_ext
    · have hu (w : ℂˣ) : (u w).left ≫ pullback.fst M.X.hom (fieldSpecMap ℝ ℂ) =
          (unitPoint (CommAlgCat.of ℝ ℂ) w).left :=
        congrArg Over.Hom.left (he complexTest w)
      simp only [Category.assoc, SM, scalarSchemeMap_fst, hu]
      have h := congrArg Over.Hom.left
        (mapPoints_unitPoint a (conjugateUnit z))
      change j ≫ (unitPoint (CommAlgCat.of ℝ ℂ) (conjugateUnit z)).left =
        (unitPoint (CommAlgCat.of ℝ ℂ) (conjugateUnit (conjugateUnit z))).left at h
      simpa only [conjugateUnit_involutive] using h
    · have hu (w : ℂˣ) : (u w).left ≫ pullback.snd M.X.hom (fieldSpecMap ℝ ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
        have h := Over.w (u w)
        change (u w).left ≫ pullback.snd M.X.hom (fieldSpecMap ℝ ℂ) =
          Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) at h
        simpa only [show algebraMap ℂ ℂ = RingHom.id ℂ from rfl, CommRingCat.ofHom_id,
          Spec.map_id] using h
      have hSM := scalarSchemeMap_snd s M.X
      change SM ≫ pullback.snd M.X.hom (fieldSpecMap ℝ ℂ) =
        pullback.snd M.X.hom (fieldSpecMap ℝ ℂ) ≫ j at hSM
      simp only [Category.assoc, hSM, reassoc_of% hu, hu]
      exact (congrArg (j ≫ ·) (Category.id_comp j)).trans hj
  have hd : d'.hom.hom.left ≫ SG = SM ≫ d.hom.hom.left := by
    let eM := (twistBaseChangeIso s).app M.X
    let eG := (twistBaseChangeIso s).app G.val.X
    let Y := (baseChange ℝ ℂ).obj G.val.X
    let Y₀ := (baseChange ℝ ℂ).obj M.X
    let p := pullback.fst Y.hom j
    let p₀ := pullback.fst Y₀.hom j
    have hp : ((twist s).map d.hom.hom).left ≫ p = p₀ ≫ d.hom.hom.left :=
      pullback.lift_fst _ _ _
    let U := Over.forget (Spec (CommRingCat.of ℂ))
    have hi : eG.hom.left ≫ eG.inv.left = 𝟙 _ := (U.mapIso eG).hom_inv_id
    change (eM.inv.left ≫ ((twist s).map d.hom.hom).left ≫ eG.hom.left) ≫
        (eG.inv.left ≫ p) = (eM.inv.left ≫ p₀) ≫ d.hom.hom.left
    simp only [Category.assoc, reassoc_of% hi, hp]
  have hd' : d.hom.hom.left ≫ SG = SM ≫ d'.hom.hom.left := by
    have hM : SM ≫ SM = 𝟙 _ := coefficientSchemeMap_involutive M.X
    have hG : SG ≫ SG = 𝟙 _ := coefficientSchemeMap_involutive G.val.X
    calc
      d.hom.hom.left ≫ SG = SM ≫ ((SM ≫ d.hom.hom.left) ≫ SG) := by
        rw [← Category.assoc SM (SM ≫ d.hom.hom.left), ← Category.assoc SM SM,
          hM, Category.id_comp]
      _ = SM ≫ d'.hom.hom.left := by
        rw [← hd, Category.assoc d'.hom.hom.left, hG]
        exact congrArg (SM ≫ ·) (Category.comp_id d'.hom.hom.left)
  let x : GroupPoints (complexGroup G) complexTest := u (conjugateUnit z) ≫ d.hom.hom
  have hx : (conjugateTestPoint G complexTest a x).left = (u z ≫ d'.hom.hom).left := by
    rw [conjugateTestPoint_left G complexTest a (fun _ => rfl)]
    change j ≫ ((u (conjugateUnit z)).left ≫ d.hom.hom.left) ≫ SG =
      (u z).left ≫ d'.hom.hom.left
    simp only [Category.assoc, hd', reassoc_of% hunit]
  have hu (w : ℂˣ) : u w ≫ d.hom.hom = unitPoint complexTest w ≫ c.hom.hom := by
    change unitPoint complexTest w ≫ e.hom.hom.hom ≫ d.hom.hom = _
    have h : e.hom ≫ d = c := by simp [d]
    exact congrArg (fun f : Cocharacter (complexGroup G) => unitPoint complexTest w ≫ f.hom.hom) h
  have hz : pointMapToReal i c' (unitPoint complexTest z) =
      baseChangePoint ℝ ℂ G.val.X complexTest (u z ≫ d'.hom.hom) := by
    rw [pointMapToReal_apply]
    exact congrArg (baseChangePoint ℝ ℂ G.val.X complexTest) (Category.assoc _ _ _).symm
  rw [hz, ← Over.OverMorphism.ext hx, pointMapToReal_apply, ← hu]
  exact (baseChangePointsEquiv ℂ G.val.X complexTest).apply_symm_apply _

end ConjugatedCocharacters


section CompactInversion

open Filter Opposite
open Arithmetic.AdelicGroups (PointsIn asMatrix)
open Specs.IntegralModels (MatrixRealization)
open Specs.Pinning (SplitBorelPair)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.ExceptionalCompactInner (ActsOnComplexPoints fixedSubgroup realConjugation)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator diagonalGroup)
open CocharacterDynamics (unitPoint cocharacterPoint)
open private unitEquiv unitEquiv_unitPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private cocharacterPoint_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private realConjugation_involutive from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
open private glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private coordinateMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
open private matrixPresentation continuous_glEvaluation asMatrix_isClosedEmbedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

set_option maxHeartbeats 1200000 in
private theorem bounded_character_on_compact_torus_points {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) (P : SplitBorelPair ℂ) (hP : P.G = baseChangedAlgebraicGroup ℂ G)
    (K : Subgroup (PointsIn i ℂ)) [CompactSpace K] (χ : Character P.T.group) :
    ∃ b : ℝ, ∀ t : GroupPoints P.T.group complexTest, onPoints (i := i) hP P.T.inclusion t ∈ K →
      ‖(characterValue χ complexTest t : ℂ)‖ ≤ b := by
  obtain ⟨hG, iC, _, e, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G i
  let J := closedSubgroupAlgebraicGroup (G := P.G) P.T
  let f := P.T.inclusion ≫ eqToHom (congrArg Subtype.val hP)
  let iJ : MatrixRealization J := {
    size := iC.size
    ambient := iC.ambient
    matrix := iC.matrix
    embedding := f ≫ iC.embedding
    closed := by
      letI := P.T.isClosedImmersion
      letI := iC.closed
      haveI : IsIso (eqToHom (congrArg Subtype.val hP) : P.G.val ⟶ complexGroup G).hom.hom.left :=
        (Grp.forget (SchemeOver ℂ) ⋙ Over.forget _).map_isIso _
      change IsClosedImmersion (P.T.inclusion.hom.hom.left ≫
        (eqToHom (congrArg Subtype.val hP) : P.G.val ⟶ complexGroup G).hom.hom.left ≫
        iC.embedding.hom.hom.left)
      infer_instance }
  obtain ⟨D, ⟨j⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr J.property.1
  obtain ⟨a, ha, hmatrix⟩ := matrixPresentation D.unop j iJ
  let w := MonoidAlgebra.single integerGenerator (1 : ℂ)
  let p := (coordinateMap (j.hom ≫ χ.hom.hom)).hom w
  obtain ⟨v, hv⟩ := ha p
  let F := fun x : K => ‖(glEvaluation (asMatrix iC ℂ (e.symm x.val)) v : ℂ)‖
  have hcont : Continuous F := (continuous_glEvaluation v |>.comp
    ((asMatrix_isClosedEmbedding iC ℂ).continuous.comp
      (e.symm.continuous.comp continuous_subtype_val))).norm
  obtain ⟨b, hb⟩ := (isCompact_range hcont).bddAbove
  refine ⟨b, fun t ht => ?_⟩
  let tC := (show PointsIn iC ℂ from t ≫ f.hom.hom)
  have hPoint : e tC = onPoints (i := i) hP P.T.inclusion t :=
    Over.OverMorphism.ext (he tC)
  have hMat : asMatrix iJ ℂ t = asMatrix iC ℂ tC := by
    change asMatrix iJ ℂ (show PointsIn iJ ℂ from t) = _
    simp only [asMatrix, iJ, Functor.map_comp, NatTrans.comp_app]
    rfl
  have hVal : characterValue χ complexTest t = glEvaluation (asMatrix iJ ℂ t) v := by
    rw [hmatrix ℂ t]
    change (coordinateMap (t ≫ χ.hom.hom)).hom w = (coordinateMap (t ≫ j.inv)).hom (a.hom v)
    rw [hv]
    change (coordinateMap (t ≫ χ.hom.hom)).hom w =
      (((coordinateMap (j.hom ≫ χ.hom.hom)) ≫ (coordinateMap (t ≫ j.inv))).hom) w
    rw [← coordinateMap_comp, Category.assoc, Iso.inv_hom_id_assoc]
  have hbound := hb ⟨⟨onPoints hP P.T.inclusion t, ht⟩, rfl⟩
  change ‖(glEvaluation (asMatrix iC ℂ (e.symm (onPoints hP P.T.inclusion t))) v : ℂ)‖ ≤ b at hbound
  rw [← hPoint, e.symm_apply_apply, ← hMat, ← hVal] at hbound
  exact hbound

private theorem unitPoint_surjective :
    Function.Surjective (unitPoint complexTest) := fun z =>
  ⟨unitEquiv complexTest z, (unitEquiv complexTest).injective
    (unitEquiv_unitPoint complexTest _)⟩

private theorem cocharacterPoint_product {Q : GroupScheme ℂ} [IsCommMonObj Q.X]
    (c d : Cocharacter Q) (z : ℂˣ) :
    cocharacterPoint (c * d) complexTest z =
      cocharacterPoint c complexTest z * cocharacterPoint d complexTest z :=
  MonObj.comp_mul (unitPoint complexTest z) c.hom.hom d.hom.hom

private theorem cocharacterPoint_inverse {Q : GroupScheme ℂ} [IsCommMonObj Q.X]
    (c : Cocharacter Q) (z : ℂˣ) :
    cocharacterPoint c⁻¹ complexTest z = cocharacterPoint c complexTest z⁻¹ := by
  have hc : cocharacterPoint c⁻¹ complexTest z = (cocharacterPoint c complexTest z)⁻¹ := by
    change unitPoint complexTest z ≫ (c.hom.hom)⁻¹ =
      (unitPoint complexTest z ≫ c.hom.hom)⁻¹
    exact GrpObj.comp_inv _ _
  exact hc.trans (cocharacterPoint_inv c complexTest z).symm

private theorem bounded_positive_cocharacter_trivial {Q : GroupScheme ℂ}
    [IsCommMonObj Q.X]
    (p : Additive (Character Q) →ₗ[ℤ] Additive (Cocharacter Q) →ₗ[ℤ] ℤ)
    [p.IsPerfPair]
    (hp : ∀ χ c, p (Additive.ofMul χ) (Additive.ofMul c) = pairing Q χ c)
    (c : Cocharacter Q)
    (hb : ∀ χ : Character Q, ∃ B : ℝ, ∀ (r : ℝ) (hr : 0 < r),
      ‖(characterValue χ complexTest (cocharacterPoint c complexTest
        (Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne'))) : ℂ)‖ ≤ B) :
    c = 1 := by
  suffices h : p.flip (Additive.ofMul c) = 0 by
    exact congrArg Additive.toMul (p.flip.toPerfPair.injective
      (h.trans p.flip.toPerfPair.map_zero.symm))
  apply LinearMap.ext
  intro x
  let χ := x.toMul
  let n := pairing Q χ c
  change p x (Additive.ofMul c) = 0
  rw [← show Additive.ofMul χ = x from rfl, hp]
  change n = 0
  obtain ⟨B, hB⟩ := hb χ
  have hbound (r : ℝ) (hr : 0 < r) : r ^ n ≤ B := by
    have h := hB r hr
    rw [(RootData.CharacterPairing.characterPairingComposition Q χ c).2] at h
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.ofReal_zpow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos hr _)] using h
  by_contra hn
  have hpw : ∀ m : ℕ, (2 : ℝ) ^ m ≤ B := by
    intro m
    have hb2 : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    by_cases hpos : 0 < n
    · have hn1 : 1 ≤ n := by omega
      calc
        (2 : ℝ) ^ m ≤ ((2 : ℝ) ^ m) ^ n := by
          have h := zpow_right_mono₀ hb2 hn1
          simpa only [zpow_one] using h
        _ ≤ B := hbound _ (by positivity)
    · have hn1 : 1 ≤ -n := by omega
      calc
        (2 : ℝ) ^ m ≤ ((2 : ℝ) ^ m) ^ (-n) := by
          have h := zpow_right_mono₀ hb2 hn1
          simpa only [zpow_one] using h
        _ = (((2 : ℝ) ^ m)⁻¹) ^ n := by rw [inv_zpow, zpow_neg]
        _ ≤ B := hbound _ (by positivity)
  have hlarge : ∀ᶠ m : ℕ in atTop, B < (2 : ℝ) ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)) (eventually_gt_atTop B)
  obtain ⟨m, hm⟩ := hlarge.exists
  exact (not_lt_of_ge (hpw m)) hm

set_option maxHeartbeats 1200000 in
private theorem conjugate_inversion_on_torus (G : AffineAlgebraicGroup ℝ)
    (i : MatrixRealization G) (ω : MulAut (PointsIn i ℂ)) (hω : Function.Involutive ω)
    (a : Aut (complexGroup G))
    (ha : ActsOnComplexPoints (i := i) a (fun x => ω (realConjugation G i x)))
    [CompactSpace (fixedSubgroup ω)]
    (S : Subgroup (PointsIn i ℂ)) (hSω : S ≤ fixedSubgroup ω)
    (P : SplitBorelPair ℂ) (hP : P.G = baseChangedAlgebraicGroup ℂ G)
    (hC : (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) =
      Set.range (onPoints (i := i) hP P.T.inclusion))
    (c : Cocharacter P.T.group) (z : ℂˣ) :
    ω (onPoints (i := i) hP P.T.inclusion (cocharacterPoint c complexTest z)) =
      onPoints (i := i) hP P.T.inclusion (cocharacterPoint c complexTest (conjugateInverse z)) := by
  let f := P.T.inclusion ≫ eqToHom (congrArg Subtype.val hP)
  let j := pointMapToReal i f
  have hCj : (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) =
      Set.range j := by
    exact hC
  have hCm (x : PointsIn i ℂ) (hx : x ∈ Subgroup.centralizer (S : Set _)) :
      ω x ∈ Subgroup.centralizer (S : Set _) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have h := ((show Commute s x from Subgroup.mem_centralizer_iff.mp hx s hs).map
      ω.toMonoidHom).eq
    rwa [show ω.toMonoidHom s = s from hSω hs] at h
  obtain ⟨d, hd⟩ := scalar_conjugated_cocharacter i (c ≫ f)
  let g := d ≫ a.asIso.hom
  have hg (w : ℂˣ) :
      pointMapToReal i g (unitPoint complexTest w) =
        ω (j (cocharacterPoint c complexTest (conjugateUnit w))) := by
    have h := ha (unitPoint complexTest w ≫ d.hom.hom)
    change ω (realConjugation G i (pointMapToReal i d (unitPoint complexTest w))) =
      pointMapToReal i g (unitPoint complexTest w) at h
    rw [hd] at h
    have hd' := realConjugation_involutive G
      (pointMapToReal i (c ≫ f) (unitPoint complexTest (conjugateUnit w)))
    change realConjugation G i (realConjugation G i
      (pointMapToReal i (c ≫ f) (unitPoint complexTest (conjugateUnit w)))) = _ at hd'
    rw [hd'] at h
    exact h.symm.trans (congrArg ω (congrArg (baseChangePoint ℝ ℂ G.val.X complexTest)
      (Category.assoc (unitPoint complexTest (conjugateUnit w)) c.hom.hom f.hom.hom).symm))
  let F : ClosedSubgroup (complexGroup G) := ⟨P.T.group, f, by
    letI := P.T.isClosedImmersion
    haveI : IsIso (eqToHom (congrArg Subtype.val hP) : P.G.val ⟶ complexGroup G).hom.hom.left :=
      (Grp.forget (SchemeOver ℂ) ⋙ Over.forget _).map_isIso _
    change IsClosedImmersion (P.T.inclusion.hom.hom.left ≫
      (eqToHom (congrArg Subtype.val hP) : P.G.val ⟶ complexGroup G).hom.hom.left)
    infer_instance⟩
  let M := diagonalGroup ℂ IntegerCharacters
  let dℤ : Multiplicative ℤ ≃* IntegerCharacters := MulEquiv.ulift.symm
  let l := (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ ℤ).trans
    (MonoidAlgebra.domCongr ℂ ℂ dℤ)
  letI : IsDomain (MonoidAlgebra ℂ IntegerCharacters) :=
    MulEquiv.isDomain (AddMonoidAlgebra ℂ ℤ) l.symm.toRingEquiv.toMulEquiv
  letI : IsReduced M.val.X.left := inferInstanceAs
    (IsReduced (Spec (CommRingCat.of (MonoidAlgebra ℂ IntegerCharacters))))
  letI : LocallyOfFiniteType M.val.X.hom := M.property.2.1
  obtain ⟨c₀, hc'⟩ := factor_group_of_complexPoints (A := M.val) F g (by
    intro x
    obtain ⟨w, rfl⟩ := unitPoint_surjective x
    have hm : j (cocharacterPoint c complexTest (conjugateUnit w)) ∈
        (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) := by
      rw [hCj]
      exact Set.mem_range_self _
    have hr := hCm _ hm
    have hr' : ω (j (cocharacterPoint c complexTest (conjugateUnit w))) ∈ Set.range j := hCj ▸ hr
    obtain ⟨v, hv⟩ := hr'
    refine ⟨v, (baseChangePointGroupEquiv ℂ G.val complexTest).injective ?_⟩
    exact hv.trans (hg w).symm)
  let c' : Cocharacter P.T.group := c₀
  have hcact (w : ℂˣ) : j (cocharacterPoint c' complexTest w) =
      ω (j (cocharacterPoint c complexTest (conjugateUnit w))) := by
    have h := congrArg (fun f' : M.val ⟶ complexGroup G =>
      pointMapToReal i f' (unitPoint complexTest w)) hc'
    have he : j (cocharacterPoint c' complexTest w) =
        pointMapToReal i (c' ≫ f) (unitPoint complexTest w) :=
      congrArg (baseChangePoint ℝ ℂ G.val.X complexTest)
        (Category.assoc (unitPoint complexTest w) c'.hom.hom f.hom.hom)
    exact he.trans (h.trans (hg w))
  obtain ⟨hcomm, _, _, _, _, p, hp, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing P.T.group P.split
  letI := hcomm
  letI := hp
  have hprod : c * c' = 1 := by
    apply bounded_positive_cocharacter_trivial p hpair
    intro χ
    obtain ⟨B, hB⟩ := bounded_character_on_compact_torus_points i P hP (fixedSubgroup ω) χ
    refine ⟨B, fun r hr => hB _ ?_⟩
    let w := Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
    have hw : conjugateUnit w = w := Units.ext (Complex.conj_ofReal r)
    have comm : Commute (cocharacterPoint c complexTest w) (cocharacterPoint c' complexTest w) := by
      change Commute (show Points P.T.group.X complexTest from cocharacterPoint c complexTest w)
        (show Points P.T.group.X complexTest from cocharacterPoint c' complexTest w)
      exact mul_comm _ _
    have heval := hcact w
    rw [hw] at heval
    have heval' := (congrArg ω heval).trans (hω (j (cocharacterPoint c complexTest w)))
    change ω (j (cocharacterPoint (c * c') complexTest w)) =
      j (cocharacterPoint (c * c') complexTest w)
    simp only [cocharacterPoint_product, map_mul]
    exact (congrArg₂ (· * ·) heval.symm heval').trans (comm.map j).eq.symm
  have hcc : c' = c⁻¹ := eq_inv_of_mul_eq_one_right hprod
  change ω (j (cocharacterPoint c complexTest z)) =
    j (cocharacterPoint c complexTest (conjugateInverse z))
  have hz := (hcact (conjugateUnit z)).symm
  rw [conjugateUnit_involutive, hcc, cocharacterPoint_inverse] at hz
  simpa only [conjugateInverse, conjugateUnit, map_inv] using hz

end CompactInversion


section CompactTorusPoints

open Filter Opposite
open Arithmetic.AdelicGroups (PointsIn asMatrix)
open Specs.IntegralModels (MatrixRealization)
open Specs.Pinning (SplitBorelPair)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.ExceptionalCompactInner (fixedSubgroup)
open Specs.DiagonalizableGroups (IntegerCharacters)
open CocharacterDynamics (unitPoint unitCoordinates cocharacterPoint)
open private continuous_of_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
open private coordinateMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private coordinateMap_of_map asMatrix_isClosedEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private splitTorus_points_ext from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates
open private characterUnit_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private theorem continuous_cocharacter_on_actual_points {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) (c : Cocharacter (complexGroup G)) :
    Continuous (fun z : ℂˣ => pointMapToReal i c (unitPoint complexTest z)) := by
  obtain ⟨_, iC, _, e, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G i
  let B := CommAlgCat.of ℂ (MonoidAlgebra ℂ IntegerCharacters)
  have h := continuous_of_coordinates iC B c.hom.hom (unitPoint complexTest) (by
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
  exact (e.continuous.comp h).congr (fun z => Over.OverMorphism.ext (he _))

private theorem circleToUnits_continuous : Continuous Circle.toUnits := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  simp only [← map_inv]
  exact continuous_subtype_val.comp continuous_inv

private theorem conjugateInverse_fixed_iff (z : ℂˣ) :
    conjugateInverse z = z ↔ ‖(z : ℂ)‖ = 1 := by
  rw [conjugateInverse, map_inv, inv_eq_iff_mul_eq_one]
  let w := Units.map Complex.conjAe.toRingHom.toMonoidHom z
  change w * z = 1 ↔ _
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

set_option maxHeartbeats 1200000 in
private theorem connected_compact_part_of_split_torus {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) (ω : MulAut (PointsIn i ℂ))
    (P : SplitBorelPair ℂ) (hP : P.G = baseChangedAlgebraicGroup ℂ G)
    (hω : ∀ (c : Cocharacter P.T.group) (z : ℂˣ),
      ω (onPoints (i := i) hP P.T.inclusion (cocharacterPoint c complexTest z)) =
        onPoints (i := i) hP P.T.inclusion (cocharacterPoint c complexTest (conjugateInverse z))) :
    IsConnected ((fixedSubgroup ω : Set (PointsIn i ℂ)) ∩
      Set.range (onPoints (i := i) hP P.T.inclusion)) := by
  classical
  letI : IsTopologicalGroup (PointsIn i ℂ) :=
    (asMatrix_isClosedEmbedding i ℂ).isEmbedding.isTopologicalGroup (asMatrix i ℂ)
  let f := P.T.inclusion ≫ eqToHom (congrArg Subtype.val hP)
  let j := pointMapToReal i f
  letI := inclusion_mono P.T
  letI : Mono f.hom.hom :=
    show Mono ((Grp.forget (SchemeOver ℂ)).map f) from Functor.map_mono _ _
  have hj := pointMapToReal_injective i f
  obtain ⟨hComm, _, _, hfree, hfinite, p, hp, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing P.T.group P.split
  letI := hComm
  letI := hfree
  letI := hfinite
  letI := hp
  let X := Additive (Cocharacter P.T.group)
  let b₀ := Module.Free.chooseBasis ℤ X
  letI : Finite (Module.Free.ChooseBasisIndex ℤ X) := Module.Finite.finite_basis b₀
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ X) := Fintype.ofFinite _
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let b : Module.Basis (Fin n) ℤ X := b₀.reindex (Fintype.equivFin _)
  let a := b.dualBasis.map p.toPerfPair.symm
  let U (z : Fin n → ℂˣ) : GroupPoints P.T.group complexTest :=
    (List.ofFn (fun l => cocharacterPoint (b l).toMul complexTest (z l))).prod
  have hcoords (z : Fin n → ℂˣ) (l : Fin n) :
      characterUnit (a l).toMul complexTest (U z) = z l := by
    have hab (s t : Fin n) :
        pairing P.T.group (a s).toMul (b t).toMul = (Pi.single s 1 : Fin n → ℤ) t := by
      rw [← hpair]
      change p.toPerfPair (p.toPerfPair.symm (b.dualBasis s)) (b t) = _
      rw [LinearEquiv.apply_symm_apply]
      rw [Module.Basis.dualBasis_apply, Module.Basis.repr_self]
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    change characterUnitOnPoints (a l).toMul complexTest (U z) = z l
    simp only [U, map_list_prod, List.map_ofFn, List.prod_ofFn]
    rw [Finset.prod_eq_single l]
    · change characterUnit (a l).toMul complexTest
        (cocharacterPoint (b l).toMul complexTest (z l)) = z l
      rw [characterUnit_cocharacter, hab, Pi.single_eq_same, zpow_one]
    · intro t _ h
      change characterUnit (a l).toMul complexTest
        (cocharacterPoint (b t).toMul complexTest (z t)) = 1
      rw [characterUnit_cocharacter, hab, Pi.single_eq_of_ne h, zpow_zero]
    · simp
  have hsur : Function.Surjective U := by
    intro t
    let z (l : Fin n) := characterUnit (a l).toMul complexTest t
    refine ⟨z, splitTorus_points_ext P.split complexTest _ _ ?_⟩
    let F (q : GroupPoints P.T.group complexTest) :=
      (characterEvaluation complexTest q).toAdditive.toIntLinearMap
    have heq : F (U z) = F t := a.ext fun l => hcoords z l
    intro χ
    exact congrArg Additive.toMul (LinearMap.congr_fun heq (Additive.ofMul χ))
  have hinj : Function.Injective U := by
    intro z v h
    funext l
    rw [← hcoords z l, h, hcoords]
  have hact (z : Fin n → ℂˣ) : ω (j (U z)) = j (U (conjugateInverse ∘ z)) := by
    have h (l : Fin n) := hω (b l).toMul (z l)
    have h' (l : Fin n) : ω (j (cocharacterPoint (b l).toMul complexTest (z l))) =
        j (cocharacterPoint (b l).toMul complexTest (conjugateInverse (z l))) := h l
    simp only [U, map_list_prod, List.map_ofFn]
    apply congrArg (fun v : Fin n → PointsIn i ℂ => (List.ofFn v).prod)
    exact funext h'
  let φ (s : Fin n → Circle) := j (U (fun l => Circle.toUnits (s l)))
  have hφ : Continuous φ := by
    let F (l : Fin n) (s : Fin n → Circle) :=
      j (cocharacterPoint (b l).toMul complexTest (Circle.toUnits (s l)))
    have hF (l : Fin n) : Continuous (F l) := by
      have he : Continuous (fun s : Fin n → Circle => s l) := continuous_apply l
      have h := (continuous_cocharacter_on_actual_points i ((b l).toMul ≫ f)).comp
        (circleToUnits_continuous.comp he)
      apply h.congr
      intro s
      exact congrArg (baseChangePoint ℝ ℂ G.val.X complexTest)
        (Category.assoc (unitPoint complexTest (Circle.toUnits (s l))) (b l).toMul.hom.hom
          f.hom.hom).symm
    have hList (ls : List (Fin n)) : Continuous (fun s : Fin n → Circle =>
        (ls.map (fun l => F l s)).prod) := by
      induction ls with
      | nil => exact continuous_const
      | cons l ls ih => exact (hF l).mul ih
    unfold φ U
    simp only [map_list_prod, List.map_ofFn]
    change Continuous (fun s : Fin n → Circle => (List.ofFn (fun l => F l s)).prod)
    exact (hList (List.finRange n)).congr fun s =>
      congrArg List.prod (List.ofFn_eq_map (f := fun l => F l s)).symm
  have heq : (fixedSubgroup ω : Set (PointsIn i ℂ)) ∩
      Set.range (onPoints (i := i) hP P.T.inclusion) = Set.range φ := by
    ext x
    constructor
    · rintro ⟨hx, t, rfl⟩
      obtain ⟨z, hz⟩ := hsur t
      change ω (j t) = j t at hx
      have hzfix : conjugateInverse ∘ z = z := by
        apply hinj
        apply hj
        change j (U (conjugateInverse ∘ z)) = j (U z)
        rw [← hact, hz, hx]
      let s (l : Fin n) : Circle := ⟨(z l : ℂ),
        mem_sphere_zero_iff_norm.mpr ((conjugateInverse_fixed_iff _).mp (congr_fun hzfix l))⟩
      have hs : (fun l => Circle.toUnits (s l)) = z := funext fun l => Units.ext rfl
      refine ⟨s, ?_⟩
      change j (U (fun l => Circle.toUnits (s l))) = j t
      rw [hs, hz]
    · rintro ⟨s, rfl⟩
      let z (l : Fin n) := Circle.toUnits (s l)
      have hz : conjugateInverse ∘ z = z := funext fun l =>
        (conjugateInverse_fixed_iff _).mpr (s l).norm_coe
      refine ⟨?_, ⟨U z, rfl⟩⟩
      change ω (j (U z)) = j (U z)
      rw [hact, hz]
  rw [heq]
  exact isConnected_range hφ

end CompactTorusPoints

open Specs.ExceptionalCompactInner (fixedSubgroup HasCompactDifferential HasExceptionalType
  ActsOnComplexPoints realConjugation)
open Specs.Pinning (SplitBorelPair)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Arithmetic.AdelicGroups (PointsIn)

set_option maxHeartbeats 1200000 in
/-- The compact centralizer is the compact part of a split maximal torus on
the actual complexification, with an invariant regular chamber. -/
theorem algebraicBorelPair : Statement := by
  intro G i hG hsc htype ω θ hωcont _ hωAlg hθAlg hω hθ _ hK _ S T hS hTcomp _ hT
  letI := hK
  obtain ⟨a, ha, hdiff⟩ := hωAlg
  obtain ⟨b, hb⟩ := hθAlg
  have hSfix : S ≤ fixedSubgroup ω ⊓ fixedSubgroup θ := by
    intro x hx
    obtain ⟨y, _, hy⟩ := hS.2.1 hx
    exact hy ▸ y.prop
  have hSω : S ≤ fixedSubgroup ω := hSfix.trans inf_le_left
  have hSθ : S ≤ fixedSubgroup θ := hSfix.trans inf_le_right
  have hC := complexCentralizer_isAbelian G i hG hsc htype ω hωcont a ha hdiff
    S T hS.1 hSω hT.1 hTcomp
  obtain ⟨P, hP, hCG, hroots⟩ := algebraicTorusOfAbelianCentralizer G i hG hsc htype S hS.1 hC
  have hInv := conjugate_inversion_on_torus G i ω hω a ha S hSω P hP hCG
  have hConnect := connected_compact_part_of_split_torus i ω P hP hInv
  let J := fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set (PointsIn i ℂ))
  have hJ : (J : Set (PointsIn i ℂ)) = (fixedSubgroup ω : Set (PointsIn i ℂ)) ∩
      Set.range (onPoints (i := i) hP P.T.inclusion) := by
    change (fixedSubgroup ω : Set (PointsIn i ℂ)) ∩
      (Subgroup.centralizer (S : Set (PointsIn i ℂ)) : Set (PointsIn i ℂ)) = _
    rw [hCG]
  letI : ConnectedSpace J := isConnected_iff_connectedSpace.mp (by rw [hJ]; exact hConnect)
  have hTJ : T = J := by
    apply SetLike.coe_injective
    rw [hTcomp]
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.prop
    · intro hx
      exact ⟨⟨x, hx⟩, by simp [PreconnectedSpace.connectedComponent_eq_univ], rfl⟩
  obtain ⟨B, hB, hTB, hStable⟩ :=
    stable_chamber_of_point_centralizer G i θ hθ b hb S hS.1 hSθ P hP hCG hroots
  let Q : SplitBorelPair ℂ := { P with B := B, borel := hB, containsTorus := hTB }
  exact ⟨Q, hP, hTJ, by rw [hTJ]; exact hJ, hroots, hInv, hStable⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterAlgebraicBorelPair
