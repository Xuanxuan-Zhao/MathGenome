import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import LinearAlgebraicGroups.Classification.RankOneRelations
import LinearAlgebraicGroups.Classification.PinnedEquivalence
import LinearAlgebraicGroups.Classification.IntegralRootRelations
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open scoped WithZero TensorProduct

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

set_option linter.style.haveILetI false

open ValuativeRel WithZero
open Specs.ExceptionalMarkedRootDescent

noncomputable section

section PinnedPoints

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : Type u} [CommRing A] [Algebra k A]

private theorem extendPoint_injective :
    Function.Injective (extendPoint (k := k) (K := K) (A := A)) := by
  intro p q hpq
  ext x
  apply (algebraMap k K).injective
  simpa [extendPoint] using congrFun (congrArg DFunLike.coe hpq) (1 ⊗ₜ[k] x)

private theorem extendPoint_range [FiniteDimensional k K] [IsGalois k K]
    (p : (K ⊗[k] A) →ₐ[K] K) :
    p ∈ Set.range (extendPoint (k := k) (K := K) (A := A)) ↔
    ∀ σ x, p ((SemilinearAction.scalarExtension (K := K) A).act σ x) = σ (p x) := by
  constructor
  · rintro ⟨q, rfl⟩ σ x
    refine TensorProduct.inductionOn (motive := fun x ↦
      extendPoint q ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
        σ (extendPoint (K := K) q x)) x ?_ ?_
    · intro a x
      change extendPoint (K := K) q (σ a ⊗ₜ[k] x) =
        σ (extendPoint (K := K) q (a ⊗ₜ[k] x))
      simp only [extendPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply,
        Algebra.ofId_apply, smul_eq_mul, map_mul, AlgEquiv.commutes]
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · intro h
    let f : A →ₐ[k] K := (AlgHom.liftEquiv k K A K).symm p
    let i : k →ₐ[k] K := Algebra.ofId k K
    have hf (x : A) : f x ∈ i.range := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed (f x)).mpr
      intro σ
      have hx := h σ (1 ⊗ₜ[k] x)
      change p (σ 1 ⊗ₜ[k] x) = σ (p (1 ⊗ₜ[k] x)) at hx
      simpa [f] using hx.symm
    let e : k ≃ₐ[k] i.range := AlgEquiv.ofInjective i (algebraMap k K).injective
    let q : A →ₐ[k] k := e.symm.toAlgHom.comp (f.codRestrict i.range hf)
    refine ⟨q, (AlgHom.liftEquiv k K A K).symm.injective ?_⟩
    unfold extendPoint
    rw [Equiv.symm_apply_apply]
    change i.comp q = f
    ext x
    change i (e.symm ⟨f x, hf x⟩) = f x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hf x⟩)

theorem pinnedFixedPoints : PinnedFixedPoints.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d
  let S := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let H := Specs.AdjointCocharacters.coordinateHopf G
  let i : (K ⊗[k] S) ≃ₐ[K] (K ⊗[k] H) :=
    { d.groupIso.hom.hom.toAlgHom with
      invFun := d.groupIso.inv.hom
      left_inv := ConcreteCategory.congr_hom d.groupIso.hom_inv_id
      right_inv := ConcreteCategory.congr_hom d.groupIso.inv_hom_id }
  have hi (p : H →ₐ[k] k) : pinnedPointMap d p = (extendPoint p).comp i.toAlgHom := rfl
  have he (σ : Gal(K/k)) (x : K ⊗[k] S) :
      (SemilinearAction.scalarExtension (K := K) H).act σ (i x) =
        i (pinnedOperator d σ x) := d.twistedAction σ x
  constructor
  · intro p q hpq
    apply extendPoint_injective (K := K)
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun (show (extendPoint p).comp i.toAlgHom =
        (extendPoint q).comp i.toAlgHom from hpq) (i.symm x)
    simpa using h
  · intro p
    constructor
    · rintro ⟨q, rfl⟩ σ x
      rw [hi]
      change extendPoint q (i (pinnedOperator d σ x)) = σ (extendPoint q (i x))
      rw [← he]
      exact (extendPoint_range _).mp ⟨q, rfl⟩ σ (i x)
    · intro hp
      let f : (K ⊗[k] H) →ₐ[K] K := p.comp i.symm.toAlgHom
      have hf (σ : Gal(K/k)) (x : K ⊗[k] H) :
          f ((SemilinearAction.scalarExtension (K := K) H).act σ x) = σ (f x) := by
        obtain ⟨y, rfl⟩ := i.surjective x
        rw [he]
        simpa [f] using hp σ y
      obtain ⟨q, hq⟩ := (extendPoint_range f).mpr hf
      refine ⟨q, ?_⟩
      rw [hi, hq]
      ext x
      simp [f]


section TestAlgebras

variable {R : Type u} [CommRing R] [Algebra k R]

private theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) := by
  let b := Module.Free.chooseBasis k R
  intro x y h
  apply b.repr.injective
  ext j
  apply (algebraMap k K).injective
  have hh := congrArg (fun z => (b.baseChange K).repr z j) h
  simpa [Algebra.smul_def] using hh

private theorem includeRight_range [FiniteDimensional k K] [IsGalois k K]
    (z : K ⊗[k] R) :
    z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).range ↔
      ∀ σ, (SemilinearAction.scalarExtension (K := K) R).act σ z = z := by
  classical
  let i : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  let ρ := SemilinearAction.scalarExtension (k := k) (K := K) R
  constructor
  · rintro ⟨r, rfl⟩ σ
    change σ 1 ⊗ₜ[k] r = 1 ⊗ₜ[k] r
    rw [map_one]
  · intro h
    let b := Module.Free.chooseBasis k R
    let B := b.baseChange K
    have hrepr (σ : Gal(K/k)) (x : K ⊗[k] R) (j : _) :
        B.repr (ρ.act σ x) j = σ (B.repr x j) := by
      refine TensorProduct.inductionOn x ?_ ?_
      · intro a r
        change B.repr (σ a ⊗ₜ[k] r) j = σ (B.repr (a ⊗ₜ[k] r) j)
        simp [B, Algebra.smul_def, AlgEquiv.commutes]
      · intro x y hx hy
        simp only [map_add, Finsupp.add_apply, hx, hy]
    have hj (j : _) : ∃ c : k, algebraMap k K c = B.repr z j := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      rw [← hrepr, h σ]
    let w := ∑ j ∈ (B.repr z).support, (hj j).choose • b j
    refine ⟨w, B.repr.injective ?_⟩
    have hw : i w = ∑ j ∈ (B.repr z).support, (B.repr z j) • B j := by
      change i.toLinearMap w = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [LinearMap.map_smul]
      change (hj j).choose • ((1 : K) ⊗ₜ[k] b j) = _
      rw [← IsScalarTower.algebraMap_smul K ((hj j).choose), (hj j).choose_spec]
      simp [B]
    change B.repr (i w) = B.repr z
    rw [hw]
    exact congrArg B.repr (B.linearCombination_repr z)

private theorem extendAlgebraPoint_injective :
    Function.Injective (extendAlgebraPoint (k := k) (K := K) (A := A) (R := R)) := by
  intro p q hpq
  apply AlgHom.ext
  intro x
  apply includeRight_injective (k := k) (K := K)
  simpa [extendAlgebraPoint, AlgHom.liftEquiv_tmul] using
    DFunLike.congr_fun hpq (1 ⊗ₜ[k] x)

private theorem extendAlgebraPoint_range [FiniteDimensional k K] [IsGalois k K]
    (p : (K ⊗[k] A) →ₐ[K] (K ⊗[k] R)) :
    p ∈ Set.range (extendAlgebraPoint (k := k) (K := K) (A := A) (R := R)) ↔
      ∀ σ x, p ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (p x) := by
  constructor
  · rintro ⟨q, rfl⟩ σ x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro a x
      change extendAlgebraPoint (K := K) q (σ a ⊗ₜ[k] x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ
          (extendAlgebraPoint (K := K) q (a ⊗ₜ[k] x))
      simp only [extendAlgebraPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply,
        (SemilinearAction.scalarExtension (k := k) (K := K) R).map_smul]
      congr 1
      change (1 : K) ⊗ₜ[k] q x = σ 1 ⊗ₜ[k] q x
      rw [map_one]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  · intro h
    let f : A →ₐ[k] K ⊗[k] R := (AlgHom.liftEquiv k K A (K ⊗[k] R)).symm p
    let i : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
    have hf (x : A) : f x ∈ i.range := by
      apply (includeRight_range _).mpr
      intro σ
      have hx := h σ (1 ⊗ₜ[k] x)
      change p (σ 1 ⊗ₜ[k] x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (p (1 ⊗ₜ[k] x)) at hx
      simpa [f] using hx.symm
    let e : R ≃ₐ[k] i.range := AlgEquiv.ofInjective i includeRight_injective
    let q : A →ₐ[k] R := e.symm.toAlgHom.comp (f.codRestrict i.range hf)
    refine ⟨q, (AlgHom.liftEquiv k K A (K ⊗[k] R)).symm.injective ?_⟩
    unfold extendAlgebraPoint
    rw [Equiv.symm_apply_apply]
    change i.comp q = f
    ext x
    change i (e.symm ⟨f x, hf x⟩) = f x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hf x⟩)

theorem pinnedAlgebraFixedPoints : PinnedAlgebraFixedPoints.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d R _ _
  let S := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let H := Specs.AdjointCocharacters.coordinateHopf G
  let i : (K ⊗[k] S) ≃ₐ[K] (K ⊗[k] H) :=
    { d.groupIso.hom.hom.toAlgHom with
      invFun := d.groupIso.inv.hom
      left_inv := ConcreteCategory.congr_hom d.groupIso.hom_inv_id
      right_inv := ConcreteCategory.congr_hom d.groupIso.inv_hom_id }
  have hi (p : H →ₐ[k] R) :
      pinnedAlgebraPointMap d p = (extendAlgebraPoint p).comp i.toAlgHom := rfl
  have he (σ : Gal(K/k)) (x : K ⊗[k] S) :
      (SemilinearAction.scalarExtension (K := K) H).act σ (i x) =
        i (pinnedOperator d σ x) := d.twistedAction σ x
  constructor
  · intro p q hpq
    apply extendAlgebraPoint_injective (K := K)
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun (show (extendAlgebraPoint p).comp i.toAlgHom =
        (extendAlgebraPoint q).comp i.toAlgHom from hpq) (i.symm x)
    simpa using h
  · intro p
    constructor
    · rintro ⟨q, rfl⟩ σ x
      rw [hi]
      change extendAlgebraPoint q (i (pinnedOperator d σ x)) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (extendAlgebraPoint q (i x))
      rw [← he]
      exact (extendAlgebraPoint_range _).mp ⟨q, rfl⟩ σ (i x)
    · intro hp
      let f : (K ⊗[k] H) →ₐ[K] (K ⊗[k] R) := p.comp i.symm.toAlgHom
      have hf (σ : Gal(K/k)) (x : K ⊗[k] H) :
          f ((SemilinearAction.scalarExtension (K := K) H).act σ x) =
            (SemilinearAction.scalarExtension (K := K) R).act σ (f x) := by
        obtain ⟨y, rfl⟩ := i.surjective x
        rw [he]
        simpa [f] using hp σ y
      obtain ⟨q, hq⟩ := (extendAlgebraPoint_range f).mpr hf
      refine ⟨q, ?_⟩
      rw [hi, hq]
      ext x
      simp [f]

end TestAlgebras

section PointGroups

open Specs.AdjointBorelCohomology (PinnedTwist)

private def extendHopfPoint {H : HopfAlgebraCategory k}
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R]
    [Algebra k S] [Algebra K S] [IsScalarTower k K S] (i : R →ₐ[k] S) :
    HopfPoints H R →* HopfPoints (extendedHopf K H) S :=
  MonoidHom.mk' (fun p ↦ WithConv.toConv (AlgHom.liftEquiv k K H S (i.comp p.ofConv))) (by
    intro p q
    apply WithConv.ofConv_injective
    apply (AlgHom.liftEquiv k K H S).symm.injective
    ext a
    change ((AlgHom.liftEquiv k K H S).symm
      (AlgHom.liftEquiv k K H S (i.comp (p * q).ofConv))) a = _
    rw [Equiv.symm_apply_apply, AlgHom.liftEquiv_symm_apply]
    let p' := WithConv.toConv (AlgHom.liftEquiv k K H S (i.comp p.ofConv))
    let q' := WithConv.toConv (AlgHom.liftEquiv k K H S (i.comp q.ofConv))
    change i ((p * q).ofConv a) = (p' * q').ofConv (1 ⊗ₜ[k] a)
    have hpq := AlgHom.convMul_apply (R := k) (A := R) (C := H) p q a
    change (p * q).ofConv a = _ at hpq
    have hpq' := AlgHom.convMul_apply p' q' (1 ⊗ₜ[k] a)
    change (p' * q').ofConv (1 ⊗ₜ[k] a) = _ at hpq'
    rw [hpq, hpq', TensorProduct.comul_tmul, Bialgebra.comul_one]
    generalize Coalgebra.comul (R := k) a = z
    induction z with
    | tmul x y =>
      simp [p', q', Algebra.TensorProduct.one_def, Algebra.TensorProduct.lift_tmul]
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy])

private def compHopfPoint {J H : HopfAlgebraCategory K}
    {R : Type u} [CommRing R] [Algebra K R] (f : J ⟶ H) :
    HopfPoints H R →* HopfPoints J R :=
  MonoidHom.mk' (fun p ↦ WithConv.toConv (p.ofConv.comp f.hom.toAlgHom)) (by
    intro p q
    exact WithConv.ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib p q f.hom))

theorem pinnedPointGroups : PinnedPointGroups.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d
  let j := (compHopfPoint (R := K) d.groupIso.hom).comp
    (extendHopfPoint (K := K) (H := Specs.AdjointCocharacters.coordinateHopf G) (Algebra.ofId k K))
  have hj (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k) : (j p).ofConv = pinnedPointMap d p.ofConv := rfl
  obtain ⟨hinj, hrange⟩ := pinnedFixedPoints d
  have hij : Function.Injective j := fun _ _ h ↦ WithConv.ofConv_injective
    (hinj (congrArg WithConv.ofConv h))
  let e := MonoidHom.ofInjective hij
  refine ⟨j.range, e, hj, fun p ↦ ?_⟩
  rw [← hrange]
  exact ⟨fun ⟨q, hq⟩ ↦ ⟨q.ofConv, congrArg WithConv.ofConv hq⟩,
    fun ⟨q, hq⟩ ↦ ⟨WithConv.toConv q, WithConv.ofConv_injective hq⟩⟩

theorem pinnedAlgebraPointGroups : PinnedAlgebraPointGroups.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d R _ _
  let j := (compHopfPoint (R := K ⊗[k] R) d.groupIso.hom).comp
    (extendHopfPoint (K := K) (H := Specs.AdjointCocharacters.coordinateHopf G)
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R))
  have hj (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R) :
      (j p).ofConv = pinnedAlgebraPointMap d p.ofConv := rfl
  obtain ⟨hinj, hrange⟩ := pinnedAlgebraFixedPoints d R
  have hij : Function.Injective j := fun _ _ h ↦ WithConv.ofConv_injective
    (hinj (congrArg WithConv.ofConv h))
  let e := MonoidHom.ofInjective hij
  refine ⟨j.range, e, hj, fun p ↦ ?_⟩
  rw [← hrange]
  exact ⟨fun ⟨q, hq⟩ ↦ ⟨q.ofConv, congrArg WithConv.ofConv hq⟩,
    fun ⟨q, hq⟩ ↦ ⟨WithConv.toConv q, WithConv.ofConv_injective hq⟩⟩

end PointGroups

/-- A nonidentity element exhausts the nontrivial part of the quadratic Galois group. -/
private theorem quadraticGalois [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1) :
    (∀ g : Gal(K/k), g = 1 ∨ g = σ) ∧ σ * σ = 1 := by
  have hcard : Nat.card (Gal(K/k)) = 2 := (IsGalois.card_aut_eq_finrank k K).trans hdegree
  have hu := (Nat.card_eq_two_iff' (1 : Gal(K/k))).mp hcard
  have hcases (g : Gal(K/k)) : g = 1 ∨ g = σ := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr (ExistsUnique.unique hu hg hσ)
  refine ⟨hcases, (hcases (σ * σ)).resolve_right (fun hs ↦ hσ ?_)⟩
  apply mul_right_cancel (b := σ)
  simpa only [one_mul] using hs

/-- Fixed coordinates of a singleton and a swapped pair, including units. -/
theorem quadraticParameterDescent : QuadraticParameterDescent.{u} := by
  intro k K _ _ _ _ _ hdegree σ hσ R _ _ i τ
  obtain ⟨hcases, hss⟩ := quadraticGalois hdegree σ hσ
  let ρ := SemilinearAction.scalarExtension (k := k) (K := K) R
  have hfix (x : K ⊗[k] R) : τ x = x ↔ ∀ g, ρ.act g x = x := by
    refine ⟨fun hx g ↦ ?_, fun h ↦ h σ⟩
    rcases hcases g with rfl | rfl
    · exact ρ.one_act x
    · exact hx
  have hfixed (x : K ⊗[k] R) : τ x = x ↔ x ∈ Set.range i :=
    (hfix x).trans (includeRight_range x).symm
  have hinv (x : K ⊗[k] R) : τ (τ x) = x := by
    change ρ.act σ (ρ.act σ x) = x
    rw [← ρ.mul_act, hss, ρ.one_act]
  have hi : Function.Injective i := includeRight_injective
  refine ⟨hi, hfixed, fun x y ↦ ?_, fun t ↦ ?_⟩
  · refine ⟨fun h ↦ (congrArg Prod.snd h).symm, fun h ↦ ?_⟩
    rw [h, hinv]
  · let φ : (K ⊗[k] R) →ₐ[k] (K ⊗[k] R) :=
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)
    have hφ (x : K ⊗[k] R) : φ x = τ x := by
      induction x using TensorProduct.inductionOn with
      | tmul a r => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    constructor
    · intro ht
      have hU : Units.map φ.toMonoidHom t = t := Units.ext ((hφ t).trans ht)
      have hti : τ (↑t⁻¹ : K ⊗[k] R) = (↑t⁻¹ : K ⊗[k] R) := by
        rw [← hφ]
        exact congrArg Units.val (by rw [map_inv, hU] : Units.map φ.toMonoidHom t⁻¹ = t⁻¹)
      obtain ⟨a, ha⟩ := (hfixed t).mp ht
      obtain ⟨b, hb⟩ := (hfixed (↑t⁻¹ : K ⊗[k] R)).mp hti
      let u : Rˣ := ⟨a, b, hi (by simp [ha, hb]), hi (by simp [ha, hb])⟩
      exact ⟨u, Units.ext ha⟩
    · rintro ⟨u, rfl⟩
      exact (hfixed (i u)).mpr ⟨u, rfl⟩

/-- Coefficient conjugation commutes with all maps of test algebras. -/
theorem quadraticParameterNaturality : QuadraticParameterNaturality.{u} := by
  intro k K R S _ _ _ _ _ _ _ σ f x
  induction x using TensorProduct.inductionOn with
  | tmul a r => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pinnedSimpleCoordinates : PinnedSimpleCoordinates.{u} := by
  intro k _ A P f a
  let x := (a.val.val, (P.pin a).val.hom ≫ (P.roots a.val).val.inclusion)
  let y := (Specs.Pinning.transportCharacter f.asIso.hom.torus x.1, x.2 ≫ f.asIso.hom.group.hom)
  have hy : y ∈ Specs.Pinning.pinGraph P := by
    rw [← f.asIso.hom.pin_comm]
    exact ⟨x, ⟨a, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := hy
  have hχ := congrArg Prod.fst hb
  refine ⟨b, ⟨hχ, (congrArg Prod.snd hb).symm⟩, fun c hc ↦ ?_⟩
  exact Subtype.ext (Subtype.ext (hc.1.trans hχ.symm))

end PinnedPoints

section RankOne

open Specs.IntegralRootRelations (upper lower)
open Matrix

private theorem upper_lower_induction {K : Type*} [Field K]
    (P : SpecialLinearGroup (Fin 2) K → Prop)
    (hu : ∀ t, P (upper t)) (hl : ∀ t, P (lower t))
    (hm : ∀ A B, P A → P B → P (A * B)) (A : SpecialLinearGroup (Fin 2) K) :
    P A := by
  apply SL2.transvection_induction P _ hm A
  intro i j hij t
  fin_cases i <;> fin_cases j
  · contradiction
  · convert hu t using 1
    apply Subtype.ext
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [SpecialLinearGroup.transvection_coe, upper, Matrix.single]
  · convert hl t using 1
    apply Subtype.ext
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [SpecialLinearGroup.transvection_coe, lower, Matrix.single]
  · contradiction

private theorem map_upper {K : Type*} [Field K] (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.map σ.toRingHom (upper t) = upper (σ t) := by
  apply Subtype.ext
  change (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).map σ = !![1, σ t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem map_lower {K : Type*} [Field K] (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.map σ.toRingHom (lower t) = lower (σ t) := by
  apply Subtype.ext
  change (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) K).map σ = !![1, 0; σ t, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pairedRankOne : PairedRankOne := by
  intro K G _ _ σ τ hσ hτ a b
  dsimp only
  intro comm hu hl
  let s := SpecialLinearGroup.map (n := Fin 2) σ.toRingHom
  have hcomm (A B : SpecialLinearGroup (Fin 2) K) : Commute (a A) (b B) := by
    have aux (X) (hx : X ∈ Set.range (upper (R := K)) ∪ Set.range (lower (R := K)))
        (Y : SpecialLinearGroup (Fin 2) K) : Commute (a X) (b Y) := by
      induction Y using upper_lower_induction
      case hu => exact comm X hx _ (Or.inl (Set.mem_range_self _))
      case hl => exact comm X hx _ (Or.inr (Set.mem_range_self _))
      case hm A B ha hb => exact (map_mul b A B).symm ▸ ha.mul_right hb
    induction A using upper_lower_induction
    case hu => exact aux _ (Or.inl (Set.mem_range_self _)) _
    case hl => exact aux _ (Or.inr (Set.mem_range_self _)) _
    case hm X Y hx hy => exact (map_mul a X Y).symm ▸ hx.mul_left hy
  have ha (A) : τ (a A) = b (s A) := by
    induction A using upper_lower_induction
    case hu t => simpa only [s, map_upper] using hu t
    case hl t => simpa only [s, map_lower] using hl t
    case hm X Y hx hy => simp only [map_mul, hx, hy]
  have hs (A) : s (s A) = A := by
    apply Subtype.ext
    ext i j
    exact hσ _
  have hb (A) : τ (b A) = a (s A) := by
    simpa only [hs] using congrArg τ (ha (s A)).symm |>.trans (hτ _)
  have hb' (A) : τ (b (s A)) = a A := by rw [hb, hs]
  let f : SpecialLinearGroup (Fin 2) K →* G :=
    { toFun := fun A ↦ a A * b (s A)
      map_one' := by simp
      map_mul' := by
        intro A B
        simp only [map_mul]
        calc
          a A * a B * (b (s A) * b (s B)) =
              a A * (a B * b (s A)) * b (s B) := by simp only [mul_assoc]
          _ = _ := by rw [(hcomm B (s A)).eq]; simp only [mul_assoc] }
  have hf (A) : f A ∈ fixedSubgroup τ := by
    change τ (a A * b (s A)) = a A * b (s A)
    rw [map_mul, ha, hb']
    exact (hcomm A (s A)).eq.symm
  refine ⟨f.codRestrict (fixedSubgroup τ) hf, fun _ ↦ rfl, ?_, ?_⟩
  · intro t
    change a (upper t) * b (s (upper t)) = _
    rw [map_upper]
  · intro t
    change a (lower t) * b (s (lower t)) = _
    rw [map_lower]

end RankOne

section OrthogonalRoots

open Specs.Pinning (AttachedDatum BasedRootDatum PinnedGroup)
open Specs.AbstractPairing (Root)

theorem orthogonalRootCombinations : OrthogonalRootCombinations.{u} := by
  intro D hsym a b hab
  have hba : D.datum.pairing b a = 0 := (hsym b a).trans hab
  constructor
  · intro m n hm _ h
    have hh := congrArg (D.datum.coroot' a) h
    change D.datum.coroot' a (m • D.datum.root a) =
      D.datum.coroot' a (n • D.datum.root b) at hh
    simp only [map_smul, D.datum.root_coroot'_eq_pairing, D.datum.pairing_same,
      hba, smul_eq_mul] at hh
    omega
  · intro m n hm hn h
    obtain ⟨i, hi⟩ := h
    have hpa : D.datum.pairing i a = m * 2 := by
      rw [RootPairing.pairing_eq_add_of_root_eq_smul_add_smul hi]
      simp [hba]
    have hpb : D.datum.pairing i b = n * 2 := by
      rw [RootPairing.pairing_eq_add_of_root_eq_smul_add_smul hi]
      simp [hab]
    have he : (2 : ℤ) = m * (m * 2) + n * (n * 2) := by
      calc
        2 = D.datum.pairing i i := (D.datum.pairing_same i).symm
        _ = m • D.datum.pairing a i + n • D.datum.pairing b i :=
          RootPairing.pairing_eq_add_of_root_eq_smul_add_smul hi
        _ = _ := by rw [hsym a i, hsym b i, hpa, hpb, smul_eq_mul, smul_eq_mul]
    have hm₂ : 1 ≤ m ^ 2 := by have := sq_pos_iff.mpr hm; omega
    have hn₂ : 1 ≤ n ^ 2 := by have := sq_pos_iff.mpr hn; omega
    nlinarith only [he, hm₂, hn₂]

theorem orthogonalRootGroups : OrthogonalRootGroups.{u} := by
  intro k _ A P D hsym a b hab i hi j hj R p q
  let := D.comm
  let Q := D.datum.rootDatum
  change Q.pairing a b = 0 at hab
  change i ∈ ({a, Q.reflectionPerm a a} : Set (Root P.pair.T)) at hi
  change j ∈ ({b, Q.reflectionPerm b b} : Set (Root P.pair.T)) at hj
  have hp : Q.pairing i j = 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simpa using hab
  obtain ⟨hind, hcone⟩ := orthogonalRootCombinations D.toBased hsym i j hp
  apply Classification.RankOneRelations.independentRootCommutation P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal i.val i.property j.val j.property _ _
    (P.roots i).val (P.roots j).val (P.roots i).property (P.roots j).property R p q
  · rintro ⟨m, n, hm, hn, he⟩
    apply hind m n hm hn
    change m • Q.root i = n • Q.root j
    rw [D.datum.root_eq, D.datum.root_eq]
    exact congrArg Additive.ofMul he
  · intro m n hm hn h
    apply hcone (m : ℤ) (n : ℤ) (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')
    let a₀ : Root P.pair.T := ⟨i.val ^ m * j.val ^ n, h⟩
    refine ⟨a₀, ?_⟩
    change Q.root a₀ = m • Q.root i + n • Q.root j
    rw [D.datum.root_eq, D.datum.root_eq, D.datum.root_eq]
    rfl

end OrthogonalRoots

section IntegralCoordinates

open Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open private additivePoint_surjective integralAdditivePoint_injective from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

private theorem integralAdditivePoint_map {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (z : R) :
    integralSpec.map f.op ≫ additivePoint R z = additivePoint S (f.hom z) := by
  unfold additivePoint
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change f.hom (Polynomial.aeval z Polynomial.X) = Polynomial.aeval (f.hom z) Polynomial.X
  simp

private theorem markedRootPoint_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (a : D.I) (z : R) :
    (integralPointFunctor M.group).map f (markedRootPoint M R a z) =
      markedRootPoint M S a (f.hom z) := by
  change integralSpec.map f.op ≫ (additivePoint R z ≫ (M.root a).hom.hom) = _
  rw [← Category.assoc, integralAdditivePoint_map]
  rfl

private theorem markedRootPoint_injective {D : BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) (a : D.I) :
    Function.Injective (markedRootPoint M R a) := by
  have := M.rootClosed a
  have : Mono (M.root a).hom.hom := Over.mono_of_mono_left _
  intro x y h
  apply integralAdditivePoint_injective R
  exact (cancel_mono (M.root a).hom.hom).mp h

private theorem integralPoint_map_injective {X : IntegralScheme.{u}} (hX : IsAffine X.left)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (fun p : integralSpec.obj (op R) ⟶ X ↦ integralSpec.map f.op ≫ p) := by
  let e := X.left.isoSpec
  intro p q h
  apply Over.OverMorphism.ext
  apply (cancel_mono e.hom).mp
  apply Spec.preimage_injective
  let j := CommRingCat.ofHom f.hom.toRingHom
  have hj : Mono j := ConcreteCategory.mono_of_injective j hf
  have h' : Spec.map j ≫ (p.left ≫ e.hom) = Spec.map j ≫ (q.left ≫ e.hom) := by
    have h'' := congrArg (fun t : integralSpec.obj (op S) ⟶ X ↦ t.left ≫ e.hom) h
    change (Spec.map j ≫ p.left) ≫ e.hom = (Spec.map j ≫ q.left) ≫ e.hom at h''
    calc
      _ = (Spec.map j ≫ p.left) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = (Spec.map j ≫ q.left) ≫ e.hom := h''
      _ = _ := Category.assoc _ _ _
  have hh := congrArg Spec.preimage h'
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at hh
  exact (cancel_mono j).mp hh

private theorem liftIntegralClosedPoint {X Y : IntegralScheme.{u}} (m : X ⟶ Y)
    [IsClosedImmersion m.left] {R S : IntegralAlgebra.{u}} [IsReduced R]
    (f : R ⟶ S) (hf : Function.Injective f.hom) (p : integralSpec.obj (op R) ⟶ Y)
    (q : integralSpec.obj (op S) ⟶ X) (heq : integralSpec.map f.op ≫ p = q ≫ m) :
    ∃ q₀ : integralSpec.obj (op R) ⟶ X, q₀ ≫ m = p := by
  let j := (integralSpec.map f.op).left
  have : IsDominant j := by
    change IsDominant (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
    rw [isDominant_iff]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker f.hom.toRingHom ≤ nilradical R
    rw [(RingHom.injective_iff_ker_eq_bot f.hom.toRingHom).mp hf]
    exact bot_le
  have : IsReduced (integralSpec.obj (op R)).left := by
    change IsReduced (Spec (CommRingCat.of R))
    infer_instance
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have hj : (j ≫ p.left).ker = p.left.ker := by
    rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hh : j ≫ p.left = q.left ≫ m.left := congrArg Over.Hom.left heq
  have hker : m.left.ker ≤ p.left.ker := by
    rw [← hj, hh]
    exact q.left.le_ker_comp m.left
  let t := IsClosedImmersion.lift m.left p.left hker
  have ht : t ≫ m.left = p.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
  rw [← Over.w m, ← Category.assoc, ht, Over.w p]

theorem integralRootTransportUnits : IntegralRootTransportUnits.{u} := by
  intro D M R S _ f hf g a b c n hg
  have (i : D.I) := M.rootClosed i
  let ψ : IntegralPoints M.group R →* IntegralPoints M.group S :=
    ((integralPointFunctor M.group).map f).hom
  have hroot (i : D.I) (z : R) : ψ (markedRootPoint M R i z) =
      markedRootPoint M S i (f.hom z) := markedRootPoint_map M f i z
  let p := g * markedRootPoint M R a 1 * g⁻¹
  have hp : ψ p = markedRootPoint M S b (c : S) := by
    change ψ (g * markedRootPoint M R a 1 * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, hroot, map_one]
    change n * markedRootPoint M S a 1 * n⁻¹ = _
    simpa only [mul_one] using hg 1
  obtain ⟨p₀, hp₀⟩ := liftIntegralClosedPoint (M.root b).hom.hom f hf p (additivePoint S c) hp
  obtain ⟨d, rfl⟩ := additivePoint_surjective R p₀
  have hd : f.hom d = (c : S) := markedRootPoint_injective M S b <| by
    rw [← hroot, show markedRootPoint M R b d = p from hp₀]
    exact hp
  let q := g⁻¹ * markedRootPoint M R b 1 * g
  have hq : ψ q = markedRootPoint M S a (↑c⁻¹ : S) := by
    have h : n * markedRootPoint M S a (↑c⁻¹ : S) * n⁻¹ = markedRootPoint M S b 1 := by
      simpa only [Units.mul_inv] using hg (↑c⁻¹ : S)
    change ψ (g⁻¹ * markedRootPoint M R b 1 * g) = _
    rw [map_mul, map_mul, map_inv, hroot, map_one, ← h]
    change n⁻¹ * (n * markedRootPoint M S a (↑c⁻¹ : S) * n⁻¹) * n = _
    simp [mul_assoc]
  obtain ⟨q₀, hq₀⟩ := liftIntegralClosedPoint (M.root a).hom.hom f hf q
    (additivePoint S (↑c⁻¹ : S)) hq
  obtain ⟨e, rfl⟩ := additivePoint_surjective R q₀
  have he : f.hom e = (↑c⁻¹ : S) := markedRootPoint_injective M S a <| by
    rw [← hroot, show markedRootPoint M R a e = q from hq₀]
    exact hq
  let v : Rˣ := ⟨d, e, hf (by simp [hd, he]), hf (by simp [hd, he])⟩
  refine ⟨v, Units.ext hd, fun z ↦ ?_⟩
  apply integralPoint_map_injective M.affine f hf
  change ψ (g * markedRootPoint M R a z * g⁻¹) = ψ (markedRootPoint M R b (d * z))
  rw [map_mul, map_mul, map_inv, hroot, hroot, map_mul, hd]
  exact hg (f.hom z)

end IntegralCoordinates
section Torus

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (IntegralAlgebra Integers IntegralMarking IntegralPoints
  TorusValues integerAlgebra torusPoint)

private theorem rootFiltrationShift (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (c : Kˣ) :
    RootFiltrationShift K c := by
  unfold RootFiltrationShift
  intro v d z j
  have hc : v (c : K) ≠ 0 := by simp [v]
  have hd : exp d = v (c : K) := exp_log hc
  rw [map_mul, sub_eq_add_neg, exp_add, hd]
  exact ⟨mul_le_mul_iff_right₀ (pos_iff_ne_zero.mpr hc),
    mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr hc)⟩

private theorem rootLayerConjugation (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {H : Type u} [Group H]
    (x : K → H) (t : H) (c : Kˣ) (hconj : ∀ z, t * x z * t⁻¹ = x ((c : K) * z)) :
    RootLayerConjugation K x t c := by
  have hImage (P Q : Set K) (h : ∀ z : K, (c : K) * z ∈ Q ↔ z ∈ P) :
      MulAut.conj t '' (x '' P) = x '' Q := by
    ext p
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, (h z).mpr hz, (hconj z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      let y := (↑c⁻¹ : K) * z
      have hy : (c : K) * y = z := by simp [y]
      have hyQ : (c : K) * y ∈ Q := by rwa [hy]
      exact ⟨x y, ⟨y, (h y).mp hyQ, rfl⟩, (hconj y).trans (congrArg x hy)⟩
  intro j
  exact ⟨hImage _ _ fun z => (rootFiltrationShift K c z j).1,
    hImage _ _ fun z => (rootFiltrationShift K c z j).2⟩

theorem markedTorusLayerConjugation : MarkedTorusLayerConjugation.{u} := by
  intro K _ _ _ _ D M t a z j R g c d
  exact ⟨M.conjugation R t a z,
    rootFiltrationShift K (t (Multiplicative.ofAdd (D.datum.root a))) z j⟩


end Torus

section Walls
universe u

open Matrix (SpecialLinearGroup)
open scoped Matrix CategoryTheory.MonObj
open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.IntegralSemisimpleModel

private theorem rankOneMatrixWord_val {R : Type*} [CommRing R] (a : Rˣ) :
    (rankOneMatrixWord a).val = !![0, (a : R); -(↑a⁻¹ : R), 0] := by
  have ha : (a : R) * (↑a⁻¹ : R) = 1 := a.mul_inv
  have ha' : (↑a⁻¹ : R) * (a : R) = 1 := a.inv_mul
  change (!![1, (a : R); 0, 1] : Matrix (Fin 2) (Fin 2) R) *
      !![1, 0; -(↑a⁻¹ : R), 1] * !![1, (a : R); 0, 1] = _
  simp [ha, ha']

private theorem wallMatrix_val {R : Type*} [CommRing R] (a : Rˣ) :
    (wallMatrix a).val = !![0, -(a : R); (↑a⁻¹ : R), 0] := by
  simpa [wallMatrix] using rankOneMatrixWord_val (-a)

theorem wallMatrixRelations : WallMatrixRelations.{u} := by
  intro R _ a t
  have ha : (a : R) * (↑a⁻¹ : R) = 1 := a.mul_inv
  have ha' : (↑a⁻¹ : R) * (a : R) = 1 := a.inv_mul
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := t.mul_inv
  have ht' : (↑t⁻¹ : R) * (t : R) = 1 := t.inv_mul
  refine ⟨rankOneMatrixWord_val a, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, rankOneMatrixWord_val, rankOneMatrixWord_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  · apply Subtype.ext
    rw [pow_two, SpecialLinearGroup.coe_mul, wallMatrix_val]
    change (!![0, -(a : R); (↑a⁻¹ : R), 0] : Matrix (Fin 2) (Fin 2) R) *
      !![0, -(a : R); (↑a⁻¹ : R), 0] = !![-1, 0; 0, ↑(-1 : Rˣ)⁻¹]
    simp [ha, ha']
  · intro z
    constructor
    · apply Subtype.ext
      rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
        wallMatrix_val, Matrix.adjugate_fin_two]
      change (!![0, -(a : R); (↑a⁻¹ : R), 0] : Matrix (Fin 2) (Fin 2) R) *
        !![1, z; 0, 1] * !![0, -(-(a : R)); -(↑a⁻¹ : R), 0] =
        !![1, 0; -(↑a⁻¹ : R) ^ 2 * z, 1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, ha']
      all_goals ring
    · apply Subtype.ext
      rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
        wallMatrix_val, Matrix.adjugate_fin_two]
      change (!![0, -(a : R); (↑a⁻¹ : R), 0] : Matrix (Fin 2) (Fin 2) R) *
        !![1, 0; z, 1] * !![0, -(-(a : R)); -(↑a⁻¹ : R), 0] =
        !![1, -(a : R) ^ 2 * z; 0, 1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, ha']
      all_goals ring
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      wallMatrix_val]
    change (!![1, (t : R); 0, 1] : Matrix (Fin 2) (Fin 2) R) *
      !![0, -(a : R); (↑a⁻¹ : R), 0] =
      !![1, 0; (↑t⁻¹ : R), 1] * !![((t * a⁻¹ : Rˣ) : R), 0; 0, (((t * a⁻¹)⁻¹ : Rˣ) : R)] *
        !![1, -(a : R) ^ 2 * (↑t⁻¹ : R); 0, 1]
    have ha₂ : (↑a⁻¹ : R) * ((a : R) ^ 2 * (↑t⁻¹ : R)) = (a : R) * (↑t⁻¹ : R) := by
      linear_combination ((a : R) * (↑t⁻¹ : R)) * ha'
    have ht₂ : (↑t⁻¹ : R) * ((t : R) * (↑a⁻¹ : R)) = (↑a⁻¹ : R) := by
      rw [← mul_assoc, ht', one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha₂, ht₂, mul_assoc]
    calc
      (a : R) = (a : R) * ((t : R) * (↑t⁻¹ : R)) := by rw [ht, mul_one]
      _ = (t : R) * ((a : R) * (↑t⁻¹ : R)) := by ring

theorem markedWallRelations : MarkedWallRelations.{u} := by
  intro D M R i a t j x h n
  let ρ : SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne i).app R).hom
  have hu (z : R) : ρ (upper z) = x i z := M.rankOneUpper i R z
  have hl (z : R) : ρ (lower z) = x j z := M.rankOneLower i R z
  have hd (b : Rˣ) : ρ (diagonal b) = h b := M.rankOneDiagonal i R b
  have hn : ρ (wallMatrix a) = n := rfl
  obtain ⟨_, _, hs, hc, hf⟩ := wallMatrixRelations a t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hn, wallMatrix, rankOneMatrixWord, map_mul, map_mul, hu, hl]
    simp
  · simpa only [map_pow, hd, hn] using congrArg ρ hs
  · intro z
    exact ⟨by simpa only [map_mul, map_inv, hu, hl, hn] using congrArg ρ (hc z).1,
      by simpa only [map_mul, map_inv, hu, hl, hn] using congrArg ρ (hc z).2⟩
  · simpa only [map_mul, hu, hl, hd, hn] using congrArg ρ hf

end Walls

section OrderedCoordinates

open AlgebraicGeometry Opposite CategoryTheory.CartesianMonoidalCategory
open Specs.IntegralSemisimpleModel Specs.Pinning
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
universe u

private def rootFactorPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (v : D.I → R) :
    (l : List D.I) → integralSpec.obj (op R) ⟶ product (fun _ : D.I => M.line.group.X) l
  | [] => toUnit _
  | a :: l => lift (M.line.point R (v a)) (rootFactorPoint M R v l)

private theorem rootFactorPoint_comp {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (v : D.I → R) (l : List D.I) :
    rootFactorPoint M R v l ≫ rootProduct M.line M.root l = orderedRootPoint M R l v := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons a l ih =>
    let T := product (fun _ : D.I => M.line.group.X) l
    change lift (M.line.point R (v a)) (rootFactorPoint M R v l) ≫
      ((fst M.line.group.X T ≫ (M.root a).hom.hom) *
        (snd M.line.group.X T ≫ rootProduct M.line M.root l)) =
        markedRootPoint M R a (v a) * orderedRootPoint M R l v
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd, ih]
    rfl

open private integralAdditivePoint_injective from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

private theorem rootFactorPoint_eq {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (v w : D.I → R) (l : List D.I)
    (h : rootFactorPoint M R v l = rootFactorPoint M R w l) :
    ∀ i ∈ l, v i = w i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · apply integralAdditivePoint_injective R
      simpa only [rootFactorPoint, lift_fst] using congrArg (fun p => p ≫ fst _ _) h
    · apply ih _ i hi
      simpa only [rootFactorPoint, lift_snd] using congrArg (fun p => p ≫ snd _ _) h

private theorem lift_cellMap_eq {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (v : D.I → R) (t : IntegralPoints (splitTorus D) R)
    (l r : List D.I) :
    lift (rootFactorPoint M R v l) (lift t (rootFactorPoint M R v r)) ≫
      cellMap M.line M.torus M.root l r = markedCellPoint M R l r v t := by
  unfold cellMap markedCellPoint
  rw [MonObj.comp_mul, ← Category.assoc, lift_fst, rootFactorPoint_comp, ← Category.assoc,
    lift_snd, MonObj.comp_mul, ← Category.assoc, lift_fst, ← Category.assoc,
    lift_snd, rootFactorPoint_comp]

private theorem markedRootPoint_neg {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (z : R) :
    markedRootPoint M R a (-z) = (markedRootPoint M R a z)⁻¹ := by
  have hh : ∀ x y : R, markedRootPoint M R a x * markedRootPoint M R a y =
      markedRootPoint M R a (x + y) := by
    intro x y
    letI : GrpObj (M.line.group.X) := M.line.operations
    have hmul := MonObj.mul_comp (M.line.point R x) (M.line.point R y) (M.root a).hom.hom
    exact hmul.symm.trans (congrArg (fun p => p ≫ (M.root a).hom.hom) (M.line.add R x y))
  have he : markedRootPoint M R a 0 = 1 := by
    have h := hh 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  apply eq_inv_of_mul_eq_one_left
  rw [hh, neg_add_cancel, he]

private theorem orderedRootPoint_reverse_neg {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (v : D.I → R) :
    orderedRootPoint M R l.reverse (fun a => -v a) = (orderedRootPoint M R l v)⁻¹ := by
  induction l with
  | nil => simp [orderedRootPoint]
  | cons a l ih =>
    simpa only [orderedRootPoint, List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev,
      markedRootPoint_neg] using congrArg (· * (markedRootPoint M R a (v a))⁻¹) ih

open Specs.OrderedRootProducts (Enumerates)

set_option backward.isDefEq.respectTransparency false in
private theorem markedCellPoint_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l r : List D.I)
    (hl : Enumerates l {i | ¬ D.base.IsPos i}) (hr : Enumerates r {i | D.base.IsPos i}) :
    Function.Injective (fun q : (D.I → R) × IntegralPoints (splitTorus D) R =>
      markedCellPoint M R l r q.1 q.2) := by
  rintro ⟨v, t⟩ ⟨w, s⟩ h
  change markedCellPoint M R l r v t = markedCellPoint M R l r w s at h
  let c := cellMap M.line M.torus M.root l r
  have hopen : IsOpenImmersion c.left := M.openCell l r hl hr
  letI : Mono ((Over.forget Base).map c) := by change Mono c.left; infer_instance
  have hmono : Mono c := (Over.forget Base).mono_of_mono_map inferInstance
  have h' : lift (rootFactorPoint M R v l) (lift t (rootFactorPoint M R v r)) =
      lift (rootFactorPoint M R w l) (lift s (rootFactorPoint M R w r)) := by
    apply (cancel_mono c).mp
    simp only [c, lift_cellMap_eq, h]
  have hleft : rootFactorPoint M R v l = rootFactorPoint M R w l := by
    simpa only [lift_fst] using congrArg (fun p => p ≫ fst _ _) h'
  have hright : lift t (rootFactorPoint M R v r) = lift s (rootFactorPoint M R w r) := by
    simpa only [lift_snd] using congrArg (fun p => p ≫ snd _ _) h'
  have hpos : rootFactorPoint M R v r = rootFactorPoint M R w r := by
    simpa only [lift_snd] using congrArg (fun p => p ≫ snd _ _) hright
  have ht : t = s := by
    simpa only [lift_fst] using congrArg (fun p => p ≫ fst _ _) hright
  apply Prod.ext _ ht
  funext i
  by_cases h : D.base.IsPos i
  · exact rootFactorPoint_eq M R v w r hpos i ((hr.2 i).mpr h)
  · exact rootFactorPoint_eq M R v w l hleft i ((hl.2 i).mpr h)

set_option backward.isDefEq.respectTransparency false in
private theorem reverseCellPoint_eq {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l r : List D.I) (v : D.I → R)
    (t : IntegralPoints (splitTorus D) R) :
    orderedRootPoint M R r.reverse v * ((t ≫ M.torus.hom.hom) *
      orderedRootPoint M R l.reverse v) =
      (markedCellPoint M R l r (fun a => -v a) t⁻¹)⁻¹ := by
  have hx (l : List D.I) : orderedRootPoint M R l.reverse v =
      (orderedRootPoint M R l (fun a => -v a))⁻¹ := by
    simpa only [neg_neg] using orderedRootPoint_reverse_neg M R l (fun a => -v a)
  have ht : ((t⁻¹ ≫ M.torus.hom.hom : IntegralPoints M.group R))⁻¹ =
      t ≫ M.torus.hom.hom := by rw [← GrpObj.inv_comp, inv_inv]
  rw [hx r, hx l, markedCellPoint, mul_inv_rev, mul_inv_rev, ht, mul_assoc]

theorem markedCellCoordinates : MarkedCellCoordinates.{u} := by
  intro D M R l r hl hr
  have hinj := markedCellPoint_injective M R l r hl hr
  refine ⟨hinj, ?_⟩
  rintro ⟨v, t⟩ ⟨w, s⟩ h
  change orderedRootPoint M R r.reverse v *
      ((t ≫ M.torus.hom.hom) * orderedRootPoint M R l.reverse v) =
    orderedRootPoint M R r.reverse w *
      ((s ≫ M.torus.hom.hom) * orderedRootPoint M R l.reverse w) at h
  rw [reverseCellPoint_eq M R l r v t, reverseCellPoint_eq M R l r w s] at h
  have e : ((fun i => -v i), t⁻¹) = ((fun i => -w i), s⁻¹) :=
    @hinj ((fun i => -v i), t⁻¹) ((fun i => -w i), s⁻¹) (inv_injective h)
  refine Prod.ext ?_ ?_
  · funext i
    exact neg_injective (congrFun (congrArg Prod.fst e) i)
  · exact inv_injective (congrArg Prod.snd e)

end OrderedCoordinates

section MarkedFibre

open Specs.IntegralSemisimpleModel Specs.Pinning Specs.RootGroups
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RationalRealization (Realization)
open scoped CategoryTheory.MonObj
universe u

attribute [local instance] integerAlgebra

theorem markedFibreExists : MarkedFibreExists.{u} := by
  intro D M k _
  obtain ⟨A, F, e, t, z, hT, hp, hv, hz⟩ := M.fieldFibre k
  exact ⟨⟨A, F, e, t, z, hT, fun i => congrArg Subtype.val (hp i), hv, hz⟩⟩

private theorem indexEquiv_reflectionPerm
    {D E : BasedRootDatum.{u}} (e : BasedIso D E) (a i : D.I) :
    e.val.indexEquiv (D.datum.reflectionPerm a i) =
      E.datum.reflectionPerm (e.val.indexEquiv a) (e.val.indexEquiv i) := by
  apply E.datum.root.injective
  rw [E.datum.root_reflectionPerm, ← RootPairing.Hom.root_weightMap_apply,
    D.datum.root_reflectionPerm]
  change e.val.weightEquiv (D.datum.reflection a (D.datum.root i)) =
    E.datum.reflection (e.val.indexEquiv a) (E.datum.root (e.val.indexEquiv i))
  rw [e.val.weightEquiv_reflection]
  congr 1
  exact RootPairing.Hom.root_weightMap_apply D.datum E.datum i e.val.toHom

open private forgetFibrePoint_mul from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

open Specs.AbstractPairing (Root)
open Specs.IntegralRootRelations (upper lower)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
theorem markedOrthogonalRootCommutation : MarkedOrthogonalRootCommutation.{u} := by
  intro D M hs a b hab k _ R S U
  obtain ⟨C⟩ := markedFibreExists M k
  let F := C.realization
  let E := F.attached.toBased
  let e := F.datumIso.val.indexEquiv
  have hp (i j : D.I) : E.datum.pairing (e i) (e j) = D.datum.pairing i j := by
    change E.datum.coroot' (e j) (E.datum.root (e i)) = D.datum.coroot' j (D.datum.root i)
    rw [← F.datumIso.val.toHom.root_weightMap_apply, ← F.datumIso.val.weightEquiv_apply]
    exact F.datumIso.val.coroot'_weightEquiv j (D.datum.root i)
  have hsym (i j : E.I) : E.datum.pairing i j = E.datum.pairing j i := by
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rw [hp, hp, hs]
  have hcom (i : D.I) (hi : i ∈ ({a, D.datum.reflectionPerm a a} : Set D.I))
      (j : D.I) (hj : j ∈ ({b, D.datum.reflectionPerm b b} : Set D.I)) (x y : R) :
      Commute (markedRootPoint M.toIntegralMarking S i x)
        (markedRootPoint M.toIntegralMarking S j y) := by
    have hmem (i a : D.I) (hi : i ∈ ({a, D.datum.reflectionPerm a a} : Set D.I)) :
        e i ∈ ({e a, E.datum.reflectionPerm (e a) (e a)} : Set E.I) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      rcases hi with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (indexEquiv_reflectionPerm F.datumIso a a)
    let p (i : D.I) (z : R) := rootPoint (C.coordinate i).val.hom R z
    have hc := orthogonalRootGroups F.pinned F.attached hsym (e a) (e b)
      ((hp a b).trans hab) (e i) (hmem i a hi) (e j) (hmem j b hj) R (p i x) (p j y)
    let φ : GroupPoints F.pinned.pair.G.val R → IntegralPoints M.group S :=
      fun g => forgetFibrePoint M.group R (g ≫ C.groupIso.inv.hom.hom)
    have hmul (g h : GroupPoints F.pinned.pair.G.val R) :
        φ (g * h) = φ g * φ h := by
      dsimp only [φ]
      rw [MonObj.mul_comp, forgetFibrePoint_mul]
    have he (i : D.I) (z : R) :
        φ (p i z ≫ (F.pinned.roots (e i)).val.inclusion.hom.hom) =
          markedRootPoint M.toIntegralMarking S i z := by
      dsimp only [φ, p, rootPoint]
      simp only [Category.assoc]
      exact C.root_eval i R z
    have h := congrArg φ hc.eq
    rw [hmul, hmul, he, he] at h
    exact h
  have hcoord (i : D.I) (A : Matrix.SpecialLinearGroup (Fin 2) S) (hA : A ∈ U) :
      ∃ j ∈ ({i, D.datum.reflectionPerm i i} : Set D.I), ∃ z : R,
        ((M.rankOne i).app S A : IntegralPoints M.group S) =
          markedRootPoint M.toIntegralMarking S j z := by
    rcases hA with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨i, Set.mem_insert _ _, z, M.rankOneUpper i S z⟩
    · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_singleton _), z, M.rankOneLower i S z⟩
  intro A hA B hB
  obtain ⟨i, hi, x, hx⟩ := hcoord a A hA
  obtain ⟨j, hj, y, hy⟩ := hcoord b B hB
  rw [hx, hy]
  exact hcom i hi j hj x y

end MarkedFibre

section RootTransport

open AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open Specs.Pinning Specs.RootGroups
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (characterValue)
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
universe u

open private normalizes_of_point_conjugation tangent_weight_of_scalarAction rootPoint_comp
  from LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private same_subgroup_trans from LinearAlgebraicGroups.RootData.RankOneFlag
open private pointMap from LinearAlgebraicGroups.Classification.RankOneRelations

set_option backward.isDefEq.respectTransparency false in
theorem rootCoordinateTransport : RootCoordinateTransport.{u} := by
  intro k _ A P f w hw a b hab x y
  let T := P.pair.T
  let G := P.pair.G.val
  let U := (P.roots a).val
  let V := (P.roots b).val
  let U' : ClosedSubgroup G := ⟨U.group, U.inclusion ≫ f.hom, by
    letI := U.isClosedImmersion
    have : IsIso f.hom.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso f.hom
    rw [Grp.comp_hom_hom, Over.comp_left]
    infer_instance⟩
  have hx : HasScalarAction T b.val (x.val.hom ≫ U'.inclusion) := by
    intro R t z
    let t₀ : GroupPoints T.group R := t ≫ w.inv.hom.hom
    have htorus' : pointMap R f.hom (pointMap R T.inclusion t₀) = pointMap R T.inclusion t := by
      have h₁ := congrArg (fun p : T.group ⟶ G => t₀ ≫ p.hom.hom) hw
      change (t₀ ≫ T.inclusion.hom.hom) ≫ f.hom.hom.hom = t ≫ T.inclusion.hom.hom
      have h₂ : t₀ ≫ (w.hom ≫ T.inclusion).hom.hom = t ≫ T.inclusion.hom.hom := by
        unfold t₀
        change t ≫ (w.inv ≫ w.hom ≫ T.inclusion).hom.hom = _
        rw [Iso.inv_hom_id_assoc]
      exact (by simpa only [Grp.comp_hom_hom, Category.assoc] using h₁.trans h₂)
    have hχ : characterValue a.val R t₀ = characterValue b.val R t := by
      rw [← hab]
      unfold characterValue t₀
      simp only [Category.assoc]
      rfl
    have hroot (v : R) : pointMap R f.hom (rootPoint (x.val.hom ≫ U.inclusion) R v) =
        rootPoint (x.val.hom ≫ U'.inclusion) R v := by
      simp only [rootPoint, U', Grp.comp_hom_hom]
      rfl
    let g : GroupPoints G R := t₀ ≫ T.inclusion.hom.hom
    have h := congrArg (pointMap R f.hom) (x.property R t₀ z)
    change pointMap R f.hom (g * rootPoint (x.val.hom ≫ U.inclusion) R z * g⁻¹) =
        pointMap R f.hom (rootPoint (x.val.hom ≫ U.inclusion) R
          (characterValue a.val R t₀ * z)) at h
    have hg : pointMap R f.hom g = pointMap R T.inclusion t := htorus'
    change pointMap R T.inclusion t * rootPoint (x.val.hom ≫ U'.inclusion) R z *
      (pointMap R T.inclusion t)⁻¹ = _
    simpa only [map_mul, map_inv, hg, hroot, hχ] using h
  have hU' : IsRootSubgroup T U' b.val := by
    refine ⟨(P.roots a).property.1, (P.roots a).property.2.1, ?_,
      tangent_weight_of_scalarAction T U' b.val A x.val hx⟩
    apply normalizes_of_point_conjugation
    intro R t p
    obtain ⟨z, rfl⟩ := rootPoint_surjective x.val R p
    refine ⟨rootPoint x.val.hom R (characterValue b.val R t * z), ?_⟩
    simpa only [rootPoint_comp] using (hx R t z).symm
  obtain ⟨W, _, _, _, _, hW⟩ := ((RootData.RootGroups.rootSubgroups P.pair.G
    P.pair.reductive T P.pair.split P.pair.maximal).2 b.val b.property).2.2
  have h₁ := hW U' hU'
  have h₂ := hW V (P.roots b).property
  let j := subgroupIso (same_subgroup_trans ⟨h₁.2, h₁.1⟩ h₂)
  have hj : (x.val ≪≫ j.val).hom ≫ V.inclusion = x.val.hom ≫ U'.inclusion := by
    simp only [Iso.trans_hom, Category.assoc, j.property]
  let q : RootCoordinate A T V b.val := ⟨x.val ≪≫ j.val, hj.symm ▸ hx⟩
  have hq : q.val.hom ≫ V.inclusion = (x.val.hom ≫ U.inclusion) ≫ f.hom := by
    rw [show q.val = x.val ≪≫ j.val from rfl, hj]
    exact (Category.assoc _ _ _).symm
  simpa only [hq] using
    (LinearAlgebraicGroups.Classification.Pinning.coordinateChanges A T V b.val y q)

end RootTransport

section WallDepth

universe u

theorem wallDepths : WallDepths.{u} := by
  intro K _ _ _ _ j v
  have hsurj : Function.Surjective v := by
    intro x
    let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    obtain ⟨t, ht⟩ := valuation_surjective (i.symm x)
    refine ⟨t, ?_⟩
    change i (valuation K t) = x
    rw [ht, i.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := hsurj (exp (-j))
    have hn : t ≠ 0 := by
      intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    exact ⟨Units.mk0 t hn, ht⟩
  intro a ha
  have haInv : v (↑a⁻¹ : K) = exp j := by
    rw [Units.val_inv_eq_inv_val, v.map_inv, ha, ← exp_neg, neg_neg]
  have hscale (z : K) : v (-(a : K) ^ 2 * z) = exp ((-j) + (-j)) * v z := by
    rw [map_mul, v.map_neg, map_pow, ha, exp_add, pow_two]
  refine ⟨fun z => ⟨?_, hscale z⟩, ?_⟩
  · rw [map_mul, v.map_neg, map_pow, haInv, exp_add, pow_two]
  · intro t ht
    have htInv : v (↑t⁻¹ : K) = exp j := by
      rw [Units.val_inv_eq_inv_val, v.map_inv, ht, ← exp_neg, neg_neg]
    refine ⟨htInv, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, ht, haInv, ← exp_add, neg_add_cancel, exp_zero]
    · rw [hscale, htInv, ← exp_add, add_assoc, neg_add_cancel, add_zero]

end WallDepth

section LinkedCoordinates

open AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.OrderedRootProducts (Enumerates)
open Specs.IntegralRootRelations (upper lower diagonal)
open scoped CategoryTheory.MonObj
universe u

attribute [local instance] integerAlgebra

private theorem markedRootPoint_zero {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (i : D.I) : markedRootPoint M R i 0 = 1 := by
  let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne i).app R).hom
  have h₀ : upper (0 : R) = 1 := by
    apply Subtype.ext
    simp [upper, Matrix.one_fin_two]
  unfold markedRootPoint
  rw [← M.rankOneUpper i R 0]
  change ρ (upper 0) = 1
  rw [h₀, map_one]

open private ordered_single from LinearAlgebraicGroups.Classification.IntegralRootRelations

set_option backward.isDefEq.respectTransparency false in
private theorem markedSingleCell_coords {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i})
    (b : D.I) (hb : D.base.IsPos b)
    (x₁ x₂ y₁ y₂ : R) (s t : IntegralPoints (splitTorus D) R) :
    let l := D.datum.reflectionPerm b b
    markedRootPoint M R l y₁ * ((s ≫ M.torus.hom.hom) * markedRootPoint M R b x₁) =
      markedRootPoint M R l y₂ * ((t ≫ M.torus.hom.hom) * markedRootPoint M R b x₂) →
    x₁ = x₂ := by
  classical
  intro l h
  have hl : ¬ D.base.IsPos l := by
    letI := D.datum.indexNeg
    change ¬ D.base.IsPos (-b)
    rw [RootPairing.Base.IsPos.neg_iff_not D.base]
    exact not_not_intro hb
  have hne : l ≠ b := fun h => hl (h ▸ hb)
  let v (x y : R) (i : D.I) : R := if i = b then x else if i = l then y else 0
  have he (x y : R) (u : IntegralPoints (splitTorus D) R) :
      markedCellPoint M R negative positive (v x y) u =
        markedRootPoint M R l y * ((u ≫ M.torus.hom.hom) * markedRootPoint M R b x) := by
    have hneg : orderedRootPoint M R negative (v x y) = markedRootPoint M R l y := by
      rw [orderedRootPoint, ← ordered_single negative hn.1 l ((hn.2 l).mpr hl) (markedRootPoint M R l y)]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hib : i ≠ b := fun e => (hn.2 i).mp hi (e ▸ hb)
      by_cases hil : i = l
      · subst i
        simp [v, hib]
      · simp [v, hib, hil, markedRootPoint_zero]
    have hpos : orderedRootPoint M R positive (v x y) = markedRootPoint M R b x := by
      rw [orderedRootPoint, ← ordered_single positive hp.1 b ((hp.2 b).mpr hb) (markedRootPoint M R b x)]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil : i ≠ l := fun e => hl (e ▸ (hp.2 i).mp hi)
      by_cases hib : i = b
      · subst i
        simp [v]
      · simp [v, hib, hil, markedRootPoint_zero]
    simp only [markedCellPoint, hneg, hpos]
  rw [← he x₁ y₁ s, ← he x₂ y₂ t] at h
  have hv : (v x₁ y₁, s) = (v x₂ y₂, t) :=
    @markedCellPoint_injective D M R negative positive hn hp
      (v x₁ y₁, s) (v x₂ y₂, t) h
  simpa [v] using congrFun (congrArg Prod.fst hv) b

private theorem markedGauss {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (i : D.I) (u v : R) (s : Rˣ)
    (hs : (s : R) = 1 + u * v) :
    let j := D.datum.reflectionPerm i i
    let x := markedRootPoint M R
    x i u * x j v =
      x j (v * (↑s⁻¹ : R)) *
        ((torusPoint D R (cocharacter D (D.datum.coroot i) R s) ≫ M.torus.hom.hom) *
          x i (u * (↑s⁻¹ : R))) := by
  intro j x
  let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne i).app R).hom
  have hu (z : R) : ρ (upper z) = x i z := M.rankOneUpper i R z
  have hl (z : R) : ρ (lower z) = x j z := M.rankOneLower i R z
  have hd (z : Rˣ) : ρ (diagonal z) =
    torusPoint D R (cocharacter D (D.datum.coroot i) R z) ≫ M.torus.hom.hom :=
    M.rankOneDiagonal i R z
  simpa only [map_mul, hu, hl, hd, mul_assoc] using
    congrArg ρ (Classification.IntegralRootRelations.oppositeRootMatrix u v s hs)

private def dualNumberUnit {k : Type u} [Field k] (z : DualNumber k)
    (h : z ^ 2 = 0) : (DualNumber k)ˣ :=
  ⟨1 + z, 1 - z, by linear_combination -h, by linear_combination -h⟩

set_option backward.isDefEq.respectTransparency false in
theorem linkedLowerCoordinateUniqueness : LinkedLowerCoordinateUniqueness.{u} := by
  intro k _ D M negative positive hn hp a b hb R x j l f c ht hupper hlower
  let ε : DualNumber k := DualNumber.eps
  let v := algebraMap k (DualNumber k) (c : k) * ε
  have hε : ε ^ 2 = 0 := DualNumber.eps_pow_two
  have hv : v ^ 2 = 0 := by rw [show v = _ from rfl, mul_pow, hε, mul_zero]
  let s := dualNumberUnit ε hε
  let s' := dualNumberUnit v hv
  have hs : (s : R) = 1 + 1 * ε := by simp [s, dualNumberUnit]
  have hs' : (s' : R) = 1 + 1 * v := by simp [s', dualNumberUnit]
  have ha := congrArg f (markedGauss M R a 1 ε s hs)
  have hb' := markedGauss M R b 1 v s' hs'
  obtain ⟨q, hq⟩ := ht (torusPoint D R (cocharacter D (D.datum.coroot a) R s))
  change f (x a 1 * x j ε) =
    f (x j (ε * (↑s⁻¹ : R)) *
      ((torusPoint D R (cocharacter D (D.datum.coroot a) R s) ≫ M.torus.hom.hom) *
        x a (1 * (↑s⁻¹ : R)))) at ha
  have hprod : x b 1 * x l v =
      x l (algebraMap k (DualNumber k) (c : k) * (ε * (↑s⁻¹ : R))) *
        ((q ≫ M.torus.hom.hom) * x b (1 * (↑s⁻¹ : R))) := by
    rw [map_mul, map_mul, map_mul, hupper, hlower, hlower, hq, hupper] at ha
    exact ha
  have he : (1 : R) * (↑s⁻¹ : R) = 1 * (↑s'⁻¹ : R) :=
    markedSingleCell_coords M R negative positive hn hp b hb _ _ _ _ _ _
      (hprod.symm.trans hb')
  simp only [one_mul] at he
  change (1 - ε : DualNumber k) = 1 - v at he
  apply Units.ext
  have hεv : ε = v := sub_right_injective he
  have hcv := congrArg TrivSqZeroExt.snd hεv
  simpa [ε, v, TrivSqZeroExt.algebraMap_eq_inl] using hcv.symm

end LinkedCoordinates

section PinnedLinkedCoordinates

open AlgebraicGeometry Opposite CategoryTheory.CartesianMonoidalCategory
open Specs.IntegralSemisimpleModel Specs.Pinning Specs.RootGroups
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Root)
open Specs.OrderedRootProducts (Enumerates)
open Specs.CharacterDescent (Character)
open scoped CategoryTheory.MonObj
universe u

attribute [local instance] integerAlgebra

open private forgetFibrePoint_comp forgetFibrePoint_mul from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

private def forgetFibrePointEquiv {k : Type u} [Field k] (G : IntegralGroup.{u})
    (R : TestAlgebra k) :
    GroupPoints ((fibre k).obj G) R ≃* IntegralPoints G (CommAlgCat.of Integers.{u} R) :=
  { Equiv.ofBijective (forgetFibrePoint G R)
      (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective G R) with
    map_mul' := forgetFibrePoint_mul G R }

private def fibrePointEquiv {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (R : TestAlgebra k) :
    GroupPoints C.realization.pinned.pair.G.val R ≃*
      IntegralPoints M.group (CommAlgCat.of Integers.{u} R) :=
  ((((groupPointsFunctor k).mapIso C.groupIso.symm).app R).groupIsoToMulEquiv.trans
    (forgetFibrePointEquiv M.group R))

private theorem fibrePointEquiv_apply {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (R : TestAlgebra k)
    (p : GroupPoints C.realization.pinned.pair.G.val R) :
    fibrePointEquiv C R p = forgetFibrePoint M.group R (p ≫ C.groupIso.inv.hom.hom) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedTorusInvariance {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (f : Aut C.realization.pinned) (R : TestAlgebra k)
    (t : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} R)) :
    let φ := fibrePointEquiv C R
    let ψ := (((groupPointsFunctor k).mapIso f.asIso.hom.group).app R).groupIsoToMulEquiv
    ∃ s : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} R),
      φ (ψ (φ.symm (t ≫ M.torus.hom.hom))) = s ≫ M.torus.hom.hom := by
  intro φ ψ
  let p := (forgetFibrePointEquiv (splitTorus D) R).symm t
  have ht : forgetFibrePoint (splitTorus D) R p = t :=
    (forgetFibrePointEquiv (splitTorus D) R).apply_symm_apply t
  let T := C.realization.pinned.pair.T
  have hs : C.torusIso.hom ≫ T.inclusion ≫ C.groupIso.inv = (fibre k).map M.torus := by
    rw [← Category.assoc, ← C.torus_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htor (q : GroupPoints ((fibre k).obj (splitTorus D)) R) :
      φ (q ≫ (C.torusIso.hom ≫ T.inclusion).hom.hom) =
        forgetFibrePoint (splitTorus D) R q ≫ M.torus.hom.hom := by
    change fibrePointEquiv C R (q ≫ _) = _
    rw [fibrePointEquiv_apply, Category.assoc, ← Grp.comp_hom_hom, Category.assoc, hs, forgetFibrePoint_comp]
  have hp : φ.symm (t ≫ M.torus.hom.hom) = p ≫ (C.torusIso.hom ≫ T.inclusion).hom.hom := by
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, htor, ht]
  let g := f.asIso.hom
  let p' : GroupPoints ((fibre k).obj (splitTorus D)) R :=
    p ≫ (C.torusIso.hom ≫ g.torus.hom ≫ C.torusIso.inv).hom.hom
  refine ⟨forgetFibrePoint (splitTorus D) R p', ?_⟩
  rw [hp, ← htor]
  apply congrArg φ
  change (p ≫ (C.torusIso.hom ≫ T.inclusion).hom.hom) ≫ g.group.hom.hom.hom =
    p' ≫ (C.torusIso.hom ≫ T.inclusion).hom.hom
  dsimp only [p']
  rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc, g.torus_comm,
    Category.assoc, ← Grp.comp_hom_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, T]

set_option backward.isDefEq.respectTransparency false in
private theorem rootLabel_opposite {D : BasedRootDatum.{u}} {M : Model D}
    {k : Type u} [Field k] (C : MarkedFibre M k) (a : D.I) :
    (C.realization.datumIso.val.indexEquiv (D.datum.reflectionPerm a a)).val =
      (C.realization.datumIso.val.indexEquiv a).val⁻¹ := by
  let E := C.realization.attached
  letI := E.comm
  let e := C.realization.datumIso
  change (e.val.indexEquiv (D.datum.reflectionPerm a a)).val = _
  rw [indexEquiv_reflectionPerm e]
  apply Additive.ofMul.injective
  let i : Root C.realization.pinned.pair.T := e.val.indexEquiv a
  change Additive.ofMul ((E.datum.rootDatum.reflectionPerm i i).val) =
    Additive.ofMul (i.val⁻¹)
  rw [← E.datum.root_eq, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
    E.datum.root_eq]
  rfl

private theorem enumerateRoots (D : BasedRootDatum.{u}) (S : Set D.I) :
    ∃ l : List D.I, Enumerates l S := by
  classical
  letI : Finite D.I := D.finiteRoots
  letI : Fintype D.I := Fintype.ofFinite D.I
  let t := Finset.univ.filter (fun i : D.I => i ∈ S)
  exact ⟨t.toList, Finset.nodup_toList _, fun i => by simp [t]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 950000 in
theorem pinnedLinkedSimpleCoordinates : PinnedLinkedSimpleCoordinates.{u} := by
  intro D M k _ C f a b e hab
  let P := C.realization.pinned
  let g := f.asIso.hom
  have hpos : C.rootMap a ≫ g.group.hom = C.rootMap b := by
    obtain ⟨b', ⟨hb', he'⟩, _⟩ :=
      pinnedSimpleCoordinates P f (C.realization.simpleRoot a)
    have hbb : b' = C.realization.simpleRoot b :=
      Subtype.ext (Subtype.ext (hb'.trans hab))
    subst b'
    unfold MarkedFibre.rootMap
    rw [C.simple_eq a, C.simple_eq b]
    exact he'
  let j := D.datum.reflectionPerm a a
  let l := D.datum.reflectionPerm b b
  have hlabel : transportCharacter g.torus (e j).val = (e l).val := by
    change transportCharacter g.torus
      (C.realization.datumIso.val.indexEquiv (D.datum.reflectionPerm a a)).val =
      (C.realization.datumIso.val.indexEquiv (D.datum.reflectionPerm b b)).val
    rw [rootLabel_opposite, rootLabel_opposite]
    exact (map_inv (charactersOfIso g.torus) _).trans (congrArg Inv.inv hab)
  obtain ⟨c, hc, _⟩ := rootCoordinateTransport P g.group g.torus g.torus_comm
    (e j) (e l) hlabel (C.coordinate j) (C.coordinate l)
  have hneg (R : TestAlgebra k) (r : R) :
      rootPoint (C.rootMap j ≫ g.group.hom) R r =
        rootPoint (C.rootMap l) R (algebraMap k R (c : k) * r) := hc R r
  suffices he : c = 1 by
    intro R r
    refine ⟨by rw [hpos], ?_⟩
    simpa only [he, Units.val_one, map_one, one_mul] using hneg R r
  obtain ⟨negative, hn⟩ := enumerateRoots D {i | ¬ D.base.IsPos i}
  obtain ⟨positive, hp⟩ := enumerateRoots D {i | D.base.IsPos i}
  let R := CommAlgCat.of k (DualNumber k)
  let S := CommAlgCat.of Integers.{u} R
  let φ := fibrePointEquiv C R
  let ψ := (((groupPointsFunctor k).mapIso g.group).app R).groupIsoToMulEquiv
  let τ := (φ.symm.trans ψ).trans φ
  have hm (i : D.I) (z : R) : φ (rootPoint (C.rootMap i) R z) =
      markedRootPoint M.toIntegralMarking S i z := by
    change fibrePointEquiv C R _ = _
    rw [fibrePointEquiv_apply, ← rootPoint_comp]
    exact C.root_eval i R z
  have hτ (i : D.I) (z : R) : τ (markedRootPoint M.toIntegralMarking S i z) =
      φ (rootPoint (C.rootMap i ≫ g.group.hom) R z) := by
    rw [← hm]
    change φ (ψ (φ.symm (φ (rootPoint (C.rootMap i) R z)))) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg φ (rootPoint_comp (C.rootMap i) g.group.hom R z).symm
  exact linkedLowerCoordinateUniqueness k M.toIntegralMarking negative positive hn hp a b
    (D.base.isPos_of_mem_support b.property) τ c (pinnedTorusInvariance C f R)
    (fun z => by rw [hτ, hpos, hm]) (fun z => by rw [hτ, hneg, hm])

end PinnedLinkedCoordinates

section Reflection

open AlgebraicGeometry Opposite
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.IntegralRootRelations (upper lower diagonal)
open scoped CategoryTheory.MonObj
universe u

open private affineTorusPointEquiv from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private def markedTorusPointHom {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) : TorusValues D R →* IntegralPoints M.group R :=
  (((yonedaGrp.map M.torus).app (op (integralSpec.obj (op R)))).hom).comp
    (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).toMonoidHom

private theorem markedTorusPointHom_apply {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (t : TorusValues D R) :
    markedTorusPointHom M R t = torusPoint D R t ≫ M.torus.hom.hom := rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedWallTorusReflection : MarkedWallTorusReflection.{u} := by
  intro D M R i a t g n t'
  let χ := t (Multiplicative.ofAdd (D.datum.root i))
  let q := markedTorusPointHom M R
  let h (b : Rˣ) := q (cocharacter D (D.datum.coroot i) R b)
  let w (b : Rˣ) : IntegralPoints M.group R :=
    ((M.rankOne i).app R).hom (rankOneMatrixWord b)
  let j := D.datum.reflectionPerm i i
  let x := markedRootPoint M R
  have hd (b : Rˣ) : w b = h b * w 1 := by
    let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
      ((M.rankOne i).app R).hom
    have hh : ρ (diagonal b) = h b := M.rankOneDiagonal i R b
    change ρ (rankOneMatrixWord b) = h b * ρ (rankOneMatrixWord 1)
    rw [(wallMatrixRelations b b).2.1, map_mul, hh]
  have hmul (b c : Rˣ) : h (b * c) = h b * h c := by
    dsimp only [h]
    rw [← map_mul]
    apply congrArg q
    apply MonoidHom.ext
    intro z
    change (b * c) ^ (D.datum.toLinearMap z.toAdd (D.datum.coroot i)) =
      b ^ (D.datum.toLinearMap z.toAdd (D.datum.coroot i)) *
        c ^ (D.datum.toLinearMap z.toAdd (D.datum.coroot i))
    exact mul_zpow _ _ _
  have hroot_neg : D.datum.root j = -D.datum.root i := by
    change D.datum.root (D.datum.reflectionPerm i i) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hneg : t (Multiplicative.ofAdd (D.datum.root j)) = χ⁻¹ := by
    rw [hroot_neg]
    exact map_inv t (Multiplicative.ofAdd (D.datum.root i))
  have hword (b : Rˣ) : w b =
      x i (b : R) * x j (-(↑b⁻¹ : R)) * x i (b : R) := by
    let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
      ((M.rankOne i).app R).hom
    have hu (z : R) : ρ (upper z) = x i z := M.rankOneUpper i R z
    have hl (z : R) : ρ (lower z) = x j z := M.rankOneLower i R z
    change ρ _ = _
    simp only [rankOneMatrixWord, map_mul, hu, hl]
  have hconj (b : Rˣ) : g * w b * g⁻¹ = w (χ * b) := by
    change MulAut.conj g (w b) = w (χ * b)
    simp only [hword, map_mul]
    have hplus (z : R) : MulAut.conj g (x i z) = x i ((χ : R) * z) :=
      M.conjugation R t i z
    have hminus (z : R) : MulAut.conj g (x j z) = x j ((↑χ⁻¹ : R) * z) := by
      change g * x j z * g⁻¹ = _
      rw [← hneg]
      exact M.conjugation R t j z
    rw [hplus, hminus]
    simp only [Units.val_mul, mul_inv_rev, mul_comm (↑χ⁻¹ : R), neg_mul]
  have hn : g * n * g⁻¹ = h χ * n := by
    change g * w (-a) * g⁻¹ = h χ * w (-a)
    rw [hconj, hd (χ * (-a)), hmul, hd (-a), mul_assoc]
  have hc : n * g * n⁻¹ = (h χ)⁻¹ * g := by
    have he := congrArg (fun z : IntegralPoints M.group R => (h χ)⁻¹ * z * g * n⁻¹) hn
    simpa [mul_assoc] using he.symm
  have hh : h (χ⁻¹) = (h χ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hmul, inv_mul_cancel]
    change q (cocharacter D (D.datum.coroot i) R 1) = 1
    have e : cocharacter D (D.datum.coroot i) R 1 = 1 := by
      apply MonoidHom.ext
      intro m
      simp [cocharacter]
    rw [e, map_one]
  refine ⟨?_, ?_⟩
  · rw [hc, ← hh]
    change h (χ⁻¹) * q t = q t'
    exact (map_mul q _ _).symm
  · intro z
    rw [RootPairing.reflection_apply]
    change (χ⁻¹ ^ D.datum.coroot' i z) * t (Multiplicative.ofAdd z) =
      t (Multiplicative.ofAdd (z - D.datum.coroot' i z • D.datum.root i))
    rw [sub_eq_add_neg]
    change _ = t (Multiplicative.ofAdd z * Multiplicative.ofAdd (-(D.datum.coroot' i z • D.datum.root i)))
    rw [map_mul]
    have e (m : ℤ) : Multiplicative.ofAdd (-(m • D.datum.root i)) =
        ((Multiplicative.ofAdd (D.datum.root i))⁻¹) ^ m := by
      simp
    rw [e, map_zpow, map_inv, mul_comm]

end Reflection

section PinnedPointCriterion

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfMap)
open Specs.AutomorphismSequence (forgetPinning)
universe u

theorem pinnedPointCriterion : PinnedPointCriterion.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d R _ _ q p
  let C := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let ρ := SemilinearAction.scalarExtension (k := k) (K := K) R
  let f (σ : Gal(K/k)) := coordinateHopfMap (G := P.pair.G) (H := P.pair.G)
    ((Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv)
  have hp (σ : Gal(K/k)) (a : K) (x : C) :
      p (pinnedOperator d σ (a ⊗ₜ[k] x)) = σ a • q ((f σ).hom x) := by
    change p ((extendedHopfMap K (f σ)).hom (σ a ⊗ₜ[k] x)) = _
    change p (σ a ⊗ₜ[k] (f σ).hom x) = _
    exact AlgHom.liftEquiv_tmul _ _ _
  rw [(pinnedAlgebraFixedPoints d R).2]
  constructor
  · intro h σ x
    have he := h σ (1 ⊗ₜ[k] x)
    rw [hp, map_one, one_smul] at he
    change q ((f σ).hom x) = ρ.act σ (p (1 ⊗ₜ[k] x)) at he
    change q ((f σ).hom x) = ρ.act σ (q x)
    simpa [p] using he
  · intro h σ z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      change p (pinnedOperator d σ (a ⊗ₜ[k] x)) = ρ.act σ (p (a ⊗ₜ[k] x))
      rw [hp, show p (a ⊗ₜ[k] x) = a • q x from AlgHom.liftEquiv_tmul _ _ _,
        ρ.map_smul, ← h σ x]
    | add x y ihx ihy =>
      change p ((extendedHopfMap K (f σ)).hom
        ((SemilinearAction.scalarExtension (K := K) C).act σ (x + y))) =
        ρ.act σ (p (x + y))
      simp only [map_add]
      exact congrArg₂ (· + ·) ihx ihy

end PinnedPointCriterion

section LocalSL

open Matrix (SpecialLinearGroup)
open scoped Matrix
open Specs.IntegralRootRelations (upper lower diagonal)
universe u

private theorem rankOneMatrixWord_neg_one_mul_one {R : Type u} [CommRing R] :
    rankOneMatrixWord (-1 : Rˣ) * rankOneMatrixWord 1 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, rankOneMatrixWord_val, rankOneMatrixWord_val,
    SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem localSL2Gauss {R : Type u} [CommRing R]
    (A : SpecialLinearGroup (Fin 2) R) (a : Rˣ) (ha : A.val 0 0 = (a : R)) :
    A = lower (A.val 1 0 * (↑a⁻¹ : R)) * diagonal a *
      upper ((↑a⁻¹ : R) * A.val 0 1) := by
  have hdet : (a : R) * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    have h := A.property
    rwa [Matrix.det_fin_two, ha] at h
  have hi : (↑a⁻¹ : R) * (a : R) = 1 := a.inv_mul
  have hi' : (a : R) * (↑a⁻¹ : R) = 1 := a.mul_inv
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  change A.val = (!![1, 0; A.val 1 0 * (↑a⁻¹ : R), 1] : Matrix (Fin 2) (Fin 2) R) *
    !![(a : R), 0; 0, (↑a⁻¹ : R)] * !![1, (↑a⁻¹ : R) * A.val 0 1; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, ← mul_assoc, hi']
  linear_combination (↑a⁻¹ : R) * hdet - A.val 1 1 * hi

theorem localSL2Generation : LocalSL2Generation.{u} := by
  intro R _ _ P hu hl hmul A
  have hw (a : Rˣ) : P (rankOneMatrixWord a) :=
    hmul _ _ (hmul _ _ (hu a) (hl _)) (hu a)
  have hd (a : Rˣ) : P (diagonal a) := by
    have hr : rankOneMatrixWord a * rankOneMatrixWord (-1) = diagonal a := by
      rw [(wallMatrixRelations a a).2.1, mul_assoc]
      have h : rankOneMatrixWord 1 * rankOneMatrixWord (-1 : Rˣ) = 1 :=
        mul_eq_one_symm rankOneMatrixWord_neg_one_mul_one
      rw [h, mul_one]
    exact hr ▸ hmul _ _ (hw a) (hw (-1))
  have hPivot (B : SpecialLinearGroup (Fin 2) R) (hb : IsUnit (B.val 0 0)) : P B := by
    obtain ⟨b, hb⟩ := hb
    rw [localSL2Gauss B b hb.symm]
    exact hmul _ _ (hmul _ _ (hl _) (hd b)) (hu _)
  by_cases h : IsUnit (A.val 0 0)
  · exact hPivot A h
  · have h' : IsUnit (A.val 1 0) := by
      obtain ⟨b, c, hbc⟩ := SpecialLinearGroup.isCoprime_col A 0
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one hbc with hab | hac
      · exact (h (isUnit_of_mul_isUnit_right hab)).elim
      · exact isUnit_of_mul_isUnit_right hac
    let B := rankOneMatrixWord (1 : Rˣ) * A
    have hb : B.val 0 0 = A.val 1 0 := by
      change ((rankOneMatrixWord (1 : Rˣ) * A : SpecialLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) 0 0 = _
      rw [SpecialLinearGroup.coe_mul, rankOneMatrixWord_val]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hA : rankOneMatrixWord (-1 : Rˣ) * B = A := by
      dsimp only [B]
      rw [← mul_assoc, rankOneMatrixWord_neg_one_mul_one, one_mul]
    exact hA ▸ hmul _ _ (hw (-1)) (hPivot B (hb.symm ▸ h'))

end LocalSL

section CommutingRankOne

open AlgebraicGeometry Opposite
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.IntegralRootRelations (upper lower)
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj
universe u

private abbrev localIntegralAlgebra (R : IntegralAlgebra.{u}) (P : Ideal R) [P.IsPrime] :
    IntegralAlgebra.{u} :=
  letI : Algebra Integers.{u} (Localization.AtPrime P) := integerAlgebra _
  CommAlgCat.of Integers.{u} (Localization.AtPrime P)

private def localIntegralMap (R : IntegralAlgebra.{u}) (P : Ideal R) [P.IsMaximal] :
    R ⟶ localIntegralAlgebra R P := by
  letI : Algebra Integers.{u} (Localization.AtPrime P) := (localIntegralAlgebra R P).algebra
  exact CommAlgCat.ofHom
    { toRingHom := algebraMap R (Localization.AtPrime P)
      commutes' := fun n => by
        have h : ((n.down : ℤ) : Integers.{u}) = n := rfl
        change algebraMap R (Localization.AtPrime P) (algebraMap Integers R n) =
          algebraMap Integers (Localization.AtPrime P) n
        rw [← h]
        simp only [map_intCast] }

set_option backward.isDefEq.respectTransparency false in
private theorem integralPoints_ext_atMaximal {X : IntegralScheme.{u}} (hX : IsAffine X.left)
    {R : IntegralAlgebra.{u}} {p q : integralSpec.obj (op R) ⟶ X}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      integralSpec.map (localIntegralMap R P).op ≫ p =
        integralSpec.map (localIntegralMap R P).op ≫ q) : p = q := by
  let e := X.left.isoSpec
  apply Over.OverMorphism.ext
  apply (cancel_mono e.hom).mp
  apply Spec.preimage_injective
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P))
  intro P mP
  letI := mP
  let j := CommRingCat.ofHom (algebraMap R (Localization.AtPrime P))
  have he : Spec.map j ≫ (p.left ≫ e.hom) = Spec.map j ≫ (q.left ≫ e.hom) := by
    have he' := congrArg (fun f => f.left ≫ e.hom) (h P)
    change (Spec.map j ≫ p.left) ≫ e.hom = (Spec.map j ≫ q.left) ≫ e.hom at he'
    simpa only [Category.assoc] using he'
  have hh := congrArg Spec.preimage he
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at hh
  exact ConcreteCategory.congr_hom hh x

private theorem commute_of_localSL2 {R : Type u} [CommRing R] [IsLocalRing R]
    {G : Type u} [Group G] (f g : SpecialLinearGroup (Fin 2) R →* G)
    (h : ∀ A ∈ (Set.range (upper (R := R)) ∪ Set.range (lower (R := R))),
      ∀ B ∈ (Set.range (upper (R := R)) ∪ Set.range (lower (R := R))), Commute (f A) (g B))
    (A B : SpecialLinearGroup (Fin 2) R) : Commute (f A) (g B) := by
  have ho (A) (hA : A ∈ (Set.range (upper (R := R)) ∪ Set.range (lower (R := R)))) (B) :
      Commute (f A) (g B) := by
    apply localSL2Generation (fun X => Commute (f A) (g X)) _ _ _ B
    · exact fun t => h A hA _ (Or.inl ⟨t, rfl⟩)
    · exact fun t => h A hA _ (Or.inr ⟨t, rfl⟩)
    · intro a b ha hb
      rw [map_mul]
      exact ha.mul_right hb
  apply localSL2Generation (fun X => Commute (f X) (g B)) _ _ _ A
  · exact fun t => ho _ (Or.inl ⟨t, rfl⟩) B
  · exact fun t => ho _ (Or.inr ⟨t, rfl⟩) B
  · intro a b ha hb
    rw [map_mul]
    exact ha.mul_left hb

set_option backward.isDefEq.respectTransparency false in
theorem markedOrthogonalRankOneCommutation : MarkedOrthogonalRankOneCommutation.{u} := by
  intro D M hs a b hab k _ R S A B
  change ((M.rankOne a).app S A : IntegralPoints M.group S) * (M.rankOne b).app S B =
    (M.rankOne b).app S B * (M.rankOne a).app S A
  apply integralPoints_ext_atMaximal M.affine
  intro P mP
  letI := mP
  let L := Localization.AtPrime P
  letI : Algebra k L := ((algebraMap S L).comp (algebraMap k R)).toAlgebra
  let Q := CommAlgCat.of k L
  let T := localIntegralAlgebra S P
  let f : S ⟶ T := localIntegralMap S P
  let j := ((integralPointFunctor M.group).map f).hom
  let m := SpecialLinearGroup.map (n := Fin 2) (algebraMap S L)
  have hn (i : D.I) (X : SpecialLinearGroup (Fin 2) S) :
      j ((M.rankOne i).app S X) = (M.rankOne i).app T (m X) := by
    exact (ConcreteCategory.congr_hom ((M.rankOne i).naturality f) X).symm
  change j ((M.rankOne a).app S A * (M.rankOne b).app S B) =
    j ((M.rankOne b).app S B * (M.rankOne a).app S A)
  have hh := @commute_of_localSL2 L _ inferInstance
    (IntegralPoints M.group T) _ ((M.rankOne a).app T).hom ((M.rankOne b).app T).hom
    (markedOrthogonalRootCommutation M hs a b hab k Q) (m A) (m B)
  simp only [map_mul, hn]
  exact hh.eq

end CommutingRankOne

section PairedRankOneProduct

open scoped CategoryTheory.MonObj
open Specs.IntegralSemisimpleModel Specs.Pinning
open Matrix (SpecialLinearGroup)
universe u

private theorem quadraticCoefficientEquiv_natural {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k))
    {R S : TestAlgebra k} (f : R ⟶ S) (z : K ⊗[k] R) :
    ((quadraticIntegralAlgebra k K).map f).hom (quadraticCoefficientEquiv σ R z) =
      quadraticCoefficientEquiv σ S (((quadraticIntegralAlgebra k K).map f).hom z) := by
  change Algebra.TensorProduct.map (AlgHom.id k K) f.hom
      (quadraticCoefficientEquiv σ R z) =
    quadraticCoefficientEquiv σ S (Algebra.TensorProduct.map (AlgHom.id k K) f.hom z)
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
theorem markedPairedRankOneProduct : MarkedPairedRankOneProduct.{u} := by
  intro D M hs a b hab k K _ _ _ σ E
  let α (R : TestAlgebra k) := ((M.rankOne a).app (E.obj R)).hom
  let coeffSL (R : TestAlgebra k) :
      SpecialLinearGroup (Fin 2) (K ⊗[k] R) →* SpecialLinearGroup (Fin 2) (K ⊗[k] R) :=
    SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom
  let β (R : TestAlgebra k) := ((M.rankOne b).app (E.obj R)).hom.comp (coeffSL R)
  have hc (R : TestAlgebra k) (A B : SpecialLinearGroup (Fin 2) (K ⊗[k] R)) :
      Commute (α R A) (β R B) :=
    markedOrthogonalRankOneCommutation M hs a b hab K
      (CommAlgCat.of K (K ⊗[k] R)) A (coeffSL R B)
  let ρ (R : TestAlgebra k) : SpecialLinearGroup (Fin 2) (K ⊗[k] R) →*
      IntegralPoints M.group (E.obj R) :=
    MonoidHom.mk' (fun A => α R A * β R A) (fun A B => by
      rw [map_mul, map_mul]
      exact ((hc R B A).symm.mul_mul_mul_comm _ _).symm)
  refine ⟨{ app := fun R => GrpCat.ofHom (ρ R), naturality := ?_ }, fun R A => rfl⟩
  intro R S f
  apply GrpCat.ext
  intro A
  let g := (E.map f)
  let j := ((integralPointFunctor M.group).map g).hom
  let m := SpecialLinearGroup.map (n := Fin 2) g.hom.toRingHom
  have hn (i : D.I) (X : SpecialLinearGroup (Fin 2) (K ⊗[k] R)) :
      j ((M.rankOne i).app (E.obj R) X) = (M.rankOne i).app (E.obj S) (m X) :=
    (ConcreteCategory.congr_hom ((M.rankOne i).naturality g) X).symm
  have hm (X : SpecialLinearGroup (Fin 2) (K ⊗[k] R)) : m (coeffSL R X) = coeffSL S (m X) := by
    apply Subtype.ext
    ext i j
    exact quadraticCoefficientEquiv_natural σ f (X.val i j)
  change α S (m A) * β S (m A) = j (α R A * β R A)
  rw [map_mul]
  change _ = j ((M.rankOne a).app (E.obj R) A) * j ((M.rankOne b).app (E.obj R) (coeffSL R A))
  rw [hn, hn, hm]
  rfl

end PairedRankOneProduct

section PinnedSchemePoints

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry
open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AutomorphismSequence (forgetPinning)
open Specs.Pinning (AttachedDatum PinnedGroup)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open scoped CategoryTheory.MonObj

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem coordinatePointEquiv_natural (G : AffineAlgebraicGroup k)
    {R S : TestAlgebra k} (f : R ⟶ S) (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R) :
    coordinatePointEquiv G S (WithConv.toConv (f.hom.comp p.ofConv)) =
      mapPoints f (coordinatePointEquiv G R p) := by
  apply Over.OverMorphism.ext
  let g := (coordinateHopfIso G).hom.hom.hom.left
  change Spec.map (CommRingCat.ofHom (f.hom.comp p.ofConv).toRingHom) ≫ g =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫ g
  rw [← Category.assoc]
  exact congrArg (· ≫ g)
    (Spec.map_comp (CommRingCat.ofHom p.ofConv.toRingHom) (CommRingCat.ofHom f.hom.toRingHom))

private theorem coordinatePresentation {G H : AffineAlgebraicGroup k} (f : G.val ⟶ H.val) :
    specGroupMap (coordinateHopfMap (G := G) (H := H) f) =
      (coordinateHopfIso G).hom ≫ f ≫ (coordinateHopfIso H).inv :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _

private theorem coordinatePointEquiv_comp {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (R : TestAlgebra k) (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R) :
    coordinatePointEquiv H R (WithConv.toConv
      (p.ofConv.comp (coordinateHopfMap (G := G) (H := H) f).hom.toAlgHom)) =
      coordinatePointEquiv G R p ≫ f.hom.hom := by
  let h := coordinateHopfMap (G := G) (H := H) f
  have hspec : specGroupMap h = (coordinateHopfIso G).hom ≫ f ≫ (coordinateHopfIso H).inv :=
    coordinatePresentation f
  have he : (specGroupMap h).hom.hom ≫ (coordinateHopfIso H).hom.hom.hom =
      (coordinateHopfIso G).hom.hom.hom ≫ f.hom.hom := by
    change (Grp.forget _).map (specGroupMap h) ≫ (Grp.forget _).map (coordinateHopfIso H).hom =
      (Grp.forget _).map (coordinateHopfIso G).hom ≫ (Grp.forget _).map f
    rw [← Functor.map_comp, ← Functor.map_comp, hspec]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let p' : GroupPoints (specGroup (Specs.AdjointCocharacters.coordinateHopf H)) R :=
    Spec.mapMulEquiv (WithConv.toConv (p.ofConv.comp h.hom.toAlgHom))
  have hp : p' = Spec.mapMulEquiv p ≫ (specGroupMap h).hom.hom := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp (CommRingCat.ofHom h.hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom p.ofConv.toRingHom)
  change p' ≫ (coordinateHopfIso H).hom.hom.hom =
    (Spec.mapMulEquiv p ≫ (coordinateHopfIso G).hom.hom.hom) ≫ f.hom.hom
  rw [hp, Category.assoc, he, Category.assoc]

private theorem quadraticCoefficientEquiv_apply (σ : Gal(K/k)) (R : TestAlgebra k)
    (z : K ⊗[k] R) :
    quadraticCoefficientEquiv σ R z =
      (SemilinearAction.scalarExtension (K := K) R).act σ z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def liftHopfPoint (H : HopfAlgebraCategory k) (S : Type u)
    [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S] :
    HopfPoints H S ≃* HopfPoints (extendedHopf K H) S := by
  let f := extendHopfPoint (K := K) (H := H) (AlgHom.id k S)
  have hf (p : HopfPoints H S) :
      f p = WithConv.toConv (AlgHom.liftEquiv k K H S p.ofConv) := rfl
  apply MulEquiv.ofBijective f
  constructor
  · intro p q h
    rw [hf, hf] at h
    exact WithConv.ofConv_injective ((AlgHom.liftEquiv k K H S).injective
      (congrArg WithConv.ofConv h))
  · intro p
    refine ⟨WithConv.toConv ((AlgHom.liftEquiv k K H S).symm p.ofConv), ?_⟩
    rw [hf]
    exact congrArg WithConv.toConv ((AlgHom.liftEquiv k K H S).apply_symm_apply p.ofConv)

private theorem liftHopfPoint_symm_apply (H : HopfAlgebraCategory k) (S : Type u)
    [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    (p : HopfPoints (extendedHopf K H) S) :
    (liftHopfPoint (K := K) H S).symm p =
      WithConv.toConv ((AlgHom.liftEquiv k K H S).symm p.ofConv) := by
  apply (liftHopfPoint (K := K) H S).injective
  rw [MulEquiv.apply_symm_apply]
  change p = WithConv.toConv
    (AlgHom.liftEquiv k K H S ((AlgHom.liftEquiv k K H S).symm p.ofConv))
  rw [Equiv.apply_symm_apply]
  rfl

variable {A : Specs.RootGroups.AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
  {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}

private def pinnedSchemePointHom (d : PinnedTwist (P := P) K D l B T) (R : TestAlgebra k) :
    HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R →*
      GroupPoints P.pair.G.val ((extendedTestAlgebra k K).obj R) :=
  let H := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let S := K ⊗[k] R
  (coordinatePointEquiv P.pair.G ((extendedTestAlgebra k K).obj R)).toMonoidHom.comp
    ((liftHopfPoint (K := K) H S).symm.toMonoidHom.comp
      ((compHopfPoint (R := S) d.groupIso.hom).comp
        (extendHopfPoint (K := K) (H := Specs.AdjointCocharacters.coordinateHopf G)
          (Algebra.TensorProduct.includeRight : R →ₐ[k] S))))

set_option maxHeartbeats 500000 in
private theorem pinnedSchemePointHom_apply (d : PinnedTwist (P := P) K D l B T)
    (R : TestAlgebra k) (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R) :
    pinnedSchemePointHom d R p = pinnedSchemePoint d R p := by
  change coordinatePointEquiv P.pair.G ((extendedTestAlgebra k K).obj R)
    ((liftHopfPoint (K := K) (Specs.AdjointCocharacters.coordinateHopf P.pair.G)
      (K ⊗[k] R)).symm (WithConv.toConv (pinnedAlgebraPointMap d p.ofConv))) = _
  rw [liftHopfPoint_symm_apply]
  rfl

private theorem pinnedSchemePoint_natural (d : PinnedTwist (P := P) K D l B T)
    {R S : TestAlgebra k} (f : R ⟶ S) (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R) :
    pinnedSchemePoint d S (WithConv.toConv (f.hom.comp p.ofConv)) =
      mapPoints ((extendedTestAlgebra k K).map f) (pinnedSchemePoint d R p) := by
  unfold pinnedSchemePoint
  rw [← coordinatePointEquiv_natural]
  apply congrArg (coordinatePointEquiv _ _)
  apply congrArg WithConv.toConv
  ext x
  simp only [AlgHom.liftEquiv_symm_apply]
  change extendAlgebraPoint (K := K) (f.hom.comp p.ofConv) (d.groupIso.hom.hom (1 ⊗ₜ[k] x)) =
    ((extendedTestAlgebra k K).map f).hom
      (extendAlgebraPoint (K := K) p.ofConv (d.groupIso.hom.hom (1 ⊗ₜ[k] x)))
  generalize d.groupIso.hom.hom (1 ⊗ₜ[k] x) = z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [extendAlgebraPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply]
    change a • ((1 : K) ⊗ₜ[k] f.hom (p.ofConv b)) =
      Algebra.TensorProduct.map (AlgHom.id k K) f.hom (a • ((1 : K) ⊗ₜ[k] p.ofConv b))
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy =>
    change extendAlgebraPoint (K := K) (f.hom.comp p.ofConv) (x + y) =
      (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)
        (extendAlgebraPoint (K := K) p.ofConv (x + y))
    have hx' := hx
    have hy' := hy
    change _ = (Algebra.TensorProduct.map (AlgHom.id k K) f.hom) _ at hx' hy'
    simp only [map_add, hx', hy']

private theorem pinnedSchemePoint_fixed_iff [FiniteDimensional k K] [IsGalois k K]
    (d : PinnedTwist (P := P) K D l B T) (R : TestAlgebra k)
    (p : GroupPoints P.pair.G.val ((extendedTestAlgebra k K).obj R)) :
    p ∈ Set.range (pinnedSchemePoint d R) ↔ ∀ σ, pinnedSchemeAction d σ R p = p := by
  let e := coordinatePointEquiv P.pair.G ((extendedTestAlgebra k K).obj R)
  obtain ⟨q, rfl⟩ := e.surjective p
  have hr : e q ∈ Set.range (pinnedSchemePoint d R) ↔
      AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf P.pair.G) (K ⊗[k] R) q.ofConv ∈
        Set.range (pinnedAlgebraPointMap d (R := R)) := by
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p.ofConv, ?_⟩
      have h := congrArg WithConv.ofConv (e.injective hp)
      exact ((AlgHom.liftEquiv k K _ _).symm_apply_eq.mp h)
    · rintro ⟨p, hp⟩
      refine ⟨WithConv.toConv p, ?_⟩
      unfold pinnedSchemePoint
      rw [show (WithConv.toConv p).ofConv = p from rfl, hp, Equiv.symm_apply_apply]
      rfl
  rw [hr]
  have hh := pinnedPointCriterion d (R : Type u) q.ofConv
  dsimp only at hh
  rw [hh]
  apply forall_congr'
  intro σ
  let g := (pinnedDiagram d σ).asIso.hom.group
  let f := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
  have hf : f = g.inv := by
    let J := (forgetPinning (A := A)).mapIso (pinnedDiagram d σ).asIso
    have hJ : J.hom = g.hom := rfl
    apply (cancel_mono g.hom).mp
    rw [g.inv_hom_id, ← hJ]
    exact J.inv_hom_id
  have he : pinnedSchemeAction d σ R (e q) = e q ↔
      mapPoints (conjugateTestAlgebra σ R) (e q) = e q ≫ f.hom.hom := by
    rw [hf]
    change (mapPoints (conjugateTestAlgebra σ R) (e q) ≫ g.hom.hom.hom = e q) ↔ _
    let iso := (Grp.forget (SchemeOver k)).mapIso g
    exact iso.eq_comp_inv.symm
  change (∀ x : Specs.AdjointCocharacters.coordinateHopf P.pair.G,
    q.ofConv ((coordinateHopfMap (G := P.pair.G) (H := P.pair.G) f).hom x) =
      (SemilinearAction.scalarExtension (K := K) R).act σ (q.ofConv x)) ↔ _
  rw [he]
  dsimp only [e]
  rw [← coordinatePointEquiv_natural, ← coordinatePointEquiv_comp]
  constructor
  · intro h
    apply congrArg (coordinatePointEquiv P.pair.G _)
    apply congrArg WithConv.toConv
    ext x
    exact (quadraticCoefficientEquiv_apply σ R (q.ofConv x)).trans (h x).symm
  · intro h x
    have hx := DFunLike.congr_fun (congrArg WithConv.ofConv (e.injective h)) x
    exact hx.symm.trans (quadraticCoefficientEquiv_apply σ R _)

set_option backward.isDefEq.respectTransparency false in
theorem pinnedSchemePointEmbedding : PinnedSchemePointEmbedding.{u} := by
  intro k K _ _ _ _ _ A P D l G B T d
  let j : convolutionPoints (Specs.AdjointCocharacters.coordinateHopf G) ⟶
      extendedTestAlgebra k K ⋙ (groupPointsFunctor k).obj P.pair.G.val :=
    { app := fun R =>
        letI := convolutionGroup (Specs.AdjointCocharacters.coordinateHopf G) R
        GrpCat.ofHom (pinnedSchemePointHom d R)
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro p
        change pinnedSchemePointHom d S (WithConv.toConv (f.hom.comp p.ofConv)) =
          mapPoints ((extendedTestAlgebra k K).map f) (pinnedSchemePointHom d R p)
        rw [pinnedSchemePointHom_apply, pinnedSchemePointHom_apply]
        exact pinnedSchemePoint_natural d f p }
  have hj (R : TestAlgebra k) (p) : j.app R p = pinnedSchemePoint d R p :=
    pinnedSchemePointHom_apply d R p
  refine ⟨j, hj, fun R => ⟨?_, ?_⟩⟩
  · intro p q hpq
    apply WithConv.ofConv_injective
    apply (pinnedAlgebraFixedPoints d R).1
    rw [hj, hj] at hpq
    exact (AlgHom.liftEquiv k K _ _).symm.injective (congrArg WithConv.ofConv
      ((coordinatePointEquiv P.pair.G ((extendedTestAlgebra k K).obj R)).injective hpq))
  · intro p
    rw [show (j.app R : _ → _) = pinnedSchemePoint d R from funext (hj R)]
    exact pinnedSchemePoint_fixed_iff d R p

end PinnedSchemePoints

section MarkedFibrePoints

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry Opposite
open Specs.IntegralSemisimpleModel Specs.Pinning Specs.RootGroups
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralRootRelations (upper lower)
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

open private fibrePointIso from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

theorem markedFibrePointComparison : MarkedFibrePointComparison.{u} := by
  intro D M k _ C
  let e := (groupPointsFunctor k).mapIso C.groupIso.symm ≪≫ fibrePointIso M.group
  exact ⟨e, fun R p => rfl⟩

private theorem markedFibrePoint_root {D : BasedRootDatum.{u}} {M : Model D}
    {k : Type u} [Field k] (C : MarkedFibre M k) (R : TestAlgebra k)
    (i : D.I) (z : R) :
    markedFibrePoint C R (rootPoint (C.rootMap i) R z) =
      markedRootPoint M.toIntegralMarking ((integralTestAlgebra k).obj R) i z := by
  unfold markedFibrePoint
  rw [← rootPoint_comp]
  exact C.root_eval i R z

private theorem naturalRankOne_ext {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    (M : IntegralMarking D)
    (f g : integralTestAlgebra k ⋙ rankOnePoints.{u} ⟶
      integralTestAlgebra k ⋙ integralPointFunctor M.group)
    (hu : ∀ (R : TestAlgebra k) (z : R), f.app R (upper z) = g.app R (upper z))
    (hl : ∀ (R : TestAlgebra k) (z : R), f.app R (lower z) = g.app R (lower z)) : f = g := by
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro A
  let S := (integralTestAlgebra k).obj R
  change (f.app R A : IntegralPoints M.group S) = g.app R A
  apply integralPoints_ext_atMaximal M.affine
  intro P hP
  letI := hP
  let L := Localization.AtPrime P
  letI : Algebra k L := ((algebraMap S L).comp (algebraMap k R)).toAlgebra
  let Q := CommAlgCat.of k L
  let t : R ⟶ Q := CommAlgCat.ofHom
    { toRingHom := algebraMap S L
      commutes' _ := rfl }
  let j := ((integralPointFunctor M.group).map (localIntegralMap S P)).hom
  let m := SpecialLinearGroup.map (n := Fin 2) (algebraMap S L)
  change j (f.app R A) = j (g.app R A)
  have hn (h : integralTestAlgebra k ⋙ rankOnePoints.{u} ⟶
      integralTestAlgebra k ⋙ integralPointFunctor M.group) :
      j (h.app R A) = h.app Q (m A) :=
    (ConcreteCategory.congr_hom (h.naturality t) A).symm
  rw [hn f, hn g]
  apply localSL2Generation (fun X => f.app Q X = g.app Q X) (hu Q) (hl Q)
  intro X Y hX hY
  simp only [map_mul, hX, hY]

theorem pinnedSimpleRankOneEquivariance : PinnedSimpleRankOneEquivariance.{u} := by
  intro D M k _ C f a b _ hab
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  let F := integralTestAlgebra k
  let t := e.inv ≫ (groupPointsFunctor k).map f.asIso.hom.group.hom ≫ e.hom
  have ht (R : TestAlgebra k) (p : GroupPoints C.realization.pinned.pair.G.val R) :
      t.app R (markedFibrePoint C R p) =
        markedFibrePoint C R (p ≫ f.asIso.hom.group.hom.hom.hom) := by
    rw [← he, ← he]
    change e.hom.app R ((e.inv.app R (e.hom.app R p) :
        GroupPoints C.realization.pinned.pair.G.val R) ≫ f.asIso.hom.group.hom.hom.hom) = _
    rw [show e.inv.app R (e.hom.app R p) = p from
      ConcreteCategory.congr_hom (e.app R).hom_inv_id p]
  have h (i j : D.I)
      (R : TestAlgebra k) (z : R)
      (hroot : rootPoint (C.rootMap i ≫ f.asIso.hom.group.hom) R z =
        rootPoint (C.rootMap j) R z) :
      t.app R (markedRootPoint M.toIntegralMarking (F.obj R) i z) =
        markedRootPoint M.toIntegralMarking (F.obj R) j z := by
    rw [← markedFibrePoint_root C R i z, ht, ← rootPoint_comp, hroot, markedFibrePoint_root]
  have hfg : Functor.whiskerLeft F (M.rankOne a) ≫ t = Functor.whiskerLeft F (M.rankOne b) := by
    apply naturalRankOne_ext M.toIntegralMarking
    · intro R z
      change t.app R ((M.rankOne a).app (F.obj R) (upper z)) = (M.rankOne b).app (F.obj R) (upper z)
      rw [M.rankOneUpper, M.rankOneUpper]
      exact h a b R z (pinnedLinkedSimpleCoordinates C f a b hab R z).1
    · intro R z
      change t.app R ((M.rankOne a).app (F.obj R) (lower z)) = (M.rankOne b).app (F.obj R) (lower z)
      rw [M.rankOneLower, M.rankOneLower]
      exact h _ _ R z (pinnedLinkedSimpleCoordinates C f a b hab R z).2
  intro R A p hp
  rw [← ht, hp]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hfg R) A

end MarkedFibrePoints

section RelativeRankOne

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel Specs.Pinning
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] integerAlgebra

private def liftPointMorphism {C : Type*} [Category C]
    {F H J : C ⥤ GrpCat.{u}} (i : H ⟶ J) (j : F ⟶ J)
    (hi : ∀ R, Function.Injective (i.app R))
    (hj : ∀ R x, j.app R x ∈ Set.range (i.app R)) :
    {h : F ⟶ H // h ≫ i = j} := by
  let f (R : C) (x : F.obj R) : H.obj R := Classical.choose (hj R x)
  have hf (R : C) (x : F.obj R) : i.app R (f R x) = j.app R x :=
    Classical.choose_spec (hj R x)
  let map (R : C) : F.obj R →* H.obj R :=
    MonoidHom.mk' (f R) (fun x y => hi R (by
      change (i.app R).hom (f R (x * y)) = (i.app R).hom (f R x * f R y)
      rw [hf R (x * y), (i.app R).hom.map_mul, hf R x, hf R y]
      exact (j.app R).hom.map_mul x y))
  refine ⟨{ app := fun R => GrpCat.ofHom (map R), naturality := ?_ }, ?_⟩
  · intro R S a
    apply GrpCat.ext
    intro x
    apply hi S
    change i.app S (f S (F.map a x)) = i.app S (H.map a (f R x))
    have h := ConcreteCategory.congr_hom (i.naturality a) (f R x)
    change i.app S (H.map a (f R x)) = J.map a (i.app R (f R x)) at h
    rw [hf, h, hf]
    exact ConcreteCategory.congr_hom (j.naturality a) x
  · apply NatTrans.ext
    funext R
    apply GrpCat.ext
    exact hf R

theorem pinnedMarkedPointEmbedding : PinnedMarkedPointEmbedding.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d
  obtain ⟨i, hi, hf⟩ := pinnedSchemePointEmbedding d
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  let j : convolutionPoints (Specs.AdjointCocharacters.coordinateHopf G) ⟶
      quadraticIntegralAlgebra k K ⋙ integralPointFunctor M.group :=
    i ≫ Functor.whiskerLeft (extendedTestAlgebra k K) e.hom
  have hj (R : TestAlgebra k) (p) : j.app R p = pinnedMarkedPoint C d R p := by
    change e.hom.app ((extendedTestAlgebra k K).obj R) (i.app R p) = _
    rw [he, hi]
    rfl
  refine ⟨j, hj, fun R => ⟨?_, ?_⟩⟩
  · exact ((e.app ((extendedTestAlgebra k K).obj R)).groupIsoToMulEquiv.injective).comp (hf R).1
  · intro p
    rw [← (hf R).2 p]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, (e.app ((extendedTestAlgebra k K).obj R)).groupIsoToMulEquiv.injective ?_⟩
      change j.app R q = e.hom.app ((extendedTestAlgebra k K).obj R) p
      exact hq.trans (he _ _).symm
    · rintro ⟨q, rfl⟩
      exact ⟨q, he _ _⟩

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

private theorem pinnedSchemeAction_one (R : TestAlgebra k)
    (p : GroupPoints C.realization.pinned.pair.G.val ((extendedTestAlgebra k K).obj R)) :
    pinnedSchemeAction d 1 R p = p := by
  have ha : pinnedDiagram d 1 = 1 := by simp [pinnedDiagram]
  have hc : conjugateTestAlgebra (1 : Gal(K/k)) R = 𝟙 _ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change quadraticCoefficientEquiv (1 : Gal(K/k)) R z = z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  unfold pinnedSchemeAction
  rw [ha, hc]
  change (testSpec k).map (𝟙 (Opposite.op ((extendedTestAlgebra k K).obj R))) ≫ p ≫
    (𝟙 C.realization.pinned.pair.G.val.X) = p
  simp

private theorem pinnedSchemeAction_mul (σ : Gal(K/k)) (R : TestAlgebra k)
    (p q : GroupPoints C.realization.pinned.pair.G.val ((extendedTestAlgebra k K).obj R)) :
    pinnedSchemeAction d σ R (p * q) =
      pinnedSchemeAction d σ R p * pinnedSchemeAction d σ R q := by
  let S := (extendedTestAlgebra k K).obj R
  let P := C.realization.pinned.pair.G.val
  let coeff := (((groupPointsFunctor k).obj P).map (conjugateTestAlgebra σ R)).hom
  let diag := (((groupPointsFunctor k).map (pinnedDiagram d σ).asIso.hom.group.hom).app S).hom
  change diag (coeff (p * q)) = diag (coeff p) * diag (coeff q)
  rw [map_mul, map_mul]

private theorem markedSchemeActionRankOne (σ : Gal(K/k)) (a b : D.base.support)
    (hab : transportCharacter (pinnedDiagram d σ).asIso.hom.torus
      (C.realization.datumIso.val.indexEquiv a).val = (C.realization.datumIso.val.indexEquiv b).val)
    (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) (K ⊗[k] R))
    (p : GroupPoints C.realization.pinned.pair.G.val ((extendedTestAlgebra k K).obj R))
    (hp : markedFibrePoint C ((extendedTestAlgebra k K).obj R) p =
      (M.rankOne a).app ((quadraticIntegralAlgebra k K).obj R) A) :
    markedFibrePoint C ((extendedTestAlgebra k K).obj R) (pinnedSchemeAction d σ R p) =
      (M.rankOne b).app ((quadraticIntegralAlgebra k K).obj R)
        (SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A) := by
  let S := (extendedTestAlgebra k K).obj R
  let f := conjugateTestAlgebra σ R
  let j := (integralTestAlgebra k).map f
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  have hn : markedFibrePoint C S (mapPoints f p) =
      (integralPointFunctor M.group).map j (markedFibrePoint C S p) := by
    rw [← he, ← he]
    exact ConcreteCategory.congr_hom (e.hom.naturality f) p
  exact pinnedSimpleRankOneEquivariance C (pinnedDiagram d σ) a b hab S
    (SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A)
    (mapPoints f p) (by
      rw [hn, hp]
      exact (ConcreteCategory.congr_hom ((M.rankOne a).naturality j) A).symm)

private def groundParameterMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    integralTestAlgebra k ⟶ quadraticIntegralAlgebra k K where
  app R := CommAlgCat.ofHom
    { toRingHom := (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom
      commutes' n := map_intCast (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) n.down }
  naturality {R S} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    rfl

private theorem groundParameterMatrix_fixed (σ : Gal(K/k)) (R : TestAlgebra k)
    (A : SpecialLinearGroup (Fin 2) R) :
    SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom
      (SpecialLinearGroup.map ((groundParameterMap k K).app R).hom.toRingHom A) =
      SpecialLinearGroup.map ((groundParameterMap k K).app R).hom.toRingHom A := by
  apply Subtype.ext
  ext i j
  change σ 1 ⊗ₜ[k] A.val i j = (1 : K) ⊗ₜ[k] A.val i j
  rw [map_one]

private theorem pairedParameterMatrix_sq (σ : Gal(K/k)) (hs : σ * σ = 1)
    (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) (K ⊗[k] R)) :
    SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom
      (SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A) = A := by
  have h (z : K ⊗[k] R) : quadraticCoefficientEquiv σ R (quadraticCoefficientEquiv σ R z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change (σ * σ) a ⊗ₜ[k] b = a ⊗ₜ[k] b
      rw [hs]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply Subtype.ext
  ext i j
  exact h (A.val i j)

set_option maxHeartbeats 800000 in
theorem pinnedSingletonRankOne : PinnedSingletonRankOne.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ a _ hab
  obtain ⟨i, hi, hf⟩ := pinnedMarkedPointEmbedding C d
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  let E := quadraticIntegralAlgebra k K
  let j := Functor.whiskerRight (groundParameterMap k K) rankOnePoints ≫
    Functor.whiskerLeft E (M.rankOne a)
  have hj (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R) :
      (j.app R A : IntegralPoints M.group (E.obj R)) =
        (M.rankOne a).app (E.obj R)
          (SpecialLinearGroup.map ((groundParameterMap k K).app R).hom.toRingHom A) := rfl
  have hr (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R) :
      j.app R A ∈ Set.range (i.app R) := by
    let φ := (e.app ((extendedTestAlgebra k K).obj R)).groupIsoToMulEquiv
    obtain ⟨p, hp⟩ := φ.surjective (j.app R A)
    have hmark : markedFibrePoint C ((extendedTestAlgebra k K).obj R) p = j.app R A :=
      (he _ _).symm.trans hp
    rw [← hmark, (hf R).2]
    intro τ
    rcases (quadraticGalois hdegree σ hσ).1 τ with hτ | hτ
    · rw [hτ]
      exact pinnedSchemeAction_one C d R p
    · subst τ
      apply φ.injective
      change e.hom.app _ (pinnedSchemeAction d σ R p) = e.hom.app _ p
      rw [he, he, hmark, hj]
      rw [markedSchemeActionRankOne C d σ a a hab R _ p (hmark.trans (hj R A)),
        groundParameterMatrix_fixed]
  let h := liftPointMorphism i j (fun R => (hf R).1) hr
  refine ⟨h.val, fun R A => ?_⟩
  rw [← hi]
  have hcomp := ConcreteCategory.congr_hom (NatTrans.congr_app h.property R) A
  change i.app R (h.val.app R A) = j.app R A at hcomp
  rw [hcomp]
  exact hj R A

set_option maxHeartbeats 850000 in
theorem pinnedPairRankOne : PinnedPairRankOne.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs a b hab _ _ ha hb E
  obtain ⟨i, hi, hf⟩ := pinnedMarkedPointEmbedding C d
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  obtain ⟨j, hj⟩ := markedPairedRankOneProduct M hs a b hab (k := k) σ
  have hr (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) (K ⊗[k] R)) :
      j.app R A ∈ Set.range (i.app R) := by
    let S := (extendedTestAlgebra k K).obj R
    let φ := (e.app S).groupIsoToMulEquiv
    let A' := SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A
    let x : IntegralPoints M.group (E.obj R) := (M.rankOne a).app (E.obj R) A
    let y : IntegralPoints M.group (E.obj R) := (M.rankOne b).app (E.obj R) A'
    let p := φ.symm x
    let q := φ.symm y
    have hx : markedFibrePoint C S p = x :=
      (he _ _).symm.trans (φ.apply_symm_apply x)
    have hy : markedFibrePoint C S q = y :=
      (he _ _).symm.trans (φ.apply_symm_apply y)
    have hpq : markedFibrePoint C S (p * q) = j.app R A := by
      rw [← he, hj]
      change φ (p * q) = x * y
      rw [map_mul, φ.apply_symm_apply, φ.apply_symm_apply]
    rw [← hpq, (hf R).2]
    intro τ
    rcases (quadraticGalois hdegree σ hσ).1 τ with hτ | hτ
    · rw [hτ]
      exact pinnedSchemeAction_one C d R (p * q)
    · subst τ
      apply φ.injective
      rw [pinnedSchemeAction_mul, map_mul, map_mul]
      change e.hom.app S _ * e.hom.app S _ = e.hom.app S p * e.hom.app S q
      rw [he, he, he, he, hx, hy]
      rw [markedSchemeActionRankOne C d σ a b ha R A p hx,
        markedSchemeActionRankOne C d σ b a hb R A' q hy]
      let aMap : SpecialLinearGroup (Fin 2) (E.obj R) →* IntegralPoints M.group (E.obj R) :=
        ((M.rankOne a).app (E.obj R)).hom
      change y * aMap (SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A') = x * y
      rw [show SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A' = A from
        pairedParameterMatrix_sq σ (quadraticGalois hdegree σ hσ).2 R A]
      exact (markedOrthogonalRankOneCommutation M hs a b hab K
        (CommAlgCat.of K (K ⊗[k] R)) A A').eq.symm
  let h := liftPointMorphism i j (fun R => (hf R).1) hr
  refine ⟨h.val, fun R A => ?_⟩
  rw [← hi]
  have hcomp := ConcreteCategory.congr_hom (NatTrans.congr_app h.property R) A
  change i.app R (h.val.app R A) = j.app R A at hcomp
  rw [hcomp]
  exact hj R A

end RelativeRankOne

section MarkedReflection

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry Opposite CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel Specs.Pinning Specs.RootGroups
open Specs.CharacterPairing (characterValue)
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private conjugation conjugationIso conjugation_apply from
  LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private forgetFibrePoint_comp from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

private theorem markedWall_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (i : D.I) :
    (integralPointFunctor M.group).map f (markedWall M R i 1) = markedWall M S i 1 := by
  have h := ConcreteCategory.congr_hom ((M.rankOne i).naturality f) (wallMatrix (1 : Rˣ))
  change (M.rankOne i).app S (Matrix.SpecialLinearGroup.map f.hom.toRingHom (wallMatrix 1)) =
    (integralPointFunctor M.group).map f (markedWall M R i 1) at h
  rw [← h]
  apply congrArg (((M.rankOne i).app S).hom)
  apply Subtype.ext
  rw [show (Matrix.SpecialLinearGroup.map f.hom.toRingHom (wallMatrix (1 : Rˣ))).val =
    (wallMatrix (1 : Rˣ)).val.map f.hom from rfl, wallMatrix_val, wallMatrix_val]
  ext r s
  fin_cases r <;> fin_cases s <;> simp

private def reflectionOfTorus (D : BasedRootDatum.{u}) (i : D.I) : splitTorus D ≅ splitTorus D :=
  let e := (D.datum.reflection i).toAddEquiv.toMultiplicative
  (hopfSpec (CommRingCat.of Integers.{u})).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv Integers.{u} Integers.{u} e)).op

set_option maxHeartbeats 450000 in
private theorem reflectionOfTorus_point (D : BasedRootDatum.{u}) (i : D.I)
    (R : IntegralAlgebra.{u}) (v : TorusValues D R) :
    torusPoint D R v ≫ (reflectionOfTorus D i).hom.hom.hom =
      torusPoint D R (v.comp (D.datum.reflection i).toAddEquiv.toMultiplicative.toMonoidHom) := by
  unfold torusPoint
  let e := (D.datum.reflection i).toAddEquiv.toMultiplicative
  let t := MonoidAlgebra.domCongrBialgEquiv Integers.{u} Integers.{u} e
  change _ ≫ integralSpec.map (CommAlgCat.ofHom t.toAlgEquiv.toAlgHom).op = _
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext
  · intro j
    change (MonoidAlgebra.lift Integers.{u} R _
      ((Units.coeHom R).comp v)) (MonoidAlgebra.domCongr Integers.{u} Integers.{u} e
        (MonoidAlgebra.single j 1)) =
      (MonoidAlgebra.lift Integers.{u} R _
        ((Units.coeHom R).comp (v.comp e.toMonoidHom))) (MonoidAlgebra.single j 1)
    rw [MonoidAlgebra.domCongr_single, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single]
    rfl
  · exact Subsingleton.elim _ _

private theorem reflectionOfTorus_inv (D : BasedRootDatum.{u}) (i : D.I) :
    (reflectionOfTorus D i).inv = (reflectionOfTorus D i).hom := rfl

private def markedTorusEquiv {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (R : TestAlgebra k) :
    GroupPoints C.realization.pinned.pair.T.group R ≃*
      IntegralPoints (splitTorus D) ((integralTestAlgebra k).obj R) :=
  ((((groupPointsFunctor k).mapIso C.torusIso.symm).app R).groupIsoToMulEquiv.trans
    (forgetFibrePointEquiv (splitTorus D) R))

private theorem markedTorusIncl {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (R : TestAlgebra k)
    (p : GroupPoints C.realization.pinned.pair.T.group R) :
    markedFibrePoint C R (p ≫ C.realization.pinned.pair.T.inclusion.hom.hom) =
      markedTorusEquiv C R p ≫ M.torus.hom.hom := by
  let T := C.realization.pinned.pair.T
  have h : T.inclusion ≫ C.groupIso.inv = C.torusIso.inv ≫ (fibre k).map M.torus := by
    apply (cancel_mono C.groupIso.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, C.torus_comm,
      Iso.inv_hom_id_assoc]
  unfold markedFibrePoint
  rw [Category.assoc, ← Grp.comp_hom_hom, h, Grp.comp_hom_hom, ← Category.assoc,
    forgetFibrePoint_comp]
  rfl

private theorem markedWall_section {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (i : D.I) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ C.realization.pinned.pair.G.val.X,
      ∀ R : TestAlgebra k, markedFibrePoint C R (toUnit _ ≫ n) =
        markedWall M.toIntegralMarking ((integralTestAlgebra k).obj R) i 1 := by
  let S := CommAlgCat.of k k
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  let w := markedWall M.toIntegralMarking ((integralTestAlgebra k).obj S) i 1
  let p := e.inv.app S w
  let t : 𝟙_ (SchemeOver k) ≅ (testSpec k).obj (op S) := Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    simp)
  refine ⟨t.hom ≫ p, fun R => ?_⟩
  let f : S ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have ht : toUnit ((testSpec k).obj (op R)) ≫ t.hom = (testSpec k).map f.op :=
    ((isTerminalTensorUnit (C := SchemeOver k)).ofIso t).hom_ext _ _
  change markedFibrePoint C R (toUnit ((testSpec k).obj (op R)) ≫ t.hom ≫ p) = _
  rw [← Category.assoc, ht, ← he]
  change e.hom.app R (((groupPointsFunctor k).obj C.realization.pinned.pair.G.val).map f p) = _
  have hn := ConcreteCategory.congr_hom (e.hom.naturality f) p
  change e.hom.app R (((groupPointsFunctor k).obj C.realization.pinned.pair.G.val).map f p) =
    (integralPointFunctor M.group).map ((integralTestAlgebra k).map f) (e.hom.app S p) at hn
  rw [hn, show e.hom.app S p = w from ConcreteCategory.congr_hom (e.app S).inv_hom_id w]
  exact markedWall_map M.toIntegralMarking _ i

set_option maxHeartbeats 950000 in
theorem markedFieldReflection : MarkedFieldReflection.{u} := by
  intro D M k _ C i P
  obtain ⟨n, hn⟩ := markedWall_section C i
  let g := conjugationIso n
  let w₀ := reflectionOfTorus D i
  let w := C.torusIso.symm ≪≫ (fibre k).mapIso w₀ ≪≫ C.torusIso
  have hw_inv : w.inv = w.hom := by
    simp only [w, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
      Functor.mapIso_inv]
    rw [show w₀.inv = w₀.hom from reflectionOfTorus_inv D i]
    simp only [Category.assoc]
  have htw (R : TestAlgebra k) (t : GroupPoints P.T.group R) :
      markedTorusEquiv C R (t ≫ w.hom.hom.hom) =
        markedTorusEquiv C R t ≫ w₀.hom.hom.hom := by
    change forgetFibrePoint (splitTorus D) R ((t ≫ w.hom.hom.hom) ≫ C.torusIso.inv.hom.hom) =
      forgetFibrePoint (splitTorus D) R (t ≫ C.torusIso.inv.hom.hom) ≫ w₀.hom.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, show w.hom ≫ C.torusIso.inv =
      C.torusIso.inv ≫ (fibre k).map w₀.hom by
        simp [w, Category.assoc], Grp.comp_hom_hom, ← Category.assoc,
      forgetFibrePoint_comp]
  have hg (R : TestAlgebra k) (p : GroupPoints P.G.val R) :
      let q := markedWall M.toIntegralMarking ((integralTestAlgebra k).obj R) i 1
      markedFibrePoint C R (p ≫ g.hom.hom.hom) = q * markedFibrePoint C R p * q⁻¹ := by
    obtain ⟨e, he⟩ := markedFibrePointComparison C
    change markedFibrePoint C R (p ≫ (conjugation n).hom.hom) = _
    rw [conjugation_apply n p]
    let φ := (e.app R).groupIsoToMulEquiv
    let nr : GroupPoints P.G.val R := toUnit ((testSpec k).obj (op R)) ≫ n
    rw [← he]
    change φ (nr * p * nr⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    change e.hom.app R nr * e.hom.app R p * (e.hom.app R nr)⁻¹ = _
    have hn' := hn R
    change markedFibrePoint C R nr = _ at hn'
    simp only [he, hn']
  have htor (R : TestAlgebra k) (t : GroupPoints P.T.group R) :
      ∃ v : TorusValues D ((integralTestAlgebra k).obj R),
        markedTorusEquiv C R t = torusPoint D ((integralTestAlgebra k).obj R) v := by
    obtain ⟨v, hv⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X)
      ((integralTestAlgebra k).obj R)).surjective (markedTorusEquiv C R t)
    exact ⟨v, hv.symm⟩
  have hχ (R : TestAlgebra k) (t : GroupPoints P.T.group R) (v : TorusValues D _)
      (ht : markedTorusEquiv C R t = torusPoint D ((integralTestAlgebra k).obj R) v) (x : D.X) :
      characterValue (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) R t =
        (v (Multiplicative.ofAdd x) : R) := by
    have h := C.torus_eval R (t ≫ C.torusIso.inv.hom.hom) v ht x
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id] at h
    change characterValue _ R (t ≫ 𝟙 _) = _ at h
    rwa [Category.comp_id] at h
  refine ⟨g, w, ?_, ?_, hg⟩
  · apply Grp.hom_ext
    apply hom_ext_of_points (Specs.Unipotent.closedSubgroupAlgebraicGroup P.T).property.1
    intro R t
    obtain ⟨e, he⟩ := markedFibrePointComparison C
    apply (e.app R).groupIsoToMulEquiv.injective
    change e.hom.app R (t ≫ (P.T.inclusion ≫ g.hom).hom.hom) =
      e.hom.app R (t ≫ (w.hom ≫ P.T.inclusion).hom.hom)
    rw [he, he]
    simp only [Grp.comp_hom_hom, ← Category.assoc]
    obtain ⟨v, hv⟩ := htor R t
    rw [hg, markedTorusIncl, markedTorusIncl, htw, hv, reflectionOfTorus_point]
    have h := markedWallTorusReflection M.toIntegralMarking ((integralTestAlgebra k).obj R) i 1 v
    rw [h.1]
    congr 2
    exact MonoidHom.ext (fun x => h.2 (Multiplicative.toAdd x))
  · intro x
    apply RootData.CharacterPairing.characterValuesDetectCharacters P.split
    intro R p
    obtain ⟨v, hv⟩ := htor R p
    change characterValue (w.inv ≫ Additive.toMul (C.realization.datumIso.val.weightEquiv x)) R p = _
    rw [hw_inv]
    rw [show characterValue (w.hom ≫ Additive.toMul (C.realization.datumIso.val.weightEquiv x)) R p =
        characterValue (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) R
          (p ≫ w.hom.hom.hom) by simp only [characterValue, Grp.comp_hom_hom, Category.assoc]]
    let v' := v.comp (D.datum.reflection i).toAddEquiv.toMultiplicative.toMonoidHom
    have hv' : markedTorusEquiv C R (p ≫ w.hom.hom.hom) =
        torusPoint D ((integralTestAlgebra k).obj R) v' := by
      rw [htw, hv, reflectionOfTorus_point]
    rw [hχ R (p ≫ w.hom.hom.hom) v' hv' x]
    exact (hχ R p v hv (D.datum.reflection i x)).symm

private theorem markedLabel_weight {D : BasedRootDatum.{u}} {M : Model D}
    {k : Type u} [Field k] (C : MarkedFibre M k) (j : D.I) :
    (C.realization.datumIso.val.indexEquiv j).val =
      Additive.toMul (C.realization.datumIso.val.weightEquiv (D.datum.root j)) := by
  let E := C.realization.attached
  letI := E.comm
  let e := C.realization.datumIso.val
  have h : e.weightEquiv (D.datum.root j) = E.datum.rootDatum.root (e.indexEquiv j) :=
    e.toHom.root_weightMap_apply D.datum E.toBased.datum j
  rw [E.datum.root_eq] at h
  exact (congrArg Additive.toMul h).symm

private theorem fieldReflectionScalars {D : BasedRootDatum.{u}} {M : Model D}
    {k : Type u} [Field k] (C : MarkedFibre M k) (i j : D.I) :
    ∃ c : kˣ, ∀ (R : TestAlgebra k) (z : R),
      let S := (integralTestAlgebra k).obj R
      let n := markedWall M.toIntegralMarking S i 1
      n * markedRootPoint M.toIntegralMarking S j z * n⁻¹ =
        markedRootPoint M.toIntegralMarking S (D.datum.reflectionPerm i j) (algebraMap k R (c : k) * z) := by
  obtain ⟨g, w, hT, hχ, hn⟩ := markedFieldReflection C i
  let j' := D.datum.reflectionPerm i j
  let e := C.realization.datumIso.val.indexEquiv
  have h : transportCharacter w (e j).val = (e j').val := by
    rw [markedLabel_weight C j, markedLabel_weight C j']
    exact (hχ (D.datum.root j)).trans
      (congrArg (fun x => Additive.toMul (C.realization.datumIso.val.weightEquiv x))
        (D.datum.root_reflectionPerm i j).symm)
  obtain ⟨c, hc, _⟩ := rootCoordinateTransport C.realization.pinned g w hT (e j) (e j') h
    (C.coordinate j) (C.coordinate j')
  refine ⟨c, fun R z => ?_⟩
  have hz : rootPoint (C.rootMap j ≫ g.hom) R z =
      rootPoint (C.rootMap j') R (algebraMap k R (c : k) * z) := hc R z
  have hm := congrArg (markedFibrePoint C R) hz
  rw [rootPoint_comp, hn, markedFibrePoint_root, markedFibrePoint_root] at hm
  exact hm

set_option maxHeartbeats 750000 in
theorem integralRootReflectionUnits : IntegralRootReflectionUnits.{u} := by
  intro D M i j
  let Q := Specs.RationalRealization.RationalField.{u}
  letI : CharZero Q := charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ ≃+* Q).toRingHom) ULift.ringEquiv.symm.injective
  obtain ⟨C⟩ := markedFibreExists M Q
  obtain ⟨c, hc⟩ := fieldReflectionScalars C i j
  letI : Algebra Integers.{u} Q := integerAlgebra Q
  let A := CommAlgCat.of Integers.{u} Integers.{u}
  let B := (integralTestAlgebra Q).obj (CommAlgCat.of Q Q)
  let f : A ⟶ B := CommAlgCat.ofHom (Algebra.ofId Integers.{u} Q)
  have hinj : Function.Injective f.hom :=
    (Int.cast_injective (α := Q)).comp ULift.ringEquiv.injective
  letI : _root_.IsReduced B := inferInstanceAs (_root_.IsReduced Q)
  letI : _root_.IsReduced A := isReduced_of_injective f.hom hinj
  obtain ⟨d, hd, _⟩ := integralRootTransportUnits M.toIntegralMarking A B f hinj
    (markedWall M.toIntegralMarking A i 1) j (D.datum.reflectionPerm i j) c (by
      rw [markedWall_map]
      exact hc (CommAlgCat.of Q Q))
  let P := CommAlgCat.of Integers.{u} (Polynomial Integers.{u})
  let U := CommAlgCat.of Q (Polynomial Q)
  let P' := (integralTestAlgebra Q).obj U
  letI : Algebra Integers.{u} (Polynomial Q) := integerAlgebra _
  let h : P ⟶ P' := CommAlgCat.ofHom
    { toRingHom := Polynomial.mapRingHom f.hom.toRingHom
      commutes' n := by
        let h₁ : Polynomial Integers.{u} →+* Polynomial Q :=
          Polynomial.mapRingHom f.hom.toRingHom
        change h₁ (algebraMap Integers.{u} P n) = (n.down : Polynomial Q)
        have hn : ((n.down : ℤ) : Integers.{u}) = n := rfl
        rw [← hn]
        change h₁ (n.down : Polynomial Integers.{u}) = (n.down : Polynomial Q)
        exact map_intCast h₁ n.down }
  have hh : Function.Injective h.hom := by
    change Function.Injective (Polynomial.map f.hom.toRingHom)
    exact Polynomial.map_injective _ hinj
  let z₀ : P := Polynomial.X
  have h₀ : markedWall M.toIntegralMarking P i 1 * markedRootPoint M.toIntegralMarking P j z₀ *
        (markedWall M.toIntegralMarking P i 1)⁻¹ =
      markedRootPoint M.toIntegralMarking P (D.datum.reflectionPerm i j)
        (algebraMap Integers.{u} P (d : Integers.{u}) * z₀) := by
    apply integralPoint_map_injective M.affine h hh
    let ψ := ((integralPointFunctor M.group).map h).hom
    change ψ _ = ψ _
    simp only [ψ, map_mul, map_inv, markedWall_map, markedRootPoint_map]
    have hcoeff : h.hom (algebraMap Integers.{u} P (d : Integers.{u})) =
        algebraMap Q U (c : Q) := by
      rw [h.hom.commutes]
      change Polynomial.C (f.hom (d : Integers.{u})) = Polynomial.C (c : Q)
      exact congrArg Polynomial.C (congrArg Units.val hd)
    rw [hcoeff]
    exact hc U (h.hom z₀)
  refine ⟨d, fun R z => ?_⟩
  let m : P ⟶ R := CommAlgCat.ofHom (Polynomial.aeval z : Polynomial Integers.{u} →ₐ[_] R)
  have he := congrArg (((integralPointFunctor M.group).map m).hom) h₀
  simp only [map_mul, map_inv, markedWall_map, markedRootPoint_map] at he
  rw [m.hom.commutes, show m.hom z₀ = z from Polynomial.aeval_X z] at he
  exact he

end MarkedReflection

section RootPairCoordinates

set_option backward.isDefEq.respectTransparency false

open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonObj

universe u

private theorem orderedRootPoint_eq_one {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (v : D.I → R)
    (h : ∀ i ∈ l, v i = 0) : orderedRootPoint M R l v = 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change markedRootPoint M R a (v a) * orderedRootPoint M R l v = 1
    rw [h a (List.mem_cons_self), markedRootPoint_zero, one_mul]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

set_option maxHeartbeats 1200000 in
theorem markedRootPairInjectivity : MarkedRootPairInjectivity.{u} := by
  classical
  intro D M R a b hab hsign
  let v (p : R × R) (j : D.I) := if j = a then p.1 else if j = b then p.2 else 0
  have ha (p : R × R) : v p a = p.1 := by simp [v]
  have hb (p : R × R) : v p b = p.2 := by simp [v, Ne.symm hab]
  have hz (p : R × R) (j : D.I) (ha : j ≠ a) (hb : j ≠ b) : v p j = 0 := by
    simp [v, ha, hb]
  let t : IntegralPoints (splitTorus D) R := 1
  have ht : (t ≫ M.torus.hom.hom : IntegralPoints M.group R) = 1 :=
    MonObj.one_comp _
  suffices h : ∃ l m, Enumerates l {i | ¬ D.base.IsPos i} ∧
      Enumerates m {i | D.base.IsPos i} ∧
      ∀ p : R × R, markedCellPoint M R l m (v p) t =
        markedRootPoint M R a p.1 * markedRootPoint M R b p.2 by
    obtain ⟨l, m, hl, hm, hval⟩ := h
    intro p q hpq
    change markedRootPoint M R a p.1 * markedRootPoint M R b p.2 =
      markedRootPoint M R a q.1 * markedRootPoint M R b q.2 at hpq
    have eq : markedCellPoint M R l m (v p) t = markedCellPoint M R l m (v q) t :=
      (hval p).trans (hpq.trans (hval q).symm)
    have he : (v p, t) = (v q, t) := (markedCellCoordinates M R l m hl hm).1 eq
    have he' : v p = v q := congrArg Prod.fst he
    exact Prod.ext (by simpa only [ha] using congrFun he' a)
      (by simpa only [hb] using congrFun he' b)
  have enum (s : Set D.I) (ha : a ∈ s) (hb : b ∈ s) :
      ∃ l : List D.I, Enumerates (a :: b :: l) s ∧ ∀ j ∈ l, j ≠ a ∧ j ≠ b := by
    obtain ⟨l, hl, hh⟩ := enumerateRoots D {j ∈ s | j ≠ a ∧ j ≠ b}
    have hmem (j : D.I) : j ∈ l ↔ j ∈ s ∧ j ≠ a ∧ j ≠ b := hh j
    refine ⟨l, ⟨?_, ?_⟩, fun j hj => ((hmem j).mp hj).2⟩
    · simp only [List.nodup_cons, List.mem_cons, hmem, not_or]
      exact ⟨⟨hab, fun h => h.2.1 rfl⟩, ⟨fun h => h.2.2 rfl, hl⟩⟩
    · intro j
      simp only [List.mem_cons, hmem]
      constructor
      · rintro (rfl | rfl | h)
        · exact ha
        · exact hb
        · exact h.1
      · intro hj
        by_cases hja : j = a
        · exact Or.inl hja
        by_cases hjb : j = b
        · exact Or.inr (Or.inl hjb)
        · exact Or.inr (Or.inr ⟨hj, hja, hjb⟩)
  by_cases hp : D.base.IsPos a
  · have hbp : D.base.IsPos b := hsign.mp hp
    obtain ⟨n, hn⟩ := enumerateRoots D {i | ¬ D.base.IsPos i}
    obtain ⟨l, hl, hl'⟩ := enum {i | D.base.IsPos i} hp hbp
    refine ⟨n, a :: b :: l, hn, hl, fun p => ?_⟩
    have hn' (j : D.I) (hj : j ∈ n) : v p j = 0 := by
      have hj' := (hn.2 j).mp hj
      exact hz p j (fun h => hj' (h ▸ hp)) (fun h => hj' (h ▸ hbp))
    unfold markedCellPoint
    rw [orderedRootPoint_eq_one M R _ _ hn', ht, one_mul, one_mul]
    change markedRootPoint M R a (v p a) *
      (markedRootPoint M R b (v p b) * orderedRootPoint M R l (v p)) = _
    rw [ha, hb, orderedRootPoint_eq_one M R _ _
      (fun j hj => hz p j (hl' j hj).1 (hl' j hj).2), mul_one]
  · have hbp : ¬ D.base.IsPos b := fun h => hp (hsign.mpr h)
    obtain ⟨n, hn⟩ := enumerateRoots D {i | D.base.IsPos i}
    obtain ⟨l, hl, hl'⟩ := enum {i | ¬ D.base.IsPos i} hp hbp
    refine ⟨a :: b :: l, n, hl, hn, fun p => ?_⟩
    have hn' (j : D.I) (hj : j ∈ n) : v p j = 0 := by
      have hj' := (hn.2 j).mp hj
      exact hz p j (fun h => hp (h ▸ hj')) (fun h => hbp (h ▸ hj'))
    unfold markedCellPoint
    rw [orderedRootPoint_eq_one M R _ _ hn', ht, mul_one, mul_one]
    change markedRootPoint M R a (v p a) *
      (markedRootPoint M R b (v p b) * orderedRootPoint M R l (v p)) = _
    rw [ha, hb, orderedRootPoint_eq_one M R _ _
      (fun j hj => hz p j (hl' j hj).1 (hl' j hj).2), mul_one]

end RootPairCoordinates

section RelativeParameterSchemes

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

private def reindexSL {R : Type*} [CommRing R] {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (e : I ≃ J) :
    SpecialLinearGroup I R ≃* SpecialLinearGroup J R :=
  let v := Matrix.reindexAlgEquiv R R e
  { toFun := fun A => ⟨v A.val, (Matrix.det_reindexAlgEquiv R R e A.val).trans A.property⟩
    invFun := fun A => ⟨v.symm A.val, by
      rw [show v.symm = Matrix.reindexAlgEquiv R R e.symm from Matrix.symm_reindexAlgEquiv R R e,
        Matrix.det_reindexAlgEquiv]
      exact A.property⟩
    left_inv := fun A => Subtype.ext (v.symm_apply_apply A.val)
    right_inv := fun A => Subtype.ext (v.apply_symm_apply A.val)
    map_mul' := fun A B => Subtype.ext (map_mul v A.val B.val) }

private def rankOneIndexIso (k : Type u) [Field k] :
    Specs.StandardGroups.specialLinearPoints k (ULift.{u} (Fin 2)) ≅
      integralTestAlgebra k ⋙ rankOnePoints.{u} :=
  NatIso.ofComponents (fun R => (reindexSL (R := R) Equiv.ulift).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro A
    apply Subtype.ext
    ext i j
    rfl)

private abbrev leftExtension (k K : Type u) [Field k] [Field K] [Algebra k K] :
    TestAlgebra k ⥤ TestAlgebra K where
  obj R := CommAlgCat.of K (K ⊗[k] R)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) f.hom)
  map_id R := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id (R := k) (S := K) (A := K) (B := R)
  map_comp {R S T} f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id K K) (g.hom.comp f.hom) z =
      Algebra.TensorProduct.map (AlgHom.id K K) g.hom
        (Algebra.TensorProduct.map (AlgHom.id K K) f.hom z)
    rw [Algebra.TensorProduct.map_id_comp]
    rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private def tensorFlipIso (k K : Type u) [Field k] [Field K] [Algebra k K] :
    WeilRestriction.extendScalars k K ≅ leftExtension k K :=
  NatIso.ofComponents (fun R => CommAlgCat.isoMk (AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm k R K).toRingEquiv) (fun _ => rfl))) (by
    intro R S f
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy =>
      change (Algebra.TensorProduct.comm k S K)
          (Algebra.TensorProduct.map f.hom (AlgHom.id k K) (x + y)) =
        Algebra.TensorProduct.map (AlgHom.id K K) f.hom
          ((Algebra.TensorProduct.comm k R K) (x + y))
      have hx' := hx
      have hy' := hy
      change (Algebra.TensorProduct.comm k S K)
          (Algebra.TensorProduct.map f.hom (AlgHom.id k K) _) =
        Algebra.TensorProduct.map (AlgHom.id K K) f.hom
          ((Algebra.TensorProduct.comm k R K) _) at hx' hy'
      simp only [map_add, hx', hy'])

theorem relativeParameterRepresentability : RelativeParameterRepresentability.{u} := by
  intro k K _ _ _ _
  let A := StandardGroups.additiveGroup k
  let H := StandardGroups.specialLinearGroup k (ULift.{u} (Fin 2))
  let AK := StandardGroups.additiveGroup K
  let HK := StandardGroups.specialLinearGroup K (ULift.{u} (Fin 2))
  let a := WeilRestriction.groupRepresentation k K AK
  let h := WeilRestriction.groupRepresentation k K HK
  let F := leftExtension k K
  let flip := tensorFlipIso k K
  let pa : (groupPointsFunctor k).obj a.1.val ≅
      extendedTestAlgebra k K ⋙ Specs.StandardGroups.additivePoints k :=
    a.2 ≪≫ Functor.isoWhiskerRight flip ((groupPointsFunctor K).obj AK.val) ≪≫
      Functor.isoWhiskerLeft F (StandardGroups.additiveGroupPointsIso K)
  let ph : (groupPointsFunctor k).obj h.1.val ≅ quadraticIntegralAlgebra k K ⋙ rankOnePoints.{u} :=
    h.2 ≪≫ Functor.isoWhiskerRight flip ((groupPointsFunctor K).obj HK.val) ≪≫
      Functor.isoWhiskerLeft F
        (StandardGroups.specialLinearGroupPointsIso K _ ≪≫ rankOneIndexIso K)
  exact ⟨⟨A, StandardGroups.additiveGroupPointsIso k, H,
    StandardGroups.specialLinearGroupPointsIso k _ ≪≫ rankOneIndexIso k, a.1, pa, h.1, ph⟩⟩

open private closedImmersion_of_injective_test_points from
  LinearAlgebraicGroups.Classification.RationalRealization

private def coordinatePointsIso {k : Type u} [Field k] (G : AffineAlgebraicGroup k) :
    convolutionPoints (Specs.AdjointCocharacters.coordinateHopf G) ≅
      (groupPointsFunctor k).obj G.val :=
  NatIso.ofComponents (fun R => (coordinatePointEquiv G R).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    exact coordinatePointEquiv_natural G f)

theorem relativeRankOneSchemeRealization : RelativeRankOneSchemeRealization.{u} := by
  intro k _ G U H P A eu eh x ρ hinj
  let e := coordinatePointsIso G
  obtain ⟨f, hf⟩ := (groupHomComparison k U.val H.val U.property.1).surjective (eu.hom ≫ x ≫ eh.inv)
  obtain ⟨g, hg⟩ := (groupHomComparison k H.val G.val H.property.1).surjective (eh.hom ≫ ρ ≫ e.hom)
  have hu (R : TestAlgebra k) (p : GroupPoints U.val R) :
      eh.hom.app R (p ≫ f.hom.hom) = x.app R (eu.hom.app R p) := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hf R) p
    change p ≫ f.hom.hom = eh.inv.app R (x.app R (eu.hom.app R p)) at h
    rw [h]
    exact ConcreteCategory.congr_hom (eh.app R).inv_hom_id _
  have hr (R : TestAlgebra k) (p : GroupPoints H.val R) :
      (coordinatePointEquiv G R).symm (p ≫ g.hom.hom) = ρ.app R (eh.hom.app R p) := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hg R) p
    change p ≫ g.hom.hom = coordinatePointEquiv G R (ρ.app R (eh.hom.app R p)) at h
    rw [h, MulEquiv.symm_apply_apply]
  refine ⟨f, g, ?_, hu, hr⟩
  apply closedImmersion_of_injective_test_points (G := U) (H := G)
  intro R p q h
  change p ≫ f.hom.hom ≫ g.hom.hom = q ≫ f.hom.hom ≫ g.hom.hom at h
  rw [← Category.assoc, ← Category.assoc] at h
  have hh := congrArg ((coordinatePointEquiv G R).symm) h
  rw [hr, hr, hu, hu] at hh
  exact (eu.app R).groupIsoToMulEquiv.injective (hinj R hh)

end RelativeParameterSchemes

section IntegralWeylWords

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.IntegralSemisimpleModel Specs.Pinning
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

private theorem mul_conjugation {G : Type*} [Group G] (x y z : G) :
    x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group

private theorem markedWeylWord_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List D.I) :
    (integralPointFunctor M.group).map f (markedWeylWord M R l) = markedWeylWord M S l := by
  let j := ((integralPointFunctor M.group).map f).hom
  change j _ = _
  induction l with
  | nil => exact map_one j
  | cons i l ih =>
    change j (markedWall M R i 1 * markedWeylWord M R l) =
      markedWall M S i 1 * markedWeylWord M S l
    rw [map_mul, ih]
    exact congrArg (· * markedWeylWord M S l) (markedWall_map M f i)

private theorem markedWeylWord_append {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l m : List D.I) :
    markedWeylWord M R (l ++ m) = markedWeylWord M R l * markedWeylWord M R m := by
  simp only [markedWeylWord, List.map_append, List.prod_append]

theorem integralWeylWordTransport : IntegralWeylWordTransport.{u} := by
  intro D M l j
  induction l with
  | nil =>
    refine ⟨1, fun R z => ?_⟩
    simp [markedWeylWord, weylWordPerm]
  | cons i l ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := integralRootReflectionUnits M i (weylWordPerm l j)
    refine ⟨d * c, fun R z => ?_⟩
    let x := markedRootPoint M.toIntegralMarking R
    let n := markedWall M.toIntegralMarking R i 1
    let w := markedWeylWord M.toIntegralMarking R l
    change (n * w) * x j z * (n * w)⁻¹ =
      x (D.datum.reflectionPerm i (weylWordPerm l j)) (algebraMap Integers R (↑(d * c)) * z)
    rw [mul_conjugation, hc R z, hd R _, Units.val_mul, map_mul, mul_assoc]

private theorem map_unitWall {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    SpecialLinearGroup.map f (wallMatrix (1 : Rˣ)) = wallMatrix (1 : Sˣ) := by
  apply Subtype.ext
  change (wallMatrix (1 : Rˣ)).val.map f = (wallMatrix (1 : Sˣ)).val
  rw [wallMatrix_val, wallMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 950000 in
theorem pinnedWeylWordFixed : PinnedWeylWordFixed.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw R
  obtain ⟨emb, he, _⟩ := pinnedMarkedPointEmbedding C d
  let E := quadraticIntegralAlgebra k K
  let S := E.obj R
  let M₀ := M.toIntegralMarking
  let nm (l : List D.I) := markedWeylWord M₀ S l
  let i := (emb.app R).hom
  suffices h : nm (w.flatMap SimpleRootOrbit.roots) ∈ Set.range i by
    obtain ⟨p, hp⟩ := h
    exact ⟨p, (he R p).symm.trans hp⟩
  have horbit (o : SimpleRootOrbit D) (h : o.Matches C (pinnedDiagram d σ)) :
      nm o.roots ∈ Set.range i := by
    rcases o with ⟨a, - | b⟩
    · obtain ⟨ρ, hr⟩ := pinnedSingletonRankOne C d hdegree σ hσ a h
      let p := ρ.app R (wallMatrix (1 : Rˣ))
      refine ⟨p, ?_⟩
      change emb.app R p = nm _
      rw [he, hr, map_unitWall]
      change markedWall M₀ S a 1 = markedWall M₀ S a 1 * 1
      rw [mul_one]
    · obtain ⟨ha, h₁, h₂⟩ := h
      obtain ⟨ρ, hr⟩ := pinnedPairRankOne C d hdegree σ hσ hs a b ha h₁ h₂
      let p := ρ.app R (wallMatrix (1 : (K ⊗[k] R)ˣ))
      refine ⟨p, ?_⟩
      change emb.app R p = nm _
      rw [he, hr, map_unitWall]
      change markedWall M₀ S a 1 * markedWall M₀ S b 1 =
        markedWall M₀ S a 1 * (markedWall M₀ S b 1 * 1)
      rw [mul_one]
  induction w with
  | nil => exact ⟨1, map_one i⟩
  | cons o w ih =>
    obtain ⟨a, ha⟩ := horbit o (hw o List.mem_cons_self)
    obtain ⟨b, hb⟩ := ih (fun s hs => hw s (List.mem_cons_of_mem _ hs))
    refine ⟨a * b, ?_⟩
    change i (a * b) = nm (o.roots ++ w.flatMap SimpleRootOrbit.roots)
    rw [map_mul, ha, hb]
    exact (markedWeylWord_append M₀ S _ _).symm

set_option maxHeartbeats 900000 in
theorem pinnedWeylRankOneTransport : PinnedWeylRankOneTransport.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw P ρ
  obtain ⟨emb, he, hf⟩ := pinnedMarkedPointEmbedding C d
  let E := quadraticIntegralAlgebra k K
  let J := E ⋙ integralPointFunctor M.group
  let n (R : TestAlgebra k) : J.obj R :=
    markedWeylWord M.toIntegralMarking (E.obj R) (w.flatMap SimpleRootOrbit.roots)
  let κ : J ⟶ J :=
    { app := fun R => GrpCat.ofHom (MulAut.conj (n R)).toMonoidHom
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro p
        let j := (J.map f).hom
        change n S * j p * (n S)⁻¹ = j (n R * p * (n R)⁻¹)
        rw [map_mul, map_mul, map_inv, show j (n R) = n S from markedWeylWord_map _ _ _] }
  let j := ρ ≫ emb ≫ κ
  have hR (R : TestAlgebra k) (x : P.obj R) : j.app R x ∈ Set.range (emb.app R) := by
    obtain ⟨p, hp⟩ := pinnedWeylWordFixed C d hdegree σ hσ hs w hw R
    have hp' : emb.app R p = n R := (he R p).trans hp
    refine ⟨p * ρ.app R x * p⁻¹, ?_⟩
    let i := (emb.app R).hom
    change i (p * ρ.app R x * p⁻¹) = n R * i (ρ.app R x) * (n R)⁻¹
    rw [map_mul, map_mul, map_inv, show i p = n R from hp']
  let h := liftPointMorphism emb j (fun R => (hf R).1) hR
  refine ⟨h.val, fun R A => ?_⟩
  have hcomp := ConcreteCategory.congr_hom (NatTrans.congr_app h.property R) A
  change emb.app R (h.val.app R A) = n R * emb.app R (ρ.app R A) * (n R)⁻¹ at hcomp
  rw [he R, he R] at hcomp
  exact hcomp

end IntegralWeylWords

section RelativeRootModels

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.IntegralRootRelations (upper)
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj Matrix

universe u

private theorem map_upperMatrix {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (z : R) : SpecialLinearGroup.map f (upper z) = upper (f z) := by
  apply Subtype.ext
  change (!![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) R).map f = !![1, f z; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 850000 in
theorem pinnedSingletonRootModel : PinnedSingletonRootModel.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw a ha
  let E := quadraticIntegralAlgebra k K
  let n (R : TestAlgebra k) := markedWeylWord M.toIntegralMarking (E.obj R)
    (w.flatMap SimpleRootOrbit.roots)
  obtain ⟨ρ, hρ⟩ := pinnedSingletonRankOne C d hdegree σ hσ a ha
  obtain ⟨ρ', hρ'⟩ := pinnedWeylRankOneTransport C d hdegree σ hσ hs w hw ρ
  have hupper (R : TestAlgebra k) (z : Multiplicative R) :
      pinnedMarkedPoint C d R (ρ'.app R ((upperParameters k).app R z)) =
        n R * markedRootPoint M.toIntegralMarking (E.obj R) a
          ((Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) z.toAdd) * (n R)⁻¹ := by
    change pinnedMarkedPoint C d R (ρ'.app R (upper z.toAdd)) = _
    rw [hρ', hρ, map_upperMatrix, M.rankOneUpper]
    rfl
  have hinj (R : TestAlgebra k) :
      Function.Injective (fun z : Multiplicative R => ρ'.app R ((upperParameters k).app R z)) := by
    intro z z' h
    have h' := congrArg (pinnedMarkedPoint C d R) h
    rw [hupper, hupper] at h'
    apply Multiplicative.toAdd.injective
    apply includeRight_injective (k := k) (K := K)
    apply markedRootPoint_injective M.toIntegralMarking (E.obj R) a
    exact (MulAut.conj (n R)).injective h'
  obtain ⟨S⟩ := relativeParameterRepresentability k K
  obtain ⟨u, r, hc, hu, hr⟩ := relativeRankOneSchemeRealization G S.additive S.rankOne
    S.additivePoints S.rankOnePoints (upperParameters k) ρ' hinj
  refine ⟨⟨S.additive, S.rankOne, S.additivePoints, S.rankOnePoints, u, r, hc, hu, ρ', hr⟩,
    fun R A => ?_⟩
  change pinnedMarkedPoint C d R (ρ'.app R A) = _
  rw [hρ', hρ]

set_option maxHeartbeats 950000 in
theorem pinnedPairRootModel : PinnedPairRootModel.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw a b hm
  obtain ⟨hab, ha, hb⟩ := hm
  let E := quadraticIntegralAlgebra k K
  let P := extendedTestAlgebra k K
  let x := Functor.whiskerLeft P (upperParameters k)
  let n (R : TestAlgebra k) := markedWeylWord M.toIntegralMarking (E.obj R)
    (w.flatMap SimpleRootOrbit.roots)
  obtain ⟨ρ, hρ⟩ := pinnedPairRankOne C d hdegree σ hσ hs a b hab ha hb
  obtain ⟨ρ', hρ'⟩ := pinnedWeylRankOneTransport C d hdegree σ hσ hs w hw ρ
  have hupper (R : TestAlgebra k) (z : Multiplicative (K ⊗[k] R)) :
      pinnedMarkedPoint C d R (ρ'.app R (x.app R z)) =
        n R * (markedRootPoint M.toIntegralMarking (E.obj R) a z.toAdd *
          markedRootPoint M.toIntegralMarking (E.obj R) b
            (quadraticCoefficientEquiv σ R z.toAdd)) * (n R)⁻¹ := by
    change pinnedMarkedPoint C d R (ρ'.app R (upper z.toAdd)) = _
    rw [hρ', hρ, map_upperMatrix, M.rankOneUpper, M.rankOneUpper]
    rfl
  have hne : (a : D.I) ≠ b := by
    intro h
    rw [h, RootPairing.pairing_same] at hab
    norm_num at hab
  have hsign : D.base.IsPos a ↔ D.base.IsPos b :=
    iff_of_true (D.base.isPos_of_mem_support a.property) (D.base.isPos_of_mem_support b.property)
  have hinj (R : TestAlgebra k) :
      Function.Injective (fun z : Multiplicative (K ⊗[k] R) => ρ'.app R (x.app R z)) := by
    intro z z' h
    have h' := congrArg (pinnedMarkedPoint C d R) h
    rw [hupper, hupper] at h'
    have he := (MulAut.conj (n R)).injective h'
    have hc := markedRootPairInjectivity M.toIntegralMarking (E.obj R) a b hne hsign
      (a₁ := (z.toAdd, quadraticCoefficientEquiv σ R z.toAdd))
      (a₂ := (z'.toAdd, quadraticCoefficientEquiv σ R z'.toAdd)) he
    exact Multiplicative.toAdd.injective (congrArg Prod.fst hc)
  obtain ⟨S⟩ := relativeParameterRepresentability k K
  obtain ⟨u, r, hc, hu, hr⟩ := relativeRankOneSchemeRealization G S.restrictedAdditive
    S.restrictedRankOne S.restrictedAdditivePoints S.restrictedRankOnePoints x ρ' hinj
  refine ⟨⟨S.restrictedAdditive, S.restrictedRankOne, S.restrictedAdditivePoints,
    S.restrictedRankOnePoints, u, r, hc, hu, ρ', hr⟩, fun R A => ?_⟩
  change pinnedMarkedPoint C d R (ρ'.app R A) = _
  rw [hρ', hρ]

theorem splitMarkedRootModel : SplitMarkedRootModel.{u} := by
  intro D M k _ C a
  let G := C.realization.pinned.pair.G
  obtain ⟨e, he⟩ := markedFibrePointComparison C
  let F := integralTestAlgebra k
  let j := Functor.whiskerLeft F (M.rankOne a)
  let ρ := j ≫ e.inv ≫ (coordinatePointsIso G).inv
  have hρ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R) :
      markedFibrePoint C R (coordinatePointEquiv G R (ρ.app R A)) =
        (M.rankOne a).app (F.obj R) A := by
    rw [← he]
    let φ := coordinatePointEquiv G R
    change e.hom.app R (φ (φ.symm (e.inv.app R (j.app R A)))) = _
    rw [MulEquiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom (e.app R).inv_hom_id (j.app R A)
  have hinj (R : TestAlgebra k) :
      Function.Injective (fun z : Multiplicative R => ρ.app R ((upperParameters k).app R z)) := by
    intro z z' h
    have h' := congrArg (fun p => markedFibrePoint C R (coordinatePointEquiv G R p)) h
    rw [hρ, hρ] at h'
    change (M.rankOne a).app (F.obj R) (upper z.toAdd) =
      (M.rankOne a).app (F.obj R) (upper z'.toAdd) at h'
    rw [M.rankOneUpper, M.rankOneUpper] at h'
    exact Multiplicative.toAdd.injective (markedRootPoint_injective M.toIntegralMarking (F.obj R) a h')
  obtain ⟨S⟩ := relativeParameterRepresentability k k
  obtain ⟨u, r, hc, hu, hr⟩ := relativeRankOneSchemeRealization G S.additive S.rankOne
    S.additivePoints S.rankOnePoints (upperParameters k) ρ hinj
  exact ⟨⟨S.additive, S.rankOne, S.additivePoints, S.rankOnePoints, u, r, hc, hu, ρ, hr⟩, hρ⟩

end RelativeRootModels

section OrderedRelativeRoots

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.IntegralRootRelations (upper)
open scoped CategoryTheory.MonObj

universe u

private theorem orbitPoint_natural {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k))
    {R S : TestAlgebra k} (f : R ⟶ S) (b : TransportedOrbit D) (v : orbitParameter K R b) :
    (integralPointFunctor M.group).map ((quadraticIntegralAlgebra k K).map f)
        (orbitPoint M σ R b v) = orbitPoint M σ S b (orbitParameterMap K f b v) := by
  let E := quadraticIntegralAlgebra k K
  let j := ((integralPointFunctor M.group).map (E.map f)).hom
  have hw (l : List D.I) : j (markedWeylWord M (E.obj R) l) = markedWeylWord M (E.obj S) l :=
    markedWeylWord_map M (E.map f) l
  have hx (i : D.I) (z : E.obj R) :
      j (markedRootPoint M (E.obj R) i z) = markedRootPoint M (E.obj S) i ((E.map f).hom z) :=
    markedRootPoint_map M (E.map f) i z
  rcases b with ⟨⟨a, b⟩, w⟩
  let l := w.flatMap SimpleRootOrbit.roots
  let n := fun T : TestAlgebra k => markedWeylWord M (E.obj T) l
  cases b with
  | none =>
    let i (T : TestAlgebra k) : T →ₐ[k] K ⊗[k] T := Algebra.TensorProduct.includeRight
    change j (n R * markedRootPoint M (E.obj R) a (i R v) * (n R)⁻¹) =
      n S * markedRootPoint M (E.obj S) a (i S (f.hom v)) * (n S)⁻¹
    have hn : j (n R) = n S := hw l
    rw [map_mul, map_mul, map_inv, hn, hx a (i R v)]
    rfl
  | some b =>
    change j (n R * (markedRootPoint M (E.obj R) a v *
      markedRootPoint M (E.obj R) b (quadraticCoefficientEquiv σ R v)) * (n R)⁻¹) =
      n S * (markedRootPoint M (E.obj S) a ((E.map f).hom v) *
        markedRootPoint M (E.obj S) b (quadraticCoefficientEquiv σ S ((E.map f).hom v))) * (n S)⁻¹
    have hc (x : K ⊗[k] R) :
        (E.map f).hom (quadraticCoefficientEquiv σ R x) =
          quadraticCoefficientEquiv σ S ((E.map f).hom x) := quadraticCoefficientEquiv_natural σ f x
    have hn : j (n R) = n S := hw l
    rw [map_mul, map_mul, map_mul, map_inv, hn, hx a v, hx b (quadraticCoefficientEquiv σ R v), hc v]

private theorem orderedOrbitPoint_natural {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k))
    {R S : TestAlgebra k} (f : R ⟶ S) (bs : List (TransportedOrbit D))
    (v : orderedParameters K R bs) :
    (integralPointFunctor M.group).map ((quadraticIntegralAlgebra k K).map f)
        (orderedOrbitPoint M σ R bs v) = orderedOrbitPoint M σ S bs (orderedParametersMap K f bs v) := by
  let E := quadraticIntegralAlgebra k K
  let j := ((integralPointFunctor M.group).map (E.map f)).hom
  change j _ = _
  induction bs with
  | nil => exact map_one j
  | cons b bs ih =>
    change j (orbitPoint M σ R b v.1 * orderedOrbitPoint M σ R bs v.2) =
      orbitPoint M σ S b (orbitParameterMap K f b v.1) *
        orderedOrbitPoint M σ S bs (orderedParametersMap K f bs v.2)
    rw [map_mul, orbitPoint_natural M σ f b v.1, ih v.2]

set_option maxHeartbeats 950000 in
theorem pinnedOrderedRootProducts : PinnedOrderedRootProducts.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs bs hbs
  obtain ⟨emb, he, hf⟩ := pinnedMarkedPointEmbedding C d
  let E := quadraticIntegralAlgebra k K
  let H := convolutionPoints (Specs.AdjointCocharacters.coordinateHopf G)
  have hsingle (R : TestAlgebra k) (b : TransportedOrbit D)
      (hb : b.1.Matches C (pinnedDiagram d σ) ∧ ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ))
      (v : orbitParameter K R b) :
        orbitPoint M.toIntegralMarking σ R b v ∈ Set.range (emb.app R) := by
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b with
    | none =>
      obtain ⟨H, hr⟩ := pinnedSingletonRootModel C d hdegree σ hσ hs w hb.2 a hb.1
      refine ⟨H.pointMap.app R (upper v), ?_⟩
      rw [he, hr]
      dsimp only
      rw [map_upperMatrix, M.rankOneUpper]
      rfl
    | some b =>
      obtain ⟨H, hr⟩ := pinnedPairRootModel C d hdegree σ hσ hs w hb.2 a b hb.1
      refine ⟨H.pointMap.app R (upper v), ?_⟩
      rw [he, hr]
      dsimp only
      rw [map_upperMatrix, M.rankOneUpper, M.rankOneUpper]
      rfl
  have hrange (R : TestAlgebra k) (v : orderedParameters K R bs) :
      orderedOrbitPoint M.toIntegralMarking σ R bs v ∈ Set.range (emb.app R) := by
    let j := (emb.app R).hom
    change _ ∈ Set.range j
    induction bs with
    | nil => exact ⟨1, map_one j⟩
    | cons b bs ih =>
      obtain ⟨p, hp⟩ := hsingle R b (hbs b List.mem_cons_self) v.1
      obtain ⟨q, hq⟩ := ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) v.2
      refine ⟨p * q, ?_⟩
      change j (p * q) = orbitPoint M.toIntegralMarking σ R b v.1 *
        orderedOrbitPoint M.toIntegralMarking σ R bs v.2
      rw [map_mul]
      exact congrArg₂ (· * ·) hp hq
  let product (R : TestAlgebra k) (v : orderedParameters K R bs) : H.obj R :=
    Classical.choose (hrange R v)
  have hp (R : TestAlgebra k) (v : orderedParameters K R bs) :
      emb.app R (product R v) = orderedOrbitPoint M.toIntegralMarking σ R bs v :=
    Classical.choose_spec (hrange R v)
  refine ⟨product, fun R v => (he R (product R v)).symm.trans (hp R v), ?_⟩
  intro R S f v
  apply (hf S).1
  have hn := ConcreteCategory.congr_hom (emb.naturality f) (product R v)
  change emb.app S (H.map f (product R v)) =
    (integralPointFunctor M.group).map (E.map f) (emb.app R (product R v)) at hn
  rw [hn, hp, hp, orderedOrbitPoint_natural]

end OrderedRelativeRoots

section RationalParameters

set_option backward.isDefEq.respectTransparency false

open Specs.IntegralSemisimpleModel Specs.Pinning
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] integerAlgebra

set_option maxHeartbeats 950000 in
theorem pinnedRationalPairedRankOne : PinnedRationalPairedRankOne.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw a b hm
  obtain ⟨H, hH⟩ := pinnedPairRootModel C d hdegree σ hσ hs w hw a b hm
  let R := CommAlgCat.of k k
  let S := CommAlgCat.of Integers.{u} K
  let U := (quadraticIntegralAlgebra k K).obj R
  let e := Algebra.TensorProduct.rid k K K
  let f := evaluateGroundTensor k K
  let s := SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom
  let t := SpecialLinearGroup.map (n := Fin 2) e.toRingHom
  let c := SpecialLinearGroup.map (n := Fin 2) (quadraticCoefficientEquiv σ R).toRingHom
  let ρ := (H.pointMap.app R).hom.comp s
  have ht (A : SpecialLinearGroup (Fin 2) K) : t (s A) = A := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (A.val i j)
  have hc (A : SpecialLinearGroup (Fin 2) K) : t (c (s A)) =
      SpecialLinearGroup.map σ.toRingHom A := by
    apply Subtype.ext
    ext i j
    change e (σ (A.val i j) ⊗ₜ[k] (1 : k)) = σ (A.val i j)
    simp only [e, Algebra.TensorProduct.rid_tmul, one_smul]
  let j := ((integralPointFunctor M.group).map f).hom
  have hn (i : D.I) (A : SpecialLinearGroup (Fin 2) U) :
      j ((M.rankOne i).app U A) = (M.rankOne i).app S (t A) :=
    (ConcreteCategory.congr_hom ((M.rankOne i).naturality f) A).symm
  let n := fun T : IntegralAlgebra.{u} => markedWeylWord M.toIntegralMarking T
    (w.flatMap SimpleRootOrbit.roots)
  have hword : j (n U) = n S := markedWeylWord_map M.toIntegralMarking f _
  refine ⟨ρ, fun A => ?_⟩
  change j (pinnedMarkedPoint C d R (H.pointMap.app R (s A))) = _
  rw [hH R (s A)]
  let x : IntegralPoints M.group U := (M.rankOne a).app U (s A)
  let y : IntegralPoints M.group U := (M.rankOne b).app U (c (s A))
  change j (n U * (x * y) * (n U)⁻¹) = _
  have hx := hn a (s A)
  have hy := hn b (c (s A))
  rw [ht A] at hx
  rw [hc A] at hy
  rw [map_mul, map_mul, map_mul, map_inv, hword, show j x = _ from hx, show j y = _ from hy]

theorem integralUnitValuation : IntegralUnitValuation.{u} := by
  intro K _ _ _ _ c z
  let f : Integers.{u} ≃+* ℤ := ULift.ringEquiv
  have e : c = 1 ∨ c = -1 := by
    rcases Int.units_eq_one_or (Units.map f.toMonoidHom c) with h | h
    · left
      apply Units.ext
      apply f.injective
      have h' := congrArg (fun x : ℤˣ => (x : ℤ)) h
      change f (c : Integers.{u}) = 1 at h'
      simpa only [Units.val_one, map_one]
    · right
      apply Units.ext
      apply f.injective
      have h' := congrArg (fun x : ℤˣ => (x : ℤ)) h
      change f (c : Integers.{u}) = -1 at h'
      simpa only [Units.val_neg, Units.val_one, map_neg, map_one]
  rcases e with rfl | rfl
  · simp
  · simp

end RationalParameters

section GroupedCoordinates

set_option backward.isDefEq.respectTransparency false

open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonObj

universe u

private theorem orbitAbsoluteLabels {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (b : TransportedOrbit D) (z : orbitParameter K R b) :
    (orbitAbsoluteCoordinates σ R c b z).map Prod.fst = transportedLabels b := by
  rcases b with ⟨⟨a, b⟩, w⟩
  cases b <;> rfl

theorem orderedOrbitAbsoluteComparison : OrderedOrbitAbsoluteComparison.{u} := by
  classical
  intro D M
  let c (b : TransportedOrbit D) (i : D.I) :=
    (integralWeylWordTransport M (b.2.flatMap SimpleRootOrbit.roots) i).choose
  have hc (b : TransportedOrbit D) (i : D.I) (S : IntegralAlgebra.{u}) (z : S) :=
    (integralWeylWordTransport M (b.2.flatMap SimpleRootOrbit.roots) i).choose_spec S z
  refine ⟨c, ?_⟩
  intro k K _ _ _ σ R bs v S p
  have hblock (b : TransportedOrbit D) (v : orbitParameter K R b) :
      orbitPoint M.toIntegralMarking σ R b v =
        ((orbitAbsoluteCoordinates σ R c b v).map
          fun p => markedRootPoint M.toIntegralMarking S p.1 p.2).prod := by
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b with
    | none =>
      simpa only [orbitPoint, orbitAbsoluteCoordinates, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one] using
          hc ((a, none), w) a S ((Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) v)
    | some b =>
      let n := markedWeylWord M.toIntegralMarking S (w.flatMap SimpleRootOrbit.roots)
      let x := markedRootPoint M.toIntegralMarking S
      have hi : n * (x a v * x b (quadraticCoefficientEquiv σ R v)) * n⁻¹ =
          (n * x a v * n⁻¹) * (n * x b (quadraticCoefficientEquiv σ R v) * n⁻¹) := by group
      simp only [orbitPoint, orbitAbsoluteCoordinates, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      exact hi.trans (congrArg₂ (· * ·) (hc ((a, some b), w) a S v)
        (hc ((a, some b), w) b S (quadraticCoefficientEquiv σ R v)))
  dsimp only [p]
  induction bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨hkey, hprod⟩ := ih v.2
    exact ⟨by
      simp only [orderedAbsoluteCoordinates, List.map_append, List.flatMap_cons,
        orbitAbsoluteLabels, hkey], by
      simp only [orderedAbsoluteCoordinates, List.map_append, List.prod_append, orderedOrbitPoint,
        hblock, hprod]⟩

private theorem integralUnit_mul_injective (S : IntegralAlgebra.{u}) (c : Integers.{u}ˣ) :
    Function.Injective (fun z : S => algebraMap Integers.{u} S (c : Integers.{u}) * z) := by
  let x := Units.map (algebraMap Integers.{u} S).toMonoidHom c
  intro z w h
  change (x : S) * z = (x : S) * w at h
  have hh := congrArg (fun d => (↑x⁻¹ : S) * d) h
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using hh

private theorem orderedAbsoluteCoordinates_injective {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) (l : List (TransportedOrbit D)) :
    Function.Injective (orderedAbsoluteCoordinates σ R c l) := by
  induction l with
  | nil =>
    intro a b _
    change PUnit at a b
    exact Subsingleton.elim a b
  | cons b l ih =>
    let S := (quadraticIntegralAlgebra k K).obj R
    rcases b with ⟨⟨a, b⟩, w⟩
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    let z := orderedAbsoluteCoordinates σ R c l
    cases b with
    | none =>
      let x (u : R) : S :=
        let v : S := (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) u
        algebraMap Integers.{u} S (c ((a, none), w) a : Integers.{u}) * v
      intro v v' h
      change (p a, x v.1) :: z v.2 = (p a, x v'.1) :: z v'.2 at h
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      have hv := integralUnit_mul_injective S (c ((a, none), w) a) (congrArg Prod.snd h₁)
      exact Prod.ext (includeRight_injective (k := k) (K := K) (R := R) hv) (ih h₂)
    | some b =>
      let x (u : S) : S := algebraMap Integers.{u} S (c ((a, some b), w) a : Integers.{u}) * u
      let y (u : S) : S :=
        let v : S := quadraticCoefficientEquiv σ R u
        algebraMap Integers.{u} S (c ((a, some b), w) b : Integers.{u}) * v
      intro v v' h
      change (p a, x v.1) :: (p b, y v.1) :: z v.2 =
        (p a, x v'.1) :: (p b, y v'.1) :: z v'.2 at h
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      exact Prod.ext (integralUnit_mul_injective S (c ((a, some b), w) a)
        (congrArg Prod.snd h₁)) (ih (List.cons.inj h₂).2)

private theorem exists_values_of_nodup {I A : Type u} [DecidableEq I] [Inhabited A]
    (l : List (I × A)) (h : (l.map Prod.fst).Nodup) :
    ∃ f : I → A, ∀ p ∈ l, f p.1 = p.2 := by
  induction l with
  | nil => exact ⟨fun _ => default, by simp⟩
  | cons a l ih =>
    obtain ⟨hn, hl⟩ := List.nodup_cons.mp h
    obtain ⟨f, hf⟩ := ih hl
    refine ⟨fun i => if i = a.1 then a.2 else f i, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hh : p.1 ≠ a.1 := fun e => hn (e ▸ List.mem_map_of_mem hp)
      simp [hh, hf p hp]

private theorem list_eq_of_values {I A : Type u} (l : List (I × A))
    (f : I → A) (h : ∀ p ∈ l, f p.1 = p.2) :
    l = (l.map Prod.fst).map (fun i => (i, f i)) := by
  rw [List.map_map]
  trans l.map id
  · rw [List.map_id]
  · exact List.map_congr_left (fun p hp => Prod.ext rfl (h p hp).symm)

set_option maxHeartbeats 1150000 in
theorem markedRelativeCellCoordinates : MarkedRelativeCellCoordinates.{u} := by
  classical
  intro D M k K _ _ _ σ R ns ps hn hp S N P T
  obtain ⟨c, hc⟩ := orderedOrbitAbsoluteComparison M
  let n := ns.flatMap transportedLabels
  let p := ps.flatMap transportedLabels
  let X := orderedParameters K R ns × T × orderedParameters K R ps
  let u := orderedAbsoluteCoordinates σ R c ns
  let v := orderedAbsoluteCoordinates σ R c ps
  have hx (q : X) : ∃ w : D.I → S,
      u q.1 = n.map (fun i => (i, w i)) ∧
      v q.2.2 = p.map (fun i => (i, w i)) := by
    have hkeys : ((u q.1) ++ (v q.2.2)).map Prod.fst = n ++ p := by
      rw [List.map_append, (hc σ R ns q.1).1, (hc σ R ps q.2.2).1]
    have hnodup : (n ++ p).Nodup := by
      refine List.nodup_append.mpr ⟨hn.1, hp.1, ?_⟩
      rintro a ha b hb rfl
      exact ((hn.2 a).mp ha) ((hp.2 a).mp hb)
    obtain ⟨w, hw⟩ := exists_values_of_nodup (u q.1 ++ v q.2.2) (hkeys ▸ hnodup)
    refine ⟨w, ?_, ?_⟩
    · exact (list_eq_of_values _ w (fun i hi => hw i (List.mem_append_left _ hi))).trans
        (congrArg (List.map fun i => (i, w i)) (hc σ R ns q.1).1)
    · exact (list_eq_of_values _ w (fun i hi => hw i (List.mem_append_right _ hi))).trans
        (congrArg (List.map fun i => (i, w i)) (hc σ R ps q.2.2).1)
  let w (q : X) := (hx q).choose
  have hu (q : X) : u q.1 = n.map (fun i => (i, w q i)) := (hx q).choose_spec.1
  have hv (q : X) : v q.2.2 = p.map (fun i => (i, w q i)) := (hx q).choose_spec.2
  have hinj : Function.Injective (fun q : X => (w q, q.2.1)) := by
    intro q q' h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    have hn' : u q.1 = u q'.1 := by rw [hu, hu, h₁]
    have hp' : v q.2.2 = v q'.2.2 := by rw [hv, hv, h₁]
    exact Prod.ext (orderedAbsoluteCoordinates_injective σ R c ns hn')
      (Prod.ext h₂ (orderedAbsoluteCoordinates_injective σ R c ps hp'))
  have hN (q : X) : N q.1 = orderedRootPoint M.toIntegralMarking S n (w q) := by
    have h := (hc σ R ns q.1).2
    change N q.1 = ((u q.1).map fun x => markedRootPoint M.toIntegralMarking S x.1 x.2).prod at h
    rw [hu, List.map_map] at h
    exact h
  have hP (q : X) : P q.2.2 = orderedRootPoint M.toIntegralMarking S p (w q) := by
    have h := (hc σ R ps q.2.2).2
    change P q.2.2 = ((v q.2.2).map fun x => markedRootPoint M.toIntegralMarking S x.1 x.2).prod at h
    rw [hv, List.map_map] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro q q' e
    apply hinj
    apply (markedCellCoordinates M.toIntegralMarking S n p hn hp).1
    unfold markedCellPoint
    simpa only [hN, hP] using e
  · intro q q' e
    apply hinj
    have hn' : Enumerates n.reverse {i | ¬ D.base.IsPos i} :=
      ⟨List.nodup_reverse.mpr hn.1, fun i => List.mem_reverse.trans (hn.2 i)⟩
    have hp' : Enumerates p.reverse {i | D.base.IsPos i} :=
      ⟨List.nodup_reverse.mpr hp.1, fun i => List.mem_reverse.trans (hp.2 i)⟩
    apply (markedCellCoordinates M.toIntegralMarking S n.reverse p.reverse hn' hp').2
    simpa only [List.reverse_reverse, hN, hP] using e

end GroupedCoordinates

section ValuedRankOne

open Specs.IntegralRootRelations (upper lower diagonal)

universe u

theorem valuedRankOneWall : ValuedRankOneWall.{u} := by
  intro K _ _ _ _ G _ ρ j v
  obtain ⟨⟨a, ha⟩, hdepth⟩ := wallDepths K j
  obtain ⟨hz, ht⟩ := hdepth a ha
  have hm := wallMatrixRelations a a
  refine ⟨a, ha, ?_, ?_, ?_, ?_⟩
  · change ρ (upper (-(a : K)) * lower (-(↑(-a)⁻¹ : K)) * upper (-(a : K))) = _
    simp only [map_mul, inv_neg, Units.val_neg, neg_neg]
  · exact (map_pow ρ _ _).symm.trans (congrArg ρ hm.2.2.1)
  · intro z
    exact ⟨by simpa only [map_mul, map_inv] using congrArg ρ ((hm.2.2.2.1 z).1),
      by simpa only [map_mul, map_inv] using congrArg ρ ((hm.2.2.2.1 z).2), (hz z).1, (hz z).2⟩
  · intro t ht'
    exact ⟨by simpa only [map_mul] using congrArg ρ (wallMatrixRelations a t).2.2.2.2,
      ht t ht'⟩

end ValuedRankOne

section FixedRelativeRootCoordinates

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralRootRelations (upper)
open Specs.IntegralSemisimpleModel Specs.Pinning
open scoped CategoryTheory.MonObj

universe u

set_option maxHeartbeats 1250000 in
theorem pinnedTransportedOrbitFixedParameters : PinnedTransportedOrbitFixedParameters.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw R S n x fixed
  obtain ⟨emb, he, hf⟩ := pinnedMarkedPointEmbedding C d
  obtain ⟨e, hE⟩ := markedFibrePointComparison C
  let U := (extendedTestAlgebra k K).obj R
  let φ := (e.app U).groupIsoToMulEquiv
  let τ := MonoidHom.mk' (pinnedSchemeAction d σ R) (pinnedSchemeAction_mul C d σ R)
  let f := φ.toMonoidHom.comp (τ.comp φ.symm.toMonoidHom)
  have hφ (p : GroupPoints C.realization.pinned.pair.G.val U) :
      f (markedFibrePoint C U p) = markedFibrePoint C U (pinnedSchemeAction d σ R p) := by
    rw [← hE, ← hE]
    change φ (pinnedSchemeAction d σ R (φ.symm (φ p))) = φ (pinnedSchemeAction d σ R p)
    rw [MulEquiv.symm_apply_apply]
  have hfix (z : IntegralPoints M.group S) : z ∈ fixed ↔ f z = z := by
    let p := φ.symm z
    have hp : markedFibrePoint C U p = z := (hE U p).symm.trans (φ.apply_symm_apply z)
    change z ∈ Set.range (pinnedMarkedPoint C d R) ↔ _
    rw [show pinnedMarkedPoint C d R = (emb.app R : _ → _) from (funext (he R)).symm,
      ← hp, (hf R).2, hφ]
    constructor
    · intro h
      rw [h σ]
    · intro h
      have h' := φ.injective ((hE _ _).trans (h.trans (hE _ _).symm))
      intro g
      rcases (quadraticGalois hdegree σ hσ).1 g with hg | hg
      · rw [hg]
        exact pinnedSchemeAction_one C d R p
      · rw [hg]
        exact h'
  have hn : f n = n := by
    apply (hfix n).mp
    exact pinnedWeylWordFixed C d hdegree σ hσ hs w hw R
  let cd := quadraticCoefficientEquiv σ R
  let eI := C.realization.datumIso.val.indexEquiv
  have hx (a b : D.base.support)
      (h : transportCharacter (pinnedDiagram d σ).asIso.hom.torus (eI a).val = (eI b).val)
      (z : K ⊗[k] R) : f (x a z) = x b (cd z) := by
    let p := φ.symm (x a z)
    have hp : markedFibrePoint C U p = x a z :=
      (hE U p).symm.trans (φ.apply_symm_apply _)
    rw [← hp, hφ]
    rw [markedSchemeActionRankOne C d σ a b h R (upper z) p (hp.trans (M.rankOneUpper a S z).symm),
      map_upperMatrix, M.rankOneUpper]
    rfl
  have hp := quadraticParameterDescent hdegree σ hσ R
  refine ⟨?_, ?_⟩
  · intro a ha u
    rw [hfix, map_mul, map_mul, map_inv, hn, hx a a ha]
    change (MulAut.conj n) (x a (cd u)) = (MulAut.conj n) (x a u) ↔ _
    rw [(MulAut.conj n).injective.eq_iff, (markedRootPoint_injective M.toIntegralMarking S a).eq_iff]
    exact (quadraticCoefficientEquiv_apply σ R u) ▸ hp.2.1 u
  · intro a b h u v
    obtain ⟨hab, ha, hb⟩ := h
    have hne : (a : D.I) ≠ b := by
      intro hh
      rw [hh, RootPairing.pairing_same] at hab
      norm_num at hab
    have hcomm : Commute (x a (cd v)) (x b (cd u)) := by
      have h := markedOrthogonalRankOneCommutation M hs a b hab K
        (CommAlgCat.of K (K ⊗[k] R)) (upper (cd v)) (upper (cd u))
      change Commute ((M.rankOne a).app S (upper (cd v)) : IntegralPoints M.group S)
        ((M.rankOne b).app S (upper (cd u))) at h
      rw [M.rankOneUpper, M.rankOneUpper] at h
      exact h
    have hsign : D.base.IsPos a ↔ D.base.IsPos b :=
      iff_of_true (D.base.isPos_of_mem_support a.property) (D.base.isPos_of_mem_support b.property)
    rw [hfix, map_mul, map_mul, map_mul, map_inv, hn, hx a b ha, hx b a hb, ← hcomm.eq]
    change (MulAut.conj n) (x a (cd v) * x b (cd u)) =
      (MulAut.conj n) (x a u * x b v) ↔ v = cd u
    rw [(MulAut.conj n).injective.eq_iff]
    let g : S × S → IntegralPoints M.group S := fun p => x a p.1 * x b p.2
    change g (cd v, cd u) = g (u, v) ↔ _
    rw [(markedRootPairInjectivity M.toIntegralMarking S a b hne hsign).eq_iff]
    exact (by simpa only [← quadraticCoefficientEquiv_apply σ R] using hp.2.2.1 u v)

end FixedRelativeRootCoordinates

section SplitCellCoordinates

set_option backward.isDefEq.respectTransparency false

open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonObj

universe u

theorem transportedIntegralCoordinates : TransportedIntegralCoordinates.{u} := by
  intro D M
  choose c hc using fun (b : TransportedOrbit D) (a : D.I) =>
    integralWeylWordTransport M (b.2.flatMap SimpleRootOrbit.roots) a
  exact ⟨c, fun S b a z => hc b a S z⟩

theorem transportedOrbitParameterComparison : TransportedOrbitParameterComparison.{u} := by
  intro k K _ _ _ D M σ R bs v S
  have hblock (b : TransportedOrbit D) (z : orbitParameter K R b) :
      splitOrbitPoint M S b (extendOrbitParameter σ R b z) = orbitPoint M σ R b z := by
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b with
    | none => rfl
    | some b =>
      let n := markedWeylWord M S (w.flatMap SimpleRootOrbit.roots)
      let x := markedRootPoint M S
      let c := quadraticCoefficientEquiv σ R
      change (n * x a z * n⁻¹) * (n * x b (c z) * n⁻¹) = n * (x a z * x b (c z)) * n⁻¹
      group
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change splitOrbitPoint M S b (extendOrbitParameter σ R b v.1) *
      splitOrderedOrbitPoint M S bs (extendOrderedParameters σ R bs v.2) =
      orbitPoint M σ R b v.1 * orderedOrbitPoint M σ R bs v.2
    rw [hblock, ih]

private def transportUnit (S : IntegralAlgebra.{u}) (c : Integers.{u}ˣ) : Sˣ :=
  Units.map (algebraMap Integers.{u} S).toMonoidHom c

private def splitOrbitValues {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) :
    (b : TransportedOrbit D) → splitOrbitParameter S b → List (D.I × S)
  | (⟨a, none⟩, w) => fun z =>
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    [(p a, (transportUnit S (c ((a, none), w) a) : S) * (show S from z))]
  | (⟨a, some b⟩, w) => fun z =>
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    [(p a, (transportUnit S (c ((a, some b), w) a) : S) * z.1),
      (p b, (transportUnit S (c ((a, some b), w) b) : S) * z.2)]

private def splitOrderedValues {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) :
    (bs : List (TransportedOrbit D)) → splitOrderedParameters S bs → List (D.I × S)
  | [] => fun _ => []
  | b :: bs => fun v => splitOrbitValues S c b v.1 ++ splitOrderedValues S c bs v.2

private theorem splitOrderedValues_labels {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (bs : List (TransportedOrbit D)) (v : splitOrderedParameters S bs) :
    (splitOrderedValues S c bs v).map Prod.fst = bs.flatMap transportedLabels := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (splitOrbitValues S c b v.1 ++ splitOrderedValues S c bs v.2).map Prod.fst =
      transportedLabels b ++ bs.flatMap transportedLabels
    rw [List.map_append, ih]
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b <;> rfl

private theorem splitOrderedValues_injective {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) (bs : List (TransportedOrbit D)) :
    Function.Injective (splitOrderedValues S c bs) := by
  induction bs with
  | nil =>
    intro u v _
    change PUnit at u v
    exact Subsingleton.elim u v
  | cons b bs ih =>
    rcases b with ⟨⟨a, b⟩, w⟩
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    let f := splitOrderedValues S c bs
    cases b with
    | none =>
      let C := transportUnit S (c ((a, none), w) a)
      intro u v h
      change (p a, (C : S) * (show S from u.1)) :: f u.2 =
        (p a, (C : S) * (show S from v.1)) :: f v.2 at h
      obtain ⟨h₁, h₂⟩ := List.cons.inj h
      exact Prod.ext (integralUnit_mul_injective S _ (congrArg Prod.snd h₁)) (ih h₂)
    | some b =>
      let C := transportUnit S (c ((a, some b), w) a)
      let E := transportUnit S (c ((a, some b), w) b)
      intro u v h
      change (p a, (C : S) * u.1.1) :: (p b, (E : S) * u.1.2) :: f u.2 =
        (p a, (C : S) * v.1.1) :: (p b, (E : S) * v.1.2) :: f v.2 at h
      obtain ⟨h₁, h⟩ := List.cons.inj h
      obtain ⟨h₂, h₃⟩ := List.cons.inj h
      exact Prod.ext (Prod.ext (integralUnit_mul_injective S _ (congrArg Prod.snd h₁))
        (integralUnit_mul_injective S _ (congrArg Prod.snd h₂))) (ih h₃)

private def splitOrbitFromValues {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) (v : D.I → S) :
    (b : TransportedOrbit D) → splitOrbitParameter S b
  | (⟨a, none⟩, w) =>
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    (↑(transportUnit S (c ((a, none), w) a))⁻¹ : S) * v (p a)
  | (⟨a, some b⟩, w) =>
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    ((↑(transportUnit S (c ((a, some b), w) a))⁻¹ : S) * v (p a),
      (↑(transportUnit S (c ((a, some b), w) b))⁻¹ : S) * v (p b))

private def splitOrderedFromValues {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) (v : D.I → S) :
    (bs : List (TransportedOrbit D)) → splitOrderedParameters S bs
  | [] => PUnit.unit
  | b :: bs => (splitOrbitFromValues S c v b, splitOrderedFromValues S c v bs)

private theorem splitOrderedValues_fromValues {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) (v : D.I → S)
    (bs : List (TransportedOrbit D)) :
    splitOrderedValues S c bs (splitOrderedFromValues S c v bs) =
      (bs.flatMap transportedLabels).map (fun a => (a, v a)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [splitOrderedValues, splitOrderedFromValues, List.flatMap_cons, List.map_append, ih]
    congr 1
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b <;>
      simp only [splitOrbitValues, splitOrbitFromValues, ← mul_assoc, Units.mul_inv,
        one_mul, transportedLabels, SimpleRootOrbit.roots, Option.toList, List.map_cons,
        List.map_nil]

private theorem splitOrderedOrbitPoint_values {D : BasedRootDatum.{u}} (M : Model D)
    (S : IntegralAlgebra.{u}) (c : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (hc : ∀ b a z, transportedRootPoint M.toIntegralMarking S b a z =
      markedRootPoint M.toIntegralMarking S (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) a)
        ((transportUnit S (c b a) : S) * z))
    (bs : List (TransportedOrbit D)) (v : splitOrderedParameters S bs) :
    splitOrderedOrbitPoint M.toIntegralMarking S bs v =
      ((splitOrderedValues S c bs v).map
        fun p => markedRootPoint M.toIntegralMarking S p.1 p.2).prod := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [splitOrderedOrbitPoint, splitOrderedValues, List.map_append, List.prod_append,
      ← ih]
    congr 1
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b <;> simp only [splitOrbitPoint, splitOrbitValues, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, hc]

private theorem markedAbsoluteCell_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (ns ps : List D.I)
    (hn : Enumerates ns {a | ¬ D.base.IsPos a}) (hp : Enumerates ps {a | D.base.IsPos a})
    (positiveFirst : Bool) : Function.Injective (markedAbsoluteCell M S ns ps positiveFirst) := by
  cases positiveFirst
  · exact (markedCellCoordinates M S ns ps hn hp).1
  · have hn' : Enumerates ns.reverse {a | ¬ D.base.IsPos a} :=
      ⟨List.nodup_reverse.mpr hn.1, fun i => List.mem_reverse.trans (hn.2 i)⟩
    have hp' : Enumerates ps.reverse {a | D.base.IsPos a} :=
      ⟨List.nodup_reverse.mpr hp.1, fun i => List.mem_reverse.trans (hp.2 i)⟩
    change Function.Injective (fun q : (D.I → S) × IntegralPoints (splitTorus D) S =>
      orderedRootPoint M S ps q.1 * ((q.2 ≫ M.torus.hom.hom) * orderedRootPoint M S ns q.1))
    simpa only [List.reverse_reverse] using (markedCellCoordinates M S ns.reverse ps.reverse hn' hp').2

set_option maxHeartbeats 950000 in
theorem markedSplitCellCoordinates : MarkedSplitCellCoordinates.{u} := by
  classical
  intro D M S ns ps hn hp positiveFirst
  letI : Inhabited S := ⟨0⟩
  obtain ⟨c, hc⟩ := transportedIntegralCoordinates M
  let n := ns.flatMap transportedLabels
  let p := ps.flatMap transportedLabels
  let X := splitOrderedParameters S ns × IntegralPoints (splitTorus D) S × splitOrderedParameters S ps
  let N := splitOrderedValues S c ns
  let P := splitOrderedValues S c ps
  have hcoords (q : X) : ∃ v : D.I → S,
      N q.1 = n.map (fun a => (a, v a)) ∧ P q.2.2 = p.map (fun a => (a, v a)) := by
    have hlabels : (N q.1 ++ P q.2.2).map Prod.fst = n ++ p := by
      rw [List.map_append, splitOrderedValues_labels S c ns q.1, splitOrderedValues_labels S c ps q.2.2]
    have hnodup : (n ++ p).Nodup := by
      refine List.nodup_append.mpr ⟨hn.1, hp.1, ?_⟩
      rintro a ha b hb rfl
      exact ((hn.2 a).mp ha) ((hp.2 a).mp hb)
    obtain ⟨v, hv⟩ := exists_values_of_nodup (N q.1 ++ P q.2.2) (hlabels ▸ hnodup)
    exact ⟨v, (list_eq_of_values _ v (fun i hi => hv i (List.mem_append_left _ hi))).trans
      (congrArg _ (splitOrderedValues_labels S c ns q.1)),
      (list_eq_of_values _ v (fun i hi => hv i (List.mem_append_right _ hi))).trans
      (congrArg _ (splitOrderedValues_labels S c ps q.2.2))⟩
  let f := markedSplitCell M.toIntegralMarking S ns ps positiveFirst
  let g := markedAbsoluteCell M.toIntegralMarking S n p positiveFirst
  have hcomp (q : X) (v : D.I → S) (hn' : N q.1 = n.map (fun a => (a, v a)))
      (hp' : P q.2.2 = p.map (fun a => (a, v a))) : f q = g (v, q.2.1) := by
    have hN := splitOrderedOrbitPoint_values M S c (hc S) ns q.1
    have hP := splitOrderedOrbitPoint_values M S c (hc S) ps q.2.2
    change _ = ((N q.1).map _).prod at hN
    change _ = ((P q.2.2).map _).prod at hP
    rw [hn', List.map_map] at hN
    rw [hp', List.map_map] at hP
    unfold f g markedSplitCell markedAbsoluteCell orderedRootPoint
    rw [hN, hP]
    rfl
  change Function.Injective f ∧ Set.range f = Set.range g
  constructor
  · intro q q' h
    obtain ⟨v, hn₁, hp₁⟩ := hcoords q
    obtain ⟨v', hn₂, hp₂⟩ := hcoords q'
    have hh : (v, q.2.1) = (v', q'.2.1) :=
      markedAbsoluteCell_injective M.toIntegralMarking S n p hn hp positiveFirst
        ((hcomp q v hn₁ hp₁).symm.trans (h.trans (hcomp q' v' hn₂ hp₂)))
    obtain ⟨hv, ht⟩ := Prod.mk.inj hh
    exact Prod.ext (splitOrderedValues_injective S c ns
      (show N q.1 = N q'.1 by rw [hn₁, hn₂, hv]))
      (Prod.ext ht (splitOrderedValues_injective S c ps
        (show P q.2.2 = P q'.2.2 by rw [hp₁, hp₂, hv])))
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      obtain ⟨v, hn', hp'⟩ := hcoords q
      exact ⟨(v, q.2.1), (hcomp q v hn' hp').symm⟩
    · rintro _ ⟨⟨v, t⟩, rfl⟩
      exact ⟨(splitOrderedFromValues S c v ns, t, splitOrderedFromValues S c v ps),
        hcomp _ v (splitOrderedValues_fromValues S c v ns) (splitOrderedValues_fromValues S c v ps)⟩

end SplitCellCoordinates

section PinnedTorusPoints

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

private theorem restrictExtended_comp (R : TestAlgebra k) {H J : HopfAlgebraCategory k}
    (f : H ⟶ J) (v : extendedHopf K J →ₐ[K] K ⊗[k] R) :
    (AlgHom.liftEquiv k K H (K ⊗[k] R)).symm
      (v.comp (extendedHopfMap K f).hom.toAlgHom) =
      ((AlgHom.liftEquiv k K J (K ⊗[k] R)).symm v).comp f.hom.toAlgHom := by
  apply AlgHom.ext
  intro x
  rfl

private theorem torusComparison_comm (R : TestAlgebra k)
    (v : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf (closedSubgroupAlgebraicGroup T))
      →ₐ[K] K ⊗[k] R) :
    (v.comp (extendedHopfMap K
      (coordinateHopfMap (G := closedSubgroupAlgebraicGroup T) (H := G)
        T.inclusion)).hom.toAlgHom).comp d.groupIso.hom.hom.toAlgHom =
      (v.comp d.torusIso.hom.hom.toAlgHom).comp (extendedHopfMap K
        (coordinateHopfMap (G := closedSubgroupAlgebraicGroup C.realization.pinned.pair.T)
          (H := C.realization.pinned.pair.G)
          C.realization.pinned.pair.T.inclusion)).hom.toAlgHom := by
  apply AlgHom.ext
  intro x
  exact congrArg v (ConcreteCategory.congr_hom d.torusComm x)

set_option maxHeartbeats 650000 in
private theorem pinnedTorusSchemePoint_incl (R : TestAlgebra k)
    (t : HopfPoints (Specs.AdjointCocharacters.coordinateHopf (closedSubgroupAlgebraicGroup T)) R) :
    pinnedSchemePoint d R (descendedTorusInclusion R t) =
      pinnedTorusSchemePoint C d R t ≫ C.realization.pinned.pair.T.inclusion.hom.hom := by
  let v := extendAlgebraPoint (K := K) t.ofConv
  let j := coordinateHopfMap (G := closedSubgroupAlgebraicGroup T) (H := G) T.inclusion
  have he : extendAlgebraPoint (K := K) (descendedTorusInclusion (G := G) R t).ofConv =
      v.comp (extendedHopfMap K j).hom.toAlgHom := by
    apply (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf G) (K ⊗[k] R)).symm.injective
    rw [restrictExtended_comp]
    dsimp only [v, extendAlgebraPoint, descendedTorusInclusion]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, AlgHom.comp_assoc]
  unfold pinnedSchemePoint pinnedTorusSchemePoint pinnedAlgebraPointMap
  rw [he, torusComparison_comm C d, restrictExtended_comp]
  exact coordinatePointEquiv_comp
    (G := closedSubgroupAlgebraicGroup C.realization.pinned.pair.T)
    (H := C.realization.pinned.pair.G) C.realization.pinned.pair.T.inclusion _ _

set_option maxHeartbeats 900000 in
private theorem pinnedTorusSchemePoint_range (R : TestAlgebra k)
    (s : GroupPoints C.realization.pinned.pair.T.group ((extendedTestAlgebra k K).obj R))
    (p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) R)
    (h : pinnedSchemePoint d R p = s ≫ C.realization.pinned.pair.T.inclusion.hom.hom) :
    s ∈ Set.range (pinnedTorusSchemePoint C d R) := by
  let U := (extendedTestAlgebra k K).obj R
  let H := C.realization.pinned.pair.G
  let A := closedSubgroupAlgebraicGroup C.realization.pinned.pair.T
  let J := closedSubgroupAlgebraicGroup T
  let r₀ := coordinateHopfMap (G := A) (H := H) C.realization.pinned.pair.T.inclusion
  let r₁ := coordinateHopfMap (G := J) (H := G) T.inclusion
  let e := coordinatePointEquiv A U
  let a := (e.symm s).ofConv
  let aE := AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf A) (K ⊗[k] R) a
  let bE := aE.comp d.torusIso.inv.hom.toAlgHom
  have hs : pinnedAlgebraPointMap d p.ofConv =
      aE.comp (extendedHopfMap K r₀).hom.toAlgHom := by
    apply (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf H) (K ⊗[k] R)).symm.injective
    rw [restrictExtended_comp]
    dsimp only [aE]
    rw [Equiv.symm_apply_apply]
    have hi := (coordinatePointEquiv_comp C.realization.pinned.pair.T.inclusion U (e.symm s))
    change coordinatePointEquiv H U (WithConv.toConv (a.comp r₀.hom.toAlgHom)) =
      e (e.symm s) ≫ C.realization.pinned.pair.T.inclusion.hom.hom at hi
    rw [MulEquiv.apply_symm_apply] at hi
    exact congrArg WithConv.ofConv ((coordinatePointEquiv H U).injective (h.trans hi.symm))
  have ht : bE.comp d.torusIso.hom.hom.toAlgHom = aE := by
    apply AlgHom.ext
    intro x
    exact congrArg aE (ConcreteCategory.congr_hom d.torusIso.hom_inv_id x)
  have hq := torusComparison_comm C d R bE
  rw [ht, ← hs] at hq
  have hbE : extendAlgebraPoint (K := K) p.ofConv =
      bE.comp (extendedHopfMap K r₁).hom.toAlgHom := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso d.groupIso.hom).surjective x
    exact (DFunLike.congr_fun hq y).symm
  let b := (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf J) (K ⊗[k] R)).symm bE
  let i : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  have hb := congrArg
    (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf G) (K ⊗[k] R)).symm hbE
  rw [restrictExtended_comp, extendAlgebraPoint, Equiv.symm_apply_apply] at hb
  change i.comp p.ofConv = b.comp r₁.hom.toAlgHom at hb
  have hr₁ : Function.Surjective r₁.hom := (hopfMapClosedImmersion k r₁).mp (by
    rw [coordinatePresentation (G := J) (H := G) T.inclusion]
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    letI : IsClosedImmersion (F.map T.inclusion) := T.isClosedImmersion
    change IsClosedImmersion (F.map ((coordinateHopfIso J).hom ≫ T.inclusion ≫
      (coordinateHopfIso G).inv))
    simp only [F.map_comp]
    infer_instance)
  have hmem (x : Specs.AdjointCocharacters.coordinateHopf J) : b x ∈ i.range := by
    obtain ⟨y, rfl⟩ := hr₁ x
    exact ⟨p.ofConv y, DFunLike.congr_fun hb y⟩
  let iE : R ≃ₐ[k] i.range := AlgEquiv.ofInjective i includeRight_injective
  let q := iE.symm.toAlgHom.comp (b.codRestrict i.range hmem)
  have hqE : extendAlgebraPoint (K := K) q = bE := by
    apply (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf J) (K ⊗[k] R)).symm.injective
    rw [extendAlgebraPoint, Equiv.symm_apply_apply]
    change i.comp q = b
    apply AlgHom.ext
    intro x
    exact congrArg Subtype.val (iE.apply_symm_apply ⟨b x, hmem x⟩)
  refine ⟨WithConv.toConv q, ?_⟩
  unfold pinnedTorusSchemePoint
  change e (WithConv.toConv
    ((AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf A) (K ⊗[k] R)).symm
      ((extendAlgebraPoint q).comp d.torusIso.hom.hom.toAlgHom))) = s
  rw [hqE, ht]
  dsimp only [aE]
  rw [Equiv.symm_apply_apply]
  exact e.apply_symm_apply s

set_option maxHeartbeats 650000 in
theorem pinnedMarkedTorusPointComparison : PinnedMarkedTorusPointComparison.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d R
  let U := (extendedTestAlgebra k K).obj R
  let e := markedTorusEquiv C U
  have he (t) : pinnedMarkedTorusPoint C d R t = e (pinnedTorusSchemePoint C d R t) := rfl
  have hj (t) : pinnedMarkedPoint C d R (descendedTorusInclusion R t) =
      pinnedMarkedTorusPoint C d R t ≫ M.torus.hom.hom := by
    unfold pinnedMarkedPoint
    rw [pinnedTorusSchemePoint_incl C d, markedTorusIncl, he]
  refine ⟨?_, hj, ?_⟩
  · intro t t' h
    apply WithConv.ofConv_injective
    apply extendAlgebraPoint_injective (K := K)
    have h' := e.injective ((he t).symm.trans (h.trans (he t')))
    unfold pinnedTorusSchemePoint at h'
    have h'' := (AlgHom.liftEquiv k K _ (K ⊗[k] R)).symm.injective
      (congrArg WithConv.ofConv ((coordinatePointEquiv _ U).injective h'))
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso d.torusIso.hom).surjective x
    exact DFunLike.congr_fun h'' y
  · intro s
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨descendedTorusInclusion R t, hj t⟩
    · rintro ⟨p, hp⟩
      let z := e.symm s
      have hz : markedFibrePoint C U (z ≫ C.realization.pinned.pair.T.inclusion.hom.hom) =
          s ≫ M.torus.hom.hom := by rw [markedTorusIncl, e.apply_symm_apply]
      have h := (fibrePointEquiv C U).injective (hp.trans hz.symm)
      obtain ⟨t, ht⟩ := pinnedTorusSchemePoint_range C d R z p h
      exact ⟨t, (he t).trans ((congrArg e ht).trans (e.apply_symm_apply s))⟩

end PinnedTorusPoints

section PinnedFixedCells

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralRootRelations (upper)
open Specs.IntegralSemisimpleModel Specs.Pinning
open scoped CategoryTheory.MonObj

universe u

private def actOnSplitOrbitParameters {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k) :
    (b : TransportedOrbit D) → splitOrbitParameter (K ⊗[k] R) b →
      splitOrbitParameter (K ⊗[k] R) b
  | (⟨_, none⟩, _) => fun z => quadraticCoefficientEquiv σ R z
  | (⟨_, some _⟩, _) => fun z =>
    (quadraticCoefficientEquiv σ R z.2, quadraticCoefficientEquiv σ R z.1)

private def actOnSplitOrderedParameters {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k) :
    (bs : List (TransportedOrbit D)) → splitOrderedParameters (K ⊗[k] R) bs →
      splitOrderedParameters (K ⊗[k] R) bs
  | [] => id
  | b :: bs => fun p =>
    (actOnSplitOrbitParameters σ R b p.1, actOnSplitOrderedParameters σ R bs p.2)

private theorem extendOrderedParameters_injective {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
    (bs : List (TransportedOrbit D)) : Function.Injective (extendOrderedParameters σ R bs) := by
  have hblock (b : TransportedOrbit D) : Function.Injective (extendOrbitParameter σ R b) := by
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b with
    | none => exact includeRight_injective (k := k) (K := K) (R := R)
    | some b => exact fun _ _ h => congrArg Prod.fst h
  induction bs with
  | nil =>
    intro a b _
    change PUnit at a b
    exact Subsingleton.elim a b
  | cons b bs ih =>
    intro v w h
    change (extendOrbitParameter σ R b v.1, extendOrderedParameters σ R bs v.2) =
      (extendOrbitParameter σ R b w.1, extendOrderedParameters σ R bs w.2) at h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (hblock b h₁) (ih h₂)

private theorem extendOrderedParameters_range {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1) (R : TestAlgebra k)
    (bs : List (TransportedOrbit D)) (v : splitOrderedParameters (K ⊗[k] R) bs) :
    actOnSplitOrderedParameters σ R bs v = v ↔ v ∈ Set.range (extendOrderedParameters σ R bs) := by
  have hblock (b : TransportedOrbit D) (z : splitOrbitParameter (K ⊗[k] R) b) :
      actOnSplitOrbitParameters σ R b z = z ↔ z ∈ Set.range (extendOrbitParameter σ R b) := by
    have h := quadraticParameterDescent hdegree σ hσ R
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b with
    | none =>
      change quadraticCoefficientEquiv σ R z = z ↔
        z ∈ Set.range (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)
      rw [quadraticCoefficientEquiv_apply]
      exact h.2.1 z
    | some b =>
      let τ := quadraticCoefficientEquiv σ R
      change (K ⊗[k] R) × (K ⊗[k] R) at z
      rcases z with ⟨u, v⟩
      change (τ v, τ u) = (u, v) ↔ (u, v) ∈ Set.range (fun x => (x, τ x))
      have he : (τ v, τ u) = (u, v) ↔ v = τ u := by
        simpa only [τ, ← quadraticCoefficientEquiv_apply σ R] using h.2.2.1 u v
      rw [he]
      exact ⟨fun hh => ⟨u, Prod.ext rfl hh.symm⟩,
        fun ⟨x, hx⟩ => (congrArg Prod.snd hx).symm.trans (congrArg τ (congrArg Prod.fst hx))⟩
  induction bs with
  | nil => exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩, fun _ => rfl⟩
  | cons b bs ih =>
    constructor
    · intro h
      change (actOnSplitOrbitParameters σ R b v.1, actOnSplitOrderedParameters σ R bs v.2) =
        (v.1, v.2) at h
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
      obtain ⟨z, hz⟩ := (hblock b v.1).mp h₁
      obtain ⟨w, hw⟩ := (ih v.2).mp h₂
      exact ⟨(z, w), Prod.ext hz hw⟩
    · rintro ⟨u, hu⟩
      have h₁ := (hblock b v.1).mpr ⟨u.1, congrArg Prod.fst hu⟩
      have h₂ := (ih v.2).mpr ⟨u.2, congrArg Prod.snd hu⟩
      exact Prod.ext h₁ h₂

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

private def markedCellAction (σ : Gal(K/k)) (R : TestAlgebra k) :
    IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R) →*
      IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R) :=
  let e := fibrePointEquiv C ((extendedTestAlgebra k K).obj R)
  let τ := MonoidHom.mk' (pinnedSchemeAction d σ R) (pinnedSchemeAction_mul C d σ R)
  e.toMonoidHom.comp (τ.comp e.symm.toMonoidHom)

private theorem markedCellAction_apply (σ : Gal(K/k)) (R : TestAlgebra k)
    (p : GroupPoints C.realization.pinned.pair.G.val ((extendedTestAlgebra k K).obj R)) :
    markedCellAction C d σ R (markedFibrePoint C ((extendedTestAlgebra k K).obj R) p) =
      markedFibrePoint C ((extendedTestAlgebra k K).obj R) (pinnedSchemeAction d σ R p) := by
  let e := fibrePointEquiv C ((extendedTestAlgebra k K).obj R)
  change e (pinnedSchemeAction d σ R (e.symm (e p))) = e (pinnedSchemeAction d σ R p)
  rw [MulEquiv.symm_apply_apply]

private theorem markedCellAction_fixed_iff [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1) (R : TestAlgebra k)
    (v : IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R)) :
    v ∈ Set.range (pinnedMarkedPoint C d R) ↔ markedCellAction C d σ R v = v := by
  let U := (extendedTestAlgebra k K).obj R
  let e := fibrePointEquiv C U
  obtain ⟨p, rfl⟩ := e.surjective v
  have he : e p = markedFibrePoint C U p := rfl
  rw [he, markedCellAction_apply]
  have hmem : markedFibrePoint C U p ∈ Set.range (pinnedMarkedPoint C d R) ↔
      p ∈ Set.range (pinnedSchemePoint d R) :=
    ⟨fun ⟨q, hq⟩ => ⟨q, e.injective hq⟩, fun ⟨q, hq⟩ => ⟨q, congrArg e hq⟩⟩
  rw [hmem, pinnedSchemePoint_fixed_iff]
  constructor
  · intro h
    rw [h σ]
  · intro h g
    rcases (quadraticGalois hdegree σ hσ).1 g with hg | hg
    · rw [hg]
      exact pinnedSchemeAction_one C d R p
    · rw [hg]
      exact e.injective h

private theorem markedCellAction_simpleRoot (σ : Gal(K/k)) (R : TestAlgebra k)
    (a b : D.base.support)
    (h : transportCharacter (pinnedDiagram d σ).asIso.hom.torus
      (C.realization.datumIso.val.indexEquiv a).val =
      (C.realization.datumIso.val.indexEquiv b).val) (z : K ⊗[k] R) :
    let S := (quadraticIntegralAlgebra k K).obj R
    markedCellAction C d σ R (markedRootPoint M.toIntegralMarking S a z) =
      markedRootPoint M.toIntegralMarking S b (quadraticCoefficientEquiv σ R z) := by
  intro S
  let U := (extendedTestAlgebra k K).obj R
  let e := fibrePointEquiv C U
  let x := markedRootPoint M.toIntegralMarking S a z
  let p := e.symm x
  have hp : markedFibrePoint C U p = x := e.apply_symm_apply x
  change markedCellAction C d σ R x = _
  rw [← hp, markedCellAction_apply]
  rw [markedSchemeActionRankOne C d σ a b h R (upper z) p (hp.trans (M.rankOneUpper a S z).symm),
    map_upperMatrix, M.rankOneUpper]
  rfl

private theorem markedCellAction_torus (σ : Gal(K/k)) (R : TestAlgebra k)
    (t : IntegralPoints (splitTorus D) ((quadraticIntegralAlgebra k K).obj R)) :
    ∃ t' : IntegralPoints (splitTorus D) ((quadraticIntegralAlgebra k K).obj R),
      markedCellAction C d σ R (t ≫ M.torus.hom.hom) = t' ≫ M.torus.hom.hom := by
  let U := (extendedTestAlgebra k K).obj R
  let e := markedTorusEquiv C U
  let s := e.symm t
  let f := (pinnedDiagram d σ).asIso.hom
  let i := C.realization.pinned.pair.T.inclusion.hom.hom
  let s' : GroupPoints C.realization.pinned.pair.T.group U :=
    mapPoints (conjugateTestAlgebra σ R) s ≫ f.torus.hom.hom.hom
  have he : markedFibrePoint C U (s ≫ i) = t ≫ M.torus.hom.hom := by
    rw [markedTorusIncl, e.apply_symm_apply]
  have hi : i ≫ f.group.hom.hom.hom = f.torus.hom.hom.hom ≫ i :=
    congrArg (fun j => j.hom.hom) f.torus_comm
  have hs : pinnedSchemeAction d σ R (s ≫ i) = s' ≫ i := by
    have h := congrArg (fun j => mapPoints (conjugateTestAlgebra σ R) s ≫ j) hi
    simpa only [pinnedSchemeAction, s', mapPoints, Category.assoc, f] using h
  refine ⟨e s', ?_⟩
  rw [← he, markedCellAction_apply, hs, markedTorusIncl]

private theorem markedModelTorusInclusion_injective {D : BasedRootDatum.{u}}
    (M : IntegralMarking D) (S : IntegralAlgebra.{u}) :
    Function.Injective (fun t : IntegralPoints (splitTorus D) S => t ≫ M.torus.hom.hom) := by
  have := M.torusClosed
  have : Mono M.torus.hom.hom := Over.mono_of_mono_left _
  exact fun _ _ h => (cancel_mono M.torus.hom.hom).mp h

set_option maxHeartbeats 650000 in
private theorem markedCellAction_orbit [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1)
    (hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i) (R : TestAlgebra k)
    (b : TransportedOrbit D) (hb : b.1.Matches C (pinnedDiagram d σ))
    (hw : ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ))
    (v : splitOrbitParameter (K ⊗[k] R) b) :
    let S := (quadraticIntegralAlgebra k K).obj R
    markedCellAction C d σ R (splitOrbitPoint M.toIntegralMarking S b v) =
      splitOrbitPoint M.toIntegralMarking S b (actOnSplitOrbitParameters σ R b v) := by
  intro S
  let n := markedWeylWord M.toIntegralMarking S (b.2.flatMap SimpleRootOrbit.roots)
  let x := markedRootPoint M.toIntegralMarking S
  let τ := markedCellAction C d σ R
  have hn : τ n = n :=
    (markedCellAction_fixed_iff C d hdegree σ hσ R n).mp
      (pinnedWeylWordFixed C d hdegree σ hσ hs b.2 hw R)
  rcases b with ⟨⟨a, b⟩, w⟩
  let g := quadraticCoefficientEquiv σ R
  cases b with
  | none =>
    change τ (n * x a v * n⁻¹) = n * x a (g v) * n⁻¹
    rw [map_mul, map_mul, map_inv, hn, markedCellAction_simpleRoot C d σ R a a hb]
  | some b =>
    obtain ⟨hab, ha, hb⟩ := hb
    change τ ((n * x a v.1 * n⁻¹) * (n * x b v.2 * n⁻¹)) =
      (n * x a (g v.2) * n⁻¹) * (n * x b (g v.1) * n⁻¹)
    have hcomm : Commute (x a (g v.2)) (x b (g v.1)) := by
      have h := markedOrthogonalRankOneCommutation M hs a b hab K
        (CommAlgCat.of K (K ⊗[k] R)) (upper (g v.2)) (upper (g v.1))
      change Commute ((M.rankOne a).app S (upper (g v.2)) : IntegralPoints M.group S)
        ((M.rankOne b).app S (upper (g v.1))) at h
      rw [M.rankOneUpper, M.rankOneUpper] at h
      exact h
    have hx : τ (x a v.1) = x b (g v.1) := markedCellAction_simpleRoot C d σ R a b ha v.1
    have hy : τ (x b v.2) = x a (g v.2) := markedCellAction_simpleRoot C d σ R b a hb v.2
    simp only [map_mul, map_inv, hn, hx, hy]
    exact (hcomm.map (MulAut.conj n).toMonoidHom).eq.symm

private theorem markedCellAction_ordered [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1)
    (hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i) (R : TestAlgebra k)
    (bs : List (TransportedOrbit D))
    (hbs : ∀ b ∈ bs, b.1.Matches C (pinnedDiagram d σ) ∧
      ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ)) (v : splitOrderedParameters (K ⊗[k] R) bs) :
    let S := (quadraticIntegralAlgebra k K).obj R
    markedCellAction C d σ R (splitOrderedOrbitPoint M.toIntegralMarking S bs v) =
      splitOrderedOrbitPoint M.toIntegralMarking S bs (actOnSplitOrderedParameters σ R bs v) := by
  intro S
  induction bs with
  | nil => exact map_one _
  | cons b bs ih =>
    obtain ⟨hb, hw⟩ := hbs b List.mem_cons_self
    have h : markedCellAction C d σ R (splitOrbitPoint M.toIntegralMarking S b v.1) =
        splitOrbitPoint M.toIntegralMarking S b (actOnSplitOrbitParameters σ R b v.1) :=
      markedCellAction_orbit C d hdegree σ hσ hs R b hb hw v.1
    simp only [splitOrderedOrbitPoint, actOnSplitOrderedParameters, map_mul,
      h,
      ih (fun a ha => hbs a (List.mem_cons_of_mem b ha))]

private theorem map_triangularProduct {H J : Type*} [Monoid H] [Monoid J] (f : H →* J)
    (positiveFirst : Bool) (n t p : H) :
    f (triangularProduct positiveFirst n t p) = triangularProduct positiveFirst (f n) (f t) (f p) := by
  cases positiveFirst <;> simp [triangularProduct, map_mul]

set_option maxHeartbeats 1050000 in
theorem pinnedFixedCellCoordinates : PinnedFixedCellCoordinates.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hdegree σ hσ hs ns ps hbs hn hp R positiveFirst abs rel
  let S := (quadraticIntegralAlgebra k K).obj R
  let g := markedSplitCell M.toIntegralMarking S ns ps positiveFirst
  let τ := markedCellAction C d σ R
  let eN := extendOrderedParameters σ R ns
  let eP := extendOrderedParameters σ R ps
  let eT := pinnedMarkedTorusPoint C d R
  let aN := actOnSplitOrderedParameters σ R ns
  let aP := actOnSplitOrderedParameters σ R ps
  let incl := fun t : IntegralPoints (splitTorus D) S => t ≫ M.torus.hom.hom
  obtain ⟨hg, hgRange⟩ := markedSplitCellCoordinates M S ns ps hn hp positiveFirst
  obtain ⟨heT, _, htRange⟩ := pinnedMarkedTorusPointComparison C d R
  have hN (v : splitOrderedParameters S ns) :
      τ (splitOrderedOrbitPoint M.toIntegralMarking S ns v) =
        splitOrderedOrbitPoint M.toIntegralMarking S ns (aN v) :=
    markedCellAction_ordered C d hdegree σ hσ hs R ns
    (fun b hb => hbs b (List.mem_append_left ps hb))
      v
  have hP (v : splitOrderedParameters S ps) :
      τ (splitOrderedOrbitPoint M.toIntegralMarking S ps v) =
        splitOrderedOrbitPoint M.toIntegralMarking S ps (aP v) :=
    markedCellAction_ordered C d hdegree σ hσ hs R ps
    (fun b hb => hbs b (List.mem_append_right ns hb))
      v
  have hchart (q : splitOrderedParameters S ns × IntegralPoints (splitTorus D) S ×
      splitOrderedParameters S ps) : g q ∈ Set.range (pinnedMarkedPoint C d R) ↔
        q.1 ∈ Set.range eN ∧ q.2.1 ∈ Set.range eT ∧ q.2.2 ∈ Set.range eP := by
    obtain ⟨s, ht⟩ := markedCellAction_torus C d σ R q.2.1
    change τ (incl q.2.1) = incl s at ht
    have hτ : τ (g q) = g (aN q.1, s, aP q.2.2) := by
      change τ (triangularProduct positiveFirst (splitOrderedOrbitPoint M.toIntegralMarking S ns q.1)
        (incl q.2.1) (splitOrderedOrbitPoint M.toIntegralMarking S ps q.2.2)) =
        triangularProduct positiveFirst (splitOrderedOrbitPoint M.toIntegralMarking S ns (aN q.1))
          (incl s) (splitOrderedOrbitPoint M.toIntegralMarking S ps (aP q.2.2))
      rw [map_triangularProduct, hN, ht, hP]
    have hi : s = q.2.1 ↔ q.2.1 ∈ Set.range eT := by
      rw [htRange, markedCellAction_fixed_iff C d hdegree σ hσ]
      change s = q.2.1 ↔ τ (incl q.2.1) = incl q.2.1
      rw [ht, (markedModelTorusInclusion_injective M.toIntegralMarking S).eq_iff]
    rw [markedCellAction_fixed_iff C d hdegree σ hσ, hτ, hg.eq_iff]
    change (aN q.1, s, aP q.2.2) = (q.1, q.2.1, q.2.2) ↔ _
    rw [Prod.mk.injEq, Prod.mk.injEq, hi, extendOrderedParameters_range hdegree σ hσ,
      extendOrderedParameters_range hdegree σ hσ]
  constructor
  · intro u v h
    have hi : (eN u.1, eT u.2.1, eP u.2.2) = (eN v.1, eT v.2.1, eP v.2.2) := hg h
    obtain ⟨hn', h'⟩ := Prod.mk.inj hi
    obtain ⟨ht', hp'⟩ := Prod.mk.inj h'
    exact Prod.ext (extendOrderedParameters_injective σ R ns hn')
      (Prod.ext (heT ht') (extendOrderedParameters_injective σ R ps hp'))
  · have hr : Set.range g = Set.range abs := hgRange
    rw [← hr]
    apply Set.Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      let v := (eN q.1, eT q.2.1, eP q.2.2)
      exact ⟨⟨v, rfl⟩, (hchart v).mpr ⟨⟨q.1, rfl⟩, ⟨q.2.1, rfl⟩, ⟨q.2.2, rfl⟩⟩⟩
    · rintro _ ⟨⟨q, rfl⟩, hfix⟩
      obtain ⟨⟨u, hu⟩, ⟨t, ht⟩, ⟨v, hv⟩⟩ := (hchart q).mp hfix
      exact ⟨(u, t, v), congrArg g (Prod.ext hu (Prod.ext ht hv))⟩

end PinnedFixedCells

section RationalCellCoordinates

set_option backward.isDefEq.respectTransparency false

open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] integerAlgebra

private def groundTensorIso (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (quadraticIntegralAlgebra k K).obj (CommAlgCat.of k k) ≅ CommAlgCat.of Integers.{u} K :=
  let e := Algebra.TensorProduct.rid k K K
  CommAlgCat.isoMk
    { e.toRingEquiv with
      commutes' n := map_intCast e.toRingHom n.down }

private def rationalOrbitEquiv {D : BasedRootDatum.{u}} (k K : Type u)
    [Field k] [Field K] [Algebra k K] :
    (b : TransportedOrbit D) → orbitParameter K (CommAlgCat.of k k) b ≃ rationalOrbitParameter k K b
  | (⟨_, none⟩, _) => Equiv.refl k
  | (⟨_, some _⟩, _) => (Algebra.TensorProduct.rid k K K).toEquiv

private def rationalOrderedEquiv {D : BasedRootDatum.{u}} (k K : Type u)
    [Field k] [Field K] [Algebra k K] :
    (bs : List (TransportedOrbit D)) →
      orderedParameters K (CommAlgCat.of k k) bs ≃ rationalOrderedParameters k K bs
  | [] => Equiv.refl PUnit
  | b :: bs => (rationalOrbitEquiv k K b).prodCongr (rationalOrderedEquiv k K bs)

private theorem evaluateGroundTensor_conjugate {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) (x : K ⊗[k] k) :
    (evaluateGroundTensor k K).hom (quadraticCoefficientEquiv σ (CommAlgCat.of k k) x) =
      σ ((evaluateGroundTensor k K).hom x) := by
  let e := Algebra.TensorProduct.rid k K K
  obtain ⟨z, rfl⟩ := e.symm.surjective x
  change e (σ z ⊗ₜ[k] (1 : k)) = σ (e (e.symm z))
  rw [e.apply_symm_apply]
  simp only [e, Algebra.TensorProduct.rid_tmul, one_smul]

private theorem transportedRootPoint_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S U : IntegralAlgebra.{u}} (f : S ⟶ U) (b : TransportedOrbit D) (a : D.I) (z : S) :
    (integralPointFunctor M.group).map f (transportedRootPoint M S b a z) =
      transportedRootPoint M U b a (f.hom z) := by
  let j := ((integralPointFunctor M.group).map f).hom
  let w := b.2.flatMap SimpleRootOrbit.roots
  change j (markedWeylWord M S w * markedRootPoint M S a z * (markedWeylWord M S w)⁻¹) =
    markedWeylWord M U w * markedRootPoint M U a (f.hom z) * (markedWeylWord M U w)⁻¹
  rw [map_mul, map_mul, map_inv]
  have hword : j (markedWeylWord M S w) = markedWeylWord M U w := markedWeylWord_map M f w
  have hx : j (markedRootPoint M S a z) = markedRootPoint M U a (f.hom z) :=
    markedRootPoint_map M f a z
  rw [hword, hx]

private theorem evaluateOrderedCoordinates {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k))
    (bs : List (TransportedOrbit D)) (v : orderedParameters K (CommAlgCat.of k k) bs) :
    let R := CommAlgCat.of k k
    let S := (quadraticIntegralAlgebra k K).obj R
    let U := CommAlgCat.of Integers.{u} K
    (integralPointFunctor M.group).map (evaluateGroundTensor k K)
        (splitOrderedOrbitPoint M S bs (extendOrderedParameters σ R bs v)) =
      splitOrderedOrbitPoint M U bs (rationalOrderedCoordinates σ bs (rationalOrderedEquiv k K bs v)) := by
  intro R S U
  let f := evaluateGroundTensor k K
  let j := ((integralPointFunctor M.group).map f).hom
  have hblock (b : TransportedOrbit D) (z : orbitParameter K R b) :
      j (splitOrbitPoint M S b (extendOrbitParameter σ R b z)) =
        splitOrbitPoint M U b (rationalOrbitCoordinates σ b (rationalOrbitEquiv k K b z)) := by
    rcases b with ⟨⟨a, b⟩, w⟩
    cases b with
    | none =>
      let block : TransportedOrbit D := ((a, none), w)
      let i : k →ₐ[k] K ⊗[k] k := Algebra.TensorProduct.includeRight
      change j (transportedRootPoint M S block a (i z)) =
        transportedRootPoint M U block a (algebraMap k K z)
      rw [show j (transportedRootPoint M S block a (i z)) =
        transportedRootPoint M U block a (f.hom (i z)) from transportedRootPoint_map M f block a (i z)]
      congr 1
      change (Algebra.TensorProduct.rid k K K) (1 ⊗ₜ[k] (show k from z)) = algebraMap k K z
      simp only [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
    | some b =>
      let block : TransportedOrbit D := ((a, some b), w)
      let w' : U := f.hom z
      change j (transportedRootPoint M S block a z *
        transportedRootPoint M S block b (quadraticCoefficientEquiv σ R z)) =
        transportedRootPoint M U block a w' * transportedRootPoint M U block b (σ w')
      rw [map_mul]
      exact congrArg₂ (· * ·) (transportedRootPoint_map M f block a z)
        ((transportedRootPoint_map M f block b (quadraticCoefficientEquiv σ R z)).trans
          (congrArg (transportedRootPoint M U block b) (evaluateGroundTensor_conjugate σ z)))
  induction bs with
  | nil => exact map_one j
  | cons b bs ih =>
    change j (splitOrbitPoint M S b (extendOrbitParameter σ R b v.1) *
      splitOrderedOrbitPoint M S bs (extendOrderedParameters σ R bs v.2)) =
      splitOrbitPoint M U b (rationalOrbitCoordinates σ b (rationalOrbitEquiv k K b v.1)) *
        splitOrderedOrbitPoint M U bs (rationalOrderedCoordinates σ bs (rationalOrderedEquiv k K bs v.2))
    have ht : j (splitOrderedOrbitPoint M S bs (extendOrderedParameters σ R bs v.2)) =
        splitOrderedOrbitPoint M U bs
          (rationalOrderedCoordinates σ bs (rationalOrderedEquiv k K bs v.2)) := ih v.2
    rw [map_mul, hblock, ht]

private theorem orderedRootPoint_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S U : IntegralAlgebra.{u}} (f : S ⟶ U) (xs : List D.I) (v : D.I → S) :
    (integralPointFunctor M.group).map f (orderedRootPoint M S xs v) =
      orderedRootPoint M U xs (fun a => f.hom (v a)) := by
  let j := ((integralPointFunctor M.group).map f).hom
  induction xs with
  | nil => exact map_one j
  | cons a xs ih =>
    change j (markedRootPoint M S a (v a) * orderedRootPoint M S xs v) =
      markedRootPoint M U a (f.hom (v a)) * orderedRootPoint M U xs (fun a => f.hom (v a))
    rw [map_mul]
    exact congrArg₂ (· * ·) (markedRootPoint_map M f a (v a)) ih

private theorem markedTorusPoint_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S U : IntegralAlgebra.{u}} (f : S ⟶ U) (t : IntegralPoints (splitTorus D) S) :
    (integralPointFunctor M.group).map f (t ≫ M.torus.hom.hom) =
      (integralPointFunctor (splitTorus D)).map f t ≫ M.torus.hom.hom := by
  change integralSpec.map f.op ≫ (t ≫ M.torus.hom.hom) =
    (integralSpec.map f.op ≫ t) ≫ M.torus.hom.hom
  exact (Category.assoc _ _ _).symm

private theorem range_eq_image {A B H J : Type*} (f : A → H) (g : B → J) (j : H → J)
    (r : A → B) (hr : Function.Surjective r) (h : ∀ x, g (r x) = j (f x)) :
    Set.range g = j '' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨f a, ⟨a, rfl⟩, (h a).symm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨r a, h a⟩

set_option maxHeartbeats 1350000 in
theorem pinnedRationalFixedCellCoordinates : PinnedRationalFixedCellCoordinates.{u} := by
  intro k K _ _ _ _ _ D M C l G B T d hd σ hσ hs ns ps hb hn hp positiveFirst abs rel fix
  let R := CommAlgCat.of k k
  let S := (quadraticIntegralAlgebra k K).obj R
  let U := CommAlgCat.of Integers.{u} K
  let f := evaluateGroundTensor k K
  let j := ((integralPointFunctor M.group).map f).hom
  let jT := ((integralPointFunctor (splitTorus D)).map f).hom
  have hj : Function.Injective j :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective
  have hjT : Function.Surjective jT :=
    (((integralPointFunctor (splitTorus D)).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).surjective
  let ns' := ns.flatMap transportedLabels
  let ps' := ps.flatMap transportedLabels
  let absS := markedAbsoluteCell M.toIntegralMarking S ns' ps' positiveFirst
  let relS := pinnedRelativeCell C d σ R ns ps positiveFirst
  have hAbs (q : (D.I → S) × IntegralPoints (splitTorus D) S) :
      abs (fun a => f.hom (q.1 a), jT q.2) = j (absS q) := by
    symm
    change j (triangularProduct positiveFirst (orderedRootPoint M.toIntegralMarking S ns' q.1)
      (q.2 ≫ M.torus.hom.hom) (orderedRootPoint M.toIntegralMarking S ps' q.1)) =
      triangularProduct positiveFirst (orderedRootPoint M.toIntegralMarking U ns' (fun a => f.hom (q.1 a)))
        (jT q.2 ≫ M.torus.hom.hom) (orderedRootPoint M.toIntegralMarking U ps' (fun a => f.hom (q.1 a)))
    have ht : j (q.2 ≫ M.torus.hom.hom) = jT q.2 ≫ M.torus.hom.hom :=
      markedTorusPoint_map M.toIntegralMarking f q.2
    rw [map_triangularProduct, ht]
    congr 1
    · exact orderedRootPoint_map M.toIntegralMarking f ns' q.1
    · exact orderedRootPoint_map M.toIntegralMarking f ps' q.1
  have hAbsRange : Set.range abs = j '' Set.range absS := by
    refine range_eq_image absS abs j _ ?_ hAbs
    rintro ⟨v, t⟩
    obtain ⟨t', ht⟩ := hjT t
    let e := Algebra.TensorProduct.rid k K K
    refine ⟨(e.symm ∘ v, t'), Prod.ext ?_ ht⟩
    funext a
    exact e.apply_symm_apply (v a)
  let X := HopfPoints (Specs.AdjointCocharacters.coordinateHopf (closedSubgroupAlgebraicGroup T)) k
  let e := (rationalOrderedEquiv k K ns).prodCongr
    ((Equiv.refl X).prodCongr (rationalOrderedEquiv k K ps))
  have hRel (q) : rel (e q) = j (relS q) := by
    symm
    let x := splitOrderedOrbitPoint M.toIntegralMarking S ns
      (extendOrderedParameters σ R ns q.1)
    let y := splitOrderedOrbitPoint M.toIntegralMarking S ps
      (extendOrderedParameters σ R ps q.2.2)
    let t := pinnedMarkedTorusPoint C d R q.2.1
    change j (triangularProduct positiveFirst x (t ≫ M.torus.hom.hom) y) =
      triangularProduct positiveFirst
        (splitOrderedOrbitPoint M.toIntegralMarking U ns
          (rationalOrderedCoordinates σ ns (rationalOrderedEquiv k K ns q.1)))
        (jT t ≫ M.torus.hom.hom) (splitOrderedOrbitPoint M.toIntegralMarking U ps
          (rationalOrderedCoordinates σ ps (rationalOrderedEquiv k K ps q.2.2)))
    have ht : j (t ≫ M.torus.hom.hom) = jT t ≫ M.torus.hom.hom :=
      markedTorusPoint_map M.toIntegralMarking f t
    rw [map_triangularProduct, ht]
    congr 1
    · exact evaluateOrderedCoordinates M.toIntegralMarking σ ns q.1
    · exact evaluateOrderedCoordinates M.toIntegralMarking σ ps q.2.2
  have hRelRange : Set.range rel = j '' Set.range relS :=
    range_eq_image relS rel j e e.surjective hRel
  have hFixRange : Set.range fix = j '' Set.range (pinnedMarkedPoint C d R) := by
    change Set.range (j ∘ pinnedMarkedPoint C d R) = _
    exact Set.range_comp _ _
  obtain ⟨hr, hrange⟩ := pinnedFixedCellCoordinates C d hd σ hσ hs ns ps hb hn hp R positiveFirst
  have hrange' : Set.range relS = Set.range absS ∩ Set.range (pinnedMarkedPoint C d R) := hrange
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    exact congrArg e (hr (hj ((hRel a).symm.trans (h.trans (hRel b)))))
  · rw [hRelRange, hrange', Set.image_inter hj, ← hAbsRange, ← hFixRange]

end RationalCellCoordinates

section RationalTorusConjugation

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.IntegralRootRelations (upper)
open Specs.IntegralSemisimpleModel Specs.Pinning
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

open private affineTorusPointEquiv from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem evaluateGroundTensor_includeRight {k K : Type u} [Field k] [Field K]
    [Algebra k K] (z : k) :
    (evaluateGroundTensor k K).hom ((Algebra.TensorProduct.includeRight : k →ₐ[k] K ⊗[k] k) z) =
      algebraMap k K z := by
  change Algebra.TensorProduct.rid k K K (1 ⊗ₜ[k] z) = _
  simp only [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

private theorem markedWeylWord_torusConjugation {D : BasedRootDatum.{u}} (M : Model D)
    (S : IntegralAlgebra.{u}) (w : List D.I) (s : TorusValues D S) (a : D.I) (z : S) :
    let n := markedWeylWord M.toIntegralMarking S w
    let t := torusPoint D S s ≫ M.torus.hom.hom
    let x := fun v : S => MulAut.conj n (markedRootPoint M.toIntegralMarking S a v)
    let c := s (Multiplicative.ofAdd (D.datum.root (weylWordPerm w a)))
    MulAut.conj t (x z) = x ((c : S) * z) := by
  intro n t x c
  obtain ⟨u, hu⟩ := integralWeylWordTransport M w a
  let y := markedRootPoint M.toIntegralMarking S (weylWordPerm w a)
  let f := algebraMap Integers.{u} S (u : Integers.{u})
  have hx (v : S) : x v = y (f * v) := by
    change n * markedRootPoint M.toIntegralMarking S a v * n⁻¹ = _
    exact hu S v
  have hy (v : S) : MulAut.conj t (y v) = y ((c : S) * v) := by
    rw [MulAut.conj_apply]
    exact M.conjugation S s (weylWordPerm w a) v
  rw [hx, hy, hx]
  congr 1
  exact mul_left_comm _ _ _

attribute [local instance] integerAlgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

set_option maxHeartbeats 800000 in
private theorem pinnedRationalOrbitFixedParameters [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : Gal(K/k)) (hσ : σ ≠ 1)
    (hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (w : List (SimpleRootOrbit D)) (hw : ∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) :
    let R := CommAlgCat.of k k
    let S := CommAlgCat.of Integers.{u} K
    let splitPoint := fun p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k =>
      (integralPointFunctor M.group).map (evaluateGroundTensor k K) (pinnedMarkedPoint C d R p)
    let n := markedWeylWord M.toIntegralMarking S (w.flatMap SimpleRootOrbit.roots)
    let x := fun (a : D.I) (z : K) => MulAut.conj n (markedRootPoint M.toIntegralMarking S a z)
    (∀ a : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, none) →
      ∀ z : K, x a z ∈ Set.range splitPoint ↔ z ∈ Set.range (algebraMap k K)) ∧
    ∀ a b : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, some b) →
      ∀ u v : K, x a u * x b v ∈ Set.range splitPoint ↔ v = σ u := by
  intro R S splitPoint n x
  let E := (quadraticIntegralAlgebra k K).obj R
  let f := evaluateGroundTensor k K
  let j := ((integralPointFunctor M.group).map f).hom
  let e := Algebra.TensorProduct.rid k K K
  let w' := w.flatMap SimpleRootOrbit.roots
  let n' := markedWeylWord M.toIntegralMarking E w'
  let x' := markedRootPoint M.toIntegralMarking E
  have hj : Function.Injective j :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective
  have hmem (p : IntegralPoints M.group E) :
      j p ∈ Set.range splitPoint ↔ p ∈ Set.range (pinnedMarkedPoint C d R) := by
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hj hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, congrArg j hq⟩
  have hx (a : D.I) (z : K ⊗[k] k) :
      j (MulAut.conj n' (x' a z)) = x a (f.hom z) := by
    change j (n' * markedRootPoint M.toIntegralMarking E a z * n'⁻¹) =
      n * markedRootPoint M.toIntegralMarking S a (f.hom z) * n⁻¹
    rw [map_mul, map_mul, map_inv, markedWeylWord_map, markedRootPoint_map]
  obtain ⟨hsingle, hpair⟩ := pinnedTransportedOrbitFixedParameters C d hdegree σ hσ hs w hw R
  constructor
  · intro a ha z
    let v := e.symm z
    have hv : f.hom v = z := e.apply_symm_apply z
    have hxv := hx a v
    rw [hv] at hxv
    calc
      x a z ∈ Set.range splitPoint ↔
          MulAut.conj n' (x' a v) ∈ Set.range (pinnedMarkedPoint C d R) := by rw [← hxv, hmem]
      _ ↔ v ∈ Set.range (Algebra.TensorProduct.includeRight : k →ₐ[k] K ⊗[k] k) :=
        hsingle a ha v
      _ ↔ z ∈ Set.range (algebraMap k K) := by
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, (evaluateGroundTensor_includeRight c).symm.trans
            ((congrArg f.hom hc).trans hv)⟩
        · rintro ⟨c, hc⟩
          refine ⟨c, e.injective ?_⟩
          change f.hom ((Algebra.TensorProduct.includeRight : k →ₐ[k] K ⊗[k] k) c) = f.hom v
          rw [evaluateGroundTensor_includeRight, hv, hc]
  · intro a b hab u v
    let u' := e.symm u
    let v' := e.symm v
    have hu : f.hom u' = u := e.apply_symm_apply u
    have hv : f.hom v' = v := e.apply_symm_apply v
    have hxy : j (MulAut.conj n' (x' a u' * x' b v')) = x a u * x b v := by
      rw [map_mul (MulAut.conj n'), map_mul, hx, hx, hu, hv]
    calc
      x a u * x b v ∈ Set.range splitPoint ↔
          MulAut.conj n' (x' a u' * x' b v') ∈ Set.range (pinnedMarkedPoint C d R) := by
        rw [← hxy, hmem]
      _ ↔ v' = quadraticCoefficientEquiv σ R u' := hpair a b hab u' v'
      _ ↔ e v' = e (quadraticCoefficientEquiv σ R u') := e.injective.eq_iff.symm
      _ ↔ v = σ u := by
        change f.hom v' = f.hom (quadraticCoefficientEquiv σ R u') ↔ _
        rw [hv, evaluateGroundTensor_conjugate, hu]

set_option maxHeartbeats 1100000 in
theorem pinnedRelativeTorusLayerConjugation : PinnedRelativeTorusLayerConjugation.{u} := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ D M C l G B T d hdegree σ hσ hs w hw
    R S splitPoint torus g word n x χ
  let f := evaluateGroundTensor k K
  let j := ((integralPointFunctor M.group).map f).hom
  obtain ⟨emb, he, hEmb⟩ := pinnedMarkedPointEmbedding C d
  let i : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k →* IntegralPoints M.group S :=
    j.comp (emb.app R).hom
  have hi : Function.Injective i :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective.comp
      (hEmb R).1
  have heq (p) : i p = splitPoint p := congrArg j (he R p)
  obtain ⟨_, ht, _⟩ := pinnedMarkedTorusPointComparison C d R
  have hg (t) : i (g t) = torus t ≫ M.torus.hom.hom := by
    rw [heq]
    exact (congrArg j (ht t)).trans (markedTorusPoint_map M.toIntegralMarking f _)
  have hvalues (t) : ∃ s : TorusValues D S, torusPoint D S s = torus t :=
    (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) S).surjective _
  have hconj (t) (s : TorusValues D S) (hts : torusPoint D S s = torus t) (a : D.I) (z : K) :
      MulAut.conj (i (g t)) (x a z) = x a ((χ s a : K) * z) := by
    rw [hg, ← hts]
    exact markedWeylWord_torusConjugation M S word s a z
  have hfixed (t) {p} (hp : p ∈ Set.range splitPoint) :
      MulAut.conj (i (g t)) p ∈ Set.range splitPoint := by
    obtain ⟨q, rfl⟩ := hp
    refine ⟨g t * q * (g t)⁻¹, ?_⟩
    rw [← heq, ← heq q, map_mul, map_mul, map_inv]
    rfl
  obtain ⟨hsingle, hpair⟩ := pinnedRationalOrbitFixedParameters C d hdegree σ hσ hs w hw
  constructor
  · intro a ha
    obtain ⟨H, hH⟩ := pinnedSingletonRootModel C d hdegree σ hσ hs w hw a ha
    let ρ : SpecialLinearGroup (Fin 2) k →* HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k :=
      (H.pointMap.app R).hom
    have hρ (u : k) : splitPoint (ρ (upper u)) = x a (algebraMap k K u) := by
      change j (pinnedMarkedPoint C d R (H.pointMap.app R (upper u))) = _
      rw [hH R (upper u), map_upperMatrix, M.rankOneUpper]
      change j (transportedRootPoint M.toIntegralMarking _ ((a, none), w) a
        ((Algebra.TensorProduct.includeRight : k →ₐ[k] K ⊗[k] k) u)) = _
      rw [transportedRootPoint_map, evaluateGroundTensor_includeRight]
      rfl
    refine ⟨ρ, hρ, fun t => ?_⟩
    obtain ⟨s, hts⟩ := hvalues t
    have h1 : x a 1 ∈ Set.range splitPoint := (hsingle a ha 1).mpr ⟨1, map_one _⟩
    have hu := hfixed t h1
    rw [hconj t s hts a 1, mul_one] at hu
    obtain ⟨c, hc⟩ := (hsingle a ha _).mp hu
    have hc₀ : c ≠ 0 := by
      intro h
      rw [h, map_zero] at hc
      exact (χ s a).ne_zero hc.symm
    let v := Units.mk0 c hc₀
    have hρi (z : k) : i (ρ (upper z)) = x a (algebraMap k K z) := (heq _).trans (hρ z)
    have hAction (u : k) : g t * ρ (upper u) * (g t)⁻¹ = ρ (upper ((v : k) * u)) := by
      apply hi
      rw [map_mul, map_mul, map_inv, hρi, hρi]
      change MulAut.conj (i (g t)) (x a (algebraMap k K u)) =
        x a (algebraMap k K (c * u))
      rw [hconj t s hts, map_mul, hc]
    exact ⟨s, hts, v, Units.ext hc, hAction, rootFiltrationShift k v,
      rootLayerConjugation k (fun u => ρ (upper u)) (g t) v hAction⟩
  · intro a b hab
    obtain ⟨ρ, hρ'⟩ := pinnedRationalPairedRankOne C d hdegree σ hσ hs w hw a b hab
    have hρ (u : K) : splitPoint (ρ (upper u)) = x a u * x b (σ u) := by
      have h := hρ' (upper u)
      change splitPoint (ρ (upper u)) = MulAut.conj n
        (((M.rankOne a).app S (upper u) : IntegralPoints M.group S) *
          (M.rankOne b).app S (SpecialLinearGroup.map σ.toRingHom (upper u))) at h
      rw [map_upperMatrix, M.rankOneUpper, M.rankOneUpper] at h
      exact h.trans (map_mul (MulAut.conj n) _ _)
    refine ⟨ρ, hρ, fun t => ?_⟩
    obtain ⟨s, hts⟩ := hvalues t
    have h1 : x a 1 * x b 1 ∈ Set.range splitPoint := (hpair a b hab 1 1).mpr (map_one σ).symm
    have hu := hfixed t h1
    rw [map_mul, hconj t s hts a 1, hconj t s hts b 1, mul_one, mul_one] at hu
    have hc : (χ s b : K) = σ (χ s a : K) := (hpair a b hab _ _).mp hu
    have hρi (z : K) : i (ρ (upper z)) = x a z * x b (σ z) := (heq _).trans (hρ z)
    have hAction (u : K) : g t * ρ (upper u) * (g t)⁻¹ = ρ (upper ((χ s a : K) * u)) := by
      apply hi
      rw [map_mul, map_mul, map_inv, hρi, hρi]
      change MulAut.conj (i (g t)) (x a u * x b (σ u)) =
        x a ((χ s a : K) * u) * x b (σ ((χ s a : K) * u))
      simp only [map_mul, hconj t s hts, hc]
    exact ⟨s, hts, Units.ext hc, hAction, rootFiltrationShift K (χ s a),
      rootLayerConjugation K (fun u => ρ (upper u)) (g t) (χ s a) hAction⟩

end RationalTorusConjugation

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
