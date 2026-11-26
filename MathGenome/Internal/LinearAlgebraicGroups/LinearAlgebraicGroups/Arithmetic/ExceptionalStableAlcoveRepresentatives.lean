import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives

open Set CategoryTheory
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer exceptionalCartan)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalStableAlcoveRepresentatives
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open scoped TensorProduct Pointwise BigOperators CategoryTheory.MonObj Matrix

noncomputable section

open private base_chart_place from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
open private type_eq_one_iff lengthZero_lift lengthZero_mem_iff type_eq_label
  mem_chamber_stabilizer_iff affine_eq_one_iff unit_le_iwahori lengthZero_normalizes from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingActions
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

section MarkedArithmetic

attribute [local instance] integerAlgebra

private theorem change_cocycle {Γ G : Type*} [Group Γ] [Group G]
    (ρ : Γ →* MulAut G) (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (g : G) (σ τ : Γ) :
    g⁻¹ * a (σ * τ) * ρ (σ * τ) g =
      (g⁻¹ * a σ * ρ σ g) * ρ σ (g⁻¹ * a τ * ρ τ g) := by
  rw [ha, map_mul ρ]
  simp only [MulAut.mul_apply, map_mul, map_inv]
  group

section CyclicCocycles

variable {Γ G : Type*} [Group Γ] [Group G]

private theorem cocycle_one (ρ : Γ →* MulAut G) (a : Γ → G)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) : a 1 = 1 := by
  simpa using ha 1 1

/-- A crossed homomorphism from a cyclic group is determined by its
generator value in the case where that value is the identity. -/
theorem cocycle_trivial_of_generator (ρ : Γ →* MulAut G) (a : Γ → G)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) (generator : Γ)
    (hgenerator : Subgroup.zpowers generator = ⊤) (hagenerator : a generator = 1) : ∀ σ, a σ = 1 := by
  let H : Subgroup Γ :=
    { carrier := {σ | a σ = 1}
      one_mem' := cocycle_one ρ a ha
      mul_mem' := by
        intro σ τ hσ hτ
        change a σ = 1 at hσ
        change a τ = 1 at hτ
        show a (σ * τ) = 1
        rw [ha, hσ, hτ, map_one, one_mul]
      inv_mem' := by
        intro σ hσ
        change a σ = 1 at hσ
        show a σ⁻¹ = 1
        simpa [hσ, cocycle_one ρ a ha] using (ha σ⁻¹ σ).symm }
  have htop : (⊤ : Subgroup Γ) ≤ H := hgenerator ▸ Subgroup.zpowers_le.mpr hagenerator
  exact fun σ => htop (Subgroup.mem_top σ)

/-- Inversion by Frobenius removes a cocycle in the length-zero quotient
of order three by the correction given by its generator value. -/
theorem cyclic_order_three_cocycle (ρ : Γ →* MulAut G) (a : Γ → G)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) (generator : Γ)
    (hgenerator : Subgroup.zpowers generator = ⊤) (hInv : ∀ z, ρ generator z = z⁻¹)
    (hCard : Nat.card G = 3) :
    ∀ σ, a generator * a σ * ρ σ (a generator)⁻¹ = 1 := by
  let k := (a generator)⁻¹
  let b (σ : Γ) := k⁻¹ * a σ * ρ σ k
  have hb : ∀ σ τ, b (σ * τ) = b σ * ρ σ (b τ) := change_cocycle ρ a ha k
  have hbgenerator : b generator = 1 := by
    have h := pow_card_eq_one' (x := a generator)
    rw [hCard] at h
    simpa only [b, k, hInv, inv_inv, pow_succ, pow_zero, one_mul] using h
  intro σ
  simpa only [b, k, inv_inv, map_inv] using cocycle_trivial_of_generator ρ b hb generator hgenerator hbgenerator σ

end CyclicCocycles
section FixedFace

universe u v

variable {K G W V : Type u} {J : Type v} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} [Group G] [Group W]
  {j : G →* FieldPoints M K} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}
  {B : Building C} {Q : C.TypeQuotient}

/-- On the marked alcove stabilizer, the kernel of the actual type quotient
is precisely the Iwahori. -/
theorem alcove_stabilizer_trivial_type (B : Building C) (Q : C.TypeQuotient) (g : G)
    (hg : g ∈ C.I ⊔ lengthZeroNormalizer C) :
    typeChange Q g = 1 ↔ g ∈ C.I := by
  refine ⟨fun h => ?_, fun hi => (type_eq_one_iff Q g).mpr (B.realization.iwahori_mem hi)⟩
  have hi := (mem_chamber_stabilizer_iff Q g).mp hg
  have hlabel : C.affine (Q.lift 1) = 1 := Q.affine_lift 1
  have hI : (Q.lift 1 : G) ∈ C.I := unit_le_iwahori ((affine_eq_one_iff _).mp hlabel)
  change g * (1 : G) * (Q.lift (typeChange Q g) : G)⁻¹ ∈ C.I at hi
  rw [h, mul_one] at hi
  simpa only [inv_mul_cancel_right] using C.I.mul_mem hi hI

end FixedFace

section Stability

universe u v

variable {K G W V : Type u} {J : Type v} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} [Group G] [Group W]
  {j : G →* FieldPoints M K} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}
  {B : Building C} {Q : C.TypeQuotient}
  {Γ : Type u} [Group Γ] {ρ : Γ →* MulAut G} {f : Γ → V ≃ᵃ[ℚ] V}

open LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingTransport (transportWeights transportWeights_apply)

private theorem coefficient_preserves_standard_alcove (coef : CoefficientAction B ρ f) (σ : Γ) :
    coef.action σ '' B.realization.closedFace 1 ∅ = B.realization.closedFace 1 ∅ := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨_, ⟨t, _, rfl⟩, rfl⟩
    let s := transportWeights (coef.types σ) t
    refine ⟨s, Set.empty_subset _, ?_⟩
    exact (coef.place_action σ 1 1 (by simp) t s
      (transportWeights_apply _ t)).symm
  · rintro x ⟨s, _, rfl⟩
    let t := transportWeights (coef.types σ).symm s
    refine ⟨B.realization.place 1 t, ⟨t, Set.empty_subset _, rfl⟩, ?_⟩
    exact coef.place_action σ 1 1 (by simp) t s
      (fun i => by simp [t, transportWeights, Function.comp_def])

private theorem translate_standard_alcove (ad : AdjointAction B Q) (g : C.G₀) :
    ad.action (g : G) '' B.realization.closedFace 1 ∅ = B.realization.closedFace g ∅ := by
  classical
  ext x
  rw [Realization.closedFace, Realization.closedFace, Set.image_image]
  have h (t : Weights (A.SimpleWall p)) :
      ad.action (g : G) (B.realization.place 1 t) = B.realization.place g t := by
    rw [← base_chart_place B 1 t, ad.restrict, B.realization.translate_chart, mul_one,
      base_chart_place]
  simp only [h]

private theorem coefficient_actions_agree
    (h : ∀ σ, AutomorphismComparison C (ρ σ) (f σ))
    (coef coef' : CoefficientAction B ρ f) (σ : Γ) (x : B.realization.Point) :
    coef.action σ x = coef'.action σ x := by
  obtain ⟨g, t, rfl⟩ := B.realization.place_surjective x
  have hg₀ : ρ σ (g : G) ∈ C.G₀.map (ρ σ).toMonoidHom := ⟨g, g.property, rfl⟩
  have hg : ρ σ (g : G) ∈ C.G₀ :=
    (congrArg (fun H : Subgroup G => ρ σ (g : G) ∈ H) (h σ).2.2.2.1).mp hg₀
  let g' : C.G₀ := ⟨ρ σ (g : G), hg⟩
  rw [← base_chart_place B g t, coef.chart σ g g' rfl, coef'.chart σ g g' rfl]

private theorem coefficient_conjugation (ad : AdjointAction B Q)
    (coef : CoefficientAction B ρ f)
    (hc : ∀ σ g x, coef.action σ (ad.action g x) = ad.action (ρ σ g) (coef.action σ x))
    (σ : Γ) (g a : G) (x : B.realization.Point) :
    ad.action (g⁻¹ * a * ρ σ g) (coef.action σ x) =
      ad.action g⁻¹ (ad.action a (coef.action σ (ad.action g x))) := by
  rw [hc, map_mul, map_mul, IsometryEquiv.mul_apply, IsometryEquiv.mul_apply]

private theorem transport_stable_alcove (ad : AdjointAction B Q)
    (coef : CoefficientAction B ρ f)
    (hc : ∀ σ g x, coef.action σ (ad.action g x) = ad.action (ρ σ g) (coef.action σ x))
    (σ : Γ) (g : C.G₀) (a : G)
    (ha : ad.action a '' (coef.action σ '' B.realization.closedFace g ∅) =
      B.realization.closedFace g ∅) :
    (g : G)⁻¹ * a * ρ σ g ∈ C.I ⊔ lengthZeroNormalizer C := by
  apply (ad.chamber_stabilizer _).mp
  let S := B.realization.closedFace 1 ∅
  have hg := translate_standard_alcove ad g
  change ad.action (g : G) '' S = _ at hg
  change ad.action ((g : G)⁻¹ * a * ρ σ g) '' S = S
  calc
    _ = ad.action ((g : G)⁻¹ * a * ρ σ g) '' (coef.action σ '' S) := by
      rw [coefficient_preserves_standard_alcove coef σ]
    _ = ad.action (g : G)⁻¹ '' (ad.action a '' (coef.action σ '' (ad.action (g : G) '' S))) := by
      simp only [Set.image_image]
      congr 1
      funext x
      exact coefficient_conjugation ad coef hc σ g a x
    _ = S := by
      rw [hg, ha, ← hg, Set.image_image]
      have hh : (ad.action (g : G)⁻¹ : B.realization.Point → B.realization.Point) ∘
          (ad.action (g : G)) = id := by
        funext x
        change ad.action (g : G)⁻¹ (ad.action (g : G) x) = x
        rw [← IsometryEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      change (_ ∘ _) '' S = S
      rw [hh, Set.image_id]

end Stability

private theorem stable_alcove_stabilizer.{u} : StableAlcoveStabilizer.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y B Γ _ ρ f h coef a g ha hstable
  obtain ⟨coef', hcomm', _⟩ := B.coefficients Γ ρ f h
  have hcomm σ g x :
      coef.action σ (B.adjoint.action g x) = B.adjoint.action (ρ σ g) (coef.action σ x) := by
    rw [coefficient_actions_agree h coef coef', coefficient_actions_agree h coef coef' σ x]
    exact hcomm' σ g x
  refine ⟨change_cocycle ρ a ha (g : FieldPoints M' K), fun σ => ?_⟩
  have hs := transport_stable_alcove B.adjoint coef hcomm σ g (a σ) (hstable σ)
  refine ⟨?_, hs, alcove_stabilizer_trivial_type B.ad Y.typeQuotient _ hs⟩
  rw [coefficient_preserves_standard_alcove coef σ]
  exact (B.adjoint.chamber_stabilizer _).mpr hs

private theorem det_of_triangular_factors {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (L U : Matrix (Fin n) (Fin n) ℚ)
    (h : A.map (Int.castRingHom ℚ) = L * U)
    (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular) :
    (A.det : ℚ) = (∏ i, L i i) * ∏ i, U i i := by
  change (Int.castRingHom ℚ) A.det = _
  rw [RingHom.map_det]
  change (A.map (Int.castRingHom ℚ)).det = _
  rw [h, Matrix.det_mul, Matrix.det_of_isLowerTriangular L hL,
    Matrix.det_of_isUpperTriangular hU]


set_option maxHeartbeats 2000000 in
private theorem det_exceptionalCartan_6 : (exceptionalCartan 6).det = 3 := by
  let L : Matrix (Fin 6) (Fin 6) ℚ :=
    !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      (-1 / 2), 0, 1, 0, 0, 0;
      0, (-1 / 2), (-2 / 3), 1, 0, 0;
      0, 0, 0, (-6 / 5), 1, 0;
      0, 0, 0, 0, (-5 / 4), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ :=
    !![2, 0, -1, 0, 0, 0;
      0, 2, 0, -1, 0, 0;
      0, 0, (3 / 2), -1, 0, 0;
      0, 0, 0, (5 / 6), -1, 0;
      0, 0, 0, 0, (4 / 5), -1;
      0, 0, 0, 0, 0, (3 / 4)]
  have h : (exceptionalCartan 6).map (Int.castRingHom ℚ) = L * U := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hL : L.IsLowerTriangular := by
    change ∀ i j : Fin 6, i < j → L i j = 0
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hU : U.IsUpperTriangular := by
    change ∀ i j : Fin 6, j < i → U i j = 0
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hd := det_of_triangular_factors _ L U h hL hU
  norm_num [L, U, Fin.prod_univ_succ] at hd
  exact_mod_cast hd


set_option maxHeartbeats 2000000 in
private theorem det_exceptionalCartan_7 : (exceptionalCartan 7).det = 2 := by
  let L : Matrix (Fin 7) (Fin 7) ℚ :=
    !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      (-1 / 2), 0, 1, 0, 0, 0, 0;
      0, (-1 / 2), (-2 / 3), 1, 0, 0, 0;
      0, 0, 0, (-6 / 5), 1, 0, 0;
      0, 0, 0, 0, (-5 / 4), 1, 0;
      0, 0, 0, 0, 0, (-4 / 3), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ :=
    !![2, 0, -1, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0;
      0, 0, (3 / 2), -1, 0, 0, 0;
      0, 0, 0, (5 / 6), -1, 0, 0;
      0, 0, 0, 0, (4 / 5), -1, 0;
      0, 0, 0, 0, 0, (3 / 4), -1;
      0, 0, 0, 0, 0, 0, (2 / 3)]
  have h : (exceptionalCartan 7).map (Int.castRingHom ℚ) = L * U := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hL : L.IsLowerTriangular := by
    change ∀ i j : Fin 7, i < j → L i j = 0
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hU : U.IsUpperTriangular := by
    change ∀ i j : Fin 7, j < i → U i j = 0
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hd := det_of_triangular_factors _ L U h hL hU
  norm_num [L, U, Fin.prod_univ_succ] at hd
  exact_mod_cast hd


set_option maxHeartbeats 2000000 in
private theorem det_exceptionalCartan_8 : (exceptionalCartan 8).det = 1 := by
  let L : Matrix (Fin 8) (Fin 8) ℚ :=
    !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      (-1 / 2), 0, 1, 0, 0, 0, 0, 0;
      0, (-1 / 2), (-2 / 3), 1, 0, 0, 0, 0;
      0, 0, 0, (-6 / 5), 1, 0, 0, 0;
      0, 0, 0, 0, (-5 / 4), 1, 0, 0;
      0, 0, 0, 0, 0, (-4 / 3), 1, 0;
      0, 0, 0, 0, 0, 0, (-3 / 2), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ :=
    !![2, 0, -1, 0, 0, 0, 0, 0;
      0, 2, 0, -1, 0, 0, 0, 0;
      0, 0, (3 / 2), -1, 0, 0, 0, 0;
      0, 0, 0, (5 / 6), -1, 0, 0, 0;
      0, 0, 0, 0, (4 / 5), -1, 0, 0;
      0, 0, 0, 0, 0, (3 / 4), -1, 0;
      0, 0, 0, 0, 0, 0, (2 / 3), -1;
      0, 0, 0, 0, 0, 0, 0, (1 / 2)]
  have h : (exceptionalCartan 8).map (Int.castRingHom ℚ) = L * U := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hL : L.IsLowerTriangular := by
    change ∀ i j : Fin 8, i < j → L i j = 0
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hU : U.IsUpperTriangular := by
    change ∀ i j : Fin 8, j < i → U i j = 0
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hd := det_of_triangular_factors _ L U h hL hU
  norm_num [L, U, Fin.prod_univ_succ] at hd
  exact_mod_cast hd

open Module TensorProduct

private theorem integral_coweight_coordinates.{u} (E : BasedRootDatum.{u}) {n : ℕ}
    (b : Fin n ≃ E.base.support) (had : E.datum.rootSpan ℤ = ⊤) :
    ∃ c : Basis (Fin n) ℤ E.Y, ∀ y i,
      c.repr y i = E.datum.toLinearMap (E.datum.root (b i)) y := by
  classical
  let r : Fin n → E.X := fun i => E.datum.root (b i)
  have hrange : Set.range r = E.datum.root '' (E.base.support : Set E.I) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b i, (b i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨b.symm ⟨i, hi⟩, by simp [r]⟩
  let rb : Basis (Fin n) ℤ E.X :=
    Basis.mk (E.base.linearIndepOn_root.comp b b.injective) (by
      change ⊤ ≤ Submodule.span ℤ (Set.range r)
      rw [hrange, E.base.span_int_root_support]
      exact had.ge)
  have hr (i) : rb i = r i := Basis.mk_apply _ _ i
  let pf := E.datum.toLinearMap.flip.toPerfPair
  let c := rb.dualBasis.map pf.symm
  refine ⟨c, fun y i => ?_⟩
  change (c.repr y) i = E.datum.toLinearMap (r i) y
  rw [← hr]
  change ((rb.dualBasis.repr (pf y)) i) = _
  exact Basis.dualBasis_repr rb (pf y) i

private theorem coweight_lattice_equiv.{u} (E : BasedRootDatum.{u}) {n : ℕ}
    (b : Fin n ≃ E.base.support) (c : Basis (Fin n) ℤ E.Y)
    (hc : ∀ y i, c.repr y i = E.datum.toLinearMap (E.datum.root (b i)) y) :
    let A := ApartmentRoots.split E.datum ℚ
    ∃ f : E.Y ≃ₗ[ℤ] A.coweightLattice.toIntSubmodule,
      ∀ y, (f y : ℚ ⊗[ℤ] E.Y) = (1 : ℚ) ⊗ₜ[ℤ] y := by
  classical
  let A := ApartmentRoots.split E.datum ℚ
  let f : E.Y →ₗ[ℤ] (ℚ ⊗[ℤ] E.Y) := TensorProduct.mk ℤ ℚ E.Y 1
  have hf (y) : f y ∈ A.coweightLattice.toIntSubmodule := by
    intro i
    exact ⟨E.datum.root' i y, RootData.extendFunctional_one_tmul ℚ (E.datum.root' i) y⟩
  let bQ := c.baseChange ℚ
  have hcoe (y i) : bQ.repr (f y) i = (c.repr y i : ℚ) := by
    change (bQ.repr ((1 : ℚ) ⊗ₜ[ℤ] y)) i = _
    rw [Basis.baseChange_repr_tmul]
    simp [zsmul_eq_mul]
  have happ (i) : A.root (b i) =
      (Finsupp.lapply i).comp bQ.repr.toLinearMap := by
    apply bQ.ext
    intro j
    change A.root (b i) ((c.baseChange ℚ) j) = bQ.repr (bQ j) i
    rw [show c.baseChange ℚ = bQ from rfl, Basis.repr_self]
    rw [show bQ j = (1 : ℚ) ⊗ₜ[ℤ] c j from Basis.baseChange_apply ℚ c j]
    change RootData.extendFunctional ℚ (E.datum.root' (b i)) (1 ⊗ₜ[ℤ] c j) = _
    rw [RootData.extendFunctional_one_tmul]
    change (E.datum.toLinearMap (E.datum.root (b i)) (c j) : ℚ) = _
    rw [← hc, Basis.repr_self]
    by_cases h : j = i <;> simp [h]
  let F := f.codRestrict A.coweightLattice.toIntSubmodule hf
  have hinj : Function.Injective F := by
    intro y z h
    have h' : f y = f z := congrArg Subtype.val h
    apply c.repr.injective
    ext i
    apply Rat.intCast_injective
    rw [← hcoe, ← hcoe, h']
  have hsurj : Function.Surjective F := by
    intro x
    have hx (i : Fin n) : ∃ m : ℤ, bQ.repr x.val i = (m : ℚ) := by
      obtain ⟨m, hm⟩ := x.property (b i)
      refine ⟨m, ?_⟩
      simpa [happ] using hm
    choose m hm using hx
    refine ⟨c.equivFun.symm m, Subtype.ext ?_⟩
    change f (c.equivFun.symm m) = x.val
    apply bQ.repr.injective
    ext i
    rw [hcoe, hm]
    exact_mod_cast congrFun (c.equivFun.apply_symm_apply m) i
  exact ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩, fun _ => rfl⟩

set_option maxHeartbeats 800000 in
private theorem exceptional_alcove_quotient_order.{u} : ExceptionalAlcoveQuotientOrder.{u} := by
  classical
  intro K _ _ _ _ D E M M' c p p' e Y n b hn hnum had
  let A := ApartmentRoots.split E.datum ℚ
  let P := A.coweightLattice
  let Q := A.corootLattice.comap P.subtype
  obtain ⟨r, hr⟩ := integral_coweight_coordinates E b had
  obtain ⟨f, hf⟩ := coweight_lattice_equiv E b r hr
  let cor (i : Fin n) := E.datum.coroot (b i)
  let S : Submodule ℤ E.Y := Submodule.span ℤ (Set.range cor)
  have hcor : LinearIndependent ℤ cor :=
    E.base.linearIndepOn_coroot.comp b b.injective
  let s := Basis.span hcor
  have hs (i) : (s i : E.Y) = cor i := by simp [s]
  let t : E.Y →+ (ℚ ⊗[ℤ] E.Y) := (TensorProduct.mk ℤ ℚ E.Y 1).toAddMonoidHom
  have hQ : A.corootLattice = S.toAddSubgroup.map t := by
    have hrange : Set.range cor = E.datum.coroot '' (E.base.support : Set E.I) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, (b i).property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨b.symm ⟨i, hi⟩, by simp [cor]⟩
    have hS : S = Submodule.span ℤ (Set.range E.datum.coroot) := by
      change Submodule.span ℤ (Set.range cor) = _
      rw [hrange, E.base.span_int_coroot_support]
    rw [hS, Submodule.span_int_eq_addSubgroupClosure, AddMonoidHom.map_closure]
    change AddSubgroup.closure (Set.range A.coroot) =
      AddSubgroup.closure (t '' Set.range E.datum.coroot)
    rw [← Set.range_comp]
    rfl
  have hmap : Submodule.map f.toLinearMap S = Q.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (f y : ℚ ⊗[ℤ] E.Y) ∈ A.corootLattice
      rw [hQ, hf]
      exact ⟨y, hy, rfl⟩
    · intro hx
      change x.val ∈ A.corootLattice at hx
      obtain ⟨y, hy, hyx⟩ := hQ ▸ hx
      exact ⟨y, hy, Subtype.ext ((hf y).trans hyx)⟩
  have hm : r.toMatrix (Subtype.val ∘ s) = exceptionalCartan n := by
    ext i j
    rw [Basis.toMatrix_apply, Function.comp_apply, hs, hr]
    exact hnum.2 i j
  obtain ⟨q⟩ := Y.ad.geometry.stabilizer
  rw [Nat.card_congr q.toEquiv]
  change Nat.card (P ⧸ Q.toIntSubmodule) = _
  rw [← Nat.card_congr (Submodule.Quotient.equiv S Q.toIntSubmodule f hmap).toEquiv]
  letI := E.freeY
  letI := E.finiteY
  rw [← Submodule.natAbs_det_basis_change r S s, Basis.det_apply, hm]
  rcases hn with rfl | rfl | rfl
  · simp [det_exceptionalCartan_6]
  · simp [det_exceptionalCartan_7]
  · simp [det_exceptionalCartan_8]


section CoefficientStabilizer

universe u v

variable {K G W V : Type u} {J : Type v} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} [Group G] [Group W]
  {j : G →* FieldPoints M K} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}
  {B : Building C} {Q : C.TypeQuotient}
  {Γ : Type u} [Group Γ] {ρ : Γ →* MulAut G} {f : Γ → V ≃ᵃ[ℚ] V}

private theorem coefficient_preserves_stabilizer (ad : AdjointAction B Q)
    (coef : CoefficientAction B ρ f)
    (hc : ∀ σ g x, coef.action σ (ad.action g x) = ad.action (ρ σ g) (coef.action σ x))
    (σ : Γ) {g : G} (hg : g ∈ C.I ⊔ lengthZeroNormalizer C) :
    ρ σ g ∈ C.I ⊔ lengthZeroNormalizer C := by
  let S := B.realization.closedFace 1 ∅
  have hS := coefficient_preserves_standard_alcove coef σ
  change coef.action σ '' S = S at hS
  have hg' := (ad.chamber_stabilizer g).2 hg
  change ad.action g '' S = S at hg'
  apply (ad.chamber_stabilizer _).1
  change ad.action (ρ σ g) '' S = S
  calc
    _ = ad.action (ρ σ g) '' (coef.action σ '' S) := by rw [hS]
    _ = coef.action σ '' (ad.action g '' S) := by
      simp only [Set.image_image]
      congr 1
      funext x
      exact (hc σ g x).symm
    _ = S := by rw [hg', hS]

end CoefficientStabilizer

private theorem outer_alcove_type_correction.{u} : OuterAlcoveTypeCorrection.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y B b hnum had Γ _ φ hφ ρ f β hcomp hinv a ha hstab
  obtain ⟨coef, hcomm, _⟩ := B.coefficients Γ ρ f (fun σ => (hcomp σ).1)
  let q := typeChange Y.typeQuotient
  have hq (σ : Γ) (g : FieldPoints M' K) : q (ρ σ g) = β σ (q g) :=
    (hcomp σ).2.1 g
  have hb (σ τ : Γ) : q (a (σ * τ)) = q (a σ) * β σ (q (a τ)) := by rw [ha, map_mul, hq]
  have hcard := exceptional_alcove_quotient_order Y 6 b (Or.inl rfl) hnum had
  have hcard' : Nat.card (alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
      ((ApartmentRoots.split E.datum ℚ).alcove p')) = 3 := by simpa using hcard
  have hcancel := cyclic_order_three_cocycle β (q ∘ a) hb φ hφ hinv hcard'
  let z := (q (a φ))⁻¹
  let k : lengthZeroNormalizer Y.ad :=
    ⟨Y.typeQuotient.lift z, lengthZero_lift Y.typeQuotient z⟩
  have hk : q k = z := Y.typeQuotient.quotient_lift z
  refine ⟨k, hk, change_cocycle ρ a ha (k : FieldPoints M' K), fun σ => ?_⟩
  let S := Y.ad.I ⊔ lengthZeroNormalizer Y.ad
  have hkS : (k : FieldPoints M' K) ∈ S := (show lengthZeroNormalizer Y.ad ≤ S from le_sup_right) k.property
  have hρk : ρ σ k ∈ S := coefficient_preserves_stabilizer B.adjoint coef hcomm σ hkS
  have hz := S.mul_mem (S.mul_mem (S.inv_mem hkS) (hstab σ)) hρk
  apply (alcove_stabilizer_trivial_type B.ad Y.typeQuotient _ hz).mp
  change q ((k : FieldPoints M' K)⁻¹ * a σ * ρ σ k) = 1
  rw [map_mul, map_mul, map_inv, hq, hk]
  simpa only [z, inv_inv, map_inv, Function.comp_apply] using hcancel σ


private theorem cyclic_hom_of_order_dvd {Γ G : Type*} [Group Γ] [Group G] [Finite Γ]
    (φ : Γ) (hφ : Subgroup.zpowers φ = ⊤) (t : G)
    (ht : orderOf t ∣ Nat.card Γ) :
    ∃ r : Γ →* G, r φ = t ∧ ∀ σ, r σ ∈ Subgroup.zpowers t := by
  let f := zpowersHom Γ φ
  let h := zpowersHom G t
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, Subgroup.range_zpowersHom, hφ]
  have horder : orderOf φ = Nat.card Γ := by
    rw [← Nat.card_zpowers, hφ]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hker : f.ker ≤ h.ker := by
    change (zpowersHom Γ φ).ker ≤ (zpowersHom G t).ker
    rw [zpowersHom_ker_eq, Subgroup.zpowers_le]
    simpa [zpowersHom_apply, zpow_natCast, horder] using orderOf_dvd_iff_pow_eq_one.mp ht
  let e := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  let r := (QuotientGroup.lift f.ker h hker).comp e.symm.toMonoidHom
  have hr (i : Multiplicative ℤ) : r (f i) = h i := by
    have he : e (QuotientGroup.mk i) = f i := rfl
    rw [← he]
    change QuotientGroup.lift f.ker h hker (e.symm (e (QuotientGroup.mk i))) = h i
    rw [e.symm_apply_apply, QuotientGroup.lift_mk]
  refine ⟨r, ?_, fun σ => ?_⟩
  · simpa [f, h] using hr (Multiplicative.ofAdd 1)
  · obtain ⟨i, rfl⟩ := hsurj σ
    exact ⟨i.toAdd, (hr i).symm⟩

open Specs.ExceptionalIwahoriCongruence (integralRingMap changeRingHom)

private theorem scalar_points_comp.{u} {D : BasedRootDatum.{u}} (M : Model D)
    {F K L : Type u} [Field F] [Field K] [Field L] (f : F →+* K) (g : K →+* L) :
    (scalarPoints M g).comp (scalarPoints M f) = scalarPoints M (g.comp f) :=
  congrArg GrpCat.Hom.hom
    ((Specs.IntegralSemisimpleModel.integralPointFunctor M.group).map_comp
      (integralRingMap f) (integralRingMap g)).symm

private theorem scalar_length_zero_mem.{u}
    {K L : Type u} [Field K] [Field L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : Specs.ExceptionalIwahoriImageComparison.MarkedCentralCover M M'}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} {Z : SplitLevel L c p p' e}
    {f : K →+* L} {s : FieldPoints M' K →* FieldPoints M' L}
    (h : ScalarComparison f s Y.ad Z.ad) {g : FieldPoints M' K}
    (hg : g ∈ lengthZeroNormalizer Y.ad) : s g ∈ lengthZeroNormalizer Z.ad := by
  obtain ⟨n, ⟨w, hw, hn⟩, hng⟩ := hg
  have hN : Z.ad.N.comap s = Y.ad.N := h.2.2.2.1
  have hn' : s (n : FieldPoints M' K) ∈ Z.ad.N := by
    change (n : FieldPoints M' K) ∈ Z.ad.N.comap s
    rw [hN]
    exact n.property
  let n' : Z.ad.N := ⟨s n, hn'⟩
  have hAffine := h.2.2.2.2.2.2.2.2.1 n n' rfl
  exact ⟨n', ⟨w, hw, hn.trans hAffine.1.symm⟩, congrArg s hng⟩

private theorem scalar_alcove_cocycle_inflation.{u} : ScalarAlcoveCocycleInflation.{u} := by
  intro F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _hK _hL D E M M' c p p' e
    Y Z res hres s hscalar htype ρ ρ' hρ hρ' a ha hstab a'
  have hcompare (σ : Gal(L/F)) (g : FieldPoints M' K) :
      s (ρ (res σ) g) = ρ' σ (s g) := by
    rw [hρ, hρ']
    change ((s.comp (scalarPoints M' (res σ).toRingHom)) g) =
      (((scalarPoints M' σ.toRingHom).comp s) g)
    have he : (algebraMap K L).comp (res σ).toRingHom =
        σ.toRingHom.comp (algebraMap K L) := RingHom.ext (hres σ)
    rw [scalar_points_comp, scalar_points_comp, he]
  let H := Z.ad.I ⊔ lengthZeroNormalizer Z.ad
  have hH : Y.ad.I ⊔ lengthZeroNormalizer Y.ad ≤ H.comap s := by
    refine sup_le ?_ ?_
    · intro g hg
      have hi : Z.ad.I.comap s = Y.ad.I := hscalar.2.2.1
      exact (show Z.ad.I ≤ H from le_sup_left) (show g ∈ Z.ad.I.comap s from hi ▸ hg)
    · intro g hg
      exact (show lengthZeroNormalizer Z.ad ≤ H from le_sup_right)
        (scalar_length_zero_mem hscalar hg)
  refine ⟨?_, fun σ => hH (hstab (res σ)), fun σ => htype.1 (a (res σ))⟩
  intro σ τ
  change s (a (res (σ * τ))) = s (a (res σ)) * ρ' σ (s (a (res τ)))
  rw [map_mul res, ha, map_mul s, hcompare]

private theorem inner_alcove_representative_cocycle.{u} :
    InnerAlcoveRepresentativeCocycle.{u} := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ hL D E M M' c p p' e X Z B
  intro s hscalar htransport φ hφ ρ hρ hρtype a ha hstab t htype ht
  let T := FieldPoints M' L
  let tL : T := s t
  have horder : orderOf tL ∣ Nat.card Gal(L/F) := by
    apply dvd_trans _ ht
    apply orderOf_dvd_of_pow_eq_one
    change s (t : FieldPoints M' F) ^ orderOf (t : FieldPoints M' F) = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  letI : Finite Gal(L/F) := Finite.of_fintype _
  obtain ⟨r, hr, hrmem⟩ := cyclic_hom_of_order_dvd φ hφ.1 tL horder
  have htL : tL ∈ lengthZeroNormalizer Z.ad := scalar_length_zero_mem hscalar t.property
  have hrL (σ) : r σ ∈ lengthZeroNormalizer Z.ad :=
    (Subgroup.zpowers_le.mpr htL) (hrmem σ)
  have hfixed (σ) : ρ σ tL = tL := by
    rw [hρ]
    change ((scalarPoints M' σ.toRingHom).comp s) (t : FieldPoints M' F) = tL
    rw [scalar_points_comp]
    have hbase : σ.toRingHom.comp (algebraMap F L) = algebraMap F L := by
      ext x
      exact σ.commutes x
    rw [hbase]
  have hrc (σ τ) : r (σ * τ) = r σ * ρ σ (r τ) := by
    obtain ⟨i, hi⟩ := hrmem τ
    rw [map_mul, ← hi, map_zpow, hfixed]
  let q := typeChange Z.typeQuotient
  have hq (σ) (g : T) : q (ρ σ g) = q g := (hρtype σ).1 g
  let aQ : Gal(L/F) →* _ :=
    { toFun := q ∘ a
      map_one' := by simpa only [Function.comp_apply, map_one] using congrArg q (cocycle_one ρ a ha)
      map_mul' := fun σ τ => by simp only [Function.comp_apply, ha, map_mul, hq] }
  have hgen : (q.comp r) φ = aQ φ := by
    change q (r φ) = q (a φ)
    rw [hr]
    exact (htransport.1 t).trans htype
  have hqr : q.comp r = aQ := by
    ext σ
    have hz : σ ∈ Subgroup.zpowers φ := hφ.1 ▸ Subgroup.mem_top _
    obtain ⟨i, rfl⟩ := hz
    simp only [map_zpow, hgen]
  have htype' (σ) : q (r σ) = q (a σ) := DFunLike.congr_fun hqr σ
  obtain ⟨negative, positive, hneg, hpos⟩ := rootOrderings_exist E
  have hρI (σ : Gal(L/F)) : Z.ad.I.map (ρ σ).toMonoidHom = Z.ad.I := by
    let P := Z.ad.localIwahori
    have hp := LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat.splitIwahoriScalar
      P P σ.toRingHom
      (LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat.normalizedValuation_unramifiedAut hL σ)
      negative positive hneg hpos
    rw [← (MonoidHom.ext (hρ σ) : (ρ σ).toMonoidHom = scalarPoints M' σ.toRingHom)] at hp
    calc
      Z.ad.I.map (ρ σ).toMonoidHom =
          (Z.ad.I.comap (ρ σ).toMonoidHom).map (ρ σ).toMonoidHom :=
        congrArg (Subgroup.map (ρ σ).toMonoidHom) hp.symm
      _ = Z.ad.I := Subgroup.map_comap_eq_self_of_surjective (ρ σ).surjective _
  refine ⟨r, hr, hrL, hrc, htype', fun σ => ?_, fun σ => ?_, fun σ τ => ?_⟩
  · let H := Z.ad.I ⊔ lengthZeroNormalizer Z.ad
    have hrH : r σ ∈ H := (show lengthZeroNormalizer Z.ad ≤ H from le_sup_right) (hrL σ)
    apply (alcove_stabilizer_trivial_type B.ad Z.typeQuotient _ (H.mul_mem (hstab σ) (H.inv_mem hrH))).mp
    change q (a σ * (r σ)⁻¹) = 1
    rw [map_mul, map_inv, htype', mul_inv_cancel]
  · change Z.ad.I.map ((MulAut.conj (r σ)).toMonoidHom.comp (ρ σ).toMonoidHom) = Z.ad.I
    rw [← Subgroup.map_map, hρI]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (lengthZero_normalizes Z.typeQuotient (hrL σ))
  · rw [ha, hrc, MulAut.conj_apply, map_mul, map_inv, mul_inv_rev]
    group

private theorem marked_alcove_coefficient_comparison.{u}
    (h : SplitAffineBuildings.{u}) : MarkedAlcoveCoefficientComparison.{u} := by
  intro F _ _ _ _ D E M M' c n b b' hn hb hb' hsc had
  obtain ⟨p, p', e, X, BX, he, hp, hlevels⟩ := h F c n b b' hn hb hb' hsc had
  refine ⟨p, p', e, X, BX, he, hp, ?_⟩
  intro K _ _ _ _ _ _ _ hK
  obtain ⟨Y, BY, _, hs, ht, _, hcoeff, houter⟩ := hlevels K hK
  exact ⟨Y, BY, hs, ht, exceptional_alcove_quotient_order Y n b' hn hb' had, hcoeff, houter⟩


end MarkedArithmetic

open Module TensorProduct
open Specs.ExceptionalIwahoriCongruence (integralRingMap changeRingHom)

open AlgebraicGeometry Opposite
open Specs.IntegralSemisimpleModel (IntegralAlgebra IntegralPoints Integers TorusValues cocharacter
  integralSpec integralPointFunctor splitTorus torusPoint)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom MarkedLocalNormalizer)
open Specs.ExceptionalMarkedRootDescent (markedWall wallMatrix rankOneMatrixWord markedWeylWord)
open Specs.IntegralRootRelations (upper lower diagonal)

open private affineTorusPointEquiv torusPoint_natural cocharacter_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private elementaryWord elementaryWord_diagonal rankOneWord_reflection from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private def markedTorusHom.{u} {D : BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) : TorusValues D R →* IntegralPoints M.group R :=
  (integralPointHom M.torus R).comp
    (show TorusValues D R ≃* IntegralPoints (splitTorus D) R from
      affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).toMonoidHom

private theorem markedTorusHom_apply.{u} {D : BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) (t : TorusValues D R) :
    markedTorusHom M R t = torusPoint D R t ≫ M.torus.hom.hom := rfl

private theorem base_change_torus.{u} {D : BasedRootDatum.{u}} (M : Model D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (t : TorusValues D R) :
    changeRingHom M.group f (markedTorusHom M R t) =
      markedTorusHom M S ((Units.map f.hom.toMonoidHom).comp t) := by
  change integralSpec.map f.op ≫ (torusPoint D R t ≫ M.torus.hom.hom) =
    torusPoint D S ((Units.map f.hom.toMonoidHom).comp t) ≫ M.torus.hom.hom
  rw [← Category.assoc, torusPoint_natural]

open private markedWeylWord_map from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private splitMarkedNormalizerWord fibreNormalizerPoint_injective from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedWord_mem_splitNormalizer from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private simpleWeylWords from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

private theorem base_change_word.{u} {D : BasedRootDatum.{u}} (M : Model D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (word : List D.I) :
    changeRingHom M.group f (markedWeylWord M.toIntegralMarking R word) =
      markedWeylWord M.toIntegralMarking S word :=
  markedWeylWord_map M.toIntegralMarking f word

private theorem integral_torus_factor.{u} {D : BasedRootDatum.{u}} (M : Model D)
    {R S : IntegralAlgebra.{u}} [IsReduced R] (f : R ⟶ S)
    (hf : Function.Injective f.hom) (x : IntegralPoints M.group R) (v : TorusValues D S)
    (hv : changeRingHom M.group f x = markedTorusHom M S v) :
    ∃ w : TorusValues D R, markedTorusHom M R w = x ∧
      (Units.map f.hom.toMonoidHom).comp w = v := by
  let i := M.torus.hom.hom
  let f' := integralSpec.map f.op
  letI : IsClosedImmersion i.left := M.torusClosed
  letI : IsDominant f'.left := by
    change IsDominant (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap f.hom.toRingHom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot f.hom.toRingHom).mp hf]
    exact bot_le
  letI : AlgebraicGeometry.IsReduced (integralSpec.obj (op R)).left := by
    change AlgebraicGeometry.IsReduced (Spec (CommRingCat.of R))
    infer_instance
  letI : IsSchemeTheoreticallyDominant f'.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have he : f' ≫ x = torusPoint D S v ≫ i := by
    rw [markedTorusHom_apply] at hv
    exact hv
  have hk : i.left.ker ≤ x.left.ker := by
    have h := (torusPoint D S v).left.le_ker_comp i.left
    rw [← Over.comp_left, ← he, Over.comp_left, Scheme.Hom.ker_comp,
      f'.left.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h
    exact h
  let y : IntegralPoints (splitTorus D) R :=
    Over.homMk (IsClosedImmersion.lift i.left x.left hk) (by
      rw [← i.w, ← Category.assoc, IsClosedImmersion.lift_fac, x.w])
  have hy : y ≫ i = x :=
    Over.OverMorphism.ext (IsClosedImmersion.lift_fac i.left x.left hk)
  obtain ⟨w, hw⟩ := (affineTorusPointEquiv
    (k := Integers.{u}) (M := Multiplicative D.X) R).surjective y
  change torusPoint D R w = y at hw
  refine ⟨w, ?_, ?_⟩
  · rw [markedTorusHom_apply, hw, hy]
  · apply (affineTorusPointEquiv
      (k := Integers.{u}) (M := Multiplicative D.X) S).injective
    change torusPoint D S ((Units.map f.hom.toMonoidHom).comp w) = torusPoint D S v
    haveI : Mono i := Over.mono_of_mono_left i
    rw [← cancel_mono i, ← torusPoint_natural, Category.assoc, hw, hy, he]

private theorem marked_wall_conj_cocharacter.{u} {D : BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) (i : D.I) (π : Rˣ) (y : D.Y) :
    let w := markedWall M.toIntegralMarking R i 1
    let τ := fun z => markedTorusHom M R (cocharacter D z R π)
    w * τ y * w⁻¹ = τ (D.datum.coreflection i y) := by
  let τ := fun z => markedTorusHom M R (cocharacter D z R π)
  let t := τ y
  let χ := D.datum.toLinearMap (D.datum.root i) y
  let p := π ^ χ
  let ρ : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R := ((M.rankOne i).app R).hom
  have hupper (z : R) : t * ρ (upper z) * t⁻¹ = ρ (upper ((p : R) * z)) := by
    have hu (v : R) : ρ (upper v) = M.line.point R v ≫ (M.root i).hom.hom :=
      M.rankOneUpper i R v
    rw [hu, hu]
    exact M.conjugation R (cocharacter D y R π) i z
  have hlower (z : R) : t * ρ (lower z) * t⁻¹ = ρ (lower ((↑p⁻¹ : R) * z)) := by
    have hl (v : R) : ρ (lower v) = M.line.point R v ≫ (M.root (D.datum.reflectionPerm i i)).hom.hom :=
      M.rankOneLower i R v
    rw [hl, hl]
    have hneg : D.datum.root (D.datum.reflectionPerm i i) = -D.datum.root i := by
      rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
    have h := M.conjugation R (cocharacter D y R π) (D.datum.reflectionPerm i i) z
    change t * _ * t⁻¹ = _ at h
    change _ = M.line.point R ((↑(π ^ D.datum.toLinearMap
      (D.datum.root (D.datum.reflectionPerm i i)) y) : R) * z) ≫ _ at h
    rw [hneg, map_neg, LinearMap.neg_apply, zpow_neg] at h
    exact h
  have hdiag (a : Rˣ) : ρ (diagonal a) = markedTorusHom M R (cocharacter D (D.datum.coroot i) R a) :=
    (M.rankOneDiagonal i R a).trans (markedTorusHom_apply M R _).symm
  have hcomm (a : Rˣ) : Commute t (ρ (diagonal a)) := by
    rw [hdiag]
    change markedTorusHom M R (cocharacter D y R π) * markedTorusHom M R _ =
      markedTorusHom M R _ * markedTorusHom M R (cocharacter D y R π)
    rw [← map_mul, ← map_mul]
    apply congrArg (markedTorusHom M R)
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.mul_apply]
    exact mul_comm _ _
  have he := rankOneWord_reflection ρ t p hupper hlower (hcomm p)
  have hτ : t * (ρ (diagonal p))⁻¹ = τ (D.datum.coreflection i y) := by
    change markedTorusHom M R _ * (ρ (diagonal p))⁻¹ = markedTorusHom M R _
    rw [hdiag, ← map_inv, ← map_mul]
    apply congrArg (markedTorusHom M R)
    apply MonoidHom.ext
    intro x
    change π ^ D.datum.toLinearMap x.toAdd y *
      ((π ^ χ) ^ D.datum.toLinearMap x.toAdd (D.datum.coroot i))⁻¹ =
      π ^ D.datum.toLinearMap x.toAdd (D.datum.coreflection i y)
    rw [D.datum.coreflection_apply, map_sub, map_zsmul, smul_eq_mul, zpow_sub, zpow_mul]
  have he' := he.trans hτ
  change ρ (elementaryWord (-1 : Rˣ)) * t * (ρ (elementaryWord (-1 : Rˣ)))⁻¹ = _
  rw [elementaryWord_diagonal, map_mul, mul_inv_rev]
  calc
    _ = ρ (diagonal (-1)) * (ρ (elementaryWord 1) * t * (ρ (elementaryWord 1))⁻¹) *
        (ρ (diagonal (-1)))⁻¹ := by group
    _ = τ (D.datum.coreflection i y) := by
      rw [he']
      have hc : Commute (ρ (diagonal (-1))) (τ (D.datum.coreflection i y)) := by
        rw [hdiag]
        change markedTorusHom M R _ * markedTorusHom M R (cocharacter D (D.datum.coreflection i y) R π) =
          markedTorusHom M R (cocharacter D (D.datum.coreflection i y) R π) * markedTorusHom M R _
        rw [← map_mul, ← map_mul]
        apply congrArg (markedTorusHom M R)
        apply MonoidHom.ext
        intro x
        simp only [MonoidHom.mul_apply]
        exact mul_comm _ _
      rw [hc.eq, mul_inv_cancel_right]


section LocalNormalizer

attribute [local instance] integerAlgebra

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {p : ℚ ⊗[ℤ] D.Y}
  {C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p}

open Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer)
open Specs.ExceptionalIwahoriImageComparison (integralUnitTorus)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open scoped WithZero

local notation "Nₖ" => LocalIwahori.normalizer (LocalComparison.localIwahori C)

private theorem split_simple_word_label {B : Specs.ExceptionalMarkedRootDescent.MarkedFibre M K}
    {ad : Bool} (hC : SplitPointComparison B ad C)
    (word : List D.I) (hw : ∀ i ∈ word, i ∈ D.base.support) :
    ∃ n : C.N, (n : FieldPoints M K) = markedWeylWord M.toIntegralMarking (integralRing K) word ∧
      (Nₖ).label n = (word.map (RootPairing.weylGroup.ofIdx D.datum)).prod := by
  let n : C.N := ⟨_, markedWord_mem_splitNormalizer C hC word hw⟩
  obtain ⟨_, F, hF, _⟩ := hC.2.1
  obtain ⟨a, ha, hlabel⟩ := splitMarkedNormalizerWord F word hw
  obtain ⟨b, hb, hlocal⟩ := hF n
  have hpoint : F.point b = F.point a := hb.trans ha.symm
  have hab := fibreNormalizerPoint_injective F hpoint
  exact ⟨n, rfl, hlocal.symm.trans ((congrArg F.label hab).trans hlabel)⟩

local notation "Oₖ" => Valuation.valuationSubring (ValuativeRel.valuation K)

private theorem integral_torus_valuation
    (x : (Nₖ).torus)
    (hx : ∃ y : IntegralPoints M.group (integralRing Oₖ),
      changeRingHom M.group (integralRingMap (Oₖ).subtype) y = (x : FieldPoints M K)) :
    (Nₖ).translation x = 1 := by
  obtain ⟨v, hv⟩ := ((Nₖ).torusPoints x).1 x.property
  obtain ⟨y, hy⟩ := hx
  obtain ⟨t, _, ht⟩ := integral_torus_factor M (integralRingMap (Oₖ).subtype)
    Subtype.val_injective y v (hy.trans (hv.trans (markedTorusHom_apply M _ v).symm))
  apply Multiplicative.toAdd.injective
  apply D.datum.toLinearMap.flip.toPerfPair.injective
  ext χ
  change D.datum.toLinearMap χ ((Nₖ).translation x).toAdd = D.datum.toLinearMap χ 0
  rw [map_zero]
  rw [(Nₖ).characterLog x v hv, ← ht]
  have hval : ValuativeRel.valuation K ((t (Multiplicative.ofAdd χ) : Oₖ) : K) = 1 := by
    apply le_antisymm (t (Multiplicative.ofAdd χ)).val.property
    have hinvle : ValuativeRel.valuation K
        ((↑(t (Multiplicative.ofAdd χ))⁻¹ : Oₖ) : K) ≤ 1 :=
      (t (Multiplicative.ofAdd χ))⁻¹.val.property
    have he : ValuativeRel.valuation K ((t (Multiplicative.ofAdd χ) : Oₖ) : K) *
        ValuativeRel.valuation K ((↑(t (Multiplicative.ofAdd χ))⁻¹ : Oₖ) : K) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
    calc
      1 = _ := he.symm
      _ ≤ _ := mul_le_of_le_one_right' hinvle
  change WithZero.log (normalizedValuation K ((t (Multiplicative.ofAdd χ) : Oₖ) : K)) = _
  rw [normalizedValuation, Valuation.map_apply, hval, map_one, WithZero.log_one]

end LocalNormalizer


private def cocharacterAction.{u} (D : BasedRootDatum.{u}) :
    D.datum.weylGroup →* (D.Y ≃ₗ[ℤ] D.Y) where
  toFun w := w.val.coweightEquiv.symm
  map_one' := by
    have h := (RootPairing.Equiv.coweightHom D.datum).map_one
    exact congrArg (fun e : (D.Y ≃ₗ[ℤ] D.Y)ᵐᵒᵖ => e.unop.symm) h
  map_mul' a b := by
    change (a.val * b.val).coweightEquiv.symm = a.val.coweightEquiv.symm * b.val.coweightEquiv.symm
    have h := (RootPairing.Equiv.coweightHom D.datum).map_mul a.val b.val
    exact congrArg (fun e : (D.Y ≃ₗ[ℤ] D.Y)ᵐᵒᵖ => e.unop.symm) h

private theorem word_conj_cocharacter.{u} {D : BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) (word : List D.I) (π : Rˣ) (y : D.Y) :
    let n := markedWeylWord M.toIntegralMarking R word
    let w := (word.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    let τ := fun z => markedTorusHom M R (cocharacter D z R π)
    n * τ y * n⁻¹ = τ (cocharacterAction D w y) := by
  induction word with
  | nil => simp [markedWeylWord, cocharacterAction]
  | cons i l ih =>
    simp only [markedWeylWord, List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply]
    let n := markedWeylWord M.toIntegralMarking R l
    let s := markedWall M.toIntegralMarking R i (1 : Rˣ)
    let τ := fun z => markedTorusHom M R (cocharacter D z R π)
    let w := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    change s * n * τ y * (s * n)⁻¹ =
      τ (cocharacterAction D (RootPairing.weylGroup.ofIdx D.datum i) (cocharacterAction D w y))
    have he : cocharacterAction D (RootPairing.weylGroup.ofIdx D.datum i) = D.datum.coreflection i := by
      change (RootPairing.Equiv.reflection D.datum i).coweightEquiv.symm = _
      rw [RootPairing.Equiv.reflection_coweightEquiv]
      exact D.datum.coreflection_inv i
    calc
      _ = s * (n * τ y * n⁻¹) * s⁻¹ := by group
      _ = _ := by rw [ih, he]; exact marked_wall_conj_cocharacter M R i π _

private def torusCocharacterHom.{u} {D : BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) (π : Rˣ) : Multiplicative D.Y →* IntegralPoints M.group R :=
  MonoidHom.mk' (fun y => markedTorusHom M R (cocharacter D y.toAdd R π)) fun y z => by
    rw [← map_mul]
    apply congrArg (markedTorusHom M R)
    apply MonoidHom.ext
    intro x
    change π ^ D.datum.toLinearMap x.toAdd (y.toAdd + z.toAdd) =
      π ^ D.datum.toLinearMap x.toAdd y.toAdd * π ^ D.datum.toLinearMap x.toAdd z.toAdd
    rw [map_add, zpow_add]

private theorem affine_apply_of_linear_add {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g : V ≃ᵃ[ℚ] V) (x : V) : g x = g.linear x + g 0 := by
  simpa using g.map_vadd (0 : V) x

private theorem affine_linear_of_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g : V ≃ᵃ[ℚ] V) (w : V ≃ₗ[ℚ] V) (y : V)
    (h : ∀ x, g x = w x + y) : g.linear = w := by
  ext x
  apply add_right_cancel (b := y)
  calc
    g.linear x + y = g x := by
      rw [affine_apply_of_linear_add g x, h 0, map_zero, zero_add]
    _ = _ := h x

private theorem affine_pow_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g : V ≃ᵃ[ℚ] V) (m : ℕ) :
    (g ^ m) 0 = ∑ j ∈ Finset.range m, (g.linear ^ j) (g 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ, AffineEquiv.coe_mul, Function.comp_apply, affine_apply_of_linear_add, ih]
    have h := ((AffineEquiv.linearHom : (V ≃ᵃ[ℚ] V) →* (V ≃ₗ[ℚ] V))).map_pow g m
    change (g ^ m).linear = g.linear ^ m at h
    rw [h, add_comm]

private theorem torus_word_power.{u} {D : BasedRootDatum.{u}} (M : Model D)
    (R : IntegralAlgebra.{u}) (word : List D.I) (π : Rˣ) (y : D.Y) (m : ℕ) :
    let n := markedWeylWord M.toIntegralMarking R word
    let w := cocharacterAction D (word.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    let τ := torusCocharacterHom M R π
    (τ (Multiplicative.ofAdd y) * n) ^ m =
      τ (Multiplicative.ofAdd (∑ j ∈ Finset.range m, (w ^ j) y)) * n ^ m := by
  let n := markedWeylWord M.toIntegralMarking R word
  let w := cocharacterAction D (word.map (RootPairing.weylGroup.ofIdx D.datum)).prod
  let τ := torusCocharacterHom M R π
  have h (j : ℕ) (v : D.Y) : n ^ j * τ (Multiplicative.ofAdd v) * (n ^ j)⁻¹ =
      τ (Multiplicative.ofAdd ((w ^ j) v)) := by
    induction j generalizing v with
    | zero => simp
    | succ j ih =>
      rw [pow_succ n, pow_succ w, LinearEquiv.mul_apply]
      calc
        _ = n ^ j * (n * τ (Multiplicative.ofAdd v) * n⁻¹) * (n ^ j)⁻¹ := by group
        _ = _ := by
          have hw := word_conj_cocharacter M R word π v
          change n * τ (Multiplicative.ofAdd v) * n⁻¹ = τ (Multiplicative.ofAdd (w v)) at hw
          rw [hw, ih]
  induction m with
  | zero =>
    change (τ (Multiplicative.ofAdd y) * n) ^ 0 =
      τ (Multiplicative.ofAdd (∑ j ∈ Finset.range 0, (w ^ j) y)) * n ^ 0
    simp
  | succ m ih =>
    change (τ (Multiplicative.ofAdd y) * n) ^ (m + 1) =
      τ (Multiplicative.ofAdd (∑ j ∈ Finset.range (m + 1), (w ^ j) y)) * n ^ (m + 1)
    change (τ (Multiplicative.ofAdd y) * n) ^ m =
      τ (Multiplicative.ofAdd (∑ j ∈ Finset.range m, (w ^ j) y)) * n ^ m at ih
    rw [Finset.sum_range_succ, pow_succ (τ _ * n), ih, pow_succ n]
    calc
      _ = τ (Multiplicative.ofAdd (∑ j ∈ Finset.range m, (w ^ j) y)) *
          (n ^ m * τ (Multiplicative.ofAdd y) * (n ^ m)⁻¹) * (n ^ m * n) := by group
      _ = _ := by
        rw [h]
        exact congrArg (· * (n ^ m * n)) (map_mul τ _ _).symm


section LocalLifts

attribute [local instance] integerAlgebra
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer)
open scoped WithZero

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {p : ℚ ⊗[ℤ] D.Y}
  {C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p}

local notation "Nₖ" => LocalIwahori.normalizer (LocalComparison.localIwahori C)
local notation "Oₖ" => Valuation.valuationSubring (ValuativeRel.valuation K)

private theorem split_affine_integral
    (H : ∀ (n : C.N) (x : ℚ ⊗[ℤ] D.Y), C.affine n x =
      ((Nₖ).label n).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x +
        ((1 : ℚ) ⊗ₜ[ℤ] ((Nₖ).translation ((Nₖ).torusPart n)).toAdd))
    (n : C.N)
    (hn : ∃ y : IntegralPoints M.group (integralRing Oₖ),
      changeRingHom M.group (integralRingMap (Oₖ).subtype) y = (n : FieldPoints M K)) :
    C.affine n = (((Nₖ).label n).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y).toAffineEquiv := by
  obtain ⟨y, hy⟩ := hn
  let w := (Nₖ).label n
  let f := integralRingMap (Oₖ).subtype
  let n' := markedWeylWord M.toIntegralMarking (integralRing Oₖ) ((Nₖ).word w)
  have hchange : changeRingHom M.group f n' = ((Nₖ).lift w : FieldPoints M K) :=
    (base_change_word M f ((Nₖ).word w)).trans ((Nₖ).lift_point w).symm
  have hval : (Nₖ).translation ((Nₖ).torusPart n) = 1 := by
    apply integral_torus_valuation (C := C)
    refine ⟨y * n'⁻¹, ?_⟩
    change (changeRingHom M.group f) (y * n'⁻¹) =
      (n : FieldPoints M K) * ((Nₖ).lift w : FieldPoints M K)⁻¹
    rw [map_mul, map_inv, hchange, hy]
  ext x
  rw [H, hval]
  simp

private theorem split_affine_uniformizer_cocharacter
    (H : ∀ (n : C.N) (x : ℚ ⊗[ℤ] D.Y), C.affine n x =
      ((Nₖ).label n).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x +
        ((1 : ℚ) ⊗ₜ[ℤ] ((Nₖ).translation ((Nₖ).torusPart n)).toAdd))
    (π : Kˣ) (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ)) (y : D.Y) :
    ∃ t : C.N, (t : FieldPoints M K) =
      markedTorusHom M (integralRing K) (cocharacter D y (integralRing K) π) ∧
      ∀ x, C.affine t x = x + ((1 : ℚ) ⊗ₜ[ℤ] (-y)) := by
  let v := cocharacter D y (integralRing K) π
  let g := markedTorusHom M (integralRing K) v
  have hg : g ∈ (Nₖ).torus := ((Nₖ).torusPoints g).2 ⟨v, markedTorusHom_apply M _ v⟩
  let t : (Nₖ).torus := ⟨g, hg⟩
  let n : C.N := ⟨g, (Nₖ).torus_le hg⟩
  let e := (Nₖ).lift 1
  have hl : (Nₖ).label (n * e) = 1 := by
    rw [map_mul, ((Nₖ).labelKernel n).2 hg, (Nₖ).lift_label, mul_one]
  have hte : (Nₖ).torusPart (n * e) = t := by
    apply Subtype.ext
    change ((n * e * ((Nₖ).lift ((Nₖ).label (n * e)))⁻¹ : C.N) : FieldPoints M K) = g
    rw [hl]
    change (g : FieldPoints M K) * (e : FieldPoints M K) * (e : FieldPoints M K)⁻¹ = g
    exact mul_inv_cancel_right _ _
  have he : C.affine e = 1 := by
    rw [split_affine_integral H e, (Nₖ).lift_label]
    · change ((cocharacterAction D 1).baseChange ℤ ℚ D.Y D.Y).toAffineEquiv = 1
      rw [map_one, LinearEquiv.baseChange_one]
      rfl
    · exact ⟨markedWeylWord M.toIntegralMarking (integralRing Oₖ) ((Nₖ).word 1),
        (base_change_word M _ _).trans ((Nₖ).lift_point 1).symm⟩
  have ht : ((Nₖ).translation t).toAdd = -y := by
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.toLinearMap χ ((Nₖ).translation t).toAdd = D.datum.toLinearMap χ (-y)
    rw [(Nₖ).characterLog t v (markedTorusHom_apply M _ v)]
    change WithZero.log (normalizedValuation K ((π ^ D.datum.toLinearMap χ y : Kˣ) : K)) = _
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, WithZero.log_zpow, WithZero.log_exp, map_neg, zsmul_eq_mul]
    simp
  refine ⟨n, rfl, fun x => ?_⟩
  have h := H (n * e) x
  rw [map_mul, he, mul_one, hl, hte, ht] at h
  change (C.affine n) x = (cocharacterAction D 1).baseChange ℤ ℚ D.Y D.Y x + _ at h
  simpa [LinearEquiv.baseChange_one] using h

/-- If an integral pinned word has trivial Weyl label, its rational
specialization is toral. Factoring the integral point through the closed
torus makes it a sign point, and the same identity holds in every field. -/
private theorem integral_word_power_sq
    (word : List D.I) (hw : ∀ i ∈ word, i ∈ D.base.support) (m : ℕ)
    (hlabel : ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod : D.datum.weylGroup) ^ m = 1) :
    (markedWeylWord M.toIntegralMarking (integralRing K) word ^ m) ^ 2 = 1 := by
  let Q := ULift.{u} ℚ
  obtain ⟨F⟩ := LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer.markedFibreNormalizer Q M
  obtain ⟨n, hn, hq⟩ := splitMarkedNormalizerWord F word hw
  obtain ⟨T, hT, _⟩ :=
    LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer.fibreNormalizerTorusAction F
  let q : F.label.ker := ⟨n ^ m, by rw [MonoidHom.mem_ker, map_pow, hq, hlabel]⟩
  let v := T.symm q
  let f := integralRingMap (algebraMap Integers.{u} Q)
  let z := markedWeylWord M.toIntegralMarking (integralRing Integers.{u}) word ^ m
  have hz : changeRingHom M.group f z = markedTorusHom M (integralRing Q) v := by
    have hv := hT v
    change F.point (T v).val = _ at hv
    rw [T.apply_symm_apply] at hv
    change F.point (n ^ m) = _ at hv
    rw [map_pow F.point, hn] at hv
    rw [show z = _ from rfl, map_pow, base_change_word, markedTorusHom_apply]
    exact hv
  let e : Integers.{u} ≃+* ℤ := ULift.ringEquiv
  letI : IsDomain Integers.{u} := e.injective.isDomain e
  have hf : Function.Injective f.hom :=
    ULift.up_injective.comp ((Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ)).comp e.injective)
  obtain ⟨t, ht, _⟩ := integral_torus_factor M f hf z v hz
  have hsign : t ^ 2 = 1 := by
    apply MonoidHom.ext
    intro x
    apply Units.ext
    apply e.injective
    exact congrArg Units.val (Int.units_sq (Units.map e.toMonoidHom (t x)))
  let s := changeRingHom M.group (integralRingMap (algebraMap Integers.{u} K))
  have hzs : s z = markedWeylWord M.toIntegralMarking (integralRing K) word ^ m := by
    rw [show z = _ from rfl, map_pow, base_change_word]
  rw [← hzs, ← ht, ← map_pow, ← map_pow, hsign, map_one, map_one]

end LocalLifts


section Representatives

attribute [local instance] integerAlgebra
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open scoped WithZero

private theorem inner_length_zero_representatives.{u} : InnerLengthZeroRepresentatives.{u} := by
  classical
  intro K _ _ _ _ D E M M' c p p' e X _ n b hn hnum had π hπ A z
  let C := X.ad
  let Q := X.typeQuotient
  let N := C.localIwahori.normalizer
  by_cases hz : z = 1
  · subst z
    refine ⟨0, [], 1, by simp, ?_, by simp, by simp,
      (lengthZeroNormalizer X.ad).one_mem, IsOfFinOrder.one, by simp, fun _ => rfl⟩
    have h := (torusCocharacterHom M' (integralRing K) π).map_one
    change markedTorusHom M' (integralRing K) (cocharacter E 0 (integralRing K) π) = 1 at h
    rw [markedTorusHom_apply] at h
    change (1 : FieldPoints M' K) = _ * _
    rw [h]
    simp [markedWeylWord]
  let z₀ : C.N := Q.lift z
  let w₀ := N.label z₀
  let y := -(N.translation (N.torusPart z₀)).toAdd
  have haff := X.ad_points.2.2.2.2.2.2.1
  obtain ⟨words, hsimp, hprod⟩ := simpleWeylWords E
  let word := words w₀
  have hw := hsimp w₀
  have hw₀ := hprod w₀
  obtain ⟨v, hv, hvl⟩ := split_simple_word_label X.ad_points word hw
  have hv₀ : N.label v = w₀ := hvl.trans hw₀
  obtain ⟨s, hs, hsa⟩ := split_affine_uniformizer_cocharacter (C := C) haff π hπ y
  let t : C.N := s * v
  let w := cocharacterAction E w₀
  let R := integralRing K
  let O := (ValuativeRel.valuation K).valuationSubring
  have hwa : C.affine v = (w.baseChange ℤ ℚ E.Y E.Y).toAffineEquiv := by
    rw [split_affine_integral (C := C) haff v, hv₀]
    all_goals try rfl
    exact ⟨markedWeylWord M'.toIntegralMarking (integralRing O) word,
      (base_change_word M' (integralRingMap O.subtype) word).trans hv.symm⟩
  have hta (x : ℚ ⊗[ℤ] E.Y) :
      C.affine t x = w.baseChange ℤ ℚ E.Y E.Y x + ((1 : ℚ) ⊗ₜ[ℤ] (-y)) := by
    change C.affine (s * v) x = _
    rw [map_mul, AffineEquiv.coe_mul, Function.comp_apply, hsa, hwa]
    rfl
  have hat : C.affine t = z.val.val := by
    rw [← Q.affine_lift z]
    ext x
    rw [hta, haff z₀ x]
    change w.baseChange ℤ ℚ E.Y E.Y x + (1 : ℚ) ⊗ₜ[ℤ] (-y) =
      w.baseChange ℤ ℚ E.Y E.Y x + (1 : ℚ) ⊗ₜ[ℤ] ((N.translation (N.torusPart z₀)).toAdd)
    rw [show -y = (N.translation (N.torusPart z₀)).toAdd from neg_neg _]
  have htype : typeChange Q t = z := type_eq_label Q t z hat
  have ht_eq : (t : FieldPoints M' K) =
      torusCocharacterHom M' R π (Multiplicative.ofAdd y) *
        markedWeylWord M'.toIntegralMarking R word := by
    change (s : FieldPoints M' K) * (v : FieldPoints M' K) = _
    rw [hs, hv]
    rfl
  have hlen : (t : FieldPoints M' K) ∈ lengthZeroNormalizer C :=
    lengthZero_mem_iff.mpr ⟨z, hat⟩
  have hfinite : IsOfFinOrder (t : FieldPoints M' K) ∧
      (t : FieldPoints M' K) ^ (Nat.card (alcoveStabilizer A (A.alcove p')) * 2) = 1 := by
    let m := Nat.card (alcoveStabilizer A (A.alcove p'))
    have hm : m ≠ 0 := by
      have hc := exceptional_alcove_quotient_order X n b hn hnum had
      change m = _ at hc
      rw [hc]
      split_ifs <;> decide
    have hpow : (C.affine t) ^ m = 1 := by
      have hz' : z ^ m = 1 := pow_card_eq_one' (x := z)
      rw [hat]
      exact congrArg (fun a : alcoveStabilizer A (A.alcove p') => a.val.val) hz'
    have hlin : (C.affine t).linear = w.baseChange ℤ ℚ E.Y E.Y :=
      affine_linear_of_apply _ _ _ hta
    obtain ⟨bY, hbY⟩ := integral_coweight_coordinates E b had
    obtain ⟨fY, hfY⟩ := coweight_lattice_equiv E b bY hbY
    have hinj : Function.Injective (fun y : E.Y => (1 : ℚ) ⊗ₜ[ℤ] y) :=
      fun _ _ h => fY.injective (Subtype.ext ((hfY _).trans (h.trans (hfY _).symm)))
    have hsum : ∑ j ∈ Finset.range m, (w ^ j) y = 0 := by
      have h := affine_pow_zero (C.affine t) m
      have ht0 := hta 0
      rw [map_zero (w.baseChange ℤ ℚ E.Y E.Y), zero_add] at ht0
      rw [hpow, hlin, ht0] at h
      change (0 : ℚ ⊗[ℤ] E.Y) =
        ∑ j ∈ Finset.range m, ((w.baseChange ℤ ℚ E.Y E.Y) ^ j)
          ((1 : ℚ) ⊗ₜ[ℤ] (-y)) at h
      let lift : E.Y →ₗ[ℤ] (ℚ ⊗[ℤ] E.Y) := TensorProduct.mk ℤ ℚ E.Y 1
      have hh : 0 = lift (∑ j ∈ Finset.range m, (w ^ j) (-y)) := by
        rw [map_sum, h]
        apply Finset.sum_congr rfl
        intro j _
        rw [← LinearEquiv.baseChange_pow, LinearEquiv.baseChange_tmul]
        rfl
      simp_rw [map_neg, Finset.sum_neg_distrib] at hh
      apply hinj
      change lift _ = lift 0
      rw [map_zero, ← neg_eq_zero, ← map_neg, ← hh]
    have hwPow : w ^ m = 1 := by
      have h := congrArg ((AffineEquiv.linearHom : ((ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)) →* _)) hpow
      rw [map_pow, map_one] at h
      change (C.affine t).linear ^ m = 1 at h
      rw [hlin, ← LinearEquiv.baseChange_pow] at h
      ext u
      apply hinj
      have hh := LinearEquiv.congr_fun h ((1 : ℚ) ⊗ₜ[ℤ] u)
      rwa [LinearEquiv.baseChange_tmul] at hh
    have hlabel : ((word.map (RootPairing.weylGroup.ofIdx E.datum)).prod : E.datum.weylGroup) ^ m = 1 := by
      apply Subtype.ext
      apply (RootPairing.Equiv.coweightHom_injective E.datum)
      have h : cocharacterAction E (((word.map (RootPairing.weylGroup.ofIdx E.datum)).prod) ^ m) = 1 := by
        rw [hw₀, map_pow]
        exact hwPow
      have hh := congrArg (fun a : E.Y ≃ₗ[ℤ] E.Y => MulOpposite.op a.symm) h
      exact hh.trans ((RootPairing.Equiv.coweightHom E.datum).map_one).symm
    have hp := torus_word_power M' R word π y m
    dsimp only at hp
    rw [hw₀, show cocharacterAction E w₀ = w from rfl, hsum, ← ht_eq] at hp
    change (t : FieldPoints M' K) ^ m = torusCocharacterHom M' R π 1 *
      markedWeylWord M'.toIntegralMarking R word ^ m at hp
    rw [map_one, one_mul] at hp
    have hsign := integral_word_power_sq (K := K) (M := M') word hw m hlabel
    have htSign : ((t : FieldPoints M' K) ^ m) ^ 2 = 1 := hp.symm ▸ hsign
    exact ⟨(isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, htSign⟩).of_pow hm,
      (pow_mul _ _ _).trans htSign⟩
  refine ⟨y, word, t, hw, ht_eq.trans ?_, hat, htype, hlen, hfinite.1, hfinite.2, fun h => (hz h).elim⟩
  rw [show torusCocharacterHom M' R π (Multiplicative.ofAdd y) =
      markedTorusHom M' R (cocharacter E y R π) from rfl, markedTorusHom_apply]

end Representatives

theorem exceptionalAlcoveQuotientOrder.{u} : ExceptionalAlcoveQuotientOrder.{u} :=
  exceptional_alcove_quotient_order

theorem stableAlcoveStabilizer.{u} : StableAlcoveStabilizer.{u} :=
  stable_alcove_stabilizer

theorem markedAlcoveCoefficientComparison.{u} : MarkedAlcoveCoefficientComparison.{u} :=
  marked_alcove_coefficient_comparison
    LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding.splitAffineBuildings

theorem outerAlcoveTypeCorrection.{u} : OuterAlcoveTypeCorrection.{u} :=
  outer_alcove_type_correction

theorem innerLengthZeroRepresentatives.{u} : InnerLengthZeroRepresentatives.{u} :=
  inner_length_zero_representatives

theorem scalarAlcoveCocycleInflation.{u} : ScalarAlcoveCocycleInflation.{u} :=
  scalar_alcove_cocycle_inflation

theorem innerAlcoveRepresentativeCocycle.{u} : InnerAlcoveRepresentativeCocycle.{u} :=
  inner_alcove_representative_cocycle

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives
