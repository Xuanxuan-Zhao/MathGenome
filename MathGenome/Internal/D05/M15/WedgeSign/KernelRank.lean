import MathGenome.Internal.Specs.D05.M15.WedgeSign.KernelRank
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M06.Complement
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

noncomputable section
namespace D05.M15.WedgeSign.KernelRank
open Specs.D05.M15.WedgeSign.KernelRank

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Factoring through the actual image also factors the induced algebra map. -/
theorem exterior_map_range_factor (f : V →ₗ[K] W) :
    (_root_.ExteriorAlgebra.map (LinearMap.range f).subtype).comp
      (_root_.ExteriorAlgebra.map f.rangeRestrict) = _root_.ExteriorAlgebra.map f := by
  rw [_root_.ExteriorAlgebra.map_comp_map]
  rfl

theorem image : Specs.D05.M15.WedgeSign.KernelRank.image := by
  intro K V W _ _ _ _ _ _ _ f
  change (_root_.ExteriorAlgebra.map f).range = (_root_.ExteriorAlgebra.map f.range.subtype).range
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_root_.ExteriorAlgebra.map f.rangeRestrict a,
      AlgHom.congr_fun (exterior_map_range_factor f) a⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (_root_.ExteriorAlgebra.map_surjective_iff.mpr
      f.surjective_rangeRestrict) b
    exact ⟨a, (AlgHom.congr_fun (exterior_map_range_factor f) a).symm⟩

theorem image_embedding : Specs.D05.M15.WedgeSign.KernelRank.image_embedding := by
  intro K W _ _ _ S
  exact _root_.ExteriorAlgebra.map_injective_field (Submodule.ker_subtype S)

theorem power_image : Specs.D05.M15.WedgeSign.KernelRank.power_image := by
  intro K V W _ _ _ _ _ _ _ f p
  have hf : (LinearMap.range f).subtype.comp f.rangeRestrict = f := rfl
  change LinearMap.range (exteriorPower.map p f) = _
  conv_lhs => rw [← hf, exteriorPower.map_comp]
  rw [LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (exteriorPower.map_surjective f.surjective_rangeRestrict)]
  simp

theorem power_rank : Specs.D05.M15.WedgeSign.KernelRank.power_rank := by
  intro K V W _ _ _ _ _ _ _ f p
  rw [power_image f p]
  change Module.finrank K (LinearMap.range (exteriorPower.map p (LinearMap.range f).subtype)) = _
  rw [LinearMap.finrank_range_of_inj
    (exteriorPower.map_injective_field (Submodule.subtype_injective _))]
  exact D05.M15.ExteriorBasis.dimension p

theorem degree_zero_rank : Specs.D05.M15.WedgeSign.KernelRank.degree_zero_rank := by
  intro K V W _ _ _ _ _ _ _ f
  rw [power_rank f 0, Nat.choose_zero_right]

theorem above_rank : Specs.D05.M15.WedgeSign.KernelRank.above_rank := by
  intro K V W _ _ _ _ _ _ _ f p hp
  apply LinearMap.range_eq_bot.mp
  apply (Submodule.finrank_eq_zero).mp
  rw [power_rank f p, Nat.choose_eq_zero_of_lt hp]

theorem fixes_unit : Specs.D05.M15.WedgeSign.KernelRank.fixes_unit := by
  intro K V W _ _ _ _ _ f
  exact map_one _

theorem quotient_generator : Specs.D05.M15.WedgeSign.KernelRank.quotient_generator := by
  intro K V _ _ _ U x
  exact _root_.ExteriorAlgebra.map_apply_ι U.mkQ x

/-- A kernel vector becomes zero in the quotient by its generated ideal. -/
theorem quotientProjection_generator_zero (U : Submodule K V) (x : V) (hx : x ∈ U) :
    quotientProjection U (_root_.ExteriorAlgebra.ι K x) = 0 := by
  apply (generatedIdeal U).ringCon.eq.mpr
  exact TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩

/-- The map on generators V/U → Λ(V)/⟨U⟩. -/
def quotientGenerator (U : Submodule K V) : V ⧸ U →ₗ[K] ExteriorQuotient U :=
  U.liftQ ((quotientProjection U).toLinearMap.comp (_root_.ExteriorAlgebra.ι K))
    (fun x hx => quotientProjection_generator_zero U x hx)

@[simp] theorem quotientGenerator_mkQ (U : Submodule K V) (x : V) :
    quotientGenerator U (U.mkQ x) = quotientProjection U (_root_.ExteriorAlgebra.ι K x) := rfl

/-- The reverse universal-property map; no choice of complement occurs. -/
def quotientReverse (U : Submodule K V) :
    _root_.ExteriorAlgebra K (V ⧸ U) →ₐ[K] ExteriorQuotient U :=
  _root_.ExteriorAlgebra.lift K ⟨quotientGenerator U, by
    intro x
    obtain ⟨v, rfl⟩ := U.mkQ_surjective x
    rw [quotientGenerator_mkQ, ← map_mul, _root_.ExteriorAlgebra.ι_sq_zero, map_zero]⟩

theorem quotientReverse_comp_map (U : Submodule K V) :
    (quotientReverse U).comp (_root_.ExteriorAlgebra.map U.mkQ) = quotientProjection U := by
  apply _root_.ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    _root_.ExteriorAlgebra.map_apply_ι]
  rw [quotientReverse, _root_.ExteriorAlgebra.lift_ι_apply, quotientGenerator_mkQ]

/-- Exactness of the exterior quotient, proved by the two universal properties. -/
theorem quotient_map_kernel (U : Submodule K V) :
    TwoSidedIdeal.ker (_root_.ExteriorAlgebra.map U.mkQ).toRingHom = generatedIdeal U := by
  apply le_antisymm
  · intro x hx
    have h := AlgHom.congr_fun (quotientReverse_comp_map U) x
    change quotientReverse U (_root_.ExteriorAlgebra.map U.mkQ x) = quotientProjection U x at h
    have hx' : _root_.ExteriorAlgebra.map U.mkQ x = 0 := (TwoSidedIdeal.mem_ker _).mp hx
    rw [hx', map_zero] at h
    exact (generatedIdeal U).ringCon.eq.mp h.symm
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    apply (TwoSidedIdeal.mem_ker _).mpr
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      _root_.ExteriorAlgebra.map_apply_ι]
    have hv' : U.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hv
    rw [hv', map_zero]

theorem kernel : Specs.D05.M15.WedgeSign.KernelRank.kernel := by
  intro K V W _ _ _ _ _ _ _ f
  let U := LinearMap.ker f
  let g : V ⧸ U →ₗ[K] W := U.liftQ f le_rfl
  have hg : Function.Injective g := LinearMap.ker_eq_bot.mp (U.ker_liftQ_eq_bot' f rfl)
  have hgi := _root_.ExteriorAlgebra.map_injective_field (LinearMap.ker_eq_bot.mpr hg)
  have hcomp : (_root_.ExteriorAlgebra.map g).comp (_root_.ExteriorAlgebra.map U.mkQ) =
      _root_.ExteriorAlgebra.map f := by
    rw [_root_.ExteriorAlgebra.map_comp_map, Submodule.liftQ_mkQ]
  rw [← quotient_map_kernel U]
  ext x
  simp only [TwoSidedIdeal.mem_ker]
  change _root_.ExteriorAlgebra.map f x = 0 ↔ _root_.ExteriorAlgebra.map U.mkQ x = 0
  rw [← hcomp]
  change _root_.ExteriorAlgebra.map g (_root_.ExteriorAlgebra.map U.mkQ x) = 0 ↔ _
  exact ⟨fun h => hgi (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

/-- The forward map on the quotient algebra, fixed by its representative formula. -/
def quotientForward (U : Submodule K V) :
    ExteriorQuotient U →ₐ[K] _root_.ExteriorAlgebra K (V ⧸ U) :=
  (generatedIdeal U).ringCon.liftₐ (_root_.ExteriorAlgebra.map U.mkQ) (by
    rw [← quotient_map_kernel U]
    exact le_rfl)

@[simp] theorem quotientForward_projection (U : Submodule K V) (x : _root_.ExteriorAlgebra K V) :
    quotientForward U (quotientProjection U x) = _root_.ExteriorAlgebra.map U.mkQ x := rfl

theorem quotientForward_bijective (U : Submodule K V) :
    Function.Bijective (quotientForward U) := by
  constructor
  · apply RingCon.lift_injective_iff.mpr
    change (generatedIdeal U).ringCon = (TwoSidedIdeal.ker
      (_root_.ExteriorAlgebra.map U.mkQ).toRingHom).ringCon
    rw [quotient_map_kernel]
  · exact RingCon.lift_surjective_of_surjective _
      (_root_.ExteriorAlgebra.map_surjective_iff.mpr U.mkQ_surjective)

/-- The canonical algebra equivalence. Its grading is established below. -/
def quotientEquiv (U : Submodule K V) :
    ExteriorQuotient U ≃ₐ[K] _root_.ExteriorAlgebra K (V ⧸ U) :=
  AlgEquiv.ofBijective (quotientForward U) (quotientForward_bijective U)

theorem quotient_equiv : Specs.D05.M15.WedgeSign.KernelRank.quotient_equiv := by
  intro K V _ _ _ _ U
  refine ⟨quotientEquiv U, fun _ => rfl, ?_⟩
  intro p
  rw [← Submodule.map_comp]
  have h : (quotientEquiv U).toLinearMap.comp (quotientProjection U).toLinearMap =
      (_root_.ExteriorAlgebra.map U.mkQ).toLinearMap := rfl
  rw [h]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact D05.M15.WedgeSign.degree_preserved U.mkQ p y hy
  · intro x hx
    obtain ⟨a, ha⟩ := exteriorPower.map_surjective (n := p) U.mkQ_surjective ⟨x, hx⟩
    refine ⟨a, a.property, ?_⟩
    exact (exteriorPower.coe_map U.mkQ a).symm.trans (congrArg Subtype.val ha)

attribute [local instance] Classical.propDecidable

/-- The coordinate projection which deletes a specified subset of basis vectors. -/
def coordinateProjection {I : Type*} (b : Module.Basis I K V) (S : Set I) : V →ₗ[K] V := by
  classical
  exact b.constr K (fun i => if i ∈ S then 0 else b i)

@[simp] theorem coordinateProjection_basis {I : Type*} (b : Module.Basis I K V)
    (S : Set I) (i : I) :
    coordinateProjection b S (b i) = if i ∈ S then 0 else b i := by
  classical
  exact b.constr_basis K _ i

theorem coordinateProjection_coord {I : Type*} (b : Module.Basis I K V)
    (S : Set I) (i : I) (x : V) :
    b.repr (coordinateProjection b S x) i = if i ∈ S then 0 else b.repr x i := by
  classical
  have h : (b.coord i).comp (coordinateProjection b S) =
      if i ∈ S then 0 else b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ S <;> simp [hi]
    · by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
        simp [coordinateProjection_basis, hi, hj, Module.Basis.coord_apply,
          Module.Basis.repr_self, hij]
  by_cases hi : i ∈ S <;>
    simpa [hi, Module.Basis.coord_apply] using LinearMap.congr_fun h x

theorem coordinateProjection_ker {I : Type*} (b : Module.Basis I K V) (S : Set I) :
    LinearMap.ker (coordinateProjection b S) = Submodule.span K (b '' S) := by
  classical
  ext x
  rw [b.mem_span_image]
  constructor
  · intro hx i hi
    by_contra his
    have h : b.repr x i = 0 := by
      have hx' : coordinateProjection b S x = 0 := hx
      have hc := coordinateProjection_coord b S i x
      rw [hx', map_zero, Finsupp.zero_apply, ite_eq_right his] at hc
      exact hc.symm
    exact (Finsupp.mem_support_iff.mp hi) h
  · intro hx
    change coordinateProjection b S x = 0
    apply b.repr.injective
    ext i
    rw [coordinateProjection_coord]
    by_cases hi : i ∈ S
    · simp [hi]
    · have hz : b.repr x i = 0 := by
        by_contra h
        exact hi (hx (Finsupp.mem_support_iff.mpr h))
      simp [hi, hz]

/-- Exterior powers of a coordinate projection delete precisely the monomials
using at least one deleted index. -/
theorem exterior_map_coordinateProjection {I : Type*} [LinearOrder I]
    (b : Module.Basis I K V) (S : Set I) (t : Finset I) :
    _root_.ExteriorAlgebra.map (coordinateProjection b S) (b.ExteriorAlgebra t) =
      if (∃ i ∈ t, i ∈ S) then 0 else b.ExteriorAlgebra t := by
  classical
  by_cases ht : ∃ i ∈ t, i ∈ S
  · rw [ite_eq_left ht, _root_.ExteriorAlgebra.basis_apply_ofCard b (s := t) rfl,
      _root_.ExteriorAlgebra.map_apply_ιMulti]
    obtain ⟨i, hit, hi⟩ := ht
    obtain ⟨j, hj⟩ := (show i ∈ Set.range (t.orderEmbOfFin rfl) from by simpa using hit)
    apply (_root_.ExteriorAlgebra.ιMulti K t.card).map_coord_zero j
    change coordinateProjection b S (b (t.orderEmbOfFin rfl j)) = 0
    rw [hj, coordinateProjection_basis, ite_eq_left hi]
  · rw [ite_eq_right ht, _root_.ExteriorAlgebra.basis_apply_ofCard b (s := t) rfl,
      _root_.ExteriorAlgebra.map_apply_ιMulti]
    congr 1
    funext j
    change coordinateProjection b S (b (t.orderEmbOfFin rfl j)) = b (t.orderEmbOfFin rfl j)
    rw [coordinateProjection_basis, ite_eq_right]
    exact fun h => ht ⟨_, t.orderEmbOfFin_mem rfl j, h⟩

theorem ideal_monomial_basis : Specs.D05.M15.WedgeSign.KernelRank.ideal_monomial_basis := by
  intro K V _ _ _ _ n b S
  classical
  have h : (_root_.ExteriorAlgebra.map (coordinateProjection b S)).toLinearMap =
      coordinateProjection b.ExteriorAlgebra {t | ∃ i ∈ t, i ∈ S} := by
    apply b.ExteriorAlgebra.ext
    intro t
    by_cases ht : ∃ i ∈ t, i ∈ S <;>
      simpa [coordinateProjection_basis, ht] using exterior_map_coordinateProjection b S t
  constructor
  · intro x
    rw [← coordinateProjection_ker b S,
      ← kernel (coordinateProjection b S), TwoSidedIdeal.mem_ker]
    change (_root_.ExteriorAlgebra.map (coordinateProjection b S)).toLinearMap x = 0 ↔ _
    rw [h]
    change x ∈ LinearMap.ker (coordinateProjection b.ExteriorAlgebra {t | ∃ i ∈ t, i ∈ S}) ↔ _
    rw [coordinateProjection_ker]
  · exact b.ExteriorAlgebra.linearIndependent.comp Subtype.val Subtype.val_injective

end D05.M15.WedgeSign.KernelRank
