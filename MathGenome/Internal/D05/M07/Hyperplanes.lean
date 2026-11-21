import MathGenome.Internal.Specs.D05.M07.Hyperplanes
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free

/-! K05.07.hyperplanes: maximal proper subspaces and algebraic functionals. -/

namespace D05.M07.Hyperplanes

abbrev hyperplane (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) : Prop := IsCoatom U

theorem hyperplane_iff_maximal_proper :
    Specs.D05.M07.Hyperplanes.hyperplane_iff_maximal_proper := by
  intro K V _ _ _ U
  rfl

theorem exists_value_one : Specs.D05.M07.Hyperplanes.exists_value_one := by
  intro K V _ _ _ f hf
  obtain ⟨x, hx⟩ : ∃ x : V, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    simpa using not_exists.mp h x
  exact ⟨(f x)⁻¹ • x, by simp [hx]⟩

theorem kernel_unique_decomposition :
    Specs.D05.M07.Hyperplanes.kernel_unique_decomposition := by
  intro K V _ _ _ f v hv x
  refine ⟨(⟨x - f x • v, by simp [LinearMap.mem_ker, hv]⟩, f x), ?_, ?_⟩
  · exact (sub_add_cancel x (f x • v)).symm
  · rintro ⟨u, a⟩ h
    have ha : a = f x := by
      have := congrArg f h
      simpa [u.property, hv] using this.symm
    apply Prod.ext
    · apply Subtype.ext
      change (u : V) = x - f x • v
      rw [← ha, h]
      exact (add_sub_cancel_right (u : V) (a • v)).symm
    · exact ha

private theorem kernel_isCoatom {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.Dual K V) (hf : f ≠ 0) : IsCoatom (LinearMap.ker f) := by
  obtain ⟨v, hv⟩ := exists_value_one f hf
  refine ⟨?_, ?_⟩
  · intro htop
    have : f v = 0 := (show v ∈ LinearMap.ker f from htop ▸ Submodule.mem_top)
    exact one_ne_zero (hv.symm.trans this)
  · intro W hW
    obtain ⟨x, hxW, hxf⟩ := IsConcreteLE.exists_of_lt hW
    have hfx : f x ≠ 0 := hxf
    have hspan := LinearMap.span_singleton_sup_ker_eq_top f hfx
    apply top_unique
    rw [← hspan]
    exact sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxW)) hW.le

private theorem quotient_rank_of_kernel {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : Module.Dual K V) (hf : f ≠ 0) :
    Module.rank K (V ⧸ LinearMap.ker f) = 1 := by
  obtain ⟨v, hv⟩ := exists_value_one f hf
  apply rank_eq_one (Submodule.Quotient.mk v)
  · intro hz
    have : f v = 0 := (Submodule.Quotient.mk_eq_zero (LinearMap.ker f)).mp hz
    exact one_ne_zero (hv.symm.trans this)
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker f) q
    refine ⟨f x, ?_⟩
    change Submodule.Quotient.mk (f x • v) = Submodule.Quotient.mk x
    apply (Submodule.Quotient.eq (LinearMap.ker f)).mpr
    simp [LinearMap.mem_ker, hv]

theorem quotient_dimension_one_iff_kernel :
    Specs.D05.M07.Hyperplanes.quotient_dimension_one_iff_kernel := by
  intro K V _ _ _ U
  constructor
  · intro h
    obtain ⟨e⟩ := (Module.nonempty_linearEquiv_iff_rank_eq_one
      (R := K) (M := V ⧸ U)).mpr h
    let f : Module.Dual K V := e.symm.toLinearMap.comp U.mkQ
    have hsurj : Function.Surjective f := e.symm.surjective.comp U.mkQ_surjective
    refine ⟨f, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := hsurj 1
      intro hf
      have hzero : f v = 0 := by rw [hf]; rfl
      exact one_ne_zero (hv.symm.trans hzero)
    · ext x
      simp [f]
  · rintro ⟨f, hf, rfl⟩
    exact quotient_rank_of_kernel f hf

theorem maximal_proper_iff_quotient_dimension_one :
    Specs.D05.M07.Hyperplanes.maximal_proper_iff_quotient_dimension_one := by
  intro K V _ _ _ U
  constructor
  · intro hU
    obtain ⟨v, hv⟩ := SetLike.exists_notMem_of_ne_top U hU.1 rfl
    have hv0 : v ≠ 0 := by rintro rfl; exact hv U.zero_mem
    let e := (LinearEquiv.toSpanNonzeroSingleton K V v hv0).trans
      (U.quotientEquivOfIsCompl (K ∙ v)
        (Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hU hv)).symm
    exact (Module.nonempty_linearEquiv_iff_rank_eq_one).mp ⟨e⟩
  · intro h
    obtain ⟨f, hf, rfl⟩ := (quotient_dimension_one_iff_kernel U).mp h
    exact kernel_isCoatom f hf

theorem maximal_proper_iff_kernel :
    Specs.D05.M07.Hyperplanes.maximal_proper_iff_kernel := by
  intro K V _ _ _ U
  exact (maximal_proper_iff_quotient_dimension_one U).trans
    (quotient_dimension_one_iff_kernel U)

theorem same_kernel_iff_nonzero_smul :
    Specs.D05.M07.Hyperplanes.same_kernel_iff_nonzero_smul := by
  intro K V _ _ _ f g hf hg
  constructor
  · intro hker
    obtain ⟨v, hv⟩ := exists_value_one f hf
    have hc : g v ≠ 0 := by
      intro hz
      have : v ∈ LinearMap.ker f := hker ▸ hz
      have : f v = 0 := this
      exact one_ne_zero (hv.symm.trans this)
    refine ⟨g v, hc, ?_⟩
    ext x
    have hx : x - f x • v ∈ LinearMap.ker f := by
      simp [LinearMap.mem_ker, hv]
    have hxg : x - f x • v ∈ LinearMap.ker g := hker ▸ hx
    change g (x - f x • v) = 0 at hxg
    simpa [map_sub, map_smul, sub_eq_zero, mul_comm] using hxg
  · rintro ⟨c, hc, rfl⟩
    exact (LinearMap.ker_smul f c hc).symm

theorem zero_space_boundary : Specs.D05.M07.Hyperplanes.zero_space_boundary := by
  intro K V _ _ _ _
  constructor
  · intro U hU
    apply hU.1
    exact Submodule.eq_top_iff'.mpr fun x => by
      have : x = 0 := Subsingleton.elim _ _
      simp [this]
  · intro f
    ext x
    have : x = 0 := Subsingleton.elim _ _
    simp [this]

end D05.M07.Hyperplanes
