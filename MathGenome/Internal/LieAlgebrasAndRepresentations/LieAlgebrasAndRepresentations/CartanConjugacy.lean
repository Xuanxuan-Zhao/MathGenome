import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanEqualsToral
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RegularSemisimple
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanConjugacy

/-! Conjugacy by convergent inner exponentials, using the connected regular
semisimple locus and the local conjugation chart. -/
universe u
namespace LieAlgebrasAndRepresentations

noncomputable def innerAutomorphisms (L : Type u) [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] : Subgroup (L ≃ₗ[ℂ] L) :=
  Specs.LieAlgebrasAndRepresentations.CartanConjugacy.innerAutomorphisms_value L

/-- Every member of the generated subgroup lifts to a Lie algebra automorphism. -/
theorem exists_lieEquiv_of_mem_innerAutomorphisms {L : Type u}
    [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {e : L ≃ₗ[ℂ] L} (he : e ∈ innerAutomorphisms L) :
    ∃ f : L ≃ₗ⁅ℂ⁆ L, f.toLinearEquiv = e := by
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ f : L ≃ₗ⁅ℂ⁆ L, f.toLinearEquiv = g) ?_ ?_ ?_ ?_ he
  · rintro g ⟨x, hx⟩
    refine ⟨RegularSemisimple.expAdEquiv x, LinearEquiv.ext fun y => ?_⟩
    exact (LinearMap.congr_fun hx y).symm
  · exact ⟨LieEquiv.refl, rfl⟩
  · rintro g h _ _ ⟨f, rfl⟩ ⟨k, rfl⟩
    exact ⟨k.trans f, rfl⟩
  · rintro g _ ⟨f, rfl⟩
    exact ⟨f.symm, rfl⟩

namespace CartanConjugacy
open Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
open Specs.LieAlgebrasAndRepresentations.RegularSemisimple
open RegularSemisimple
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

def IsInner (e : L ≃ₗ⁅ℂ⁆ L) : Prop := e.toLinearEquiv ∈ innerAutomorphisms L

lemma inner_one : IsInner (LieEquiv.refl : L ≃ₗ⁅ℂ⁆ L) :=
  (innerAutomorphisms L).one_mem

lemma inner_trans {e f : L ≃ₗ⁅ℂ⁆ L} (he : IsInner e) (hf : IsInner f) :
    IsInner (e.trans f) := (innerAutomorphisms L).mul_mem hf he

lemma inner_symm {e : L ≃ₗ⁅ℂ⁆ L} (he : IsInner e) : IsInner e.symm :=
  (innerAutomorphisms L).inv_mem he

lemma inner_exp (x : L) : IsInner (expAdEquiv x) :=
  Subgroup.subset_closure ⟨x, rfl⟩

lemma map_refl (H : LieSubalgebra ℂ L) : H.map (LieEquiv.refl.toLieHom) = H := by
  ext x
  simp only [LieSubalgebra.mem_map, LieEquiv.coe_toLieHom, LieEquiv.refl_apply]
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

lemma map_trans (H : LieSubalgebra ℂ L) (e f : L ≃ₗ⁅ℂ⁆ L) :
    H.map (e.trans f).toLieHom = (H.map e.toLieHom).map f.toLieHom := by
  ext x
  simp only [LieSubalgebra.mem_map, LieEquiv.coe_toLieHom, LieEquiv.trans_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

lemma map_centralizer (e : L ≃ₗ⁅ℂ⁆ L) (x : L) :
    (elementCentralizer x).map e.toLieHom = elementCentralizer (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ⁅e x, e z⁆ = 0
    rw [← e.map_lie, show ⁅x, z⁆ = 0 from hz, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change ⁅x, e.symm y⁆ = 0
    apply e.toLinearEquiv.injective
    change e ⁅x, e.symm y⁆ = e 0
    rw [e.map_lie, e.apply_symm_apply, map_zero]
    exact hy

/-- Equivalence of the Cartans associated to two elements, by the generated
inner subgroup. This relation is defined on all elements. -/
def Related (x y : L) : Prop :=
  ∃ e : L ≃ₗ⁅ℂ⁆ L, IsInner e ∧ (elementCentralizer x).map e.toLieHom = elementCentralizer y

lemma related_refl (x : L) : Related x x :=
  ⟨LieEquiv.refl, inner_one, map_refl _⟩

lemma related_trans {x y z : L} (hxy : Related x y) (hyz : Related y z) : Related x z := by
  obtain ⟨e, he, hE⟩ := hxy
  obtain ⟨f, hf, hF⟩ := hyz
  exact ⟨e.trans f, inner_trans he hf, by rw [map_trans, hE, hF]⟩

lemma related_symm {x y : L} (hxy : Related x y) : Related y x := by
  obtain ⟨e, he, hE⟩ := hxy
  refine ⟨e.symm, inner_symm he, ?_⟩
  rw [← hE, ← map_trans, LieEquiv.self_trans_symm, map_refl]

/-- The inverse-function chart gives a neighborhood in one equivalence class.
Its intersection with the regular locus is still an ambient open neighborhood. -/
lemma local_related (hss : IsSemisimple ℂ L) (x : L)
    (hx : x ∈ minimalMultiplicityLocus L) :
    letI : NormedAddCommGroup L := algebraNorm
    letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
      (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
    ∃ U : Set L, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ minimalMultiplicityLocus L ∧ Related x y := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  let H := elementCentralizer x
  have hH : IsMaximalToral H := (regular_centralizer L hss x hx).1
  let h : H := ⟨x, lie_self x⟩
  have hh : h ∈ rootRegular H := by
    rw [← toral_regular L hss H hH]
    exact hx
  obtain ⟨M, hM⟩ := H.toSubmodule.exists_isCompl
  obtain ⟨e, he, hd, φ, hφ, hs⟩ := local_conjugation L hss H hH M hM.symm h hh
  have hpoint : φ (0, h) = x := by
    rw [hφ]
    change (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (LieAlgebra.ad ℂ L (0 : L)))) x = x
    simp
  refine ⟨(φ '' φ.source) ∩ minimalMultiplicityLocus L,
    (φ.isOpen_image_of_subset_source φ.open_source Set.Subset.rfl).inter
      (MinimalZeroMultiplicityLocus.topology L).1,
    ⟨⟨(0, h), hs, hpoint⟩, hx⟩, ?_⟩
  rintro y ⟨⟨p, hp, rfl⟩, hy⟩
  refine ⟨hy, ?_⟩
  have hE : φ p = expAdEquiv (p.1 : L) (p.2 : L) := by rw [hφ]; rfl
  have hz : (p.2 : L) ∈ minimalMultiplicityLocus L := by
    change zeroMultiplicity L (p.2 : L) = minimalZeroMultiplicity L
    change zeroMultiplicity L (φ p) = minimalZeroMultiplicity L at hy
    rwa [hE, zeroMultiplicity_lieEquiv] at hy
  have hc : H = elementCentralizer (p.2 : L) :=
    (regular_centralizer L hss (p.2 : L) hz).2.2.2 H hH p.2.property
  refine ⟨expAdEquiv (p.1 : L), inner_exp _, ?_⟩
  change H.map _ = _
  calc
    H.map (expAdEquiv (p.1 : L)).toLieHom =
        (elementCentralizer (p.2 : L)).map (expAdEquiv (p.1 : L)).toLieHom :=
      congrArg (fun J : LieSubalgebra ℂ L => J.map (expAdEquiv (p.1 : L)).toLieHom) hc
    _ = elementCentralizer (expAdEquiv (p.1 : L) (p.2 : L)) := map_centralizer _ _
    _ = elementCentralizer (φ p) := congrArg elementCentralizer hE.symm

/-- A connected set cannot be partitioned into open equivalence classes. -/
lemma related_of_regular (hss : IsSemisimple ℂ L) (x y : L)
    (hx : x ∈ minimalMultiplicityLocus L) (hy : y ∈ minimalMultiplicityLocus L) :
    Related x y := by
  classical
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  let U : Set L := {z | z ∈ minimalMultiplicityLocus L ∧ Related x z}
  let V : Set L := {z | z ∈ minimalMultiplicityLocus L ∧ ¬ Related x z}
  have hU : IsOpen U := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro z ⟨hz, hxz⟩
    obtain ⟨W, ho, hw, hW⟩ := local_related hss z hz
    exact ⟨W, fun t ht => ⟨(hW t ht).1, related_trans hxz (hW t ht).2⟩, ho, hw⟩
  have hV : IsOpen V := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro z ⟨hz, hxz⟩
    obtain ⟨W, ho, hw, hW⟩ := local_related hss z hz
    refine ⟨W, ?_, ho, hw⟩
    intro t ht
    exact ⟨(hW t ht).1, fun hxt => hxz (related_trans hxt (related_symm (hW t ht).2))⟩
  have hd : Disjoint U V := Set.disjoint_left.mpr fun z hu hv => hv.2 hu.2
  have hcover : minimalMultiplicityLocus L ⊆ U ∪ V := by
    intro z hz
    by_cases hr : Related x z
    · exact Or.inl ⟨hz, hr⟩
    · exact Or.inr ⟨hz, hr⟩
  have hconn := (MinimalZeroMultiplicityLocus.topology L).2.2.isConnected.isPreconnected
  exact (hconn.subset_left_of_subset_union hU hV hd hcover
    ⟨x, hx, hx, related_refl x⟩ hy).2

end CartanConjugacy

/-- All Cartans of a finite-dimensional complex semisimple Lie algebra are
conjugate by the subgroup generated by convergent adjoint exponentials. -/
theorem cartan_conjugacy :
    Specs.LieAlgebrasAndRepresentations.CartanConjugacy.cartan_conjugacy_type := by
  intro L _ _ _ hss H K hH hK
  have hHt := (isCartan_iff_maximal_toral hss H).mp hH
  have hKt := (isCartan_iff_maximal_toral hss K).mp hK
  obtain ⟨h, hh⟩ := RegularSemisimple.rootRegular_nonempty H hHt.1
  obtain ⟨k, hk⟩ := RegularSemisimple.rootRegular_nonempty K hKt.1
  have hhR : (h : L) ∈ Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus.minimalMultiplicityLocus L := by
    have := RegularSemisimple.toral_regular L hss H hHt
    rw [← this] at hh
    exact hh
  have hkR : (k : L) ∈ Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus.minimalMultiplicityLocus L := by
    have := RegularSemisimple.toral_regular L hss K hKt
    rw [← this] at hk
    exact hk
  obtain ⟨e, he, hE⟩ := CartanConjugacy.related_of_regular hss (h : L) (k : L) hhR hkR
  refine ⟨e, he, ?_⟩
  rwa [RegularSemisimple.centralizer_eq_torus_of_rootRegular hss H hHt h hh,
    RegularSemisimple.centralizer_eq_torus_of_rootRegular hss K hKt k hk] at hE

end LieAlgebrasAndRepresentations
