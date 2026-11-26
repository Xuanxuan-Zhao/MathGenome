import Specs.LinearAlgebraicGroups.Descent.SmoothPoint
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Descent

variable {k : Type u} [Field k] [IsSepClosed k]

private theorem infinite_of_isSepClosed : Infinite k := by
  by_contra! h
  exact (not_infinite_iff_finite.mpr h) (inferInstance : Infinite k)

omit [IsSepClosed k] in
private theorem exists_rational_point_in_polynomial_open [Infinite k] {n : ℕ}
    {W : Set (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))}
    (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k)),
      s default ∈ W ∧ s ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, hxp, hpW⟩ :=
    (PrimeSpectrum.isBasis_basic_opens (R := MvPolynomial (Fin n) k)).exists_subset_of_mem_open
      hx hW
  have hp : p ≠ 0 := fun e ↦ (PrimeSpectrum.mem_basicOpen p x).mp hxp (e ▸ x.asIdeal.zero_mem)
  obtain ⟨a, ha⟩ : ∃ a : Fin n → k, MvPolynomial.eval a p ≠ 0 := by
    by_contra! H
    exact hp (MvPolynomial.funext (q := 0) (by simpa using H))
  refine ⟨Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)), hpW ?_, ?_⟩
  · change PrimeSpectrum.comap (MvPolynomial.eval a) (⊥ : PrimeSpectrum k) ∈
      PrimeSpectrum.basicOpen p
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr ha
  · rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact MvPolynomial.eval_C c

private theorem exists_rational_point_of_smooth_aux {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (hX : Nonempty X) :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  let : Infinite k := infinite_of_isSepClosed
  obtain ⟨x⟩ := hX
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have htop : U = ⊤ := by
    ext y
    have hy : y = f x := Subsingleton.elim _ _
    simp [hy, show f x ∈ U from e hx]
  subst U
  let φ : CommRingCat.of k ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V e
  have hφ : φ.hom.IsStandardSmooth :=
    (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso _ _).mpr hstd
  have hφSpec : Spec.map φ = hV.fromSpec ≫ f := by
    unfold φ
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e
  obtain ⟨n, g, hg, hEtale⟩ := hφ.exists_etale_mvPolynomial
  let t := Spec.map (CommRingCat.ofHom g)
  have : Etale t := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hEtale
  have hW : IsOpen (Set.range t) := by
    simpa only [Set.image_univ] using t.isOpenMap Set.univ isOpen_univ
  have hxRange : x ∈ Set.range hV.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact hx
  obtain ⟨y, _⟩ := hxRange
  obtain ⟨s, ⟨z, hz⟩, hs⟩ :=
    exists_rational_point_in_polynomial_open hW ⟨t y, y, rfl⟩
  obtain ⟨ℓ, hℓ, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed t s z hz
  refine ⟨ℓ ≫ hV.fromSpec, ?_⟩
  have ht : t ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = Spec.map φ := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hg)
  rw [Category.assoc, ← hφSpec, ← ht, ← Category.assoc, hℓ, hs]

/-- A nonempty smooth finite-type scheme over a separably closed field has a rational point. -/
theorem exists_rational_point_of_smooth {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f] (hX : Nonempty X) :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ :=
  exists_rational_point_of_smooth_aux f hX

/-- A nonempty open subscheme of a smooth finite-type scheme has a rational point
over the same separably closed field. -/
theorem exists_rational_point_of_smooth_open {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
    (U : X.Opens) (hU : Nonempty U) :
    ∃ s : Spec (CommRingCat.of k) ⟶ U, s ≫ (U.ι ≫ f) = 𝟙 _ :=
  exists_rational_point_of_smooth_aux (U.ι ≫ f) hU

end LinearAlgebraicGroups.Descent
