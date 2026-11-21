import MathGenome.Internal.Specs.D07.Ch01.Presentations
import MathGenome.Internal.D07.Ch01.FreeGroupUniversalProperty
import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.D07.Ch01.GroupNormalQuotient

/-!
Generators and relations, `K07.01.presentations` (paper.tex:399–409).

The normal closure is the intersection of all normal subgroups containing the
relators. Its quotient is consequently a group. A generator map extends to the
free group; its normal kernel contains the normal closure exactly when it kills
every relator. The upstream quotient descent theorem supplies the unique
factorization. Free-group uniqueness identifies factorization with agreement
on the presented generators, so this also proves the converse and uniqueness
in the generator formulation.
-/

namespace D07.Ch01.Presentations

universe u v

abbrev Presentation (S : Type u) (R : Set (FreeGroup S)) : Type u :=
  FreeGroup S ⧸ Subgroup.normalClosure R

def projection (S : Type u) (R : Set (FreeGroup S)) :
    FreeGroup S →* Presentation S R :=
  QuotientGroup.mk' (Subgroup.normalClosure R)

def generator (S : Type u) (R : Set (FreeGroup S)) (s : S) : Presentation S R :=
  projection S R (FreeGroup.of s)

theorem normal_closure_eq_intersection (S : Type u) (R : Set (FreeGroup S)) :
    Subgroup.normalClosure R =
      ⨅ (N : Subgroup (FreeGroup S)) (_ : N.Normal) (_ : R ⊆ N), N :=
  Subgroup.normalClosure_eq_iInf

theorem normal_closure_normal (S : Type u) (R : Set (FreeGroup S)) :
    (Subgroup.normalClosure R).Normal := inferInstance

theorem relators_subset_normal_closure (S : Type u) (R : Set (FreeGroup S)) :
    R ⊆ Subgroup.normalClosure R := Subgroup.subset_normalClosure

theorem projection_surjective (S : Type u) (R : Set (FreeGroup S)) :
    Function.Surjective (projection S R) :=
  GroupNormalQuotient.projection_surjective (FreeGroup S) (Subgroup.normalClosure R)

theorem projection_kernel (S : Type u) (R : Set (FreeGroup S)) :
    (projection S R).ker = Subgroup.normalClosure R :=
  GroupNormalQuotient.projection_kernel (FreeGroup S) (Subgroup.normalClosure R)

theorem relators_vanish (S : Type u) (R : Set (FreeGroup S)) (r : FreeGroup S)
    (hr : r ∈ R) : projection S R r = 1 :=
  QuotientGroup.eq_one_iff r |>.mpr (relators_subset_normal_closure S R hr)

theorem descends_unique_iff (S : Type u) (R : Set (FreeGroup S))
    (H : Type v) [Group H] (f : S → H) :
    (∃! φ : Presentation S R →* H,
      φ.comp (projection S R) = FreeGroup.lift f) ↔
      ∀ r ∈ R, FreeGroup.lift f r = 1 := by
  unfold projection
  rw [GroupNormalQuotient.descends_unique_iff]
  constructor
  · intro h r hr
    exact h (relators_subset_normal_closure S R hr)
  · intro h
    letI := KernelImage.kernel_normal (FreeGroup S) H (FreeGroup.lift f)
    exact Subgroup.normalClosure_le_normal h

/-- Agreement on the quotient generators means that composition is the free
extension; this uses uniqueness of the upstream free-group universal property. -/
theorem factorization_iff_generator_values (S : Type u) (R : Set (FreeGroup S))
    (H : Type v) [Group H] (f : S → H) (φ : Presentation S R →* H) :
    φ.comp (projection S R) = FreeGroup.lift f ↔
      ∀ s : S, φ (generator S R s) = f s := by
  constructor
  · intro h s
    exact (DFunLike.congr_fun h (FreeGroup.of s)).trans FreeGroup.lift_apply_of
  · intro h
    obtain ⟨u, _, hu⟩ := FreeGroupUniversalProperty.universal_property S H f
    exact (hu (φ.comp (projection S R)) h).trans
      (hu (FreeGroup.lift f) (fun _ => FreeGroup.lift_apply_of)).symm

theorem induced_hom_unique_iff (S : Type u) (R : Set (FreeGroup S))
    (H : Type v) [Group H] (f : S → H) :
    (∃! φ : Presentation S R →* H,
      ∀ s : S, φ (generator S R s) = f s) ↔
      ∀ r ∈ R, FreeGroup.lift f r = 1 := by
  rw [← descends_unique_iff S R H f]
  constructor
  · rintro ⟨φ, hφ, unique⟩
    refine ⟨φ, (factorization_iff_generator_values S R H f φ).mpr hφ, ?_⟩
    intro ψ hψ
    exact unique ψ ((factorization_iff_generator_values S R H f ψ).mp hψ)
  · rintro ⟨φ, hφ, unique⟩
    refine ⟨φ, (factorization_iff_generator_values S R H f φ).mp hφ, ?_⟩
    intro ψ hψ
    exact unique ψ ((factorization_iff_generator_values S R H f ψ).mpr hψ)

theorem induced_hom_exists_iff (S : Type u) (R : Set (FreeGroup S))
    (H : Type v) [Group H] (f : S → H) :
    (∃ φ : Presentation S R →* H,
      ∀ s : S, φ (generator S R s) = f s) ↔
      ∀ r ∈ R, FreeGroup.lift f r = 1 := by
  constructor
  · rintro ⟨φ, hφ⟩ r hr
    have hfactor := (factorization_iff_generator_values S R H f φ).mpr hφ
    calc
      FreeGroup.lift f r = φ (projection S R r) := (DFunLike.congr_fun hfactor r).symm
      _ = φ 1 := congrArg φ (relators_vanish S R r hr)
      _ = 1 := φ.map_one
  · intro h
    obtain ⟨φ, hφ, _⟩ := (induced_hom_unique_iff S R H f).mpr h
    exact ⟨φ, hφ⟩

end D07.Ch01.Presentations
