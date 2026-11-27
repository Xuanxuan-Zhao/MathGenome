import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.LocalizationCoverFaithfulness
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! The affine-intersection diagram of a finite principal-open cover. -/

open CategoryTheory

namespace LocalizationAmitsurDiagramSpec

universe u v

variable {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)

/-- The algebra of the disjoint union of the principal opens. -/
abbrev coverAlgebra := ∀ i : ι, Localization.Away (f i)

/-- The function defining the intersection indexed by an ordered tuple. -/
def denominator {n : ℕ} (t : Fin n → ι) : A := ∏ i, f (t i)

abbrev intersection {n : ℕ} (t : Fin n → ι) := Localization.Away (denominator f t)

abbrev intersectionAlgebra (n : ℕ) := ∀ t : Fin n → ι, intersection f t

/-- The map of principal localizations whenever the target inverts the source denominator. -/
noncomputable def localize {a : A} {C : Type*} [CommRing C] [Algebra A C]
    (h : IsUnit (algebraMap A C a)) : Localization.Away a →ₐ[A] C :=
  IsLocalization.Away.liftAlgHom a (f := Algebra.ofId A C) h

/-- A map from a principal localization to an algebra over its base is unique. -/
theorem localization_hom_ext {a : A} {C : Type*} [CommRing C] [Algebra A C]
    (g h : Localization.Away a →ₐ[A] C) : g = h := by
  apply Localization.algHom_ext (Submonoid.powers a)
  exact Subsingleton.elim _ _

theorem factor_isUnit {n : ℕ} (t : Fin n → ι) (i : Fin n) :
    IsUnit (algebraMap A (intersection f t) (f (t i))) :=
  IsLocalization.Away.isUnit_of_dvd (denominator f t)
    (Finset.dvd_prod_of_mem (fun j ↦ f (t j)) (Finset.mem_univ i))

/-- In component t, restrict from the component indexed by t composed with α. -/
noncomputable def restrictComponent {m n : ℕ} (α : Fin m → Fin n) (t : Fin n → ι) :
    intersection f (t ∘ α) →ₐ[A] intersection f t :=
  localize (by
    change IsUnit (algebraMap A (intersection f t) (∏ i, f (t (α i))))
    rw [map_prod]
    exact IsUnit.prod_iff.mpr fun i _ ↦ factor_isUnit f t (α i))

/-- The ring map on products, with all tuple positions retained. -/
noncomputable def restrict {m n : ℕ} (α : Fin m → Fin n) :
    intersectionAlgebra f m →ₐ[A] intersectionAlgebra f n :=
  AlgHom.pi fun t ↦ (restrictComponent f α t).comp
    (Pi.evalAlgHom A (fun s : Fin m → ι ↦ intersection f s) (t ∘ α))

/-- The component of the comparison on the tensor factor at position i. -/
noncomputable def factorComponent {n : ℕ} (t : Fin n → ι) (i : Fin n) :
    coverAlgebra f →ₐ[A] intersection f t :=
  (localize (factor_isUnit f t i)).comp
    (Pi.evalAlgHom A (fun j ↦ Localization.Away (f j)) (t i))

/-- The canonical comparison is specified by the evaluations on individual tensor factors. -/
noncomputable def comparison (n : ℕ) :
    AmitsurAlgebrasSpec.tensorPower A (coverAlgebra f) n →ₐ[A] intersectionAlgebra f n :=
  AlgHom.pi fun t ↦ AmitsurAlgebrasSpec.liftFactors (factorComponent f t)

noncomputable def diagram : SimplexCategory ⥤ CommAlgCat.{max u v} A where
  obj p := CommAlgCat.of A (intersectionAlgebra f (p.len + 1))
  map α := CommAlgCat.ofHom (restrict f α.toOrderHom)
  map_id p := by
    apply CommAlgCat.hom_ext
    refine AlgHom.ext fun x ↦ funext fun t ↦ ?_
    change restrictComponent f id t (x t) = x t
    have h : restrictComponent f id t = AlgHom.id A _ := localization_hom_ext _ _
    rw [h, AlgHom.id_apply]
  map_comp α β := by
    apply CommAlgCat.hom_ext
    refine AlgHom.ext fun x ↦ funext fun t ↦ ?_
    change restrictComponent f (β.toOrderHom ∘ α.toOrderHom) t (x _) =
      restrictComponent f β.toOrderHom t
        (restrictComponent f α.toOrderHom (t ∘ β.toOrderHom) (x _))
    exact DFunLike.congr_fun
      (localization_hom_ext (restrictComponent f (β.toOrderHom ∘ α.toOrderHom) t)
        ((restrictComponent f β.toOrderHom t).comp
          (restrictComponent f α.toOrderHom (t ∘ β.toOrderHom)))) _

/-- The augmentation is the base algebra mapping by the usual structural maps. -/
noncomputable def augmentedDiagram : AugmentedSimplexCategory ⥤ CommAlgCat.{max u v} A :=
  WithInitial.lift (Z := CommAlgCat.of A (ULift.{max u v} A)) (diagram f)
    (fun p ↦ CommAlgCat.ofHom
      ((Algebra.ofId A (intersectionAlgebra f (p.len + 1))).comp ULift.algEquiv.toAlgHom))
    (fun _ _ α ↦ by
      apply CommAlgCat.hom_ext
      exact AlgHom.ext fun x ↦ (restrict f α.toOrderHom).commutes x.down)

def comparisonBijective : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} [Finite ι] (f : ι → A) (n : ℕ),
    Function.Bijective (comparison f n)

def comparisonNatural : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)
    {m n : ℕ} (α : Fin m → Fin n),
    (comparison f n).comp (AmitsurAlgebrasSpec.map α) =
      (restrict f α).comp (comparison f m)

/-- The full ordered augmented identification, with the specified comparison in each degree. -/
def augmentedComparison : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} [Finite ι] (f : ι → A),
    Ideal.span (Set.range f) = ⊤ →
    (algebraMap A (coverAlgebra f)).FaithfullyFlat ∧
      ∃ e : AmitsurAlgebrasSpec.augmentedDiagram A (coverAlgebra f) ≅ augmentedDiagram f,
        (∀ p : SimplexCategory, (e.hom.app (WithInitial.of p)).hom = comparison f (p.len + 1)) ∧
        (e.hom.app WithInitial.star).hom = AlgHom.id A (ULift.{max u v} A)

/-- The localization models the intersection as a distinguished open of the base spectrum. -/
def intersectionOpen : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)
    {n : ℕ} (t : Fin n → ι),
    PrimeSpectrum.basicOpen (denominator f t) = ⨅ i, PrimeSpectrum.basicOpen (f (t i))

/-- The component of a coface is restriction from the tuple with that entry omitted. -/
def cofaceComponent : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)
    {p : ℕ} (i : Fin (p + 2)) (t : Fin (p + 2) → ι)
    (x : AmitsurAlgebrasSpec.degree A (coverAlgebra f) p),
    comparison f (p + 2) (AmitsurAlgebrasSpec.coface i x) t =
      restrictComponent f i.succAbove t (comparison f (p + 1) x (t ∘ i.succAbove))

/-- The spectrum of the component localization is open in the base spectrum, with
image the intersection of the tuple's distinguished opens. -/
def intersectionSpectrum : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)
    {n : ℕ} (t : Fin n → ι),
    Topology.IsOpenEmbedding (PrimeSpectrum.comap (algebraMap A (intersection f t))) ∧
      Set.range (PrimeSpectrum.comap (algebraMap A (intersection f t))) =
        ((⨅ i, PrimeSpectrum.basicOpen (f (t i))) : TopologicalSpace.Opens (PrimeSpectrum A))

/-- A codegeneracy repeats a tuple entry. Its component restriction is an isomorphism
of the two localizations of the same distinguished open. -/
def codegeneracyComponent : Prop :=
  ∀ {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)
    {p : ℕ} (i : Fin (p + 1)) (t : Fin (p + 1) → ι),
    ∃ e : intersection f (t ∘ i.predAbove) ≃ₐ[A] intersection f t,
      e.toAlgHom = restrictComponent f i.predAbove t ∧
      PrimeSpectrum.basicOpen (denominator f (t ∘ i.predAbove)) =
        PrimeSpectrum.basicOpen (denominator f t) ∧
      (t ∘ i.predAbove) i.castSucc = t i ∧ (t ∘ i.predAbove) i.succ = t i ∧
      ∀ x : AmitsurAlgebrasSpec.degree A (coverAlgebra f) (p + 1),
        comparison f (p + 1) (AmitsurAlgebrasSpec.codegeneracy i x) t =
          e (comparison f (p + 2) x (t ∘ i.predAbove))

end LocalizationAmitsurDiagramSpec
