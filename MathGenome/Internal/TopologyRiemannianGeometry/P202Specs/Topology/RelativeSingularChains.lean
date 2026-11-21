import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.ChainLongExactSequence
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! Relative chains for arbitrary subspaces, paper.tex 1147–1207.
The cokernel is taken in complexes, hence carries the induced differential.
Ordinary and reduced versions use exactly the upstream complexes, including
all their negative degrees. No nonemptiness or separation condition is imposed. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped Simplicial

universe u v w t
namespace P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.ChainLES

structure Pair where
  space : TopCat.{w}
  subspace : Set space

abbrev Pair.sub (P : Pair.{w}) : TopCat.{w} := TopCat.of P.subspace

def Pair.inclusion (P : Pair.{w}) : P.sub ⟶ P.space :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

structure PairMap (P Q : Pair.{w}) where
  map : P.space ⟶ Q.space
  mapsTo : Set.MapsTo map P.subspace Q.subspace

@[ext] lemma PairMap.ext {P Q : Pair.{w}} (f g : PairMap P Q) (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

instance : Category Pair.{w} where
  Hom := PairMap
  id P := ⟨𝟙 P.space, fun _ h => h⟩
  comp f g := ⟨f.map ≫ g.map, fun _ h => g.mapsTo (f.mapsTo h)⟩
  id_comp _ := PairMap.ext _ _ (by rfl)
  comp_id _ := PairMap.ext _ _ (by rfl)
  assoc _ _ _ := PairMap.ext _ _ (by rfl)

def PairMap.restrict {P Q : Pair.{w}} (f : P ⟶ Q) : P.sub ⟶ Q.sub :=
  TopCat.ofHom ⟨fun x => ⟨f.map x, f.mapsTo x.property⟩,
    (f.map.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

lemma PairMap.square {P Q : Pair.{w}} (f : P ⟶ Q) :
    P.inclusion ≫ f.map = f.restrict ≫ Q.inclusion := rfl

section Categorical
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} {shape : ComplexShape ι}
  (K : TopCat.{w} ⥤ HomologicalComplex C shape)

abbrev inclusion (P : Pair.{w}) := K.map P.inclusion
abbrev relativeComplex (P : Pair.{w}) := cokernel (inclusion K P)
abbrev projection (P : Pair.{w}) := cokernel.π (inclusion K P)
abbrev sequence (P : Pair.{w}) := ShortComplex.cokernelSequence (inclusion K P)

lemma inclusion_square {P Q : Pair.{w}} (f : P ⟶ Q) :
    inclusion K P ≫ K.map f.map = K.map f.restrict ≫ inclusion K Q := by
  rw [← K.map_comp, ← K.map_comp, f.square]

def relativeMap {P Q : Pair.{w}} (f : P ⟶ Q) :
    relativeComplex K P ⟶ relativeComplex K Q :=
  cokernel.map _ _ (K.map f.restrict) (K.map f.map) (inclusion_square K f)

@[reassoc (attr := simp)] lemma projection_map {P Q : Pair.{w}} (f : P ⟶ Q) :
    projection K P ≫ relativeMap K f = K.map f.map ≫ projection K Q :=
  cokernel.π_desc _ _ _

def sequenceMap {P Q : Pair.{w}} (f : P ⟶ Q) : sequence K P ⟶ sequence K Q :=
  ShortComplex.Hom.mk (K.map f.restrict) (K.map f.map) (relativeMap K f)
    (inclusion_square K f).symm (projection_map K f).symm

def relativeFunctor : Pair.{w} ⥤ HomologicalComplex C shape where
  obj := relativeComplex K
  map := relativeMap K
  map_id P := by
    apply (cancel_epi (projection K P)).mp
    rw [projection_map, Category.comp_id]
    change K.map (𝟙 P.space) ≫ projection K P = projection K P
    simp
  map_comp f g := by
    apply (cancel_epi (projection K _)).mp
    simp only [projection_map, projection_map_assoc]
    rw [← Category.assoc, ← K.map_comp]
    rfl

/-- The categorical quotient is the ordinary module quotient in every degree. -/
def degreeQuotientIso (P : Pair.{w}) (n : ι) :
    (relativeComplex K P).X n ≅ cokernel ((inclusion K P).f n) :=
  PreservesCokernel.iso (HomologicalComplex.eval C shape n) _

end Categorical

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

abbrev ordinary (P : Pair.{w}) := relativeComplex (ordinaryFunctor R M) P
abbrev reduced (P : Pair.{w}) := relativeComplex (reducedFunctor R M) P
abbrev nonnegative (P : Pair.{w}) := relativeComplex (chainFunctor R M) P
abbrev relativeHomology (P : Pair.{w}) (n : ℤ) := (ordinary R M P).homology n
abbrev reducedRelativeHomology (P : Pair.{w}) (n : ℤ) := (reduced R M P).homology n

def relativeHomologyFunctor (n : ℤ) : Pair.{w} ⥤ ModuleCat.{max v w} R :=
  relativeFunctor (ordinaryFunctor R M) ⋙ HomologicalComplex.homologyFunctor _ _ n

def reducedRelativeHomologyFunctor (n : ℤ) : Pair.{w} ⥤ ModuleCat.{max v w} R :=
  relativeFunctor (reducedFunctor R M) ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- A simplex is in the subspace precisely when its continuous map has image there. -/
def InSubspace (P : Pair.{w}) (n : ℕ) (s : Simplex P.space n) : Prop :=
  ∀ x, simplexEquiv P.space n s x ∈ P.subspace

abbrev Outside (P : Pair.{w}) (n : ℕ) := {s : Simplex P.space n // ¬ InSubspace P n s}

/-- Explicit quotient by the image of the subspace chains. -/
abbrev chainQuotient (P : Pair.{w}) (n : ℕ) :=
  Chains M P.space n ⧸ ((chainMap R M P.inclusion).f n).hom.range

def chainQuotientEquiv (P : Pair.{w}) (n : ℕ) :
    (nonnegative R M P).X n ≃ₗ[R] chainQuotient R M P n :=
  ((degreeQuotientIso (chainFunctor R M) P n) ≪≫
    ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv

/-- Exactness, naturality and the positive boundary-of-a-lift formula, with
short exactness supplied as a conclusion rather than an assumed certificate. -/
def PairLESType {ι : Type t} {shape : ComplexShape ι}
    (K : TopCat.{w} ⥤ HomologicalComplex (ModuleCat.{max v w} R) shape) : Prop :=
  ∃ h : ∀ P : Pair.{w}, DegreewiseShortExact (sequence K P),
    (∀ P, (∀ n, (HomologicalComplex.HomologySequence.composableArrows₂ (sequence K P) n).Exact) ∧
      (∀ i j (hij : shape.Rel i j), (segment (h P) i j hij).Exact) ∧
      LiftsExist (sequence K P) (h P) ∧ LiftFormula (sequence K P) (h P) ∧
      Independence (sequence K P) (h P)) ∧
    (∀ (P Q : Pair.{w}) (f : P ⟶ Q),
      (∀ n, homologyMap (inclusion K P) n ≫ homologyMap (K.map f.map) n =
        homologyMap (K.map f.restrict) n ≫ homologyMap (inclusion K Q) n) ∧
      (∀ n, homologyMap (projection K P) n ≫ homologyMap (relativeMap K f) n =
        homologyMap (K.map f.map) n ≫ homologyMap (projection K Q) n) ∧
      (∀ i j (hij : shape.Rel i j), connecting (h P) i j hij ≫ homologyMap (K.map f.restrict) j =
        homologyMap (relativeMap K f) i ≫ connecting (h Q) i j hij))

def ordinaryLESType : Prop := PairLESType R (ordinaryFunctor R M :
  TopCat.{w} ⥤ _)
def reducedLESType : Prop := PairLESType R (reducedFunctor R M :
  TopCat.{w} ⥤ _)

def inclusionInjectiveType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ), Function.Injective ((chainMap R M P.inclusion).f n)

def simplexImageType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ) (s : Simplex P.space n),
    s ∈ Set.range ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌)) ↔ InSubspace P n s

def outsideProjection (P : Pair.{w}) (n : ℕ) :
    Chains M P.space n →ₗ[R] (Outside P n →₀ M) :=
  Finsupp.lsubtypeDomain {s | ¬ InSubspace P n s}

def quotientCoordinatesType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ), ∃ e : (nonnegative R M P).X n ≃ₗ[R] (Outside P n →₀ M),
    ∀ c : Chains M P.space n, e ((projection (chainFunctor R M) P).f n c) =
      outsideProjection R M P n c

def quotientBasisType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ), ∃ b : Module.Basis (Outside P n) R ((nonnegative R R P).X n),
    ∀ s, b s = (projection (chainFunctor R R) P).f n (Finsupp.single s.val 1)

lemma ordinary_inclusion_degree (P : Pair.{w}) (n : ℕ) :
    (inclusion (ordinaryFunctor R M) P).f (n : ℤ) ≫ (ordinaryNonnegativeIso R M P.space n).hom =
      (ordinaryNonnegativeIso R M P.sub n).hom ≫ (inclusion (chainFunctor R M) P).f n := by
  change (HomologicalComplex.extendMap (chainMap R M P.inclusion) (degreeEmbedding 0)).f _ ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by
    change (0 : ℤ) + n = n; omega)]
  simp [ordinaryNonnegativeIso]

lemma reduced_inclusion_degree (P : Pair.{w}) (n : ℕ) :
    (inclusion (reducedFunctor R M) P).f (n : ℤ) ≫ (reducedNonnegativeIso R M P.space n).hom =
      (reducedNonnegativeIso R M P.sub n).hom ≫ (inclusion (chainFunctor R M) P).f n := by
  change (HomologicalComplex.extendMap (augmentedShiftedMap R M P.inclusion) (degreeEmbedding (-1))).f _ ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by
    change (-1 : ℤ) + ((n+1 : ℕ) : ℤ) = n; omega)]
  simp [reducedNonnegativeIso, augmentedShiftedMap]

/-- Canonical quotient identifications in the nonnegative degrees. -/
def ordinaryDegreeIso (P : Pair.{w}) (n : ℕ) :
    (ordinary R M P).X (n : ℤ) ≅ (nonnegative R M P).X n :=
  degreeQuotientIso (ordinaryFunctor R M) P n ≪≫
    asIso (cokernel.map _ _ (ordinaryNonnegativeIso R M P.sub n).hom
      (ordinaryNonnegativeIso R M P.space n).hom (ordinary_inclusion_degree R M P n)) ≪≫
        (degreeQuotientIso (chainFunctor R M) P n).symm

def reducedDegreeIso (P : Pair.{w}) (n : ℕ) :
    (reduced R M P).X (n : ℤ) ≅ (nonnegative R M P).X n :=
  degreeQuotientIso (reducedFunctor R M) P n ≪≫
    asIso (cokernel.map _ _ (reducedNonnegativeIso R M P.sub n).hom
      (reducedNonnegativeIso R M P.space n).hom (reduced_inclusion_degree R M P n)) ≪≫
        (degreeQuotientIso (chainFunctor R M) P n).symm

def ordinaryDegreeType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ),
    (projection (ordinaryFunctor R M) P).f (n : ℤ) ≫ (ordinaryDegreeIso R M P n).hom =
      (ordinaryNonnegativeIso R M P.space n).hom ≫ (projection (chainFunctor R M) P).f n

def reducedDegreeType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ),
    (projection (reducedFunctor R M) P).f (n : ℤ) ≫ (reducedDegreeIso R M P n).hom =
      (reducedNonnegativeIso R M P.space n).hom ≫ (projection (chainFunctor R M) P).f n

def ordinaryBoundaryType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ),
    (ordinaryDegreeIso R M P (n+1)).inv ≫ (ordinary R M P).d (n+1 : ℕ) n ≫
      (ordinaryDegreeIso R M P n).hom = (nonnegative R M P).d (n+1) n

def reducedBoundaryType : Prop :=
  ∀ (P : Pair.{w}) (n : ℕ),
    (reducedDegreeIso R M P (n+1)).inv ≫ (reduced R M P).d (n+1 : ℕ) n ≫
      (reducedDegreeIso R M P n).hom = (nonnegative R M P).d (n+1) n

def ordinaryNegativeType : Prop :=
  ∀ (P : Pair.{w}) (n : ℤ), n < 0 →
    IsZero ((ordinary R M P).X n) ∧ IsZero (relativeHomology R M P n)

def reducedNegativeType : Prop :=
  ∀ (P : Pair.{w}) (n : ℤ), n < 0 →
    IsZero ((reduced R M P).X n) ∧ IsZero (reducedRelativeHomology R M P n)

/-- The ordinary degree zero endpoint, valid also for empty subspaces and spaces. -/
def ordinaryEndpointType : Prop :=
  ∀ (P : Pair.{w}), Epi (homologyMap (projection (ordinaryFunctor R M) P) 0)


def ordinaryShortExactType : Prop :=
  ∀ P : Pair.{w}, DegreewiseShortExact (sequence (ordinaryFunctor R M) P)

def reducedShortExactType : Prop :=
  ∀ P : Pair.{w}, DegreewiseShortExact (sequence (reducedFunctor R M) P)

def relativeVersionsIsoType : Prop :=
  ∀ P : Pair.{w}, Nonempty (reduced R M P ≅ ordinary R M P)

def relativeChainFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Pair.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ

def relativeChainFunctor_value (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Pair.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  relativeFunctor (ordinaryFunctor R M)

def reducedRelativeChainFunctor_value (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Pair.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  relativeFunctor (reducedFunctor R M)

def relativeHomologyFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ),
    Pair.{w} ⥤ ModuleCat.{max v w} R

def relativeHomologyFunctor_value (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ) :
    Pair.{w} ⥤ ModuleCat.{max v w} R := relativeHomologyFunctor R M n

def reducedRelativeHomologyFunctor_value (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ) :
    Pair.{w} ⥤ ModuleCat.{max v w} R := reducedRelativeHomologyFunctor R M n

def chainQuotient_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (P : Pair.{w}) (n : ℕ), (nonnegative R M P).X n ≃ₗ[R] chainQuotient R M P n

def chainQuotient_value (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (P : Pair.{w}) (n : ℕ) :
    (nonnegative R M P).X n ≃ₗ[R] chainQuotient R M P n := chainQuotientEquiv R M P n

/-! Full expected propositions, universally quantified over coefficients. -/

def inclusion_injective_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    inclusionInjectiveType.{u,v,w} R M

def quotient_coordinates_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    quotientCoordinatesType.{u,v,w} R M

def ordinary_les_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ordinaryLESType.{u,v,w} R M

def reduced_les_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    reducedLESType.{u,v,w} R M

def ordinary_negative_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ordinaryNegativeType.{u,v,w} R M

def reduced_negative_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    reducedNegativeType.{u,v,w} R M

def ordinary_endpoint_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ordinaryEndpointType.{u,v,w} R M

def ordinary_degree_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ordinaryDegreeType.{u,v,w} R M

def reduced_degree_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    reducedDegreeType.{u,v,w} R M

def ordinary_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ordinaryBoundaryType.{u,v,w} R M

def reduced_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    reducedBoundaryType.{u,v,w} R M

def ordinary_short_exact_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ordinaryShortExactType.{u,v,w} R M

def reduced_short_exact_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    reducedShortExactType.{u,v,w} R M

def relative_versions_iso_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    relativeVersionsIsoType.{u,v,w} R M

def quotient_basis_type : Prop :=
  ∀ (R : Type u) [CommRing R], quotientBasisType.{u,w} R

end P202Specs.RelativeSingularChains
