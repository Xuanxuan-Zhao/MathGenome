import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
import MathGenome.Internal.D07.Ch21.InductionCosetModelInductionConventionBridge

namespace D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

universe u v
noncomputable section
open Representation
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
open D07.Ch21.InductionCosetModelInductionConventionBridge

variable {G : Type u} [Group G] (H : Subgroup G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
  (r : G ⧸ H → G) (hr : IsTransversal H r)

/-- The H-coordinate in the unique factorization g = r(gH) h. -/
def coefficient (g : G) : H :=
  ⟨(r (QuotientGroup.mk g))⁻¹ * g,
    QuotientGroup.eq.mp (hr (QuotientGroup.mk g))⟩

lemma rep_mul_coefficient (g : G) :
    r (QuotientGroup.mk g) * (coefficient H r hr g : G) = g := by
  simp [coefficient]

include hr in
@[simp] lemma coset_rep_mul (q : G ⧸ H) (h : H) :
    (QuotientGroup.mk (r q * (h : G)) : G ⧸ H) = q := by
  rw [QuotientGroup.mk_mul_of_mem _ h.property, hr q]

@[simp] lemma coefficient_rep_mul (q : G ⧸ H) (h : H) :
    coefficient H r hr (r q * (h : G)) = h := by
  apply Subtype.ext
  simp [coefficient, coset_rep_mul H r hr]

lemma coefficient_mul (g : G) (h : H) :
    coefficient H r hr (g * (h : G)) = coefficient H r hr g * h := by
  apply Subtype.ext
  simp [coefficient, QuotientGroup.mk_mul_of_mem _ h.property, mul_assoc]

/-- The balanced map sending [g,v] to the one nonzero coset coordinate. -/
def generatorCoordinates (g : G) : V →ₗ[ℂ] Coordinates H (V := V) :=
  (Finsupp.lsingle (QuotientGroup.mk g : G ⧸ H)).comp (ρ (coefficient H r hr g))

lemma generatorCoordinates_balanced (g : G) (h : H) (v : V) :
    generatorCoordinates H ρ r hr (g * (h : G)) v =
      generatorCoordinates H ρ r hr g (ρ h v) := by
  simp [generatorCoordinates, coefficient_mul, QuotientGroup.mk_mul_of_mem _ h.property]

/-- Descend the inverse formula through the exact relation subspace. -/
def toCoordinates : NotesInd H ρ →ₗ[ℂ] Coordinates H (V := V) :=
  notesLift H ρ (generatorCoordinates H ρ r hr) (generatorCoordinates_balanced H ρ r hr)

@[simp] lemma toCoordinates_mk (g : G) (v : V) :
    toCoordinates H ρ r hr (notesMk H ρ g v) =
      Finsupp.single (QuotientGroup.mk g) (ρ (coefficient H r hr g) v) := by
  rw [toCoordinates, notesLift_mk]
  rfl

@[simp] lemma toCoordinates_rep_mul (q : G ⧸ H) (h : H) (v : V) :
    toCoordinates H ρ r hr (notesMk H ρ (r q * (h : G)) v) =
      Finsupp.single q (ρ h v) := by
  simp [toCoordinates_mk, coset_rep_mul H r hr, coefficient_rep_mul H r hr]

@[simp] lemma coordinateSum_single (q : G ⧸ H) (v : V) :
    coordinateSum H ρ r (Finsupp.single q v) = notesMk H ρ (r q) v := by
  exact Finsupp.lsum_single ℂ _ q v

/-- The sum map and the descended coefficient map are inverse linear maps. -/
def coordinateEquiv : Coordinates H (V := V) ≃ₗ[ℂ] NotesInd H ρ :=
  LinearEquiv.ofLinearMap (coordinateSum H ρ r) (toCoordinates H ρ r hr)
    (by
      apply notes_hom_ext
      intro g v
      change coordinateSum H ρ r (toCoordinates H ρ r hr (notesMk H ρ g v)) = _
      rw [toCoordinates_mk, coordinateSum_single, ← notes_balance,
        rep_mul_coefficient]
      rfl)
    (by
      apply Finsupp.lhom_ext
      intro q v
      change toCoordinates H ρ r hr (coordinateSum H ρ r (Finsupp.single q v)) = _
      rw [coordinateSum_single]
      simpa using toCoordinates_rep_mul H ρ r hr q 1 v)

@[simp] lemma coordinateEquiv_single (q : G ⧸ H) (v : V) :
    coordinateEquiv H ρ r hr (Finsupp.single q v) = notesMk H ρ (r q) v :=
  coordinateSum_single H ρ r q v

@[simp] lemma coordinateEquiv_symm_mk (g : G) (v : V) :
    (coordinateEquiv H ρ r hr).symm (notesMk H ρ g v) =
      Finsupp.single (QuotientGroup.mk g) (ρ (coefficient H r hr g) v) :=
  toCoordinates_mk H ρ r hr g v

/-- Transport the already descended left action through the coordinate maps. -/
def coordinateAction : Representation ℂ G (Coordinates H (V := V)) :=
  ((coordinateEquiv H ρ r hr).symm.conjRingEquiv.toMonoidHom).comp (notesRep H ρ)

lemma coordinateAction_apply (k : G) (x : Coordinates H (V := V)) :
    coordinateAction H ρ r hr k x =
      (coordinateEquiv H ρ r hr).symm (notesRep H ρ k (coordinateEquiv H ρ r hr x)) := rfl

/-- The constructed coordinate model includes equivariance on every generator. -/
def coordinateModel : CoordinateModel H ρ r where
  toQuotient := coordinateEquiv H ρ r hr
  action := coordinateAction H ρ r hr
  sum_map := rfl
  left_action k g v := by
    rw [coordinateAction_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, notesRep_mk]

lemma coordinateAction_block (k : G) (q q' : G ⧸ H) (h : H)
    (he : k * r q = r q' * (h : G)) (v : V) :
    coordinateAction H ρ r hr k (Finsupp.single q v) =
      Finsupp.single q' (ρ h v) := by
  rw [coordinateAction_apply, coordinateEquiv_single, notesRep_mk, he]
  exact toCoordinates_rep_mul H ρ r hr q' h v

/-- Any coordinate model's generator action extends to every vector. -/
lemma model_action (m : CoordinateModel H ρ r) (k : G)
    (x : Coordinates H (V := V)) :
    m.toQuotient (m.action k x) = notesRep H ρ k (m.toQuotient x) := by
  have he : m.toQuotient.toLinearMap ∘ₗ m.action k ∘ₗ m.toQuotient.symm.toLinearMap =
      notesRep H ρ k := by
    apply notes_hom_ext
    intro g v
    exact (m.left_action k g v).trans (notesRep_mk H ρ k g v).symm
  have hx := LinearMap.congr_fun he (m.toQuotient x)
  simpa using hx

lemma model_single (m : CoordinateModel H ρ r) (q : G ⧸ H) (v : V) :
    m.toQuotient (Finsupp.single q v) = notesMk H ρ (r q) v := by
  change m.toQuotient.toLinearMap _ = _
  rw [m.sum_map, coordinateSum_single]

/-- Two coordinate models are equivalent through their common quotient. -/
def changeRepresentatives {s : G ⧸ H → G}
    (m : CoordinateModel H ρ r) (n : CoordinateModel H ρ s) :
    m.action.Equiv n.action :=
  Representation.Equiv.mk (m.toQuotient.trans n.toQuotient.symm) (by
    intro k
    apply LinearMap.ext
    intro x
    apply n.toQuotient.injective
    change n.toQuotient ((m.toQuotient.trans n.toQuotient.symm) (m.action k x)) =
      n.toQuotient (n.action k ((m.toQuotient.trans n.toQuotient.symm) x))
    simp [model_action H ρ])

theorem transversal_decomposition : TransversalDecomposition.{u} := by
  intro G _ _ H
  constructor
  · exact ⟨Quotient.out, QuotientGroup.out_eq'⟩
  · intro r hr g
    refine ⟨(QuotientGroup.mk g, coefficient H r hr g),
      (rep_mul_coefficient H r hr g).symm, ?_⟩
    rintro ⟨q, h⟩ he
    have hq : (QuotientGroup.mk g : G ⧸ H) = q := by
      rw [he, coset_rep_mul H r hr]
    apply Prod.ext
    · exact hq.symm
    · apply Subtype.ext
      change (h : G) = (r (QuotientGroup.mk g))⁻¹ * g
      rw [hq, he]
      simp

theorem coordinate_construction : CoordinateConstruction.{u,v} := by
  intro G _ _ H V _ _ ρ r hr
  refine ⟨coordinateModel H ρ r hr, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro q h v
    exact toCoordinates_rep_mul H ρ r hr q h v
  · exact coordinateAction_block H ρ r hr

theorem induction_dimension : InductionDimension.{u,v} := by
  intro G _ _ H V _ _ _ ρ
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let r : G ⧸ H → G := Quotient.out
  have hr : IsTransversal H r := QuotientGroup.out_eq'
  let e := coordinateEquiv H ρ r hr
  refine ⟨e.finiteDimensional, ?_⟩
  calc
    Module.finrank ℂ (NotesInd H ρ) = Module.finrank ℂ (Coordinates H (V := V)) :=
      e.finrank_eq.symm
    _ = H.index * Module.finrank ℂ V := by
      change Module.finrank ℂ ((G ⧸ H) →₀ V) = _
      simp [Module.finrank, rank_finsupp, H.index_eq_card, Nat.card_eq_fintype_card]

theorem representative_change : RepresentativeChange.{u,v} := by
  intro G _ _ H V _ _ ρ r s _ _ m n
  refine ⟨changeRepresentatives H ρ r m n, ?_, ?_⟩
  · intro x
    exact n.toQuotient.apply_symm_apply (m.toQuotient x)
  · intro q h he v
    apply n.toQuotient.injective
    change n.toQuotient (n.toQuotient.symm (m.toQuotient (Finsupp.single q v))) = _
    rw [LinearEquiv.apply_symm_apply, model_single, model_single, he, notes_balance]

end
end D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
