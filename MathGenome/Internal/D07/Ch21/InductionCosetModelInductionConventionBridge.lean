import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModelInductionConventionBridge

namespace D07.Ch21.InductionCosetModelInductionConventionBridge

universe u v w
noncomputable section
open Representation
open scoped TensorProduct
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge

variable {G : Type u} [Group G] (H : Subgroup G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
  {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- Extension from the group basis, followed by the ordinary tensor lift. -/
def tensorLift (f : G → V →ₗ[ℂ] W) : TensorProduct ℂ (MonoidAlgebra ℂ G) V →ₗ[ℂ] W :=
  TensorProduct.lift ((Finsupp.lift _ _ _ f) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)

@[simp] lemma tensorLift_single (f : G → V →ₗ[ℂ] W) (g : G) (v : V) :
    tensorLift f (MonoidAlgebra.single g 1 ⊗ₜ[ℂ] v) = f g v := by
  simp [tensorLift]

lemma tensor_hom_ext {f g : TensorProduct ℂ (MonoidAlgebra ℂ G) V →ₗ[ℂ] W}
    (h : ∀ a v, f (MonoidAlgebra.single a 1 ⊗ₜ[ℂ] v) =
      g (MonoidAlgebra.single a 1 ⊗ₜ[ℂ] v)) : f = g := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  exact LinearMap.ext (h a)

lemma notes_hom_ext {f g : NotesInd H ρ →ₗ[ℂ] W}
    (h : ∀ a v, f (notesMk H ρ a v) = g (notesMk H ρ a v)) : f = g :=
  Submodule.linearMap_qext _ (tensor_hom_ext h)

lemma notes_balance (g : G) (h : H) (v : V) :
    notesMk H ρ (g * (h : G)) v = notesMk H ρ g (ρ h v) := by
  apply (Submodule.Quotient.eq _).mpr
  exact Submodule.subset_span (Set.mem_range_self (g, h, v))

lemma canonical_balance_apply (g : G) (h : H) (v : V) :
    canonicalMk H ρ (g * (h : G)) v = canonicalMk H ρ g (ρ h v) := by
  simpa [canonicalMk, IndV.mk, mul_inv_rev, ofMulAction_single] using
    (Coinvariants.mk_inv_tmul ((leftRegular ℂ G).comp H.subtype) ρ
      (MonoidAlgebra.single g⁻¹ 1) v h)

lemma canonical_action_apply (k g : G) (v : V) :
    ind H.subtype ρ k (canonicalMk H ρ g v) = canonicalMk H ρ (k * g) v := by
  simpa [canonicalMk, mul_inv_rev] using ind_mk H.subtype ρ k g⁻¹ v

/-- Descent through exactly the relation subspace in the notes. -/
def notesLift (f : G → V →ₗ[ℂ] W)
    (hf : ∀ g (h : H) v, f (g * (h : G)) v = f g (ρ h v)) :
    NotesInd H ρ →ₗ[ℂ] W :=
  (relations H ρ).liftQ (tensorLift f) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, h, v⟩, rfl⟩
    simp [hf])

@[simp] lemma notesLift_mk (f : G → V →ₗ[ℂ] W)
    (hf : ∀ g (h : H) v, f (g * (h : G)) v = f g (ρ h v)) (g : G) (v : V) :
    notesLift H ρ f hf (notesMk H ρ g v) = f g v := by
  change tensorLift f (MonoidAlgebra.single g 1 ⊗ₜ[ℂ] v) = f g v
  exact tensorLift_single f g v

/-- Inversion sends the notes generator to the canonical coinvariant generator. -/
def toCanonical : NotesInd H ρ →ₗ[ℂ] IndV H.subtype ρ :=
  notesLift H ρ (canonicalMk H ρ) (canonical_balance_apply H ρ)

@[simp] lemma toCanonical_mk (g : G) (v : V) :
    toCanonical H ρ (notesMk H ρ g v) = canonicalMk H ρ g v :=
  notesLift_mk H ρ _ _ _ _

/-- Inversion in the other direction kills the diagonal coinvariant relations. -/
def fromCanonical : IndV H.subtype ρ →ₗ[ℂ] NotesInd H ρ :=
  Coinvariants.lift _ (tensorLift fun g => notesMk H ρ g⁻¹) (by
    intro h
    apply tensor_hom_ext
    intro g v
    simp only [LinearMap.comp_apply, tprod_apply, TensorProduct.map_tmul,
      MonoidHom.comp_apply, ofMulAction_single, smul_eq_mul, tensorLift_single]
    change notesMk H ρ (((h : G) * g)⁻¹) (ρ h v) = notesMk H ρ g⁻¹ v
    rw [mul_inv_rev]
    simpa using notes_balance H ρ g⁻¹ h⁻¹ (ρ h v))

@[simp] lemma fromCanonical_mk (g : G) (v : V) :
    fromCanonical H ρ (IndV.mk H.subtype ρ g v) = notesMk H ρ g⁻¹ v := by
  simp [fromCanonical, IndV.mk]

/-- The quotient equivalence has inverse given by the same group-coordinate inversion. -/
def quotientEquiv : NotesInd H ρ ≃ₗ[ℂ] IndV H.subtype ρ :=
  LinearEquiv.ofLinearMap (toCanonical H ρ) (fromCanonical H ρ)
    (by
      apply IndV.hom_ext
      intro g
      ext v
      change toCanonical H ρ (fromCanonical H ρ (IndV.mk H.subtype ρ g v)) =
        IndV.mk H.subtype ρ g v
      rw [fromCanonical_mk, toCanonical_mk]
      simp only [canonicalMk, inv_inv])
    (by
      apply notes_hom_ext
      intro g v
      change fromCanonical H ρ (toCanonical H ρ (notesMk H ρ g v)) = notesMk H ρ g v
      rw [toCanonical_mk]
      change fromCanonical H ρ (IndV.mk H.subtype ρ g⁻¹ v) = _
      rw [fromCanonical_mk, inv_inv])

@[simp] lemma quotientEquiv_mk (g : G) (v : V) :
    quotientEquiv H ρ (notesMk H ρ g v) = canonicalMk H ρ g v :=
  toCanonical_mk H ρ g v

@[simp] lemma quotientEquiv_symm_mk (g : G) (v : V) :
    (quotientEquiv H ρ).symm (IndV.mk H.subtype ρ g v) = notesMk H ρ g⁻¹ v :=
  fromCanonical_mk H ρ g v

lemma canonical_hom_ext {f g : IndV H.subtype ρ →ₗ[ℂ] W}
    (h : ∀ a v, f (canonicalMk H ρ a v) = g (canonicalMk H ρ a v)) : f = g := by
  apply IndV.hom_ext
  intro a
  ext v
  simpa only [canonicalMk, inv_inv, LinearMap.comp_apply] using h a⁻¹ v

lemma relations_invariant (k : G) :
    relations H ρ ≤ (relations H ρ).comap (tensorAction (V := V) k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, h, v⟩, rfl⟩
  change tensorAction k _ ∈ relations H ρ
  simp only [map_sub, tensorAction, tprod_apply, TensorProduct.map_tmul,
    ofMulAction_single, smul_eq_mul, trivial_apply]
  rw [← mul_assoc]
  exact Submodule.subset_span (Set.mem_range_self (k * g, h, v))

/-- The left action descends from the raw tensor space by relation invariance. -/
def notesRep : Representation ℂ G (NotesInd H ρ) :=
  (tensorAction (G := G) (V := V)).quotient (relations H ρ) (relations_invariant H ρ)

@[simp] lemma notesRep_quotient (k : G) (x : TensorProduct ℂ (MonoidAlgebra ℂ G) V) :
    notesRep H ρ k ((relations H ρ).mkQ x) =
      (relations H ρ).mkQ (tensorAction (V := V) k x) := rfl

@[simp] lemma notesRep_mk (k g : G) (v : V) :
    notesRep H ρ k (notesMk H ρ g v) = notesMk H ρ (k * g) v := by
  change (relations H ρ).mkQ (tensorAction k (MonoidAlgebra.single g 1 ⊗ₜ[ℂ] v)) = _
  simp [tensorAction, notesMk]

/-- The inversion equivalence intertwines the two group actions. -/
def representationEquiv : (notesRep H ρ).Equiv (ind H.subtype ρ) :=
  Representation.Equiv.mk (quotientEquiv H ρ) (by
    intro k
    apply notes_hom_ext
    intro g v
    change quotientEquiv H ρ (notesRep H ρ k (notesMk H ρ g v)) =
      ind H.subtype ρ k (quotientEquiv H ρ (notesMk H ρ g v))
    rw [notesRep_mk, quotientEquiv_mk, quotientEquiv_mk, canonical_action_apply])

theorem canonical_balance : CanonicalBalance.{u,v} := by
  intro G _ _ H V _ _ ρ g h v
  exact canonical_balance_apply H ρ g h v

theorem canonical_action : CanonicalAction.{u,v} := by
  intro G _ _ H V _ _ ρ k g v
  exact canonical_action_apply H ρ k g v

theorem notes_balancing : NotesBalance.{u,v} := by
  intro G _ _ H V _ _ ρ g h v
  exact notes_balance H ρ g h v

theorem generation : Generation.{u,v} := by
  intro G _ _ H V _ _ ρ
  constructor
  · let S := Submodule.span ℂ (Set.range fun p : G × V => notesMk H ρ p.1 p.2)
    have hz : S.mkQ = 0 := by
      apply notes_hom_ext
      intro g v
      exact (Submodule.Quotient.mk_eq_zero S).mpr
        (Submodule.subset_span (Set.mem_range_self (g, v)))
    apply top_unique
    intro x _
    exact (Submodule.Quotient.mk_eq_zero S).mp (by
      change S.mkQ x = 0
      rw [hz]; rfl)
  · let S := Submodule.span ℂ (Set.range fun p : G × V => canonicalMk H ρ p.1 p.2)
    have hz : S.mkQ = 0 := by
      apply canonical_hom_ext
      intro g v
      exact (Submodule.Quotient.mk_eq_zero S).mpr
        (Submodule.subset_span (Set.mem_range_self (g, v)))
    apply top_unique
    intro x _
    exact (Submodule.Quotient.mk_eq_zero S).mp (by
      change S.mkQ x = 0
      rw [hz]; rfl)

theorem notes_balanced_universal : NotesBalancedUniversal.{u,v,w} := by
  intro G _ _ H V _ _ ρ W _ _ f hf
  refine ⟨notesLift H ρ f hf, notesLift_mk H ρ f hf, ?_⟩
  intro F hF
  apply notes_hom_ext
  intro g v
  rw [hF, notesLift_mk]

theorem canonical_balanced_universal : CanonicalBalancedUniversal.{u,v,w} := by
  intro G _ _ H V _ _ ρ W _ _ f hf
  let F := (notesLift H ρ f hf).comp (quotientEquiv H ρ).symm.toLinearMap
  have hF : ∀ g v, F (canonicalMk H ρ g v) = f g v := by
    intro g v
    change notesLift H ρ f hf ((quotientEquiv H ρ).symm (IndV.mk H.subtype ρ g⁻¹ v)) = _
    rw [quotientEquiv_symm_mk, inv_inv, notesLift_mk]
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  apply canonical_hom_ext
  intro g v
  rw [hF', hF]

theorem relation_invariance : RelationsInvariant.{u,v} := by
  intro G _ _ H V _ _ ρ k x hx
  exact relations_invariant H ρ k hx

theorem quotient_equivalence : QuotientEquivalence.{u,v} := by
  intro G _ _ H V _ _ ρ
  exact ⟨notesRep H ρ, representationEquiv H ρ, notesRep_quotient H ρ,
    notesRep_mk H ρ, quotientEquiv_mk H ρ, quotientEquiv_symm_mk H ρ⟩

end
end D07.Ch21.InductionCosetModelInductionConventionBridge
