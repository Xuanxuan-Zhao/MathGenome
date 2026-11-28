import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem

/-! Splitting modular systems and their native group algebras. -/

namespace RepTheorySurvey.Modular

universe uG uO uK uF uA uI uV

/-- The prime-to-`p` part of the group order. -/
noncomputable def primeToPart (G : Type uG) (p : ℕ) : ℕ :=
  ordCompl[p] (Nat.card G)

/-- A group element is `p`-regular if its order is coprime to `p`. -/
def IsPRegular {G : Type uG} [Group G] (p : ℕ) (g : G) : Prop :=
  (orderOf g).Coprime p

/-- The subtype of `p`-regular elements of `G`. -/
abbrev PRegular (G : Type uG) [Group G] (p : ℕ) :=
  {g : G // IsPRegular p g}

/-- The given algebra is a finite product of nonempty full matrix algebras over `F`. -/
def IsSplitMatrixAlgebra (F : Type uF) [Field F] (A : Type uA) [Ring A] [Algebra F A] :
    Prop :=
  ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧
    Nonempty (A ≃ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F))

/-- The group algebra modulo its Jacobson radical, with the canonical scalar algebra. -/
abbrev GroupAlgebraRadicalQuotient (F : Type uF) [Field F] (G : Type uG) [Group G] :=
  MonoidAlgebra F G ⧸ Ring.jacobson (MonoidAlgebra F G)

/-- The canonical algebra map onto the radical quotient. -/
noncomputable def groupAlgebraRadicalQuotientMap (F : Type uF) [Field F] (G : Type uG) [Group G] :
    MonoidAlgebra F G →ₐ[F] GroupAlgebraRadicalQuotient F G :=
  Ideal.Quotient.mkₐ F (Ring.jacobson (MonoidAlgebra F G))

/-- Reduce each coefficient of the integral group algebra to the residue field. -/
noncomputable def groupAlgebraReduction (O : Type uO) [CommRing O] [IsLocalRing O]
    (G : Type uG) [Group G] : MonoidAlgebra O G →+* MonoidAlgebra (IsLocalRing.ResidueField O) G :=
  MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)

/-- Map each coefficient of the integral group algebra to the fraction field. -/
noncomputable def groupAlgebraToFractionField (O : Type uO) [CommRing O]
    (K : Type uK) [Field K] [Algebra O K] (G : Type uG) [Group G] :
    MonoidAlgebra O G →+* MonoidAlgebra K G :=
  MonoidAlgebra.mapRingHom G (algebraMap O K)

/-- A splitting `p`-modular system with residue field `IsLocalRing.ResidueField O`. -/
abbrev SplittingSystem (G : Type uG) [Group G] [Finite G] (p : ℕ)
    (O : Type uO) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type uK) [Field K] [Algebra O K] :=
  MR01Spec.SplittingSystemData G p O K

/-- Representatives of all simple left modules, without repetition up to linear equivalence. -/
abbrev IsSimpleRepresentativeFamily {A : Type uA} [Ring A] {ι : Type uI}
    (S : ι → ModuleCat.{uV} A) : Prop :=
  MR01Spec.SimpleRepresentativeFamily S

/-- The action of group elements on a left group-algebra module. -/
noncomputable abbrev moduleRepresentation (F : Type uF) [Field F] (G : Type uG) [Group G]
    (M : Type uV) [AddCommGroup M] [Module (MonoidAlgebra F G) M] :
    Representation F G (RestrictScalars F (MonoidAlgebra F G) M) :=
  Representation.ofModule M

/-- The left group-algebra module obtained by extending the group action linearly. -/
noncomputable def representationModule {F : Type uF} [Field F] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    ModuleCat.{uV} (MonoidAlgebra F G) :=
  ModuleCat.of (MonoidAlgebra F G) ρ.asModule

theorem primeToPart_pos (G : Type uG) [Group G] [Finite G] (p : ℕ) :
    0 < primeToPart G p :=
  Nat.ordCompl_pos p (Nat.ne_of_gt Nat.card_pos)

theorem primeToPart_greatest (G : Type uG) [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    let m := primeToPart G p
    m ∣ Nat.card G ∧ m.Coprime p ∧
      ∀ d : ℕ, d ∣ Nat.card G → d.Coprime p → d ∣ m := by
  refine ⟨Nat.ordCompl_dvd _ _, (Nat.coprime_ordCompl hp (Nat.ne_of_gt Nat.card_pos)).symm, ?_⟩
  intro d hd hdp
  exact Nat.dvd_ordCompl_of_dvd_not_dvd hd (hp.coprime_iff_not_dvd.mp hdp.symm)

theorem orderOf_dvd_primeToPart {G : Type uG} [Group G] {p : ℕ} (hp : p.Prime)
    (g : PRegular G p) : orderOf g.val ∣ primeToPart G p :=
  Nat.dvd_ordCompl_of_dvd_not_dvd (orderOf_dvd_natCard g.val)
    (hp.coprime_iff_not_dvd.mp (show (orderOf g.val).Coprime p from g.property).symm)

theorem SplittingSystem.residue_kernel {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : SplittingSystem G p O K) :
    RingHom.ker (IsLocalRing.residue O) = Ideal.span {S.uniformizer} :=
  (IsLocalRing.ker_residue (R := O)).trans S.maximalIdeal_eq_span

end RepTheorySurvey.Modular
