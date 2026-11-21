import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.Completion

/-! Topology, density, and kernel of the profinite completion of an abstract group. -/

open Filter
open scoped Topology

namespace ALG02GroupTheory.Profinite

universe u

variable {G : Type u} [Group G]

theorem completion_topology (G : Type u) [Group G] :
    CompactSpace (Completion G) ∧ T2Space (Completion G) ∧
      TotallyDisconnectedSpace (Completion G) ∧ IsTopologicalGroup (Completion G) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem projection_continuous (N : FiniteIndexNormalSubgroup G) :
    Continuous (projection N : Completion G → finiteQuotient N) :=
  (projection N).continuous_toFun

theorem projection_surjective (N : FiniteIndexNormalSubgroup G) :
    Function.Surjective (projection N : Completion G → finiteQuotient N) := by
  intro y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N.toSubgroup y
  exact ⟨eta G g, (projection_eta N g).trans hg⟩

theorem isClopen_projection_ker (N : FiniteIndexNormalSubgroup G) :
    IsClopen ((projection N).toMonoidHom.ker : Set (Completion G)) := by
  let _ : DiscreteTopology (finiteQuotient N) := ⟨rfl⟩
  change IsClopen ((projection N : Completion G → finiteQuotient N) ⁻¹' {1})
  exact (isClopen_discrete _).preimage (projection_continuous N)

theorem projection_ker_normal (N : FiniteIndexNormalSubgroup G) :
    (projection N).toMonoidHom.ker.Normal :=
  inferInstance

/-- Every identity neighborhood contains the kernel of a single finite-quotient projection. -/
theorem nhds_one_hasBasis_projection_ker (G : Type u) [Group G] :
    (𝓝 (1 : Completion G)).HasBasis (fun _ : FiniteIndexNormalSubgroup G => True)
      (fun N => ((projection N).toMonoidHom.ker : Set (Completion G))) := by
  rw [Filter.hasBasis_iff]
  intro s
  constructor
  · intro hs
    have hnhds : 𝓝 (1 : Completion G) =
        Filter.comap (fun x : Completion G => x.1)
          (𝓝 (1 : ∀ N : FiniteIndexNormalSubgroup G, finiteQuotient N)) :=
      nhds_subtype_eq_comap (h := (1 : Completion G).2)
    obtain ⟨U, hU, hUs⟩ := Filter.mem_comap.mp (hnhds.ge hs)
    have hU' : U ∈ Filter.pi (fun N : FiniteIndexNormalSubgroup G => 𝓝 (1 : finiteQuotient N)) :=
      (nhds_pi (a := (1 : ∀ N : FiniteIndexNormalSubgroup G, finiteQuotient N))).ge hU
    obtain ⟨I, V, hV, hVU⟩ := Filter.mem_pi'.mp hU'
    let M := finiteIntersection (fun N : I => N.1)
    refine ⟨M, trivial, ?_⟩
    intro x hx
    apply hUs
    apply hVU
    intro N hN
    have hMN : M ≤ N := finiteIntersection_le (fun K : I => K.1) ⟨N, hN⟩
    have hxM : projection M x = 1 := MonoidHom.mem_ker.mp hx
    have hxN : projection N x = 1 :=
      (projection_compatible hMN x).symm.trans
        ((congrArg (transition hMN) hxM).trans (map_one (transition hMN)))
    change projection N x ∈ V N
    rw [hxN]
    exact mem_of_mem_nhds (hV N)
  · rintro ⟨N, -, hNs⟩
    exact Filter.mem_of_superset
      ((isClopen_projection_ker N).2.mem_nhds ((projection N).toMonoidHom.ker.one_mem)) hNs

theorem denseRange_eta (G : Type u) [Group G] : DenseRange (eta G : G → Completion G) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)

theorem ker_eta (G : Type u) [Group G] :
    (eta G).ker = ⨅ N : FiniteIndexNormalSubgroup G, N.toSubgroup := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_iInf]
  constructor
  · intro hg N
    apply (QuotientGroup.eq_one_iff g).mp
    exact (projection_eta N g).symm.trans
      ((congrArg (projection N) hg).trans (map_one (projection N)))
  · intro hg
    apply Subtype.ext
    funext N
    change QuotientGroup.mk (s := N.toSubgroup) g = 1
    exact (QuotientGroup.eq_one_iff g).mpr (hg N)

end ALG02GroupTheory.Profinite
