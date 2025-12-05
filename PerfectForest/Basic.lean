import Mathlib

namespace SimpleGraph
namespace Subgraph

open Classical

variable {V W : Type*} [Fintype V]
variable {G : SimpleGraph V}
variable {M : Subgraph G}

def IsPerfectForest (M : Subgraph G) : Prop :=
    M.coe.IsAcyclic ∧
    (∀ v ∈ M.verts, Odd (M.degree v)) ∧
    (∀ (c : ConnectedComponent M.coe), (M.induce c.supp).IsInduced)

lemma Perfect_Matching_also_Perfect_Forest (h : M.IsPerfectMatching) :
  M.IsPerfectForest := by
    rw [IsPerfectForest]
    constructor
    {
        rw [IsPerfectMatching] at h
        have hmatching : M.IsMatching := h.left
        have hspan := h.right
        have h1 : ∀ v : V, v ∈ M.verts → M.degree v = 1 := by
            have h_matching : M.IsMatching := h.1
            have h2 : ∀ v ∈ M.verts, M.degree v = 1 := by
                rw [isMatching_iff_forall_degree] at h_matching
                exact h_matching
            exact h2

        have h2 : M.coe.IsAcyclic := by
            rw [isAcyclic_iff_forall_adj_isBridge]
            intro v w hadj
            have hv : (v : V) ∈ M.verts := v.coe_prop
            have hw : (w : V) ∈ M.verts := w.coe_prop
            have h3 : M.degree v = 1 := h1 v v.coe_prop -- this is breaking
            have h4 : M.degree w = 1 := by
                sorry
            simp [isBridge_iff]
            <;> try { aesop }
        exact h2
    }
    constructor
    {
        rw [IsPerfectMatching] at h
        intros v hv
        have hdeg : M.degree v = 1 := by
            rw [isMatching_iff_forall_degree] at h
            exact h.left v hv
        rw [hdeg]
        exact Nat.odd_iff.mpr rfl
    }
    {sorry}
