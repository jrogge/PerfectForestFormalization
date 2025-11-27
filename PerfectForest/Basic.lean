import Mathlib

namespace SimpleGraph
namespace Subgraph

open Classical

variable {V W : Type*} [Fintype V]-- [DecidableEq V]
variable {G G' : SimpleGraph V}-- [DecidableRel G.Adj]
variable {M M' : Subgraph G} {u v m w : V}-- [DecidableRel M.Adj]
-- variable (c : ConnectedComponent G)

-- def degreeOdd (M : G.Subgraph) (v : V) : Prop :=
--     Odd (M.degree v)
    -- Odd (Fintype.card { w : V | M.Adj v w })

/-
a *perfect forest* in G is a subgraph of G such that
 - every connected component is an induced subgraph
 - every connected component is a tree (i.e. the graph is a forest)
 - every vertex has odd degree
-/

def IsPerfectForest (M : Subgraph G) : Prop :=
    M.coe.IsAcyclic ∧
    (∀ v ∈ M.verts, Odd (M.degree v)) ∧
    (∀ (c : ConnectedComponent M.coe), (M.induce c.supp).IsInduced)
-- end SimpleGraph

-- namespace Matching

lemma Perfect_Matching_also_Perfect_Forest (h : M.IsPerfectMatching) :
  M.IsPerfectForest := by
    rw [IsPerfectForest]
    constructor
    {
        have pathUnique : (h : ∀ v ∈ M.verts, ∀ w ∈ M.verts, (p q : M.coe.Path v w), p = q) := sorry
        rw [isAcyclic_of_path_unique] at pathUnique
        -- rw [IsAcyclic.path_unique]
        sorry
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
