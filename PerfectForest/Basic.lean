import Mathlib

namespace SimpleGraph
namespace Subgraph

variable {V W : Type*} [Fintype V] [DecidableEq V]
variable {G G' : SimpleGraph V} [DecidableRel G.Adj]
variable {M M' : Subgraph G} {u v m w : V} [DecidableRel M.Adj]
-- variable (c : ConnectedComponent G)
open Classical
def degreeOdd (M : G.Subgraph) (v : V) : Prop :=
    Odd (Fintype.card { w : V | M.Adj v w })

/-
a *perfect forest* in G is a subgraph of G such that
 - every connected component is an induced subgraph
 - every connected component is a tree (i.e. the graph is a forest)
 - every vertex has odd degree
-/

def IsPerfectForest (M : Subgraph G) : Prop :=
    M.coe.IsAcyclic ∧
    (∀ ⦃v⦄, v ∈ M.verts → degreeOdd M v) ∧
    (∀ ⦃c⦄, (c : ConnectedComponent M.coe) → (M.induce (M.verts ∩ c.supp)).IsInduced)
-- end SimpleGraph

-- namespace Matching

lemma Perfect_Matching_also_Perfect_Forest (h : M.IsPerfectMatching) :
  M.IsPerfectForest :=
  sorry
