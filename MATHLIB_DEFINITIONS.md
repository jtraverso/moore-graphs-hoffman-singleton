# Mathlib definitions used in Challenge.lean (Moore graphs, Hoffman–Singleton)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.neighborFinset

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 169:

```lean
/-- `G.neighborFinset v` is the `Finset` version of `G.neighborSet v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
```

## SimpleGraph.degree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 242:

```lean
/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ := #(G.neighborFinset v)
```

## SimpleGraph.IsRegularOfDegree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 390:

```lean
/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
@[wikidata Q826467]
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d
```

## SimpleGraph.commonNeighbors

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 921:

```lean
/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w
```

## SimpleGraph.IsSRGWith

`Mathlib/Combinatorics/SimpleGraph/StronglyRegular.lean`, line 50:

```lean
/-- A graph is strongly regular with parameters `n k ℓ μ` if
* its vertex set has cardinality `n`
* it is regular with degree `k`
* every pair of adjacent vertices has `ℓ` common neighbors
* every pair of nonadjacent vertices has `μ` common neighbors
-/
structure IsSRGWith (n k ℓ μ : ℕ) : Prop where
  card : Fintype.card V = n
  regular : G.IsRegularOfDegree k
  of_adj : ∀ v w, G.Adj v w → Fintype.card (G.commonNeighbors v w) = ℓ
  of_not_adj : Pairwise fun v w ↦ ¬G.Adj v w → Fintype.card (G.commonNeighbors v w) = μ
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.Walk.IsCycle

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 84:

```lean
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup
```

## SimpleGraph.egirth

`Mathlib/Combinatorics/SimpleGraph/Girth.lean`, line 31:

```lean
/--
The extended girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is
acyclic.
-/
noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length
```

## SimpleGraph.edist

`Mathlib/Combinatorics/SimpleGraph/Metric.lean`, line 55:

```lean
/--
The extended distance between two vertices is the length of the shortest walk between them.
It is `⊤` if no such walk exists.
-/
noncomputable def edist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length
```

## SimpleGraph.ediam

`Mathlib/Combinatorics/SimpleGraph/Diam.lean`, line 129:

```lean
/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  ⨆ u, G.eccent u
```
