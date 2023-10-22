/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.big_operators.fin
import algebra.big_operators.order
import algebra.char_p.pi
import data.dfinsupp.well_founded
import data.fin.basic
import data.fin.tuple.sort
import data.fin.vec_notation
import data.finite.card
import data.finset.pairwise
import data.sym.card
import tactic.fin_cases

import prereq.ramsey_prereq

/-!
# Ramsey numbers

Define edge labellings, monochromatic subsets and ramsey numbers, and prove basic properties of
these.
-/

namespace simple_graph
variables {V V' : Type*} {G : simple_graph V} {K K' : Type*}

open fintype (card)
open finset

/--
An edge labelling of a simple graph `G` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labellings where incident edges cannot share a
label.
-/
def edge_labelling (G : simple_graph V) (K : Type*) := G.edge_set → K

instance [decidable_eq V] [fintype G.edge_set] [fintype K] : fintype (edge_labelling G K) :=
pi.fintype
instance [nonempty K] : nonempty (edge_labelling G K) := pi.nonempty
instance [inhabited K] : inhabited (edge_labelling G K) := pi.inhabited _
instance [subsingleton K] : subsingleton (edge_labelling G K) := pi.subsingleton
instance [unique K] : unique (edge_labelling G K) := pi.unique

instance edge_labelling.unique_of_subsingleton [subsingleton V] : unique (edge_labelling G K) :=
pi.unique_of_is_empty _

/--
An edge labelling of the complete graph on `V` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labellings where incident edges cannot share a
label.
-/
abbreviation top_edge_labelling (V : Type*) (K : Type*) :=
edge_labelling (⊤ : simple_graph V) K

lemma card_edge_labelling [decidable_eq V] [fintype V] [fintype K] :
  card (top_edge_labelling V K) = card K ^ (card V).choose 2 :=
fintype.card_fun.trans (by rw card_top_edge_set)

/--
Convenience function to get the colour of the edge `x ~ y` in the colouring of the complete graph
on `V`.
TODO: Generalise to `edge_labelling`, taking a proof that `x ~ y` is indeed true.
-/
def top_edge_labelling.get (C : top_edge_labelling V K) (x y : V)
  (h : x ≠ y . tactic.assumption) : K :=
C ⟨⟦(x, y)⟧, by simp [h]⟩

variables {C : top_edge_labelling V K}

lemma top_edge_labelling.get_swap (x y : V) (h : x ≠ y) :
  C.get y x h.symm = C.get x y :=
by simp only [top_edge_labelling.get, sym2.eq_swap]

lemma top_edge_labelling.ext_get {C C' : top_edge_labelling V K}
  (h : ∀ x y, x ≠ y → C.get x y = C'.get x y) :
  C = C' :=
begin
  ext ⟨e, he⟩,
  induction e using sym2.induction_on,
  exact h _ _ he,
end

/--
Compose an edge-labelling with a function on the colour set.
TODO: Generalise to `edge_labelling`.
-/
def top_edge_labelling.comp_right (C : top_edge_labelling V K) (f : K → K') :
  top_edge_labelling V K' := f ∘ C

/--
Compose an edge-labelling, by an injection into the vertex type. This must be an injection, else
we don't know how to colour `x ~ y` in the case `f x = f y`.
TODO: Generalise to `edge_labelling` and a graph embedding.
-/
def top_edge_labelling.pullback (C : top_edge_labelling V K) (f : V' ↪ V) :
  top_edge_labelling V' K :=
C ∘ (embedding.complete_graph f).map_edge_set

@[simp] lemma top_edge_labelling.pullback_apply {f : V' ↪ V} (e) :
  C.pullback f e = C ((embedding.complete_graph f).map_edge_set e) := rfl

@[simp] lemma top_edge_labelling.pullback_get {f : V' ↪ V} (x y) (h : x ≠ y) :
  (C.pullback f).get x y = C.get (f x) (f y) (by simpa) := rfl

@[simp] lemma top_edge_labelling.comp_right_apply (f : K → K') (e) : C.comp_right f e = f (C e) :=
rfl
@[simp] lemma top_edge_labelling.comp_right_get (f : K → K') (x y) (h : x ≠ y) :
  (C.comp_right f).get x y = f (C.get x y) := rfl

/--
Construct an edge labelling from a symmetric function taking values everywhere except the
diagonal.
TODO: Generalise to `edge_labelling`.
-/
def top_edge_labelling.mk (f : Π x y : V, x ≠ y → K)
  (f_symm : ∀ (x y : V) (H : x ≠ y), f y x H.symm = f x y H) :
  top_edge_labelling V K :=
λ i, subtype.rec_on i $ λ e,
begin
  refine quotient.hrec_on e (λ xy, f xy.1 xy.2) _,
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨⟩,
  { refl },
  ext,
  { simp only [mem_edge_set, top_adj, ne.def, eq_iff_iff, not_iff_not],
    exact comm },
  intros h₁ h₂ h,
  exact heq_of_eq (f_symm _ _ _),
end

lemma top_edge_labelling.mk_get (f : Π x y : V, x ≠ y → K) (f_symm) (x y : V) (h : x ≠ y) :
  (top_edge_labelling.mk f f_symm).get x y = f x y h :=
rfl

/-- `χ.monochromatic_of m c` says that every edge in `m` is assigned the colour `c` by `m`. -/
def top_edge_labelling.monochromatic_of (C : top_edge_labelling V K) (m : set V) (c : K) : Prop :=
∀ ⦃x⦄, x ∈ m → ∀ ⦃y⦄, y ∈ m → x ≠ y → C.get x y = c

lemma top_edge_labelling.monochromatic_of_iff_pairwise [decidable_eq V] (C : top_edge_labelling V K)
  {m : set V} {c : K} :
  C.monochromatic_of m c ↔ m.pairwise (λ x y, if h : x = y then true else C.get x y = c) :=
forall₅_congr (λ x hx y hy h, by simp [h])

/--
Given an edge labelling and a choice of label `k`, construct the graph corresponding to the edges
labelled `k`.
-/
def edge_labelling.label_graph (C : edge_labelling G K) (k : K) : simple_graph V :=
simple_graph.from_edge_set {e | ∃ (h : e ∈ G.edge_set), C ⟨e, h⟩ = k}

lemma edge_labelling.label_graph_adj {C : edge_labelling G K} {k : K} (x y : V) :
  (C.label_graph k).adj x y ↔ ∃ H : G.adj x y, C ⟨⟦(x, y)⟧, H⟩ = k :=
begin
  rw edge_labelling.label_graph,
  simp only [mem_edge_set, from_edge_set_adj, set.mem_set_of_eq, ne.def],
  apply and_iff_left_of_imp _,
  rintro ⟨h, -⟩,
  exact h.ne,
end

instance [decidable_rel G.adj] [decidable_eq K] (k : K) {C : edge_labelling G K} :
  decidable_rel (C.label_graph k).adj :=
λ x y, decidable_of_iff' _ (edge_labelling.label_graph_adj _ _)

@[simp] lemma top_edge_labelling.label_graph_adj {C : top_edge_labelling V K} {k : K} (x y : V) :
  (C.label_graph k).adj x y ↔ ∃ H : x ≠ y, C.get x y = k :=
by { rw [edge_labelling.label_graph_adj], simpa }

lemma edge_labelling.label_graph_le (C : edge_labelling G K) {k : K} : C.label_graph k ≤ G :=
begin
  intros x y,
  rw edge_labelling.label_graph_adj,
  rintro ⟨h, -⟩,
  exact h
end

lemma edge_labelling.pairwise_disjoint {C : edge_labelling G K} :
  set.pairwise_disjoint (set.univ : set K) C.label_graph :=
begin
  intros k₁ hk₁ k₂ hk₂ h,
  simp only [function.on_fun, disjoint_left, edge_labelling.label_graph_adj, not_exists,
    forall_exists_index],
  rintro x y h rfl h',
  exact h
end

lemma edge_labelling.supr_label_graph (C : edge_labelling G K) : (⨆ k : K, C.label_graph k) = G :=
begin
  ext x y,
  simp only [supr_adj, edge_labelling.label_graph_adj],
  split,
  { rintro ⟨k, h, rfl⟩,
    exact h },
  intro h,
  exact ⟨_, h, rfl⟩,
end

lemma edge_labelling.sup_label_graph [fintype K] (C : edge_labelling G K) :
  univ.sup C.label_graph = G := (C.supr_label_graph.symm.trans (by ext; simp)).symm

/--
From a simple graph on `V`, construct the edge labelling on the complete graph of `V` given where
edges are labelled `1` and non-edges are labelled `0`.
-/
def to_edge_labelling (G : simple_graph V) [decidable_rel G.adj] :
  top_edge_labelling V (fin 2) :=
top_edge_labelling.mk (λ x y _, if G.adj x y then 1 else 0) (λ x y h, by simp only [G.adj_comm])

@[simp] lemma to_edge_labelling_get {G : simple_graph V} [decidable_rel G.adj]
  {x y : V} (H : x ≠ y) : G.to_edge_labelling.get x y = if G.adj x y then 1 else 0 :=
rfl

lemma to_edge_labelling_label_graph (G : simple_graph V) [decidable_rel G.adj] :
  G.to_edge_labelling.label_graph 1 = G :=
by { ext x y, simpa [imp_false] using G.ne_of_adj }

lemma to_edge_labelling_label_graph_compl (G : simple_graph V) [decidable_rel G.adj] :
  G.to_edge_labelling.label_graph 0 = Gᶜ :=
by { ext x y, simp [imp_false] }

lemma label_graph_to_edge_labelling [decidable_eq V] (C : top_edge_labelling V (fin 2)) :
  (C.label_graph 1).to_edge_labelling = C :=
begin
  refine top_edge_labelling.ext_get _,
  intros x y h,
  simp only [h, ne.def, not_false_iff, to_edge_labelling_get, top_edge_labelling.label_graph_adj,
    exists_true_left],
  split_ifs,
  { rw h_1 },
  exact (fin.fin_two_eq_zero_of_ne_one h_1).symm,
end

instance [decidable_eq K] [decidable_eq V] (C : top_edge_labelling V K)
  (m : finset V) (c : K) : decidable (C.monochromatic_of m c) :=
decidable_of_iff' _ C.monochromatic_of_iff_pairwise

namespace top_edge_labelling

variables {m : set V} {c : K}

@[simp] lemma monochromatic_of_empty : C.monochromatic_of ∅ c.

@[simp] lemma monochromatic_of_singleton {x : V} : C.monochromatic_of {x} c :=
by simp [top_edge_labelling.monochromatic_of]

lemma monochromatic_finset_singleton {x : V} :
  C.monochromatic_of ({x} : finset V) c :=
by simp [top_edge_labelling.monochromatic_of]

lemma monochromatic_subsingleton (hm : m.subsingleton) :
  C.monochromatic_of m c :=
λ x hx y hy h, by cases h (hm hx hy)

lemma monochromatic_subsingleton_colours [subsingleton K] :
  C.monochromatic_of m c :=
λ x hx y hy h, subsingleton.elim _ _

lemma monochromatic_of.comp_right (e : K → K') (h : C.monochromatic_of m c) :
  (C.comp_right e).monochromatic_of m (e c) :=
λ x hx y hy h', by rw [top_edge_labelling.comp_right_get, h hx hy h']

lemma monochromatic_of_injective (e : K → K') (he : function.injective e) :
  (C.comp_right e).monochromatic_of m (e c) ↔ C.monochromatic_of m c :=
forall₅_congr (λ x hx y hy h', by simp [he.eq_iff])

lemma monochromatic_of.subset {m' : set V} (h' : m' ⊆ m)
  (h : C.monochromatic_of m c) : C.monochromatic_of m' c :=
λ x hx y hy h'', h (h' hx) (h' hy) h''

lemma monochromatic_of.image {C : top_edge_labelling V' K} {f : V ↪ V'}
  (h : (C.pullback f).monochromatic_of m c) : C.monochromatic_of (f '' m) c :=
by simpa [top_edge_labelling.monochromatic_of]

lemma monochromatic_of.map {C : top_edge_labelling V' K} {f : V ↪ V'}
  {m : finset V} (h : (C.pullback f).monochromatic_of m c) : C.monochromatic_of (m.map f) c :=
by { rw [coe_map], exact h.image }

lemma monochromatic_of_insert {x : V} (hx : x ∉ m) :
  C.monochromatic_of (insert x m) c ↔
    C.monochromatic_of m c ∧ ∀ y ∈ m, C.get x y (H.ne_of_not_mem hx).symm = c :=
begin
  split,
  { intro h,
    exact ⟨h.subset (by simp), λ y hy, h (set.mem_insert _ _) (set.mem_insert_of_mem _ hy) _⟩ },
  classical,
  rintro ⟨h₁, h₂⟩,
  simp only [top_edge_labelling.monochromatic_of, ne.def, set.mem_insert_iff, forall_eq_or_imp,
    eq_self_iff_true, not_true, is_empty.forall_iff, true_and],
  refine ⟨λ _ hy _, h₂ _ hy, λ y hy, ⟨λ _, _, λ z hz, h₁ hy hz⟩⟩,
  rw top_edge_labelling.get_swap,
  exact h₂ y hy,
end

/-- The predicate `χ.monochromatic_between X Y k` says every edge between `X` and `Y` is labelled
`k` by the labelling `χ`. -/
def monochromatic_between (C : top_edge_labelling V K) (X Y : finset V) (k : K) : Prop :=
∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → x ≠ y → C.get x y = k

instance [decidable_eq V] [decidable_eq K] {X Y : finset V} {k : K} :
  decidable (monochromatic_between C X Y k) :=
finset.decidable_dforall_finset

@[simp] lemma monochromatic_between_empty_left {Y : finset V} {k : K} :
  C.monochromatic_between ∅ Y k :=
by simp [monochromatic_between]

@[simp] lemma monochromatic_between_empty_right {X : finset V} {k : K} :
  C.monochromatic_between X ∅ k :=
by simp [monochromatic_between]

lemma monochromatic_between_singleton_left {x : V} {Y : finset V} {k : K} :
  C.monochromatic_between {x} Y k ↔ ∀ ⦃y⦄, y ∈ Y → x ≠ y → C.get x y = k :=
by simp [monochromatic_between]

lemma monochromatic_between_singleton_right {y : V} {X : finset V} {k : K} :
  C.monochromatic_between X {y} k ↔ ∀ ⦃x⦄, x ∈ X → x ≠ y → C.get x y = k :=
by simp [monochromatic_between]

lemma monochromatic_between_union_left [decidable_eq V] {X Y Z : finset V} {k : K} :
  C.monochromatic_between (X ∪ Y) Z k ↔
    C.monochromatic_between X Z k ∧ C.monochromatic_between Y Z k :=
by simp only [monochromatic_between, mem_union, or_imp_distrib, forall_and_distrib]

lemma monochromatic_between_union_right [decidable_eq V] {X Y Z : finset V} {k : K} :
  C.monochromatic_between X (Y ∪ Z) k ↔
    C.monochromatic_between X Y k ∧ C.monochromatic_between X Z k :=
by simp only [monochromatic_between, mem_union, or_imp_distrib, forall_and_distrib]

lemma monochromatic_between_self {X : finset V} {k : K} :
  C.monochromatic_between X X k ↔ C.monochromatic_of X k :=
by simp only [monochromatic_between, monochromatic_of, mem_coe]

lemma _root_.disjoint.monochromatic_between {X Y : finset V} {k : K} (h : disjoint X Y) :
  C.monochromatic_between X Y k ↔
    ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → C.get x y (h.forall_ne_finset ‹_› ‹_›) = k :=
forall₄_congr $ λ x hx y hy, by simp [h.forall_ne_finset hx hy]

lemma monochromatic_between.subset_left {X Y Z : finset V} {k : K}
  (hYZ : C.monochromatic_between Y Z k) (hXY : X ⊆ Y) :
  C.monochromatic_between X Z k :=
λ x hx y hy h, hYZ (hXY hx) hy _

lemma monochromatic_between.subset_right {X Y Z : finset V} {k : K}
  (hXZ : C.monochromatic_between X Z k) (hXY : Y ⊆ Z) :
  C.monochromatic_between X Y k :=
λ x hx y hy h, hXZ hx (hXY hy) _

lemma monochromatic_between.subset {W X Y Z : finset V} {k : K}
  (hWX : C.monochromatic_between W X k) (hYW : Y ⊆ W) (hZX : Z ⊆ X) :
  C.monochromatic_between Y Z k :=
λ x hx y hy h, hWX (hYW hx) (hZX hy) _

lemma monochromatic_between.symm {X Y : finset V} {k : K}
  (hXY : C.monochromatic_between X Y k) :
  C.monochromatic_between Y X k :=
λ y hy x hx h, by { rw get_swap _ _ h.symm, exact hXY hx hy _ }

lemma monochromatic_between.comm {X Y : finset V} {k : K} :
  C.monochromatic_between Y X k ↔ C.monochromatic_between X Y k :=
⟨monochromatic_between.symm, monochromatic_between.symm⟩

lemma monochromatic_of_union {X Y : finset V} {k : K} :
  C.monochromatic_of (X ∪ Y) k ↔
    C.monochromatic_of X k ∧ C.monochromatic_of Y k ∧ C.monochromatic_between X Y k :=
begin
  have : C.monochromatic_between X Y k ∧ C.monochromatic_between Y X k ↔
    C.monochromatic_between X Y k := (and_iff_left_of_imp monochromatic_between.symm),
  rw ←this,
  simp only [monochromatic_of, set.mem_union, or_imp_distrib, forall_and_distrib, mem_coe,
    monochromatic_between],
  tauto,
end

end top_edge_labelling

open top_edge_labelling

-- TODO (BM): I think the `∃` part of this should be its own def...
/--
The predicate `is_ramsey_valid V n` says that the type `V` is large enough to guarantee a
clique of size `n k` for some colour `k : K`.
-/
def is_ramsey_valid (V : Type*) (n : K → ℕ) : Prop :=
∀ C : top_edge_labelling V K, ∃ (m : finset V) c, C.monochromatic_of m c ∧ n c ≤ m.card

lemma is_ramsey_valid.empty_colours [is_empty K] {n : K → ℕ} : is_ramsey_valid (fin 2) n :=
λ C, is_empty_elim (C.get 0 1 (by norm_num))

lemma is_ramsey_valid.exists_zero_of_is_empty [is_empty V] {n : K → ℕ} (h : is_ramsey_valid V n) :
  ∃ c, n c = 0 :=
let ⟨m, c, hm, hc⟩ := h (is_empty.elim (by simp)) in ⟨c, by simpa [subsingleton.elim m ∅] using hc⟩

lemma is_ramsey_valid_of_zero {n : K → ℕ} (c : K) (hc : n c = 0) : is_ramsey_valid V n :=
λ C, ⟨∅, c, by simp, by simp [hc]⟩

lemma is_ramsey_valid_of_exists_zero (n : K → ℕ) (h : ∃ c, n c = 0) : is_ramsey_valid V n :=
let ⟨c, hc⟩ := h in is_ramsey_valid_of_zero _ hc

lemma is_ramsey_valid.mono_right {n n' : K → ℕ} (h : n ≤ n') (h' : is_ramsey_valid V n') :
  is_ramsey_valid V n :=
λ C, let ⟨m, c, hc, hm⟩ := h' C in ⟨m, c, hc, hm.trans' (h _)⟩

lemma is_ramsey_valid_iff_eq {n : K → ℕ} :
  is_ramsey_valid V n ↔
    ∀ C : top_edge_labelling V K, ∃ (m : finset V) c, C.monochromatic_of m c ∧ n c = m.card :=
begin
  refine forall_congr (λ C, _),
  rw [exists_comm, @exists_comm (finset V)],
  refine exists_congr (λ c, _),
  split,
  { rintro ⟨a, ha, ha'⟩,
    obtain ⟨b, hb, hb'⟩ := exists_smaller_set a _ ha',
    exact ⟨b, ha.subset hb, hb'.symm⟩ },
  { rintro ⟨a, ha, ha'⟩,
    exact ⟨_, ha, ha'.le⟩ }
end

lemma is_ramsey_valid_iff_embedding_aux {n : K → ℕ} (c : K) :
  (∃ (m : finset V), C.monochromatic_of m c ∧ n c = m.card) ↔
    nonempty ((⊤ : simple_graph (fin (n c))) ↪g C.label_graph c) :=
begin
  split,
  { rintro ⟨m, hm, hm'⟩,
    have : fintype.card m = n c,
    { rw [fintype.card_coe, hm'] },
    classical,
    obtain ⟨e⟩ := fintype.trunc_equiv_fin_of_card_eq this,
    refine ⟨⟨e.symm.to_embedding.trans (function.embedding.subtype _), _⟩⟩,
    intros a b,
    simp only [ne.def, function.embedding.trans_apply, equiv.coe_to_embedding,
      function.embedding.coe_subtype, label_graph_adj, top_adj, ←subtype.ext_iff,
      embedding_like.apply_eq_iff_eq],
    split,
    { rintro ⟨h, -⟩,
      exact h },
    intro h,
    exact ⟨h, hm (e.symm a).prop (e.symm b).prop _⟩ },
  rintro ⟨f⟩,
  refine ⟨(univ : finset (fin (n c))).map f.to_embedding, _, _⟩,
  { rw monochromatic_of,
    simp only [ne.def, rel_embedding.inj, coe_map, rel_embedding.coe_fn_to_embedding, set.mem_image,
      coe_univ, set.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff'],
    intros x y h,
    have : (⊤ : simple_graph (fin (n c))).adj x y := h,
    simpa [←f.map_rel_iff, h] using this },
  rw [card_map, card_fin],
end

-- BM: pretty good chance this is a better definition...
-- it also generalises better to induced ramsey numbers of graphs
-- and if you transfer with `top_hom_graph_equiv` you get ramsey numbers of graphs
lemma is_ramsey_valid_iff_embedding {n : K → ℕ} :
  is_ramsey_valid V n ↔
    ∀ C : top_edge_labelling V K,
      ∃ c : K, nonempty ((⊤ : simple_graph (fin (n c))) ↪g C.label_graph c) :=
begin
  rw is_ramsey_valid_iff_eq,
  refine forall_congr (λ C, _),
  rw exists_comm,
  simp only [is_ramsey_valid_iff_embedding_aux],
end

lemma is_ramsey_valid.embedding {n : K → ℕ} (f : V ↪ V') (h' : is_ramsey_valid V n) :
  is_ramsey_valid V' n :=
λ C, let ⟨m', c, hc, hm'⟩ := h' (C.pullback f) in ⟨m'.map f, c,
by simpa only [coe_map] using hc.image, hm'.trans_eq (card_map _).symm⟩

lemma is_ramsey_valid.card_fin [fintype V] {N : ℕ} {n : K → ℕ} (h : N ≤ card V)
  (h' : is_ramsey_valid (fin N) n) : is_ramsey_valid V n :=
h'.embedding $ (fin.cast_le h).to_embedding.trans (fintype.equiv_fin V).symm

lemma is_ramsey_valid.equiv_left (n : K → ℕ) (f : V ≃ V') :
  is_ramsey_valid V n ↔ is_ramsey_valid V' n :=
⟨λ h, h.embedding f, λ h, h.embedding f.symm⟩

lemma is_ramsey_valid.equiv_right {n : K → ℕ} (f : K' ≃ K) (h : is_ramsey_valid V n) :
  is_ramsey_valid V (n ∘ f) :=
λ C, let ⟨m, c, hm, hc⟩ := h (C.comp_right f) in
⟨m, f.symm c, by rwa [←monochromatic_of_injective f f.injective, f.apply_symm_apply],
  by simpa using hc⟩

lemma is_ramsey_valid_equiv_right {n : K → ℕ} (f : K' ≃ K) :
  is_ramsey_valid V (n ∘ f) ↔ is_ramsey_valid V n :=
⟨λ h, by { convert h.equiv_right f.symm, ext, simp }, λ h, h.equiv_right _⟩

instance [decidable_eq K] [fintype K] [decidable_eq V] [fintype V] (n : K → ℕ) :
  decidable (is_ramsey_valid V n) :=
fintype.decidable_forall_fintype

lemma ramsey_base [nonempty V] {n : K → ℕ} (hn : ∃ k, n k ≤ 1) :
  is_ramsey_valid V n :=
begin
  inhabit V,
  obtain ⟨k, hk⟩ := hn,
  exact λ C, ⟨{arbitrary V}, k, monochromatic_finset_singleton, by simpa using hk⟩,
end

lemma ramsey_base' [fintype V] (n : K → ℕ) (hn : ∃ k, n k ≤ 1) (hV : 1 ≤ card V) :
  is_ramsey_valid V n :=
@ramsey_base _ _ (fintype.card_pos_iff.1 hV) _ hn

lemma is_ramsey_valid_min [fintype V] [nonempty K] {n : K → ℕ} {n' : ℕ} (h : is_ramsey_valid V n)
  (hn : ∀ k, n' ≤ n k) : n' ≤ card V :=
let ⟨m, h, h', hm⟩ := h (classical.arbitrary (top_edge_labelling V K))
in (hn _).trans (hm.trans (finset.card_le_univ m))

lemma is_ramsey_valid_unique [fintype V] [unique K] {n : K → ℕ} (hV : n default ≤ card V) :
  is_ramsey_valid V n :=
λ C, ⟨univ, default, monochromatic_subsingleton_colours, by simpa⟩

lemma is_ramsey_valid.remove_twos {n : K → ℕ} (h : is_ramsey_valid V n) :
  is_ramsey_valid V (λ (k : {k : K // n k ≠ 2}), n k) :=
begin
  casesI is_empty_or_nonempty V with hV hV,
  { obtain ⟨c, hc⟩ := h.exists_zero_of_is_empty,
    exact is_ramsey_valid_of_zero ⟨c, by simp [hc]⟩ hc },
  by_cases h' : ∃ k, n k ≤ 1,
  { obtain ⟨k, hk⟩ := h',
    refine ramsey_base ⟨⟨k, _⟩, hk⟩,
    linarith },
  simp only [not_exists, not_le, nat.lt_iff_add_one_le] at h',
  intro C,
  obtain ⟨m, c, hm, hc⟩ := h (C.comp_right subtype.val),
  have : 1 < m.card := (h' c).trans hc,
  rw finset.one_lt_card_iff at this,
  obtain ⟨a, b, ha, hb, hab⟩ := this,
  have : subtype.val (C.get a b hab) = c := hm ha hb hab,
  refine ⟨m, _, _, hc.trans_eq' (congr_arg n this)⟩,
  rwa [←monochromatic_of_injective _ subtype.val_injective, this],
end

lemma is_ramsey_valid.of_remove_twos {n : K → ℕ}
  (h : is_ramsey_valid V (λ (k : {k : K // n k ≠ 2}), n k)) :
  is_ramsey_valid V n :=
begin
  intro C,
  classical,
  by_cases h'' : ∃ (x y : V) (H : x ≠ y), n (C.get x y) = 2,
  { obtain ⟨x, y, H, hxy⟩ := h'',
    have : x ∉ ({y} : set V) := by simpa,
    refine ⟨({x, y} : finset V), C.get x y, _, _⟩,
    { rw [coe_pair, monochromatic_of_insert this],
      refine ⟨monochromatic_of_singleton, _⟩,
      simp only [set.mem_singleton_iff],
      rintro _ rfl,
      refl },
    rw [hxy, card_doubleton H] },
  push_neg at h'',
  let C' : top_edge_labelling V {k : K // n k ≠ 2} :=
    top_edge_labelling.mk (λ x y h, ⟨C.get x y, h'' _ _ h⟩) _,
  swap,
  { intros x y h,
    ext,
    dsimp,
    exact get_swap _ _ _ },
  obtain ⟨m, c, hm, hc⟩ := h C',
  refine ⟨m, c, _, hc⟩,
  intros x hx y hy h,
  exact subtype.ext_iff.1 (hm hx hy h),
end

lemma is_ramsey_valid_iff_remove_twos (n : K → ℕ) :
  is_ramsey_valid V (λ (k : {k : K // n k ≠ 2}), n k) ↔ is_ramsey_valid V n :=
⟨is_ramsey_valid.of_remove_twos, is_ramsey_valid.remove_twos⟩

lemma is_ramsey_valid_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
  (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
  (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
  (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
  (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) :
  is_ramsey_valid V n' ↔ is_ramsey_valid V n :=
begin
  let e : {k // n' k ≠ 2} → {k // n k ≠ 2} := λ k, ⟨f k, hf _ k.prop⟩,
  have he : function.injective e :=
    λ a b h, subtype.ext (hf_inj _ _ a.prop b.prop (subtype.ext_iff.1 h)),
  have he' : function.surjective e,
  { rintro ⟨i, hi⟩,
    simpa using hf_surj i hi },
  rw [←is_ramsey_valid_iff_remove_twos n, ←is_ramsey_valid_iff_remove_twos n',
    ←is_ramsey_valid_equiv_right (equiv.of_bijective e ⟨he, he'⟩)],
  congr' 2,
  ext ⟨k, hk⟩,
  exact (hf_comm _ hk).symm,
end

open_locale big_operators

variables [decidable_eq K'] [fintype K'] {n : K → ℕ}

theorem ramsey_fin_induct_aux {V : Type*} [decidable_eq K]
  {n : K → ℕ} (N : K → ℕ) {C : top_edge_labelling V K}
  (m : K → finset V) (x : V)
  (hN : ∀ k, is_ramsey_valid (fin (N k)) (function.update n k (n k - 1)))
  (hx : ∀ k, x ∉ m k) (h : ∃ k, N k ≤ (m k).card)
  (hm : ∀ k (y : V) (hy : y ∈ m k), C.get x y (ne_of_mem_of_not_mem hy (hx k)).symm = k) :
  ∃ (m : finset V) c, C.monochromatic_of m c ∧ n c ≤ m.card :=
begin
  classical,
  obtain ⟨k, hk⟩ := h,
  have : is_ramsey_valid (m k) (function.update n k (n k - 1)) := (hN k).card_fin (by simp [hk]),
  obtain ⟨m', k', hm', hk'⟩ := this (C.pullback (function.embedding.subtype _)),
  rcases ne_or_eq k k' with hk | rfl,
  { exact ⟨_, _, hm'.map, by simpa [hk.symm] using hk'⟩ },
  have : x ∉ (m'.map (function.embedding.subtype _) : set V),
  { simp [hx k] },
  refine ⟨insert (x : V) (m'.map (function.embedding.subtype _)), k, _, _⟩,
  { rw [coe_insert, top_edge_labelling.monochromatic_of_insert this],
    refine ⟨hm'.map, λ y hy, _⟩,
    generalize_proofs,
    simp only [mem_neighbor_finset, mem_coe, mem_map, function.embedding.coe_subtype, exists_prop,
      subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
      top_edge_labelling.label_graph_adj] at hy,
    obtain ⟨hy, _⟩ := hy,
    exact hm _ _ hy, },
  rw [card_insert_of_not_mem this, card_map, ←tsub_le_iff_right],
  rwa function.update_same at hk',
end

theorem ramsey_fin_induct [decidable_eq K] [fintype K] (n : K → ℕ) (N : K → ℕ)
  (hN : ∀ k, is_ramsey_valid (fin (N k)) (function.update n k (n k - 1))) :
  is_ramsey_valid (fin (∑ k, (N k - 1) + 2)) n :=
begin
  by_cases h : ∃ k, n k ≤ 1,
  { refine ramsey_base' _ h _,
    rw [fintype.card_fin],
    exact (nat.le_add_left _ _).trans' (by simp) },
  push_neg at h,
  have hN' : ∀ k, 1 ≤ N k,
  { intro k,
    by_contra',
    haveI : is_empty (fin (N k)),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_is_empty,
    rcases eq_or_ne k k' with rfl | hk,
    { simp only [function.update_same, tsub_eq_zero_iff_le] at hk',
      exact hk'.not_lt (h _) },
    rw function.update_noteq hk.symm at hk',
    simpa only [not_lt_zero'] using (h k').trans_eq hk' },
  classical,
  set V := fin (∑ k, (N k - 1) + 2),
  intro C,
  let x : V := 0,
  let m : K → finset V := λ k, neighbor_finset (C.label_graph k) x,
  have : univ.bUnion m = {x}ᶜ,
  { simp only [←finset.coe_inj, coe_bUnion, mem_coe, mem_univ, set.Union_true, coe_compl,
      coe_singleton, m, coe_neighbor_finset],
    rw [←neighbor_set_supr, edge_labelling.supr_label_graph C, neighbor_set_top] },
  have e : ∑ k, (m k).card = ∑ k, (N k - 1) + 1,
  { rw [←card_bUnion, this, card_compl, ←card_univ, card_fin, card_singleton, nat.add_succ_sub_one],
    rintro x hx y hy h,
    refine neighbor_finset_disjoint _,
    exact edge_labelling.pairwise_disjoint (by simp) (by simp) h },
  have : ∃ k, N k - 1 < (m k).card,
  { by_contra',
    have : ∑ k, (m k).card ≤ ∑ k, (N k - 1) := sum_le_sum (λ k _, this k),
    rw [e] at this,
    simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using this },
  obtain ⟨k, hk⟩ := this,
  rw [tsub_lt_iff_right (hN' _), nat.lt_add_one_iff] at hk,
  refine ramsey_fin_induct_aux _ m x hN _ ⟨k, hk⟩ _,
  { simp },
  { simp },
end

theorem ramsey_fin_exists [finite K] (n : K → ℕ) :
  ∃ N, is_ramsey_valid (fin N) n :=
begin
  classical,
  refine @well_founded_lt.induction _ _ _ (λ a, ∃ N, is_ramsey_valid (fin N) a) n _,
  clear n,
  intros n ih,
  by_cases h : ∃ k, n k = 0,
  { exact ⟨0, is_ramsey_valid_of_exists_zero _ h⟩ },
  push_neg at h,
  dsimp at ih,
  have : ∀ k, function.update n k (n k - 1) < n,
  { simp only [update_lt_self_iff],
    intro k,
    exact nat.pred_lt (h k) },
  have := λ k, ih _ (this k),
  choose N hN using this,
  casesI nonempty_fintype K,
  exact ⟨_, ramsey_fin_induct _ _ hN⟩,
end

-- hn can be weakened but it's just a nontriviality assumption
lemma ramsey_fin_induct' [decidable_eq K] [fintype K] (n : K → ℕ) (N : K → ℕ)
  (hn : ∀ k, 2 ≤ n k) (hN : ∀ k, is_ramsey_valid (fin (N k)) (function.update n k (n k - 1))) :
  is_ramsey_valid (fin (∑ k, N k + 2 - card K)) n :=
begin
  have hN' : ∀ k, 1 ≤ N k,
  { intro k,
    by_contra',
    haveI : is_empty (fin (N k)),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_is_empty,
    rcases eq_or_ne k k' with rfl | hk,
    { simp only [function.update_same, tsub_eq_zero_iff_le] at hk',
      exact hk'.not_lt (hn _) },
    rw function.update_noteq hk.symm at hk',
    simpa only [le_zero_iff] using (hn k').trans_eq hk' },
  have h : ∀ x : K, x ∈ (univ : finset K) → 1 ≤ N x,
  { simpa using hN' },
  have := ramsey_fin_induct n N hN,
  rwa [sum_tsub _ h, tsub_add_eq_add_tsub, ←fintype.card_eq_sum_ones] at this,
  exact sum_le_sum h,
end

open matrix (vec_cons)

theorem ramsey_fin_induct_two {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
  (hi' : is_ramsey_valid (fin Ni) ![i - 1, j])
  (hj' : is_ramsey_valid (fin Nj) ![i, j - 1]) :
  is_ramsey_valid (fin (Ni + Nj)) ![i, j] :=
begin
  have : ∑ z : fin 2, ![Ni, Nj] z + 2 - card (fin 2) = Ni + Nj,
  { simp },
  have h := ramsey_fin_induct' ![i, j] ![Ni, Nj] _ _,
  { rwa this at h },
  { rw fin.forall_fin_two,
    exact ⟨hi, hj⟩ },
  { rw [fin.forall_fin_two, function.update_head, function.update_cons_one],
    exact ⟨hi', hj'⟩ },
end

theorem ramsey_fin_induct_two_evens {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
  (hNi : even Ni) (hNj : even Nj)
  (hi' : is_ramsey_valid (fin Ni) ![i - 1, j])
  (hj' : is_ramsey_valid (fin Nj) ![i, j - 1]) :
  is_ramsey_valid (fin (Ni + Nj - 1)) ![i, j] :=
begin
  have hNi' : 1 ≤ Ni,
  { by_contra',
    haveI : is_empty (fin Ni),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := hi'.exists_zero_of_is_empty,
    revert k',
    simp only [fin.forall_fin_two, imp_false, matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      matrix.cons_val_one, matrix.head_cons],
    exact ⟨hi, by linarith⟩ },
  have hNj' : 1 ≤ Nj,
  { by_contra',
    haveI : is_empty (fin Nj),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := hj'.exists_zero_of_is_empty,
    revert k',
    simp only [fin.forall_fin_two, imp_false, matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      matrix.cons_val_one, matrix.head_cons],
    exact ⟨by linarith, hj⟩ },
  have : odd (card (fin (Ni + Nj - 1))),
  { rw [fintype.card_fin, nat.odd_sub (le_add_right hNi')],
    simp [hNi, hNj] with parity_simps },
  intro C,
  obtain ⟨x, hx⟩ := @exists_even_degree (fin (Ni + Nj - 1)) (C.label_graph 0) _ _ this,
  let m : fin 2 → finset (fin (Ni + Nj - 1)) := λ k, neighbor_finset (C.label_graph k) x,
  change even (m 0).card at hx,
  have : univ.bUnion m = {x}ᶜ,
  { simp only [←finset.coe_inj, coe_bUnion, mem_coe, mem_univ, set.Union_true, coe_compl,
      coe_singleton, m, coe_neighbor_finset],
    rw [←neighbor_set_supr, edge_labelling.supr_label_graph C, neighbor_set_top] },
  have e : ∑ k, (m k).card = Ni + Nj - 2,
  { rw [←card_bUnion, this, card_compl, ←card_univ, card_fin, card_singleton, nat.sub_sub],
    rintro x hx y hy h,
    refine neighbor_finset_disjoint _,
    exact edge_labelling.pairwise_disjoint (by simp) (by simp) h },
  have : Ni ≤ (m 0).card ∨ Nj ≤ (m 1).card,
  { have : (m 0).card + 1 ≠ Ni,
    { intro h,
      rw [←h] at hNi,
      simpa [hx] with parity_simps using hNi },
    rw [eq_tsub_iff_add_eq_of_le (add_le_add hNi' hNj'), fin.sum_univ_two] at e,
    by_contra' h',
    rw [nat.lt_iff_add_one_le, nat.lt_iff_add_one_le, le_iff_lt_or_eq, or_iff_left this,
      nat.lt_iff_add_one_le, add_assoc] at h',
    have := add_le_add h'.1 h'.2,
    rw [add_add_add_comm, ←add_assoc, e] at this,
    simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using this },
  refine ramsey_fin_induct_aux ![Ni, Nj] m x _ (by simp) _ _,
  { rw [fin.forall_fin_two, function.update_head, function.update_cons_one],
    exact ⟨hi', hj'⟩ },
  { rwa fin.exists_fin_two },
  { rw [fin.forall_fin_two],
    simp only [mem_neighbor_finset, label_graph_adj, forall_exists_index, imp_self,
      implies_true_iff, and_self] }
end

theorem ramsey_fin_induct_three {i j k Ni Nj Nk : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k)
  (hi' : is_ramsey_valid (fin Ni) ![i - 1, j, k])
  (hj' : is_ramsey_valid (fin Nj) ![i, j - 1, k])
  (hk' : is_ramsey_valid (fin Nk) ![i, j, k - 1]) :
  is_ramsey_valid (fin (Ni + Nj + Nk - 1)) ![i, j, k] :=
begin
  have : (∑ (k : fin 3), ![Ni, Nj, Nk] k + 2 - card (fin 3)) = (Ni + Nj + Nk - 1),
  { rw [fintype.card_fin, nat.succ_sub_succ_eq_sub, fin.sum_univ_three],
    refl },
  have h := ramsey_fin_induct' ![i, j, k] ![Ni, Nj, Nk] _ _,
  { rwa this at h },
  { rw [fin.forall_fin_succ, fin.forall_fin_two],
    exact ⟨hi, hj, hk⟩ },
  { rw [fin.forall_fin_succ, fin.forall_fin_two, function.update_head, fin.succ_zero_eq_one',
      fin.succ_one_eq_two', function.update_cons_one, function.update_cons_two],
    exact ⟨hi', hj', hk'⟩ }
end

variables {N : ℕ} [fintype V] [decidable_eq K] [fintype K]

/--
Given a tuple `n : K → ℕ` of naturals indexed by `K`, define the ramsey number as the smallest
`N` such that any labelling of the complete graph on `N` vertices with `K` labels contains a
subset of size `n k` in which every edge is labelled `k`.
While this definition is computable, it is not at all efficient to compute.
-/
def ramsey_number (n : K → ℕ) : ℕ := nat.find (ramsey_fin_exists n)

lemma ramsey_number_spec_fin (n : K → ℕ) : is_ramsey_valid (fin (ramsey_number n)) n :=
nat.find_spec (ramsey_fin_exists n)

lemma ramsey_number_spec (h : ramsey_number n ≤ card V) : is_ramsey_valid V n :=
(ramsey_number_spec_fin n).card_fin h

lemma ramsey_number_min_fin (hN : is_ramsey_valid (fin N) n) : ramsey_number n ≤ N :=
nat.find_min' (ramsey_fin_exists n) hN

lemma ramsey_number_min (hN : is_ramsey_valid V n) : ramsey_number n ≤ card V :=
ramsey_number_min_fin (hN.embedding (fintype.equiv_fin V).to_embedding)

lemma ramsey_number_le_iff : ramsey_number n ≤ card V ↔ is_ramsey_valid V n :=
⟨ramsey_number_spec, ramsey_number_min⟩

lemma ramsey_number_le_iff_fin : ramsey_number n ≤ N ↔ is_ramsey_valid (fin N) n :=
⟨λ h, (ramsey_number_spec_fin n).embedding (fin.cast_le h).to_embedding, ramsey_number_min_fin⟩

lemma ramsey_number_eq_of (h : is_ramsey_valid (fin (N + 1)) n) (h' : ¬ is_ramsey_valid (fin N) n) :
  ramsey_number n = N + 1 :=
by { rw ←ramsey_number_le_iff_fin at h h', exact h.antisymm (lt_of_not_le h') }

lemma ramsey_number_congr {n' : K' → ℕ}
  (h : ∀ N, is_ramsey_valid (fin N) n ↔ is_ramsey_valid (fin N) n') :
  ramsey_number n = ramsey_number n' :=
(ramsey_number_min_fin ((h _).2 (ramsey_number_spec_fin _))).antisymm
  (ramsey_number_min_fin ((h _).1 (ramsey_number_spec_fin _)))

lemma ramsey_number_equiv (f : K' ≃ K) :
  ramsey_number (n ∘ f) = ramsey_number n :=
ramsey_number_congr (λ _, is_ramsey_valid_equiv_right f)

lemma ramsey_number_first_swap {i : ℕ} (x y : ℕ) (t : fin i → ℕ) :
  ramsey_number (vec_cons x (vec_cons y t)) = ramsey_number (vec_cons y (vec_cons x t)) :=
begin
  have : vec_cons x (vec_cons y t) ∘ equiv.swap 0 1 = vec_cons y (vec_cons x t),
  { rw function.swap_cons },
  rw [←this, ramsey_number_equiv],
end

lemma ramsey_number_pair_swap (x y : ℕ) : ramsey_number ![x, y] = ramsey_number ![y, x] :=
ramsey_number_first_swap _ _ _

lemma ramsey_number.eq_zero_iff : ramsey_number n = 0 ↔ ∃ c, n c = 0 :=
begin
  rw [←le_zero_iff, ramsey_number_le_iff_fin],
  exact ⟨λ h, h.exists_zero_of_is_empty, is_ramsey_valid_of_exists_zero _⟩,
end

lemma ramsey_number.exists_zero_of_eq_zero (h : ramsey_number n = 0) : ∃ c, n c = 0 :=
ramsey_number.eq_zero_iff.1 h

lemma ramsey_number_exists_zero (c : K) (hc : n c = 0) : ramsey_number n = 0 :=
ramsey_number.eq_zero_iff.2 ⟨c, hc⟩

lemma ramsey_number_pos : 0 < ramsey_number n ↔ (∀ c, n c ≠ 0) :=
by rw [pos_iff_ne_zero, ne.def, ramsey_number.eq_zero_iff, not_exists]

lemma ramsey_number_le_one (hc : ∃ c, n c ≤ 1) : ramsey_number n ≤ 1 :=
by { rw ramsey_number_le_iff_fin, exact ramsey_base hc }

lemma ramsey_number_ge_min [nonempty K] (i : ℕ) (hk : ∀ k, i ≤ n k) : i ≤ ramsey_number n :=
(is_ramsey_valid_min (ramsey_number_spec_fin n) hk).trans_eq (card_fin _)

lemma exists_le_of_ramsey_number_le [nonempty K] (i : ℕ) (hi : ramsey_number n ≤ i) :
  ∃ k, n k ≤ i :=
by { contrapose! hi, exact ramsey_number_ge_min (i + 1) hi }

@[simp] lemma ramsey_number_empty [is_empty K] : ramsey_number n = 2 :=
begin
  refine ramsey_number_eq_of _ _,
  { exact is_ramsey_valid.empty_colours },
  simp [is_ramsey_valid],
end

lemma ramsey_number_nil : ramsey_number ![] = 2 := ramsey_number_empty

lemma exists_le_one_of_ramsey_number_le_one (hi : ramsey_number n ≤ 1) : ∃ k, n k ≤ 1 :=
begin
  haveI : nonempty K,
  { rw ←not_is_empty_iff,
    introI,
    rw ramsey_number_empty at hi,
    norm_num at hi },
  exact exists_le_of_ramsey_number_le _ hi,
end

lemma ramsey_number_eq_one (hc : ∃ c, n c = 1) (hc' : ∀ c, n c ≠ 0) : ramsey_number n = 1 :=
begin
  obtain ⟨c, hc⟩ := hc,
  refine (ramsey_number_le_one ⟨c, hc.le⟩).antisymm _,
  rwa [nat.succ_le_iff, ramsey_number_pos],
end

lemma ramsey_number_eq_one_iff : (∃ c, n c = 1) ∧ (∀ c, n c ≠ 0) ↔ ramsey_number n = 1 :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    exact ramsey_number_eq_one h₁ h₂ },
  intro h,
  have : ramsey_number n ≠ 0,
  { rw h, simp },
  rw [ne.def, ramsey_number.eq_zero_iff, not_exists] at this,
  obtain ⟨k, hk⟩ := exists_le_one_of_ramsey_number_le_one h.le,
  refine ⟨⟨k, hk.antisymm _⟩, this⟩,
  rw [nat.succ_le_iff, pos_iff_ne_zero],
  exact this _
end

lemma ramsey_number_unique_colour [unique K] : ramsey_number n = n default :=
begin
  refine le_antisymm (ramsey_number_min_fin (is_ramsey_valid_unique (by simp))) _,
  refine ramsey_number_ge_min _ (λ k, _),
  rw subsingleton.elim default k,
end

@[simp] lemma ramsey_number_singleton {i : ℕ} : ramsey_number ![i] = i :=
by rw [ramsey_number_unique_colour, matrix.cons_val_fin_one]

lemma ramsey_number.mono {n n' : K → ℕ} (h : n ≤ n') : ramsey_number n ≤ ramsey_number n' :=
by { rw [ramsey_number_le_iff_fin], exact (ramsey_number_spec_fin _).mono_right h }

lemma ramsey_number.mono_two {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
  ramsey_number ![a, c] ≤ ramsey_number ![b, d] :=
ramsey_number.mono (by { rw [pi.le_def, fin.forall_fin_two], exact ⟨hab, hcd⟩ })

lemma ramsey_number_monotone {i : ℕ} : monotone (ramsey_number : (fin i → ℕ) → ℕ) :=
λ _ _ h, ramsey_number.mono h

lemma ramsey_number_remove_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
  (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
  (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
  (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
  (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) :
  ramsey_number n' = ramsey_number n :=
ramsey_number_congr (λ N, is_ramsey_valid_two f hf hf_inj hf_surj hf_comm)

@[simp] lemma ramsey_number_cons_two {i : ℕ} {n : fin i → ℕ} :
  ramsey_number (matrix.vec_cons 2 n) = ramsey_number n :=
by { refine (ramsey_number_remove_two fin.succ _ _ _ _).symm; simp [fin.forall_fin_succ] }

@[simp] lemma ramsey_number_cons_zero {i : ℕ} {n : fin i → ℕ} :
  ramsey_number (matrix.vec_cons 0 n) = 0 :=
ramsey_number_exists_zero 0 (by simp)

lemma ramsey_number_cons_one_of_one_le {i : ℕ} {n : fin i → ℕ} (h : ∀ k, n k ≠ 0) :
  ramsey_number (matrix.vec_cons 1 n) = 1 :=
begin
  refine ramsey_number_eq_one ⟨0, rfl⟩ _,
  rw fin.forall_fin_succ,
  simpa using h,
end

lemma ramsey_number_one_succ {i : ℕ} : ramsey_number ![1, i+1] = 1 :=
ramsey_number_cons_one_of_one_le (by simp)

lemma ramsey_number_succ_one {i : ℕ} : ramsey_number ![i+1, 1] = 1 :=
by rw [ramsey_number_pair_swap, ramsey_number_one_succ]

lemma ramsey_number_two_left {i : ℕ} : ramsey_number ![2, i] = i := by simp

@[simp] lemma ramsey_number_two_right {i : ℕ} : ramsey_number ![i, 2] = i :=
by rw [ramsey_number_pair_swap, ramsey_number_two_left]

-- if the condition `h` fails, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
lemma ramsey_number_multicolour_bound (h : ∀ k, 2 ≤ n k) :
  ramsey_number n ≤ ∑ k, ramsey_number (function.update n k (n k - 1)) + 2 - card K :=
begin
  rw ramsey_number_le_iff_fin,
  exact ramsey_fin_induct' _ _ h (λ k, ramsey_number_spec_fin _),
end

-- if the conditions `hi` or `hj` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
lemma ramsey_number_two_colour_bound_aux {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
  ramsey_number ![i, j] ≤ ramsey_number ![i - 1, j] + ramsey_number ![i, j - 1] :=
begin
  rw ramsey_number_le_iff_fin,
  refine ramsey_fin_induct_two hi hj _ _;
  exact ramsey_number_spec_fin _
end

lemma ramsey_number_two_colour_bound (i j : ℕ) (hij : i ≠ 1 ∨ j ≠ 1) :
  ramsey_number ![i, j] ≤ ramsey_number ![i - 1, j] + ramsey_number ![i, j - 1] :=
begin
  wlog h : i ≤ j,
  { refine (ramsey_number_pair_swap _ _).trans_le ((this _ _ hij.symm (le_of_not_le h)).trans _),
    rw [ramsey_number_pair_swap, add_comm, add_le_add_iff_right, ramsey_number_pair_swap] },
  rcases i with (_ | _ | _),
  { simp },
  { rcases j with (_ | _ | _),
    { simp },
    { simpa using hij },
    rw [ramsey_number_one_succ, nat.sub_self, ramsey_number_cons_zero, zero_add,
      nat.succ_sub_succ_eq_sub, nat.sub_zero, ramsey_number_one_succ] },
  have : 2 ≤ i + 2, { simp },
  exact ramsey_number_two_colour_bound_aux this (this.trans h),
end

-- a slightly odd shaped bound to make it more practical for explicit computations
lemma ramsey_number_two_colour_bound_even {i j} (Ni Nj : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
  (hNi : ramsey_number ![i - 1, j] ≤ Ni) (hNj : ramsey_number ![i, j - 1] ≤ Nj)
  (hNi' : even Ni) (hNj' : even Nj) :
  ramsey_number ![i, j] ≤ Ni + Nj - 1 :=
begin
  rw ramsey_number_le_iff_fin at ⊢ hNi hNj,
  exact ramsey_fin_induct_two_evens hi hj hNi' hNj' hNi hNj,
end

-- if the conditions `hi`, `hj` or `hk` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
lemma ramsey_number_three_colour_bound {i j k : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k) :
  ramsey_number ![i, j, k] ≤
    ramsey_number ![i - 1, j, k] + ramsey_number ![i, j - 1, k] +
      ramsey_number ![i, j, k - 1] - 1 :=
begin
  rw ramsey_number_le_iff_fin,
  refine ramsey_fin_induct_three hi hj hk _ _ _;
  exact ramsey_number_spec_fin _
end

/-- The diagonal ramsey number, defined by R(k, k). -/
def diagonal_ramsey (k : ℕ) : ℕ := ramsey_number ![k, k]
lemma diagonal_ramsey.def {k : ℕ} : diagonal_ramsey k = ramsey_number ![k, k] := rfl

@[simp] lemma diagonal_ramsey_zero : diagonal_ramsey 0 = 0 := ramsey_number_cons_zero
@[simp] lemma diagonal_ramsey_one : diagonal_ramsey 1 = 1 :=
by rw [diagonal_ramsey.def, ramsey_number_one_succ]
@[simp] lemma diagonal_ramsey_two : diagonal_ramsey 2 = 2 :=
by rw [diagonal_ramsey.def, ramsey_number_cons_two, ramsey_number_singleton]
lemma diagonal_ramsey_monotone : monotone diagonal_ramsey :=
λ n m hnm, ramsey_number.mono_two hnm hnm

lemma ramsey_number_le_choose : ∀ (i j : ℕ), ramsey_number ![i, j] ≤ (i + j - 2).choose (i - 1)
| 0 _ := by simp
| _ 0 := by { rw [ramsey_number_pair_swap, ramsey_number_cons_zero], exact zero_le' }
| 1 (j+1) := by rw [ramsey_number_one_succ, nat.choose_zero_right]
| (i+1) 1 := by rw [ramsey_number_succ_one, nat.succ_sub_succ_eq_sub, nat.choose_self]
| (i+2) (j+2) :=
  begin
    refine (ramsey_number_two_colour_bound_aux (nat.le_add_left _ _) (nat.le_add_left _ _)).trans _,
    rw [nat.add_succ_sub_one, nat.add_succ_sub_one, ←add_assoc, nat.add_sub_cancel],
    refine (add_le_add (ramsey_number_le_choose _ _) (ramsey_number_le_choose _ _)).trans _,
    rw [add_add_add_comm, nat.add_sub_cancel, ←add_assoc, nat.add_sub_cancel, add_add_add_comm,
      add_right_comm i 2, nat.choose_succ_succ (i + j + 1) i],
    refl,
  end

lemma diagonal_ramsey_le_central_binom (i : ℕ) : diagonal_ramsey i ≤ (i - 1).central_binom :=
(ramsey_number_le_choose i i).trans_eq
  (by rw [nat.central_binom_eq_two_mul_choose, nat.mul_sub_left_distrib, mul_one, two_mul])

lemma diagonal_ramsey_le_central_binom' (i : ℕ) : diagonal_ramsey i ≤ i.central_binom :=
(diagonal_ramsey_le_central_binom _).trans (central_binom_monotone (nat.sub_le _ _))

lemma ramsey_number_pair_le_two_pow {i j : ℕ} : ramsey_number ![i, j] ≤ 2 ^ (i + j - 2) :=
(ramsey_number_le_choose _ _).trans nat.choose_le_two_pow

lemma ramsey_number_pair_le_two_pow' {i j : ℕ} : ramsey_number ![i, j] ≤ 2 ^ (i + j) :=
ramsey_number_pair_le_two_pow.trans (pow_le_pow one_le_two (nat.sub_le _ _))

lemma diagonal_ramsey_le_four_pow_sub_one {i : ℕ} : diagonal_ramsey i ≤ 4 ^ (i - 1) :=
ramsey_number_pair_le_two_pow.trans_eq
  (by rw [(show 4 = 2 ^ 2, from rfl), ←pow_mul, nat.mul_sub_left_distrib, two_mul, mul_one])

lemma diagonal_ramsey_le_four_pow {i : ℕ} : diagonal_ramsey i ≤ 4 ^ i :=
diagonal_ramsey_le_four_pow_sub_one.trans (pow_le_pow (by norm_num) (nat.sub_le _ _))

/-- A good bound when i is small and j is large. For `i = 1, 2` this is equality (as long as
`j ≠ 0`), and for `i = 3` and `i = 4` it is the best possible polynomial upper bound, although
lower order improvements are available. -/
lemma ramsey_number_le_right_pow_left (i j : ℕ) : ramsey_number ![i, j] ≤ j ^ (i - 1) :=
begin
  rcases nat.eq_zero_or_pos j with rfl | hj,
  { rw [ramsey_number_pair_swap, ramsey_number_cons_zero],
    exact zero_le' },
  refine (ramsey_number_le_choose i j).trans _,
  refine (nat.choose_le_choose _ add_tsub_add_le_tsub_add_tsub).trans _,
  refine (nat.choose_add_le_pow_left _ _).trans_eq _,
  rw nat.sub_add_cancel hj,
end

/-- A simplification of `ramsey_number_le_right_pow_left` which is more convenient for asymptotic
reasoning. A good bound when `i` is small and `j` is very large. -/
lemma ramsey_number_le_right_pow_left' {i j : ℕ} : ramsey_number ![i, j] ≤ j ^ i :=
(ramsey_number_le_right_pow_left (i + 1) j).trans' $ ramsey_number.mono_two (by simp) le_rfl

end simple_graph
