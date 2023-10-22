/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import prereq.ramsey
import prereq.graph_probability
import combinatorics.simple_graph.density
import data.seq.seq

/-!
# Book algorithm

Define the book algorithm with its prerequisites.
-/
open finset real
namespace simple_graph
open_locale big_operators

variables {V K : Type*}

lemma cast_card_sdiff {α R : Type*} [add_group_with_one R] [decidable_eq α] {s t : finset α}
  (h : s ⊆ t) : ((t \ s).card : R) = t.card - s.card :=
by rw [card_sdiff h, nat.cast_sub (card_le_of_subset h)]

/-- For `χ` a labelling and vertex sets `X` `Y` and a label `k`, give the edge density of
`k`-labelled edges between `X` and `Y`. -/
def col_density [decidable_eq V] [decidable_eq K] (χ : top_edge_labelling V K) (k : K)
  (X Y : finset V) : ℝ :=
edge_density (χ.label_graph k) X Y

lemma col_density_comm [decidable_eq V] [decidable_eq K] (χ : top_edge_labelling V K) (k : K)
  (X Y : finset V) :
  col_density χ k X Y = col_density χ k Y X :=
by rw [col_density, edge_density_comm, col_density]

lemma col_density_nonneg [decidable_eq V] [decidable_eq K] {χ : top_edge_labelling V K} {k : K}
  {X Y : finset V} :
  0 ≤ col_density χ k X Y :=
rat.cast_nonneg.2 (edge_density_nonneg _ _ _)

lemma col_density_le_one [decidable_eq V] [decidable_eq K] {χ : top_edge_labelling V K} {k : K}
  {X Y : finset V} :
  col_density χ k X Y ≤ 1 :=
begin
  rw ←rat.cast_one,
  exact rat.cast_le.2 (edge_density_le_one _ _ _),
end

lemma col_density_empty_left [decidable_eq V] [decidable_eq K] {χ : top_edge_labelling V K} {k : K}
  {Y : finset V} : col_density χ k ∅ Y = 0 :=
by rw [col_density, edge_density_empty_left, rat.cast_zero]

lemma col_density_empty_right [decidable_eq V] [decidable_eq K] {χ : top_edge_labelling V K} {k : K}
  {X : finset V} : col_density χ k X ∅ = 0 :=
by rw [col_density, edge_density_empty_right, rat.cast_zero]

localized "notation `red_density` χ:1024 := simple_graph.col_density χ 0" in exponential_ramsey
localized "notation `blue_density` χ:1024 := simple_graph.col_density χ 1" in exponential_ramsey

/-- the set of neighbours of x which are connected to it by edges labelled k -/
def col_neighbors [fintype V] [decidable_eq V] [decidable_eq K] (χ : top_edge_labelling V K)
  (k : K) (x : V) : finset V :=
neighbor_finset (χ.label_graph k) x

localized "notation `red_neighbors` χ:1024 := simple_graph.col_neighbors χ 0" in exponential_ramsey
localized "notation `blue_neighbors` χ:1024 := simple_graph.col_neighbors χ 1" in exponential_ramsey

open_locale exponential_ramsey

variables [decidable_eq V]

section

variables [fintype V]

lemma mem_col_neighbors [decidable_eq K] {χ : top_edge_labelling V K} {x y : V} {k : K} :
  y ∈ col_neighbors χ k x ↔ ∃ (H : x ≠ y), χ.get x y = k :=
by rw [col_neighbors, mem_neighbor_finset, top_edge_labelling.label_graph_adj]

lemma mem_col_neighbors' [decidable_eq K] {χ : top_edge_labelling V K} {x y : V} {k : K} :
  y ∈ col_neighbors χ k x ↔ ∃ (H : y ≠ x), χ.get y x = k :=
by rw [col_neighbors, mem_neighbor_finset, adj_comm, top_edge_labelling.label_graph_adj]

lemma mem_col_neighbors_comm [decidable_eq K] {χ : top_edge_labelling V K} {x y : V} {k : K} :
  y ∈ col_neighbors χ k x ↔ x ∈ col_neighbors χ k y :=
by rw [mem_col_neighbors, mem_col_neighbors']

lemma not_mem_col_neighbors [decidable_eq K] {χ : top_edge_labelling V K} {x : V} {k : K} :
  x ∉ col_neighbors χ k x := not_mem_neighbor_finset_self _ _

end

lemma interedges_card_eq_sum {V : Type*} [decidable_eq V] [fintype V] {G : simple_graph V}
  [decidable_rel G.adj] {A B : finset V} :
  (G.interedges A B).card = ∑ x in A, (G.neighbor_finset x ∩ B).card :=
begin
  have : ∀ e ∈ G.interedges A B, prod.fst e ∈ A,
  { rintro ⟨e₁, e₂⟩ h,
    rw [interedges, rel.mk_mem_interedges_iff] at h,
    exact h.1 },
  rw card_eq_sum_card_fiberwise this,
  refine sum_congr rfl _,
  intros x hx,
  rw [interedges, rel.interedges, filter_filter],
  simp only [and_comm],
  rw [←filter_filter, filter_product_left (λ i, i = x), finset.filter_eq', if_pos hx,
    singleton_product, filter_map, card_map, inter_comm, ←filter_mem_eq_inter],
  congr' 1,
  refine filter_congr _,
  simp only [function.embedding.coe_fn_mk, mem_neighbor_finset, iff_self, implies_true_iff],
end

lemma col_density_eq_sum {K : Type*} [fintype V] [decidable_eq K] {χ : top_edge_labelling V K}
  {k : K} {A B : finset V} :
  col_density χ k A B = (∑ x in A, (col_neighbors χ k x ∩ B).card) / (A.card * B.card) :=
begin
  rw [col_density, edge_density_def, interedges_card_eq_sum],
  simp only [nat.cast_sum, rat.cast_div, rat.cast_sum, rat.cast_coe_nat, rat.cast_mul],
  refl,
end

section

variable [fintype V]

/--
Define the weight of an ordered pair for the book algorithm.
`pair_weight χ X Y x y` corresponds to `ω(x, y)` in the paper, see equation (3).
-/
noncomputable def pair_weight (χ : top_edge_labelling V (fin 2)) (X Y : finset V) (x y : V) : ℝ :=
Y.card⁻¹ *
  ((red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card -
    red_density χ X Y * (red_neighbors χ x ∩ Y).card)

/--
Define the weight of a vertex for the book algorithm.
`pair_weight χ X Y x` corresponds to `ω(x)` in the paper, see equation (4).
-/
noncomputable def weight (χ : top_edge_labelling V (fin 2)) (X Y : finset V) (x : V) : ℝ :=
∑ y in X.erase x, pair_weight χ X Y x y

end

/-- Define the function `q` from the paper, see equation (5).  -/
noncomputable def q_function (k : ℕ) (p₀ : ℝ) (h : ℕ) : ℝ :=
p₀ + ((1 + k^(- 1/4 : ℝ)) ^ h - 1) / k

lemma q_function_zero {k : ℕ} {p₀ : ℝ} : q_function k p₀ 0 = p₀ :=
by rw [q_function, pow_zero, sub_self, zero_div, add_zero]

lemma q_function_one {k : ℕ} {p₀ : ℝ} : q_function k p₀ 1 = p₀ + k ^ (- 1 / 4 : ℝ) / k :=
by rw [q_function, pow_one, add_sub_cancel']

lemma q_increasing {k h₁ h₂ : ℕ} {p₀ : ℝ} (h : h₁ ≤ h₂) :
  q_function k p₀ h₁ ≤ q_function k p₀ h₂ :=
begin
  rw [q_function, q_function, add_le_add_iff_left],
  refine div_le_div_of_le (nat.cast_nonneg _) (sub_le_sub_right (pow_le_pow _ h) _),
  rw le_add_iff_nonneg_right,
  exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _,
end

lemma q_function_weak_lower {k : ℕ} {p₀ : ℝ} {h : ℕ} :
  p₀ + h * k ^ (- 1 / 4 : ℝ) / k ≤ q_function k p₀ h :=
begin
  rw [q_function, add_le_add_iff_left],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  refine (sub_le_sub_right (one_add_mul_le_pow _ h) _).trans_eq' _,
  { exact (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _).trans' (by norm_num) },
  rw add_sub_cancel'
end

-- The bound on h here is about k / ε, which is not good enough in general so I'm not gonna bother
-- exposing it, later I show h ≤ 2 log k / ε works for suff large k, which is what's actually needed
lemma q_function_above (p₀ c : ℝ) {k : ℕ} (hk : k ≠ 0) :
  ∃ h, 1 ≤ h ∧ c ≤ q_function k p₀ h :=
begin
  refine ⟨max 1 ⌈(c - p₀) * k / k ^ (- 1 / 4 : ℝ)⌉₊, le_max_left _ _, _⟩,
  refine (q_increasing (le_max_right _ _)).trans' _,
  refine q_function_weak_lower.trans' _,
  rw [←sub_le_iff_le_add', mul_div_assoc, ←div_le_iff, div_div_eq_mul_div],
  { exact nat.le_ceil _ },
  { positivity },
end

/-- Define the height, `h(p)` from the paper. See equation (5). -/
noncomputable def height (k : ℕ) (p₀ p : ℝ) : ℕ :=
if h : k ≠ 0 then nat.find (q_function_above p₀ p h) else 1

lemma one_le_height {k : ℕ} {p₀ p : ℝ} : 1 ≤ height k p₀ p :=
begin
  rw height,
  split_ifs with h,
  { exact (nat.find_spec (q_function_above p₀ p h)).1 },
  exact le_rfl
end

/-- Define function `α_h` from the paper. We use the right half of equation (6) as the definition
for simplicity, and `α_function_eq_q_diff` gives the left half. -/
noncomputable def α_function (k : ℕ) (h : ℕ) : ℝ :=
k^(- 1/4 : ℝ) * (1 + k^(- 1/4 : ℝ)) ^ (h - 1) / k

lemma α_function_eq_q_diff {k : ℕ} {p₀ : ℝ} {h : ℕ} :
  α_function k (h + 1) = q_function k p₀ (h + 1) - q_function k p₀ h :=
begin
  rw [α_function, q_function, q_function, add_sub_add_left_eq_sub, div_sub_div_same,
    sub_sub_sub_cancel_right, pow_succ, ←sub_one_mul, add_sub_cancel', nat.add_sub_cancel]
end

variable {χ : top_edge_labelling V (fin 2)}

open top_edge_labelling

/--
the quadruple of sets X,Y,A,B that we keep track of in the book algorithm, bundled with the
properties which are needed for it
-/
structure book_config (χ : top_edge_labelling V (fin 2)) :=
  (X Y A B : finset V)
  (hXY : disjoint X Y)
  (hXA : disjoint X A)
  (hXB : disjoint X B)
  (hYA : disjoint Y A)
  (hYB : disjoint Y B)
  (hAB : disjoint A B)
  (red_A : χ.monochromatic_of A 0)
  (red_XYA : χ.monochromatic_between (X ∪ Y) A 0)
  (blue_B : χ.monochromatic_of B 1)
  (blue_XB : χ.monochromatic_between X B 1)

namespace book_config

/-- Define `p` from the paper at a given configuration. -/
def p (C : book_config χ) : ℝ := red_density χ C.X C.Y

section

variable [fintype V]

/-- Given a vertex set `X`, construct the initial configuration where `X` is as given. -/
def start (X : finset V) : book_config χ :=
begin
  refine ⟨X, Xᶜ, ∅, ∅, disjoint_compl_right, _, _, _, _, _, _, _, _, _⟩,
  all_goals { simp }
end

-- todo: this instance shouldn't need fintype; just use everything empty
instance : inhabited (book_config χ) := ⟨start ∅⟩

/-- Take a red step for the book algorithm, given `x ∈ X`. -/
def red_step_basic (C : book_config χ) (x : V) (hx : x ∈ C.X) : book_config χ :=
{ X := red_neighbors χ x ∩ C.X, Y := red_neighbors χ x ∩ C.Y, A := insert x C.A, B := C.B,
  hXY := disjoint_of_subset_left (inter_subset_right _ _) (C.hXY.inf_right' _),
  hXA :=
  begin
    rw [disjoint_insert_right, mem_inter, not_and_distrib],
    refine ⟨or.inl not_mem_col_neighbors, _⟩,
    exact disjoint_of_subset_left (inter_subset_right _ _) C.hXA,
  end,
  hXB := disjoint_of_subset_left (inter_subset_right _ _) C.hXB,
  hYA :=
  begin
    rw [disjoint_insert_right, mem_inter, not_and_distrib],
    refine ⟨or.inl not_mem_col_neighbors, _⟩,
    exact disjoint_of_subset_left (inter_subset_right _ _) C.hYA,
  end,
  hYB := disjoint_of_subset_left (inter_subset_right _ _) C.hYB,
  hAB :=
  begin
    simp only [disjoint_insert_left, C.hAB, and_true],
    exact finset.disjoint_left.1 C.hXB hx,
  end,
  red_A :=
  begin
    have : x ∉ (C.A : set V) := finset.disjoint_left.1 C.hXA hx,
    rw [coe_insert, top_edge_labelling.monochromatic_of_insert this, and_iff_right C.red_A],
    intros a ha,
    exact C.red_XYA (mem_union_left _ hx) ha _,
  end,
  red_XYA :=
  begin
    rw [←inter_distrib_left, insert_eq, top_edge_labelling.monochromatic_between_union_right,
      top_edge_labelling.monochromatic_between_singleton_right],
    split,
    { simp [mem_col_neighbors'] {contextual := tt} },
    { exact C.red_XYA.subset_left (inter_subset_right _ _) },
  end,
  blue_B := C.blue_B,
  blue_XB := C.blue_XB.subset_left (inter_subset_right _ _) }

lemma red_step_basic_X {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (red_step_basic C x hx).X = red_neighbors χ x ∩ C.X := rfl

lemma red_step_basic_Y {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (red_step_basic C x hx).Y = red_neighbors χ x ∩ C.Y := rfl

lemma red_step_basic_A {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (red_step_basic C x hx).A = insert x C.A := rfl

lemma red_step_basic_B {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (red_step_basic C x hx).B = C.B := rfl

end

section

/-- Take a big blue step for the book algorithm, given a blue book `(S, T)` contained in `X`. -/
def big_blue_step_basic (C : book_config χ) (S T : finset V) (hS : S ⊆ C.X) (hT : T ⊆ C.X)
  (hSS : χ.monochromatic_of S 1) (hST : disjoint S T) (hST' : χ.monochromatic_between S T 1) :
  book_config χ :=
{ X := T, Y := C.Y, A := C.A, B := C.B ∪ S,
  hXY := disjoint_of_subset_left hT C.hXY,
  hXA := disjoint_of_subset_left hT C.hXA,
  hXB := disjoint_union_right.2 ⟨disjoint_of_subset_left hT C.hXB, hST.symm⟩,
  hYA := C.hYA,
  hYB := disjoint_union_right.2 ⟨C.hYB, disjoint_of_subset_right hS C.hXY.symm⟩,
  hAB := disjoint_union_right.2 ⟨C.hAB, disjoint_of_subset_right hS C.hXA.symm⟩,
  red_A := C.red_A,
  red_XYA := C.red_XYA.subset_left (union_subset_union hT subset.rfl),
  blue_B :=
  begin
    rw [coe_union, top_edge_labelling.monochromatic_of_union],
    exact ⟨C.blue_B, hSS, C.blue_XB.symm.subset_right hS⟩,
  end,
  blue_XB :=
  begin
    rw [top_edge_labelling.monochromatic_between_union_right],
    exact ⟨C.blue_XB.subset_left hT, hST'.symm⟩,
  end }

variable [fintype V]

/-- Take a density boost step for the book algorithm, given `x ∈ X`. -/
def density_boost_step_basic (C : book_config χ) (x : V) (hx : x ∈ C.X) : book_config χ :=
{ X := blue_neighbors χ x ∩ C.X, Y := red_neighbors χ x ∩ C.Y, A := C.A, B := insert x C.B,
  hXY := (C.hXY.inf_left' _).inf_right' _,
  hXA := C.hXA.inf_left' _,
  hXB :=
  begin
    rw [disjoint_insert_right, mem_inter, not_and_distrib],
    exact ⟨or.inl not_mem_col_neighbors, C.hXB.inf_left' _⟩,
  end,
  hYA := C.hYA.inf_left' _,
  hYB :=
  begin
    rw [disjoint_insert_right, mem_inter, not_and_distrib],
    exact ⟨or.inl not_mem_col_neighbors, C.hYB.inf_left' _⟩,
  end,
  hAB :=
  begin
    simp only [disjoint_insert_right, C.hAB, and_true],
    exact finset.disjoint_left.1 C.hXA hx,
  end,
  red_A := C.red_A,
  red_XYA := C.red_XYA.subset_left
    (union_subset_union (inter_subset_right _ _) (inter_subset_right _ _)),
  blue_B :=
  begin
    rw [insert_eq, coe_union, monochromatic_of_union, coe_singleton],
    exact ⟨monochromatic_of_singleton, C.blue_B, C.blue_XB.subset_left (by simpa using hx)⟩,
  end,
  blue_XB :=
  begin
    rw [insert_eq, monochromatic_between_union_right,
      monochromatic_between_singleton_right],
    refine ⟨_, C.blue_XB.subset_left (inter_subset_right _ _)⟩,
    simp [mem_col_neighbors'] {contextual := tt},
  end }

lemma density_boost_step_basic_X {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (density_boost_step_basic C x hx).X = blue_neighbors χ x ∩ C.X := rfl

lemma density_boost_step_basic_Y {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (density_boost_step_basic C x hx).Y = red_neighbors χ x ∩ C.Y := rfl

lemma density_boost_step_basic_A {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (density_boost_step_basic C x hx).A = C.A := rfl

lemma density_boost_step_basic_B {C : book_config χ} {x : V} (hx : x ∈ C.X) :
  (density_boost_step_basic C x hx).B = insert x C.B := rfl

end

section

/-- Take a degree regularisation step for the book algorithm, given `U ⊆ X` for the vertices we want
to keep in `X`. -/
def degree_regularisation_step_basic (C : book_config χ) (U : finset V) (h : U ⊆ C.X) :
  book_config χ :=
{ X := U, Y := C.Y, A := C.A, B := C.B,
  hXY := C.hXY.mono_left h,
  hXA := C.hXA.mono_left h,
  hXB := C.hXB.mono_left h,
  hYA := C.hYA,
  hYB := C.hYB,
  hAB := C.hAB,
  red_A := C.red_A,
  red_XYA := C.red_XYA.subset_left (union_subset_union h subset.rfl),
  blue_B := C.blue_B,
  blue_XB := C.blue_XB.subset_left h }

variable [fintype V]

/-- Take a degree regularisation step, choosing the set of vertices as in the paper. -/
noncomputable def degree_regularisation_step (k : ℕ) (p₀ : ℝ) (C : book_config χ) :
  book_config χ :=
degree_regularisation_step_basic C
  (C.X.filter
    (λ x, (C.p - k ^ (1 / 8 : ℝ) * α_function k (height k p₀ C.p)) * C.Y.card ≤
      (red_neighbors χ x ∩ C.Y).card))
  (filter_subset _ _)

lemma degree_regularisation_step_X {k : ℕ} {p₀ : ℝ} {C : book_config χ} :
  (degree_regularisation_step k p₀ C).X =
    C.X.filter (λ x, (C.p - k ^ (1 / 8 : ℝ) * α_function k (height k p₀ C.p)) * C.Y.card ≤
      (red_neighbors χ x ∩ C.Y).card) :=
rfl

lemma degree_regularisation_step_Y {k : ℕ} {p₀ : ℝ} {C : book_config χ} :
  (degree_regularisation_step k p₀ C).Y = C.Y := rfl

lemma degree_regularisation_step_A {k : ℕ} {p₀ : ℝ} {C : book_config χ} :
  (degree_regularisation_step k p₀ C).A = C.A := rfl

lemma degree_regularisation_step_B {k : ℕ} {p₀ : ℝ} {C : book_config χ} :
  (degree_regularisation_step k p₀ C).B = C.B := rfl

lemma degree_regularisation_step_X_subset {k : ℕ} {p₀ : ℝ} {C : book_config χ} :
  (degree_regularisation_step k p₀ C).X ⊆ C.X := filter_subset _ _

end

/-- Get the set of appropriately sized blue books contained in `X`. We will take a maximal
one of these later. -/
noncomputable def useful_blue_books {V : Type*} [decidable_eq V] (χ : top_edge_labelling V (fin 2))
  (μ : ℝ) (X : finset V) :
  finset (finset V × finset V) :=
(X.powerset.product X.powerset).filter
  (λ ST, disjoint ST.1 ST.2 ∧ χ.monochromatic_of ST.1 1 ∧ χ.monochromatic_between ST.1 ST.2 1
    ∧ μ ^ ST.1.card * X.card / 2 ≤ ST.2.card)

lemma mem_useful_blue_books
  {μ : ℝ} {X : finset V} {ST : finset V × finset V} :
  ST ∈ useful_blue_books χ μ X ↔
    ST.1 ⊆ X ∧ ST.2 ⊆ X ∧ disjoint ST.1 ST.2 ∧ χ.monochromatic_of ST.1 1 ∧
      χ.monochromatic_between ST.1 ST.2 1 ∧ μ ^ ST.1.card * X.card / 2 ≤ ST.2.card :=
by rw [useful_blue_books, mem_filter, mem_product, mem_powerset, mem_powerset, and_assoc]

lemma mem_useful_blue_books' {μ : ℝ} {X S T : finset V} :
  (S, T) ∈ useful_blue_books χ μ X ↔
    S ⊆ X ∧ T ⊆ X ∧ disjoint S T ∧ χ.monochromatic_of S 1 ∧ χ.monochromatic_between S T 1
      ∧ μ ^ S.card * X.card / 2 ≤ T.card :=
mem_useful_blue_books

lemma exists_useful_blue_book (μ : ℝ) (X : finset V) :
  (useful_blue_books χ μ X).nonempty :=
begin
  use (∅, X),
  rw mem_useful_blue_books',
  simp only [empty_subset, subset.refl, disjoint_empty_left, coe_empty, monochromatic_of_empty,
    top_edge_labelling.monochromatic_between_empty_left, card_empty, pow_zero, one_mul, true_and],
  exact half_le_self (nat.cast_nonneg _),
end

lemma exists_blue_book_one_le_S [fintype V] (μ : ℝ) (X : finset V)
  (hX : ∃ x ∈ X, μ * X.card ≤ (blue_neighbors χ x ∩ X).card) :
  ∃ ST : finset V × finset V, ST ∈ useful_blue_books χ μ X ∧ 1 ≤ ST.1.card :=
begin
  obtain ⟨x, hx, hx'⟩ := hX,
  cases lt_or_le μ 0,
  { refine ⟨⟨{x}, ∅⟩, _, by simp⟩,
    rw mem_useful_blue_books',
    simp only [singleton_subset_iff, empty_subset, disjoint_singleton_left, not_mem_empty,
      not_false_iff, coe_singleton, monochromatic_of_singleton, true_and, hx, nat.cast_zero,
      top_edge_labelling.monochromatic_between_empty_right, card_singleton, pow_one, card_empty],
    refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h.le _) (by norm_num1),
    positivity },
  refine ⟨⟨{x}, blue_neighbors χ x ∩ X⟩, _, by simp⟩,
  rw mem_useful_blue_books',
  simp only [hx, singleton_subset_iff, disjoint_singleton_left, mem_inter, and_true, coe_singleton,
    monochromatic_of_singleton, card_singleton, pow_one, true_and, inter_subset_right, not_true,
    not_mem_col_neighbors, top_edge_labelling.monochromatic_between_singleton_left, and_imp,
    mem_col_neighbors, ne.def, eq_self_iff_true, not_false_iff,
    is_empty.exists_iff, forall_exists_index, implies_true_iff] {contextual := tt},
  refine hx'.trans' (half_le_self _),
  positivity
end

lemma exists_maximal_blue_book_aux (χ : top_edge_labelling V (fin 2))
  (μ : ℝ) (X : finset V) :
  ∃ (ST ∈ useful_blue_books χ μ X), ∀ (ST' ∈ useful_blue_books χ μ X),
    finset.card (prod.fst ST') ≤ finset.card (prod.fst ST) :=
finset.exists_max_image (useful_blue_books χ μ X) (λ ST, ST.1.card) (exists_useful_blue_book _ _)

/-- Get a maximal book contained in `X`. -/
noncomputable def get_book (χ : top_edge_labelling V (fin 2)) (μ : ℝ) (X : finset V) :
  finset V × finset V :=
(exists_maximal_blue_book_aux χ μ X).some

lemma get_book_mem (μ : ℝ) (X : finset V) : get_book χ μ X ∈ useful_blue_books χ μ X :=
(exists_maximal_blue_book_aux χ μ X).some_spec.some

lemma get_book_fst_subset {μ : ℝ} {X : finset V} : (get_book χ μ X).1 ⊆ X :=
(mem_useful_blue_books.1 (get_book_mem μ X)).1

lemma get_book_snd_subset {μ : ℝ} {X : finset V} : (get_book χ μ X).2 ⊆ X :=
(mem_useful_blue_books.1 (get_book_mem μ X)).2.1

lemma get_book_disjoints {μ : ℝ} {X : finset V} : disjoint (get_book χ μ X).1 (get_book χ μ X).2 :=
(mem_useful_blue_books.1 (get_book_mem μ X)).2.2.1

lemma get_book_blue_fst {μ : ℝ} {X : finset V} : χ.monochromatic_of (get_book χ μ X).1 1 :=
(mem_useful_blue_books.1 (get_book_mem μ X)).2.2.2.1

lemma get_book_blue_fst_snd {μ : ℝ} {X : finset V} :
  χ.monochromatic_between (get_book χ μ X).1 (get_book χ μ X).2 1 :=
(mem_useful_blue_books.1 (get_book_mem μ X)).2.2.2.2.1

lemma get_book_relative_card {μ : ℝ} {X : finset V} :
  μ ^ (get_book χ μ X).1.card * X.card / 2 ≤ (get_book χ μ X).2.card :=
(mem_useful_blue_books.1 (get_book_mem μ X)).2.2.2.2.2

lemma get_book_max {μ : ℝ} {X : finset V} (S T : finset V)
  (hST : (S, T) ∈ useful_blue_books χ μ X) : S.card ≤ (get_book χ μ X).1.card :=
(exists_maximal_blue_book_aux χ μ X).some_spec.some_spec (S, T) hST

section

variable [fintype V]

lemma one_le_card_get_book_fst {μ : ℝ} {X : finset V}
  (hX : ∃ x ∈ X, μ * X.card ≤ (blue_neighbors χ x ∩ X).card) :
  1 ≤ (get_book χ μ X).1.card :=
begin
  obtain ⟨⟨S, T⟩, hST, hS⟩ := exists_blue_book_one_le_S _ _ hX,
  exact hS.trans (get_book_max _ _ hST),
end

lemma get_book_snd_card_le_X {μ : ℝ} {X : finset V}
  (hX : ∃ x ∈ X, μ * X.card ≤ (blue_neighbors χ x ∩ X).card) :
  (get_book χ μ X).2.card + 1 ≤ X.card :=
begin
  refine (add_le_add_left (one_le_card_get_book_fst hX) _).trans _,
  rw [add_comm, ←card_disjoint_union],
  { exact card_le_of_subset (union_subset get_book_fst_subset get_book_snd_subset) },
  exact get_book_disjoints
end

/-- The number of vertices with a large blue neighbourhood. -/
noncomputable def num_big_blues (μ : ℝ) (C : book_config χ) : ℕ :=
  (C.X.filter (λ x, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card)).card

lemma get_book_condition {μ : ℝ} {k l : ℕ} {C : book_config χ}
  (hk : k ≠ 0) (hl : l ≠ 0)
  (hX : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ num_big_blues μ C) :
  ∃ x ∈ C.X, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card :=
begin
  rw [←filter_nonempty_iff, ←card_pos],
  refine hX.trans_lt' _,
  rw ramsey_number_pos,
  rw fin.forall_fin_two,
  simp only [matrix.cons_val_zero, ne.def, matrix.cons_val_one, matrix.head_cons, nat.ceil_eq_zero,
    not_le, hk, not_false_iff, true_and],
  positivity,
end

end

/-- Perform a big blue step, picking an appropriate blue book. -/
noncomputable def big_blue_step (μ : ℝ) (C : book_config χ) : book_config χ :=
big_blue_step_basic C (get_book χ μ C.X).1 (get_book χ μ C.X).2 get_book_fst_subset
  get_book_snd_subset get_book_blue_fst get_book_disjoints get_book_blue_fst_snd

lemma big_blue_step_X {μ : ℝ} {C : book_config χ} :
  (big_blue_step μ C).X = (get_book χ μ C.X).2 := rfl

lemma big_blue_step_Y {μ : ℝ} {C : book_config χ} :
  (big_blue_step μ C).Y = C.Y := rfl

lemma big_blue_step_A {μ : ℝ} {C : book_config χ} :
  (big_blue_step μ C).A = C.A := rfl

lemma big_blue_step_B {μ : ℝ} {C : book_config χ} :
  (big_blue_step μ C).B = C.B ∪ (get_book χ μ C.X).1 := rfl

section

variable [fintype V]

/-- The set of viable central vertices. -/
noncomputable def central_vertices (μ : ℝ) (C : book_config χ) : finset V :=
C.X.filter (λ x, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card)

lemma exists_central_vertex (μ : ℝ) (C : book_config χ)
  (hX : ∃ x ∈ C.X, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card) :
  ∃ x ∈ central_vertices μ C, ∀ y ∈ central_vertices μ C, weight χ C.X C.Y y ≤ weight χ C.X C.Y x :=
exists_max_image _ _ (by rwa [central_vertices, filter_nonempty_iff])

/-- Get the central vertex as in step 3. -/
noncomputable def get_central_vertex (μ : ℝ) (C : book_config χ)
  (hX : ∃ x ∈ C.X, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card) : V :=
(exists_central_vertex μ C hX).some

lemma get_central_vertex_mem (μ : ℝ) (C : book_config χ)
  (hX : ∃ x ∈ C.X, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card) :
  get_central_vertex μ C hX ∈ central_vertices μ C :=
(exists_central_vertex μ C hX).some_spec.some

lemma get_central_vertex_mem_X (μ : ℝ) (C : book_config χ)
  (hX : ∃ x ∈ C.X, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card) :
  get_central_vertex μ C hX ∈ C.X :=
mem_of_mem_filter _ (get_central_vertex_mem _ _ _)

lemma get_central_vertex_max (μ : ℝ) (C : book_config χ)
  (hX : ∃ x ∈ C.X, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card)
  (y : V) (hy : y ∈ central_vertices μ C) :
  weight χ C.X C.Y y ≤ weight χ C.X C.Y (get_central_vertex μ C hX) :=
(exists_central_vertex μ C hX).some_spec.some_spec _ hy

lemma get_central_vertex_condition {μ : ℝ} {k l : ℕ} (C : book_config χ)
  (h : ¬ (C.X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨ C.p ≤ 1 / k))
  (h' : ¬ ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ num_big_blues μ C) :
  ∃ x ∈ C.X, ↑(blue_neighbors χ x ∩ C.X).card ≤ μ * C.X.card :=
begin
  rw [not_or_distrib, not_le] at h,
  rw not_le at h',
  rw [←filter_nonempty_iff, ←card_pos],
  simp only [←not_lt],
  rw [filter_not, card_sdiff (filter_subset _ _)],
  refine nat.sub_pos_of_lt (h.1.trans_le' _),
  refine ((card_le_of_subset _).trans_lt h').le.trans _,
  { exact monotone_filter_right _ (λ y hy, hy.le) },
  refine ramsey_number.mono_two le_rfl (nat.ceil_mono _),
  cases l,
  { rw [nat.cast_zero, zero_rpow, zero_rpow];
    norm_num1 },
  refine rpow_le_rpow_of_exponent_le _ (by norm_num1),
  simp,
end

end

end book_config

variable [fintype V]

/-- The book algorithm as an infinite sequence which is eventually constantly nothing. -/
noncomputable def algorithm_option (μ : ℝ) (k l : ℕ) (ini : book_config χ) :
    ℕ → option (book_config χ)
| 0 := some ini
| (i+1) :=
    match algorithm_option i with
    | none := none
    | some C :=
        if h : C.X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨ C.p ≤ 1 / k
          then none
          else some $
        if even i
          then C.degree_regularisation_step k ini.p
          else
        if h' : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ
          then C.big_blue_step μ
          else
        let x := C.get_central_vertex μ (C.get_central_vertex_condition h h') in
        if C.p - α_function k (height k ini.p C.p) ≤
            red_density χ (red_neighbors χ x ∩ C.X) (red_neighbors χ x ∩ C.Y)
          then C.red_step_basic x (C.get_central_vertex_mem_X _ _)
          else C.density_boost_step_basic x (C.get_central_vertex_mem_X _ _)
    end

variables {μ : ℝ} {k l : ℕ} {ini : book_config χ}

lemma algorithm_option_stays_none {i : ℕ} (hi : algorithm_option μ k l ini i = none) :
  algorithm_option μ k l ini (i + 1) = none :=
begin
  rw [algorithm_option, hi],
  refl,
end

lemma algorithm_option_is_some_of {i : ℕ} (hi : ∃ C, algorithm_option μ k l ini (i + 1) = some C) :
  ∃ C, algorithm_option μ k l ini i = some C :=
begin
  contrapose! hi,
  simp only [ne.def, ←option.mem_def, ←option.eq_none_iff_forall_not_mem] at hi ⊢,
  exact algorithm_option_stays_none hi
end

lemma algorithm_option_X_weak_bound {i : ℕ} (C : book_config χ)
  (hk : k ≠ 0) (hl : l ≠ 0) (hC : algorithm_option μ k l ini i = some C) :
  C.X.card + i / 2 ≤ ini.X.card :=
begin
  induction i with i ih generalizing C,
  { rw [nat.zero_div, add_zero],
    simp only [algorithm_option] at hC,
    rw ←hC },
  obtain ⟨C', hC'⟩ := algorithm_option_is_some_of ⟨C, hC⟩,
  rw [algorithm_option, hC', algorithm_option._match_1] at hC,
  by_cases h₁ : C'.X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨ C'.p ≤ 1 / k,
  { simpa only [dif_pos h₁] using hC },
  rw dif_neg h₁ at hC,
  by_cases h₂ : even i,
  { simp only [if_pos h₂] at hC,
    rw even_iff_exists_bit0 at h₂,
    obtain ⟨i, rfl⟩ := h₂,
    rw [nat.succ_eq_add_one, ←bit1, nat.bit1_div_two, ←hC],
    rw nat.bit0_div_two at ih,
    exact (ih _ hC').trans' (add_le_add_right (card_le_of_subset (filter_subset _ _)) _) },
  rw if_neg h₂ at hC,
  rw [←nat.odd_iff_not_even, odd] at h₂,
  obtain ⟨i, rfl⟩ := h₂,
  rw [nat.succ_eq_add_one, add_assoc, ←two_mul, ←mul_add, ←bit0_eq_two_mul, nat.bit0_div_two],
  specialize ih _ hC',
  rw [←bit0_eq_two_mul, ←bit1, nat.bit1_div_two] at ih,
  refine ih.trans' _,
  rw [←add_assoc, add_right_comm, add_le_add_iff_right],
  split_ifs at hC with h₂ h₃ h₄,
  { rw [←hC],
    refine book_config.get_book_snd_card_le_X _,
    exact book_config.get_book_condition hk hl h₂ },
  { let x := C'.get_central_vertex μ (C'.get_central_vertex_condition h₁ h₂),
    rw [←hC],
    have : red_neighbors χ x ∩ C'.X ⊆ C'.X.erase x,
    { rw subset_erase,
      refine ⟨inter_subset_right _ _, _⟩,
      simp [not_mem_col_neighbors] },
    refine (add_le_add_right (card_le_of_subset this) _).trans _,
    rw card_erase_add_one,
    exact book_config.get_central_vertex_mem_X _ _ _ },
  { let x := C'.get_central_vertex μ (C'.get_central_vertex_condition h₁ h₂),
    rw [←hC],
    have : blue_neighbors χ x ∩ C'.X ⊆ C'.X.erase x,
    { rw subset_erase,
      refine ⟨inter_subset_right _ _, _⟩,
      simp [not_mem_col_neighbors] },
    refine (add_le_add_right (card_le_of_subset this) _).trans _,
    rw card_erase_add_one,
    exact book_config.get_central_vertex_mem_X _ _ _ },
end

lemma algorithm_option_terminates (μ : ℝ) (ini : book_config χ) (hk : k ≠ 0) (hl : l ≠ 0) :
  ∃ i, algorithm_option μ k l ini (i + 1) = none :=
begin
  refine ⟨bit0 (ini.X.card + 1), _⟩,
  rw option.eq_none_iff_forall_not_mem,
  intros C hC,
  rw option.mem_def at hC,
  have := algorithm_option_X_weak_bound C hk hl hC,
  rw [←bit1, nat.bit1_div_two] at this,
  linarith only [this],
end

/-- The index of the final step. Also the number of steps the algorithm takes.
The previous two sentences may have an off-by-one error.  -/
noncomputable def final_step (μ : ℝ) (k l : ℕ) (ini : book_config χ) : ℕ :=
Inf {i | algorithm_option μ k l ini (i + 1) = none}

/--
The book algorithm. `algorithm μ k l ini i` is the state of the algorithm after the `i`th step,
when initialised with `μ`, `k, l` and initial configuration `ini`.

If we are *after* the termination has applied, this just gives `ini`. That is, this is the correct
definition of the book algorithm *as long as* `i ≤ final_step μ k l ini`, in other words it's
correct as long as the book algorithm hasn't finished.
-/
noncomputable def algorithm (μ : ℝ) (k l : ℕ) (ini : book_config χ) (i : ℕ) : book_config χ :=
(algorithm_option μ k l ini i).get_or_else ini

/-- The configuration at the end of the book algorithm. -/
noncomputable def end_state (μ : ℝ) (k l : ℕ) (ini : book_config χ) : book_config χ :=
  algorithm μ k l ini (final_step μ k l ini)

variables {i : ℕ}

lemma final_step_is_none (hk : k ≠ 0) (hl : l ≠ 0) :
  algorithm_option μ k l ini (final_step μ k l ini + 1) = none :=
begin
  have : {i | algorithm_option μ k l ini (i + 1) = none}.nonempty,
  { obtain ⟨i, hi⟩ := algorithm_option_terminates μ ini hk hl,
    exact ⟨i, hi⟩ },
  exact Inf_mem this,
end

lemma algorithm_zero : algorithm μ k l ini 0 = ini :=
begin
  rw [←option.some_inj, algorithm, algorithm_option],
  refl
end

lemma some_algorithm_of_final_step_le
  (hi : i ≤ final_step μ k l ini) :
  some (algorithm μ k l ini i) = algorithm_option μ k l ini i :=
begin
  cases i,
  { rw algorithm_zero,
    refl },
  rw nat.succ_eq_add_one at *,
  rw [algorithm, option.get_or_else_of_ne_none],
  intro hi',
  have : i ∈ {i | algorithm_option μ k l ini (i + 1) = none} := hi',
  have : final_step μ k l ini ≤ i := nat.Inf_le this,
  linarith
end

lemma condition_fails_at_end (hk : k ≠ 0) (hl : l ≠ 0) :
  (end_state μ k l ini).X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨
    (end_state μ k l ini).p ≤ 1 / k :=
begin
  by_contra h,
  have h' : some (end_state μ k l ini) =
    algorithm_option μ k l ini (final_step μ k l ini),
  { exact some_algorithm_of_final_step_le le_rfl },
  have : algorithm_option μ k l ini _ = none := final_step_is_none hk hl,
  rw [algorithm_option, ←h', algorithm_option._match_1] at this,
  simpa only [dif_neg h] using this,
end

lemma succeed_of_final_step_le' (hi : i < final_step μ k l ini) :
  ¬ ((algorithm μ k l ini i).X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨
    (algorithm μ k l ini i).p ≤ 1 / k) :=
begin
  intro h'',
  have h : some (algorithm μ k l ini i) = algorithm_option μ k l ini i,
  { exact some_algorithm_of_final_step_le hi.le },
  have h' : some (algorithm μ k l ini (i + 1)) = algorithm_option μ k l ini (i + 1),
  { exact some_algorithm_of_final_step_le hi },
  rw [algorithm_option, ←h, algorithm_option._match_1, dif_pos h''] at h',
  simpa only using h',
end

lemma ramsey_number_lt_of_lt_final_step (hi : i < final_step μ k l ini) :
  ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] < (algorithm μ k l ini i).X.card :=
begin
  have := succeed_of_final_step_le' hi,
  rw [not_or_distrib, not_le] at this,
  exact this.1
end

lemma one_div_k_lt_p_of_lt_final_step (hi : i < final_step μ k l ini) :
  1 / (k : ℝ) < (algorithm μ k l ini i).p :=
begin
  have := succeed_of_final_step_le' hi,
  rw [not_or_distrib, not_le, not_le] at this,
  exact this.2
end

lemma algorithm_succ (hi : i < final_step μ k l ini) :
  algorithm μ k l ini (i + 1) =
  let C := algorithm μ k l ini i in
  if even i
    then C.degree_regularisation_step k ini.p
    else
  if h' : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ
    then C.big_blue_step μ
    else
  let x := C.get_central_vertex μ
            (C.get_central_vertex_condition (succeed_of_final_step_le' hi) h') in
  if C.p - α_function k (height k ini.p C.p) ≤
      red_density χ (red_neighbors χ x ∩ C.X) (red_neighbors χ x ∩ C.Y)
    then C.red_step_basic x (C.get_central_vertex_mem_X _ _)
    else C.density_boost_step_basic x (C.get_central_vertex_mem_X _ _) :=
begin
  have : some (algorithm μ k l ini i) = algorithm_option μ k l ini i,
  { exact some_algorithm_of_final_step_le hi.le },
  rw [←option.some_inj, some_algorithm_of_final_step_le hi, algorithm_option, ←this,
    algorithm_option._match_1, dif_neg (succeed_of_final_step_le' hi)],
end

/-- The set of degree regularisation steps. Note this is indexed differently than the paper. -/
noncomputable def degree_steps (μ : ℝ) (k l : ℕ) (ini : book_config χ) : finset ℕ :=
(range (final_step μ k l ini)).filter even

/-- The set of big blue steps. Note this is indexed differently than the paper. -/
noncomputable def big_blue_steps (μ : ℝ) (k l : ℕ) (ini : book_config χ) : finset ℕ :=
(range (final_step μ k l ini)).filter
  (λ i, ¬ even i ∧ ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤
    (algorithm μ k l ini i).num_big_blues μ)

/-- The set of red or density steps. Note this is indexed differently than the paper. -/
noncomputable def red_or_density_steps (μ : ℝ) (k l : ℕ) (ini : book_config χ) : finset ℕ :=
(range (final_step μ k l ini)).filter
  (λ i, ¬ even i ∧
    (algorithm μ k l ini i).num_big_blues μ < ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊])

lemma degree_steps_disjoint_big_blue_steps_union_red_or_density_steps :
  disjoint (degree_steps μ k l ini) (big_blue_steps μ k l ini ∪ red_or_density_steps μ k l ini) :=
begin
  rw [big_blue_steps, red_or_density_steps, ←filter_or, degree_steps, disjoint_filter],
  intros i hi,
  rw [←and_or_distrib_left, not_and', not_not],
  exact function.const _
end

lemma big_blue_steps_disjoint_red_or_density_steps :
  disjoint (big_blue_steps μ k l ini) (red_or_density_steps μ k l ini) :=
begin
  rw [big_blue_steps, red_or_density_steps, disjoint_filter],
  rintro x hx ⟨hx₁, hx₂⟩,
  rw [not_and, not_lt],
  intro,
  exact hx₂
end

lemma of_mem_red_or_density_steps₁ {i : ℕ}
  (hi : i ∈ red_or_density_steps μ k l ini) :
 ¬ ((algorithm μ k l ini i).X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] ∨
    (algorithm μ k l ini i).p ≤ 1 / k) :=
begin
  rw [red_or_density_steps, mem_filter, mem_range] at hi,
  exact succeed_of_final_step_le' hi.1,
end

lemma of_mem_red_or_density_steps₂ {i : ℕ} (hi : i ∈ red_or_density_steps μ k l ini) :
  ¬ ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ (algorithm μ k l ini i).num_big_blues μ :=
begin
  rw [red_or_density_steps, mem_filter, ←not_le] at hi,
  exact hi.2.2,
end

/-- The choice of `x` in a red or density step. -/
noncomputable def get_x (hi : i ∈ red_or_density_steps μ k l ini) : V :=
(algorithm μ k l ini i).get_central_vertex μ
  ((algorithm μ k l ini i).get_central_vertex_condition
    (of_mem_red_or_density_steps₁ hi) (of_mem_red_or_density_steps₂ hi))

lemma get_x_mem_central_vertices (i : ℕ) (hi : i ∈ red_or_density_steps μ k l ini) :
  get_x hi ∈ (algorithm μ k l ini i).central_vertices μ :=
(algorithm μ k l ini i).get_central_vertex_mem _ _

/-- The set of red steps. -/
noncomputable def red_steps (μ : ℝ) (k l : ℕ) (ini : book_config χ) : finset ℕ :=
finset.image coe $ (red_or_density_steps μ k l ini).attach.filter $
  λ i, let x := get_x i.prop,
           C := algorithm μ k l ini i in
    C.p - α_function k (height k ini.p C.p) ≤
      red_density χ (red_neighbors χ x ∩ C.X) (red_neighbors χ x ∩ C.Y)

/-- The set of density boost steps. -/
noncomputable def density_steps (μ : ℝ) (k l : ℕ) (ini : book_config χ) : finset ℕ :=
finset.image coe $ (red_or_density_steps μ k l ini).attach.filter $
  λ i, let x := get_x i.prop,
           C := algorithm μ k l ini i in
    red_density χ (red_neighbors χ x ∩ C.X) (red_neighbors χ x ∩ C.Y) <
      C.p - α_function k (height k ini.p C.p)

lemma red_steps_subset_red_or_density_steps :
  red_steps μ k l ini ⊆ red_or_density_steps μ k l ini :=
begin
  intros i hi,
  rw [red_steps] at hi,
  simp only [mem_image, exists_prop, mem_filter, mem_attach, subtype.exists, exists_eq_right,
    true_and, exists_eq_right, exists_and_distrib_right, subtype.coe_mk] at hi,
  obtain ⟨hi, -⟩ := hi,
  exact hi
end

lemma density_steps_subset_red_or_density_steps :
  density_steps μ k l ini ⊆ red_or_density_steps μ k l ini :=
begin
  intros i hi,
  rw [density_steps] at hi,
  simp only [mem_image, exists_prop, mem_filter, mem_attach, subtype.exists, exists_eq_right,
    true_and, exists_eq_right, exists_and_distrib_right, subtype.coe_mk] at hi,
  obtain ⟨hi, -⟩ := hi,
  exact hi
end

lemma red_steps_union_density_steps :
  red_steps μ k l ini ∪ density_steps μ k l ini = red_or_density_steps μ k l ini :=
begin
  refine subset.antisymm
    (union_subset red_steps_subset_red_or_density_steps density_steps_subset_red_or_density_steps)
    _,
  rw [red_steps, density_steps, ←image_union, ←filter_or],
  intros i hi,
  simp only [mem_image, subtype.exists, subtype.coe_mk, exists_prop, mem_filter, mem_attach,
    true_and, exists_eq_right, exists_and_distrib_right],
  refine ⟨hi, _⟩,
  exact le_or_lt _ _
end

lemma red_steps_disjoint_density_steps : disjoint (red_steps μ k l ini) (density_steps μ k l ini) :=
begin
  rw [red_steps, density_steps, disjoint_image subtype.coe_injective, disjoint_filter],
  intros x hx,
  simp,
end

lemma degree_regularisation_applied {i : ℕ} (hi : i ∈ degree_steps μ k l ini) :
  algorithm μ k l ini (i + 1) = (algorithm μ k l ini i).degree_regularisation_step k ini.p :=
begin
  rw [degree_steps, mem_filter, mem_range] at hi,
  rw [algorithm_succ hi.1],
  exact if_pos hi.2,
end

lemma big_blue_applied {i : ℕ} (hi : i ∈ big_blue_steps μ k l ini) :
  algorithm μ k l ini (i + 1) = (algorithm μ k l ini i).big_blue_step μ :=
begin
  rw [big_blue_steps, mem_filter, mem_range] at hi,
  rw [algorithm_succ hi.1],
  dsimp,
  rw [if_neg hi.2.1, dif_pos hi.2.2],
end

lemma red_applied {i : ℕ} (hi : i ∈ red_steps μ k l ini) :
  algorithm μ k l ini (i + 1) = (algorithm μ k l ini i).red_step_basic
      (get_x (red_steps_subset_red_or_density_steps hi))
      (book_config.get_central_vertex_mem_X _ _ _) :=
begin
  rw [red_steps, mem_image] at hi,
  simp only [subtype.coe_mk, mem_filter, mem_attach, true_and, exists_prop,
    subtype.exists, exists_and_distrib_right, exists_eq_right] at hi,
  obtain ⟨hi', hi''⟩ := hi,
  rw [red_or_density_steps, mem_filter, ←not_le, mem_range] at hi',
  rw [algorithm_succ hi'.1],
  dsimp,
  rw [if_neg hi'.2.1, dif_neg hi'.2.2, if_pos],
  { refl },
  { exact hi'' }
end

lemma density_applied {i : ℕ} (hi : i ∈ density_steps μ k l ini) :
  algorithm μ k l ini (i + 1) = (algorithm μ k l ini i).density_boost_step_basic
      (get_x (density_steps_subset_red_or_density_steps hi))
      (book_config.get_central_vertex_mem_X _ _ _) :=
begin
  rw [density_steps, mem_image] at hi,
  simp only [subtype.coe_mk, mem_filter, mem_attach, true_and, exists_prop,
    subtype.exists, exists_and_distrib_right, exists_eq_right] at hi,
  obtain ⟨hi', hi''⟩ := hi,
  rw [red_or_density_steps, mem_filter, ←not_le, mem_range] at hi',
  rw [algorithm_succ hi'.1],
  dsimp,
  rw [if_neg hi'.2.1, dif_neg hi'.2.2, if_neg],
  { refl },
  { rwa not_le }
end

lemma union_partial_steps :
  red_or_density_steps μ k l ini ∪ big_blue_steps μ k l ini ∪ degree_steps μ k l ini =
    range (final_step μ k l ini) :=
begin
  rw [red_or_density_steps, big_blue_steps, ←filter_or, degree_steps, ←filter_or],
  refine filter_true_of_mem _,
  intros i hi,
  rw [←and_or_distrib_left, and_iff_left],
  { exact em' _ },
  exact lt_or_le _ _,
end

lemma union_steps :
  red_steps μ k l ini ∪ big_blue_steps μ k l ini ∪ density_steps μ k l ini ∪ degree_steps μ k l ini
    = range (final_step μ k l ini) :=
by rw [union_right_comm (red_steps _ _ _ _), red_steps_union_density_steps,
  union_partial_steps]

lemma filter_even_thing {n : ℕ} :
  ((range n).filter even).card ≤ ((range n).filter (λ i, ¬ even i)).card + 1 :=
begin
  have : ((range n).filter even).image nat.succ ⊆ (range (n + 1)).filter (λ i, ¬ even i),
  { simp only [finset.subset_iff, mem_filter, mem_image, and_imp, exists_prop, and_assoc,
      mem_range, forall_exists_index, nat.succ_eq_add_one],
    rintro _ y hy hy' rfl,
    simp [hy, hy'] with parity_simps },
  rw ←finset.card_image_of_injective _ nat.succ_injective,
  refine (card_le_of_subset this).trans _,
  rw [range_succ, filter_insert],
  split_ifs,
  { exact nat.le_succ _ },
  exact card_insert_le _ _
end

lemma num_degree_steps_le_add :
  (degree_steps μ k l ini).card ≤ (red_steps μ k l ini).card +
    (big_blue_steps μ k l ini).card + (density_steps μ k l ini).card + 1 :=
begin
  have : big_blue_steps μ k l ini ∪ red_or_density_steps μ k l ini =
    (range (final_step μ k l ini)).filter (λ i, ¬ even i),
  { rw [big_blue_steps, red_or_density_steps, ←filter_or],
    refine filter_congr _,
    intros i hi,
    rw [←and_or_distrib_left, ←not_le, and_iff_left],
    exact em _ },
  rw [add_right_comm _ _ (finset.card _), ←card_disjoint_union red_steps_disjoint_density_steps,
    red_steps_union_density_steps, add_comm _ (finset.card _),
    ←card_disjoint_union big_blue_steps_disjoint_red_or_density_steps, this, degree_steps],
  apply filter_even_thing
end

lemma cases_of_lt_final_step {i : ℕ} (hi : i < final_step μ k l ini) :
  i ∈ red_steps μ k l ini ∨ i ∈ big_blue_steps μ k l ini ∨ i ∈ density_steps μ k l ini ∨
    i ∈ degree_steps μ k l ini :=
by rwa [←mem_range, ←union_steps, mem_union, mem_union, mem_union, or_assoc, or_assoc] at hi

-- (7)
lemma X_subset {i : ℕ} (hi : i < final_step μ k l ini) :
  (algorithm μ k l ini (i+1)).X ⊆ (algorithm μ k l ini i).X :=
begin
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi'),
  { rw [red_applied hi', book_config.red_step_basic_X],
    exact inter_subset_right _ _ },
  { rw [big_blue_applied hi', book_config.big_blue_step_X],
    exact book_config.get_book_snd_subset },
  { rw [density_applied hi', book_config.density_boost_step_basic_X],
    exact inter_subset_right _ _ },
  { rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_X],
    exact book_config.degree_regularisation_step_X_subset },
end

-- (7)
lemma Y_subset {i : ℕ} (hi : i < final_step μ k l ini) :
  (algorithm μ k l ini (i+1)).Y ⊆ (algorithm μ k l ini i).Y :=
begin
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi'),
  { rw [red_applied hi', book_config.red_step_basic_Y],
    exact inter_subset_right _ _ },
  { rw [big_blue_applied hi', book_config.big_blue_step_Y],
    refl },
  { rw [density_applied hi', book_config.density_boost_step_basic_Y],
    exact inter_subset_right _ _ },
  { rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_Y],
    refl },
end

lemma A_subset {i : ℕ} (hi : i < final_step μ k l ini) :
  (algorithm μ k l ini i).A ⊆ (algorithm μ k l ini (i+1)).A :=
begin
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi'),
  { rw [red_applied hi', book_config.red_step_basic_A],
    exact subset_insert _ _ },
  { rw [big_blue_applied hi', book_config.big_blue_step_A],
    refl },
  { rw [density_applied hi', book_config.density_boost_step_basic_A],
    refl },
  { rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_A],
    refl },
end

lemma B_subset {i : ℕ} (hi : i < final_step μ k l ini) :
  (algorithm μ k l ini i).B ⊆ (algorithm μ k l ini (i+1)).B :=
begin
  rcases cases_of_lt_final_step hi with (hi' | hi' | hi' | hi'),
  { rw [red_applied hi', book_config.red_step_basic_B],
    refl },
  { rw [big_blue_applied hi', book_config.big_blue_step_B],
    exact subset_union_left _ _ },
  { rw [density_applied hi', book_config.density_boost_step_basic_B],
    exact subset_insert _ _ },
  { rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_B],
    refl },
end

/-- Define `β` from the paper. -/
noncomputable def blue_X_ratio (μ : ℝ) (k l : ℕ) (ini : book_config χ) (i : ℕ) : ℝ :=
if h : i ∈ red_or_density_steps μ k l ini
  then
    (blue_neighbors χ (get_x h) ∩ (algorithm μ k l ini i).X).card
      / (algorithm μ k l ini i).X.card
  else 0

lemma blue_X_ratio_eq (hi : i ∈ red_or_density_steps μ k l ini) :
  blue_X_ratio μ k l ini i = (blue_neighbors χ (get_x hi) ∩ (algorithm μ k l ini i).X).card
      / (algorithm μ k l ini i).X.card :=
dif_pos hi

-- (8)
lemma blue_X_ratio_prop (hi : i ∈ red_or_density_steps μ k l ini) :
  blue_X_ratio μ k l ini i * (algorithm μ k l ini i).X.card =
    (blue_neighbors χ (get_x hi) ∩ (algorithm μ k l ini i).X).card :=
begin
  cases finset.eq_empty_or_nonempty (algorithm μ k l ini i).X with hX hX,
  { rw [hX, inter_empty, card_empty, nat.cast_zero, mul_zero] },
  rw [blue_X_ratio, dif_pos hi, div_mul_cancel],
  rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
end

lemma blue_X_ratio_nonneg : 0 ≤ blue_X_ratio μ k l ini i :=
by { rw blue_X_ratio, split_ifs; positivity }

lemma blue_X_ratio_le_mu (hi : i ∈ red_or_density_steps μ k l ini) :
  blue_X_ratio μ k l ini i ≤ μ :=
begin
  rw [blue_X_ratio_eq hi],
  have := get_x_mem_central_vertices i hi,
  rw [book_config.central_vertices, mem_filter] at this,
  rw div_le_iff,
  { exact this.2 },
  rw [red_or_density_steps, mem_filter, mem_range] at hi,
  rw [nat.cast_pos],
  refine (ramsey_number_lt_of_lt_final_step hi.1).trans_le' _,
  exact nat.zero_le _
end

end simple_graph
