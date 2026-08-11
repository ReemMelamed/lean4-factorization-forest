/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Project.GreensRelations.Order

/-!
# The Factorization Forest Theorem — Basic Definitions

This file defines the core structures needed to state and prove the
Factorization Forest Theorem (also known as Simon's Theorem).

## Main Definitions

* `MultiplicativeLabeling S α` — a function `σ : α → α → S` satisfying the
  multiplicativity property `σ x y * σ y z = σ x z` for all `x < y < z`.
* `Split α h` — a rank function from `α` into `Fin h`.
* `SplitRelation s x y` — the relation identifying pairs that share the same
  maximal rank value under the split `s`, with all intermediate elements
  having at most that rank.
* `IsNormalized s` — the split assigns the maximum rank to the minimum element.
* `IsRamsey L s` — a split is Ramsey for a labeling if all equivalence
  classes of size ≥ 3 evaluate to the same idempotent.
* `wordLabeling eval hmul u` — the multiplicative labeling induced by a word
  `u` and an evaluation function `eval`.
* `FactorizationTree A` — an inductive type for factorization trees (leaves,
  binary nodes, and n-ary nodes).
* `FactorizationTree.word` / `FactorizationTree.height` — accessors.
* `IsRamseyTree eval t` — a predicate stating that a factorization tree is
  well-formed and all n-ary nodes evaluate to the same idempotent.
* `list_to_nary` — converts a list of children into the right tree node.
* `OpenIntervalType xs i` — elements of `α` strictly between `xs[i]`
  and `xs[i+1]`.
* `nD D` — the number of H-class elements in a D-class that are related to
  an idempotent; returns 1 for non-regular D-classes.
* `jUp a` — the upward J-class closure of `a`.
* `labelingIn σ U` — all pairs `(x, y)` with `x < y` map into `U` under `σ`.
* `labeling_factor_le_J` — the J-class of any factor is bounded by the
  J-class of the full product.
* `isGreenD_of_prefix` — if a prefix product is D-related to `a`, so is the
  extended product.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace FactorizationForest

-- ---------------------------------------------------------------------------
-- Section 1: Split Definitions
-- ---------------------------------------------------------------------------

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

/-- A multiplicative labeling over a linearly ordered type `α` into a semigroup
`S`, satisfying the property that `σ x y * σ y z = σ x z` for all `x < y < z`.
This models the evaluation of subwords in a factorization. -/
structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  /-- The labeling function, mapping a pair of indices to a semigroup element. -/
  σ : α → α → S
  /-- Multiplicativity: adjacent subwords multiply together correctly. -/
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

/-- A split is a function assigning each element of `α` a bounded integer rank
in `Fin h`. The rank encodes the "level" at which an element participates in the
factorization forest construction. -/
abbrev Split (α : Type*) (h : ℕ) := α → Fin h

/-- `SplitRelation s x y` holds when `x` and `y` have the same rank under `s`,
and every element `z` between them (in the linear order) has a rank at most
equal to that of the minimum of `x` and `y`. -/
abbrev SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

/-- A split function is normalized if the minimal element of `α` receives the
maximal possible rank `Finset.max' Finset.univ`. This normalization ensures
the split is compatible with the inductive structure of the proof. -/
abbrev IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)]
    (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

/-- `IsRamsey L s` holds if the split `s` is a Ramsey split for the labeling
`L`. This means:

1. **Idempotent condition**: for any three points `x < y < z` that are
   pairwise split-related, the product `L.σ x y * L.σ x y = L.σ x y`.
2. **Uniformity condition**: for any two pairs `(x, y)` and `(u, v)` that
   are split-related and also cross-related (`SplitRelation s x u`), we have
   `L.σ x y = L.σ u v`.

These two conditions together guarantee that all pairs within the same
split-equivalence class of size ≥ 3 evaluate to the same idempotent element,
which is required for n-ary nodes in the factorization tree. -/
abbrev IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  (∀ x y z : α, x < y → y < z → SplitRelation s x y → SplitRelation s y z →
    L.σ x y * L.σ x y = L.σ x y) ∧
  (∀ x y u v : α, x < y → u < v →
    SplitRelation s x y → SplitRelation s u v → SplitRelation s x u →
    L.σ x y = L.σ u v)

end SplitDefinitions

-- ---------------------------------------------------------------------------
-- Section 2: Word Labeling
-- ---------------------------------------------------------------------------

section WordDefinitions

/-- The multiplicative labeling induced by a word `u` and an evaluation function
`eval`. The labeling maps `(i, j)` to `eval(u[i..j])`, i.e., the evaluation of
the subword from position `i` to position `j` (exclusive).

The proof of the `prop` field verifies that adjacent subwords multiply
correctly, relying on the hypothesis `hmul`. -/
abbrev wordLabeling {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) : MultiplicativeLabeling S (Fin (u.length + 1)) where
  σ := fun i j => eval ((u.drop i.val).take (j.val - i.val))
  prop := by
    intros x y z hxy hyz
    let u_xy := (u.drop x.val).take (y.val - x.val)
    let u_yz := (u.drop y.val).take (z.val - y.val)
    let u_xz := (u.drop x.val).take (z.val - x.val)
    have not_empty_xy_yz : u_xy ≠ [] ∧ u_yz ≠ [] := by
      simp [u_xy, u_yz]
      omega
    have concat_xy_yz_eq_xz : u_xy ++ u_yz = u_xz := by
      have index_diff_eq : z.val - x.val = (y.val - x.val) + (z.val - y.val) := by
        omega
      have drop_eq_nested_drop :
          u.drop y.val = (u.drop x.val).drop (y.val - x.val) := by
        simp
        grind
      grind
    grind

end WordDefinitions

-- ---------------------------------------------------------------------------
-- Section 3: Factorization Tree Definitions
-- ---------------------------------------------------------------------------

section TreeDefinitions

/-- A factorization tree over an alphabet `A`. Trees can be:
- A **leaf** labeled by a single element of `A`.
- A **binary** node with two subtrees, a word label, and a height.
- An **n-ary** node with a list of children, a word label, and a height.

The word and height are stored explicitly to avoid recomputing them. -/
inductive FactorizationTree (A : Type*)
| leaf (a : A)
| binary (left right : FactorizationTree A) (word : List A) (height : ℕ)
| nary (children : List (FactorizationTree A)) (word : List A) (height : ℕ)

/-- The word (leaf sequence) stored in a factorization tree. For a leaf, this
is the singleton list containing its label. For binary and n-ary nodes, this
is the word stored at construction time. -/
abbrev FactorizationTree.word {A : Type*} :
    FactorizationTree A → List A
| leaf a => [a]
| binary _ _ w _ => w
| nary _ w _ => w

/-- The height of a factorization tree. Leaves have height 0. Binary and n-ary
nodes store their height explicitly at construction time. -/
def FactorizationTree.height {A : Type*} :
    FactorizationTree A → ℕ
| leaf _ => 0
| binary _ _ _ h => h
| nary _ _ h => h

/-- The word of a leaf node is the singleton list containing its label. -/
@[simp] lemma word_leaf {A} (a : A) :
    (FactorizationTree.leaf a).word = [a] := rfl

/-- The word of a binary node is the word provided at construction time. -/
@[simp] lemma word_binary {A} (l r : FactorizationTree A)
    (w : List A) (h : ℕ) :
    (FactorizationTree.binary l r w h).word = w := rfl

/-- The word of an n-ary node is the word provided at construction time. -/
@[simp] lemma word_nary {A} (cs : List (FactorizationTree A))
    (w : List A) (h : ℕ) :
    (FactorizationTree.nary cs w h).word = w := rfl

/-- The height of a leaf node is 0. -/
@[simp] lemma height_leaf {A} (a : A) :
    (FactorizationTree.leaf a).height = 0 := rfl

/-- The height of a binary node is the height stored at construction time. -/
@[simp] lemma height_binary {A} (l r : FactorizationTree A)
    (w : List A) (h : ℕ) :
    (FactorizationTree.binary l r w h).height = h := rfl

/-- The height of an n-ary node is the height stored at construction time. -/
@[simp] lemma height_nary {A} (cs : List (FactorizationTree A))
    (w : List A) (h : ℕ) :
    (FactorizationTree.nary cs w h).height = h := rfl

/-- A word of length 1 is equal to the singleton list containing its head. -/
@[simp] lemma word_leaf_eq {A} (u : List A) (hu : u ≠ [])
    (h : u.length = 1) : [u.head hu] = u := by
  cases u with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil => rfl
    | cons _ _ => simp at h

/-- The word of an `if-then-else` tree is the `if-then-else` of the words. -/
lemma word_ite {A} (c : Prop) [Decidable c]
    (t f : FactorizationTree A) :
    (if c then t else f).word = if c then t.word else f.word := by
  split <;> rfl

/-- The word of a `dite` tree is the `dite` of the words. -/
lemma word_dite {A} (c : Prop) [Decidable c]
    (t : c → FactorizationTree A)
    (f : ¬c → FactorizationTree A) :
    (dite c t f).word =
    dite c (fun h => (t h).word) (fun h => (f h).word) := by
  split <;> rfl

/-- A factorization tree is a **Ramsey tree** with respect to an evaluation
function `eval` if:
- Every leaf is trivially a Ramsey tree.
- A binary node is a Ramsey tree if both children are, the word equals the
  concatenation of the children's words, and each child's height is strictly
  less than the node's height.
- An n-ary node is a Ramsey tree if it has at least 3 children, all children
  are Ramsey trees, there exists a common idempotent value `e` to which all
  children's words evaluate, the word is the concatenation of children's words,
  and each child's height is strictly less than the node's height. -/
inductive IsRamseyTree {A S : Type*} [Semigroup S]
    (eval : List A → S) :
    FactorizationTree A → Prop
| leaf (a : A) : IsRamseyTree eval (FactorizationTree.leaf a)
| binary (l r : FactorizationTree A) (w : List A) (h : ℕ) :
    IsRamseyTree eval l → IsRamseyTree eval r →
    w = l.word ++ r.word →
    l.height + 1 ≤ h → r.height + 1 ≤ h →
    IsRamseyTree eval (FactorizationTree.binary l r w h)
| nary (cs : List (FactorizationTree A)) (w : List A) (h : ℕ) :
    cs.length ≥ 3 → (∀ c ∈ cs, IsRamseyTree eval c) →
    (∃ (e : S), e * e = e ∧ ∀ c ∈ cs, eval (FactorizationTree.word c) = e) →
    w = List.flatten (cs.map FactorizationTree.word) →
    (∀ c ∈ cs, c.height + 1 ≤ h) →
    IsRamseyTree eval (FactorizationTree.nary cs w h)

end TreeDefinitions

-- ---------------------------------------------------------------------------
-- Section 4: The nD Invariant
-- ---------------------------------------------------------------------------

section nD

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- The number of elements in a Green's D-class `D` that lie in the H-class of
some idempotent also in `D`. This quantity is used to bound the split complexity
in the regular D-class case of Simon's theorem.

For non-regular D-classes, returns 1 (matching Colcombet's original bound). -/
noncomputable abbrev nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x ↦
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e
    )).card
  else
    1

open Classical in
/-- The value `nD D` is strictly positive for any Green's D-class `D`. -/
theorem nD_pos (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · obtain ⟨e, heD, he_idem⟩ :=
        (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heD, e, heD, he_idem, IsGreenH.refl _⟩⟩
  · decide

end nD

-- ---------------------------------------------------------------------------
-- Section 5: Labeling Properties
-- ---------------------------------------------------------------------------

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- The set of elements of `S` whose Green's J-class is at least as large as
that of `a`, i.e., `b` such that `a ≤_J b`. Used to bound the image of a
multiplicative labeling during the induction in Simon's theorem. -/
abbrev jUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

/-- States that all strictly ordered pairs `(x, y)` under the labeling `σ`
map into the set `U`. This is the hypothesis that the labeling takes values
in the relevant J-upward closure. -/
abbrev labelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

/-- The J-class of any factor `σ(v, w)` in a multiplicative labeling is bounded
below by the J-class of the full product `σ(u, x)`, provided `u ≤ v` and
`w ≤ x` with `v < w`. This reflects the fact that factors are J-greater than
the product they participate in. -/
lemma labeling_factor_le_J {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (u v w x : α)
    (huv : u ≤ v) (hvw : v < w) (hwx : w ≤ x) :
    GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v w) := by
  rcases huv.eq_or_lt with rfl | h_uv
  · rcases hwx.eq_or_lt with rfl | h_wx
    · exact le_rfl
    · exact (σ.prop u w x hvw h_wx).symm ▸
        (IsGreenJRel.mul_right (σ.σ w x) rfl : GreenJClass.mk _ ≤ _)
  · rcases hwx.eq_or_lt with rfl | h_wx
    · exact (σ.prop u v w h_uv hvw).symm ▸
        (IsGreenJRel.mul_left (σ.σ u v) rfl : GreenJClass.mk _ ≤ _)
    · exact (σ.prop u v x h_uv (hvw.trans h_wx)).symm ▸
          (σ.prop v w x hvw h_wx).symm ▸
          le_trans
            (IsGreenJRel.mul_left (σ.σ u v) rfl : GreenJClass.mk _ ≤ _)
            (IsGreenJRel.mul_right (σ.σ w x) rfl : GreenJClass.mk _ ≤ _)

variable [Finite S]

/-- If the product `σ(u, v)` is D-related to an element `a`, then the extended
product `σ(u, w)` (where `v ≤ w`) is also D-related to `a`. This uses the
J-order monotonicity of the labeling and the fact that D-relatedness lifts
along J-order equalities. -/
lemma isGreenD_of_prefix (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (u v w : α) (huv : u < v) (hvw : v ≤ w) (hD : IsGreenD (σ.σ u v) a) :
    IsGreenD (σ.σ u w) a := by
  rcases hvw.eq_or_lt with rfl | hvw_lt
  · exact hD
  · exact isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp (le_antisymm
      (GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD hD) ▸
        labeling_factor_le_J σ u u v w le_rfl huv hvw)
      (h_img u w (huv.trans hvw_lt))))

end LabelingProperties

-- ---------------------------------------------------------------------------
-- Section 6: General Utility Lemmas
-- ---------------------------------------------------------------------------

section GeneralUtility

/-- Taking the first `x` elements and then `y` elements from the remainder
gives the same result as taking the first `x + y` elements. -/
lemma take_append_take_drop {A : Type*} : (L : List A) → (x y : ℕ) →
    L.take x ++ (L.drop x).take y = L.take (x + y)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: l, x' + 1, y => by
    simp only [List.take_succ_cons, List.drop_succ_cons,
      List.cons_append, Nat.succ_add]
    rw [take_append_take_drop l x' y]

/-- In a sorted non-empty list, every element is at most the last element. -/
lemma idxs_le_getLast {n : ℕ} (L : List (Fin (n + 1)))
    (hL : L ≠ []) (h_sort : List.Pairwise (· < ·) L) :
    ∀ x ∈ L, x.val ≤ (L.getLast hL).val := fun x hx ↦ by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  have h_last_eq : L.getLast hL = L.get ⟨L.length - 1, by grind⟩ := by
    grind
  rw [h_last_eq]
  have h_pw := List.pairwise_iff_get.mp h_sort
  if h_eq : i.val = L.length - 1 then
    have h_i_eq : i = ⟨L.length - 1, by omega⟩ := Fin.ext h_eq
    grind
  else
    have h_lt : i.val < L.length - 1 := by omega
    have h_get_lt : L.get i < L.get ⟨L.length - 1, by omega⟩ :=
      h_pw i ⟨L.length - 1, by omega⟩ h_lt
    have h_val_lt : (L.get i).val <
        (L.get ⟨L.length - 1, by omega⟩).val := h_get_lt
    omega

/-- In a sorted non-empty list, the head is at most every element. -/
lemma head_le_idxs {n : ℕ} (L : List (Fin (n + 1)))
    (hL : L ≠ []) (h_sort : List.Pairwise (· < ·) L) :
    ∀ x ∈ L, (L.head hL).val ≤ x.val := fun x hx ↦ by
  cases L with
  | nil => contradiction
  | cons a l =>
    simp only [List.head_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have h_all : ∀ y ∈ l, a < y := List.pairwise_cons.1 h_sort |>.1
      have h_lt := h_all x hx
      omega

/-- Helper: `u.drop (u.length - 1) = [u.getLast hu]`. -/
lemma list_drop_length_sub_one {A} (u : List A) (hu : u ≠ []) :
    u.drop (u.length - 1) = [u.getLast hu] := by
  induction u with
  | nil => contradiction
  | cons head tail ih =>
    match tail with
    | [] => rfl
    | head2 :: tail2 =>
      have h_tail_ne : head2 :: tail2 ≠ [] := by simp
      exact ih h_tail_ne

/-- Decomposition of a word of length > 2 into head + middle + last. -/
lemma word_decomp {A} (u : List A) (hu : u ≠ []) (h_len : 2 < u.length) :
    u = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++
    [u.getLast hu] := by
  have h3 : u.drop 1 =
      (u.drop 1).take (u.length - 2) ++ (u.drop 1).drop (u.length - 2) :=
    (List.take_append_drop (u.length - 2) (u.drop 1)).symm
  have h4 : (u.drop 1).drop (u.length - 2) = [u.getLast hu] := by
    rw [List.drop_drop]
    have hd2 : 1 + (u.length - 2) = u.length - 1 := by omega
    rw [hd2]
    exact list_drop_length_sub_one u hu
  calc u
    _ = u.take 1 ++ u.drop 1 := (List.take_append_drop 1 u).symm
    _ = [u.head hu] ++ u.drop 1 := by
        have h2 : u.take 1 = [u.head hu] := by
          match u with
          | [] => contradiction
          | a :: tl => rfl
        rw [h2]
    _ = [u.head hu] ++ ((u.drop 1).take (u.length - 2) ++
          (u.drop 1).drop (u.length - 2)) := by
        exact congrArg (fun x => [u.head hu] ++ x) h3
    _ = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++
          (u.drop 1).drop (u.length - 2) := by rw [List.append_assoc]
    _ = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++
          [u.getLast hu] := by rw [h4]

/-- A sub-word extracted as `(u.drop i).take (j - i)` has the same evaluation
as the corresponding sublist of `u`. -/
lemma chunk_eq {A : Type*} {u w : List A} {i : ℕ}
    (hw : ∃ j, w = (u.drop i).take (j - i))
    (x y : Fin (w.length + 1)) (hxy : x ≤ y) :
    (w.drop x.val).take (y.val - x.val) =
    (u.drop (i + x.val)).take (y.val - x.val) := by
  rcases hw with ⟨j, rfl⟩
  have h_ylt := y.isLt
  have h_len : ((u.drop i).take (j - i)).length =
      min (j - i) (u.drop i).length := List.length_take
  have h_min : min (y.val - x.val) (j - i - x.val) = y.val - x.val := by
    omega
  simp only [List.drop_take, List.drop_drop, List.take_take, h_min]

/-- If every element of a list of natural numbers is ≤ k and the accumulator
is ≤ k, then `foldl max acc l ≤ k`. -/
lemma foldl_max_le (l : List ℕ) (acc k : ℕ) (h_acc : acc ≤ k)
    (h_le : ∀ x ∈ l, x ≤ k) :
    List.foldl max acc l ≤ k := by
  induction l generalizing acc with
  | nil => exact h_acc
  | cons x xs ih =>
    apply ih
    · exact max_le h_acc (h_le x List.mem_cons_self)
    · intro y hy
      exact h_le y (List.mem_cons_of_mem x hy)

/-- `foldl max` is monotone in the initial accumulator. -/
private lemma foldl_max_mono (l : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons hd tl ih => exact ih (max a hd) (max b hd) (by omega)

/-- The initial accumulator is at most `foldl max init l`. -/
private lemma le_foldl_max_init (l : List ℕ) (init : ℕ) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons hd tl ih =>
    calc init ≤ max init hd := le_max_left _ _
    _ ≤ List.foldl max (max init hd) tl := ih (max init hd)

/-- Any element of a list is at most `foldl max 0` of that list. -/
lemma foldl_max_mem (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    x ≤ l.foldl max 0 := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl h_eq =>
      rw [h_eq]
      exact le_trans (by omega : hd ≤ max 0 hd)
        (le_foldl_max_init tl (max 0 hd))
    | inr h_mem =>
      exact le_trans (ih h_mem)
        (foldl_max_mono tl 0 (max 0 hd) (by omega))

/-- A helper lemma: `a ≤ b - 1` and `0 < b` implies `a + 1 ≤ b`. -/
lemma plus_one_le {a b : ℕ} (h : a ≤ b - 1) (hb : 0 < b) : a + 1 ≤ b :=
  by omega

/-- Converts a list of children into the appropriate tree node type:
- `[]` or `[c]` → degenerate (wraps in a binary with `def_leaf`).
- `[c1, c2]` → binary node.
- Three or more → n-ary node. -/
def list_to_nary {A : Type*}
    (children : List (FactorizationTree A)) (u : List A) (h : ℕ)
    (def_leaf : FactorizationTree A) :
    FactorizationTree A :=
  match children with
  | [] => def_leaf.binary def_leaf u 0
  | [c] => c.binary c u h
  | [c1, c2] => c1.binary c2 u h
  | _::_::_::_ => FactorizationTree.nary children u h

/-- The height of `list_to_nary children w h def_leaf` is at most
`max def_leaf.height h`. -/
lemma height_list_to_nary_le {A : Type*} (children : List (FactorizationTree A))
    (w : List A) (h : ℕ) (def_leaf : FactorizationTree A) :
    (list_to_nary children w h def_leaf).height ≤
    max def_leaf.height h := by
  match children with
  | [] => simp [list_to_nary, FactorizationTree.height]
  | [c] => simp [list_to_nary, FactorizationTree.height]
  | [c1, c2] => simp [list_to_nary, FactorizationTree.height]
  | _::_::_::_ => simp [list_to_nary, FactorizationTree.height]

/-- When `children.length ≥ 3`, `list_to_nary` produces an n-ary node. -/
lemma list_to_nary_of_len_ge_3 {A : Type*} (children : List (FactorizationTree A))
    (u : List A) (h : ℕ) (def_leaf : FactorizationTree A) :
    children.length ≥ 3 →
    list_to_nary children u h def_leaf =
    FactorizationTree.nary children u h := by
  intro h_len
  match children with
  | [] => contradiction
  | [_] => contradiction
  | [_, _] => contradiction
  | _::_::_::_ => rfl

/-- The height of `list_to_nary children w h def_leaf` is at most `h`. -/
lemma list_to_nary_height_le {A : Type*}
    (children : List (FactorizationTree A))
    (w : List A) (h : ℕ) (def_leaf : FactorizationTree A) :
    (list_to_nary children w h def_leaf).height ≤ h := by
  simp only [list_to_nary]
  split <;> simp

/-- If every tree in `l` has height ≤ k, then
`foldl max 0 (l.map (·.height)) ≤ k`. -/
lemma max_h_children_le {A : Type*}
    (l : List (FactorizationTree A)) (k : ℕ)
    (h_le : ∀ t ∈ l, t.height ≤ k) :
    List.foldl max 0 (l.map (·.height)) ≤ k := by
  apply foldl_max_le
  · omega
  · intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨t, ht_mem, ht_eq⟩
    rw [← ht_eq]
    exact h_le t ht_mem

/-- `foldl max` over a list of tree heights is bounded by any uniform bound. -/
lemma foldl_max_bound {A : Type*}
    (children : List (FactorizationTree A))
    (bound : ℕ)
    (h_bound : ∀ c ∈ children, c.height ≤ bound) :
    (children.map FactorizationTree.height).foldl max 0 ≤ bound := by
  have h_fold : ∀ (l : List (FactorizationTree A)) (init : ℕ),
      init ≤ bound →
      (∀ c ∈ l, c.height ≤ bound) →
      (l.map FactorizationTree.height).foldl max init ≤ bound := by
    intro l
    induction l with
    | nil =>
      intro init h_init _
      exact h_init
    | cons hd tl ih =>
      intro init h_init h_all
      apply ih
      · have h_hd : hd.height ≤ bound := h_all hd (by simp)
        omega
      · intro c hc
        exact h_all c (by simp [hc])
  exact h_fold children 0 (by omega) h_bound

/-- The word of `list_to_nary children u h def_leaf` is always `u`. -/
@[simp] lemma list_to_nary_word_eq {A : Type*}
    (children : List (FactorizationTree A)) (u : List A)
    (h : ℕ) (def_leaf : FactorizationTree A) :
    (list_to_nary children u h def_leaf).word = u := by
  match children with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- A subtype of `α` representing elements strictly between `xs[i]` and
`xs[i+1]` (or between `xs[i]` and +∞ if `i` is the last index).
Used to restrict the inductive hypothesis to proper sub-intervals. -/
abbrev OpenIntervalType {α : Type*} [LinearOrder α] (xs : List α) (i : ℕ) :=
  { y : α // ∃ (hi_lt : i < xs.length),
    xs.get ⟨i, hi_lt⟩ < y ∧
    ∀ (h_next_lt : i + 1 < xs.length), y < xs.get ⟨i + 1, h_next_lt⟩ }

/-- A strictly increasing sequence covering a domain bounds any element `x`
either at one of the sequence points or within a consecutive interval.
This is the key covering lemma used in the split combination construction. -/
lemma list_interval_covers {α : Type*} [LinearOrder α] (x : α) :
    ∀ (xs : List α), x ∉ xs →
    (∃ y ∈ xs, y < x) →
    ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (hi_succ_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, hi_succ_lt⟩
| [], _, ⟨_, hy, _⟩ => nomatch hy
| a :: tail, h_not_in, h_lb => by
  by_cases h_tail : ∃ y ∈ tail, y < x
  · obtain ⟨i, hi, hlt, hgt⟩ :=
        list_interval_covers x tail (fun h => h_not_in (List.Mem.tail _ h)) h_tail
    exact ⟨i + 1, by simp; omega, hlt, fun h => hgt (by simp at h; omega)⟩
  · grind

/-- An element in an open interval `OpenIntervalType xs i` is never a member
of the sequence `xs` itself (since it is strictly between two consecutive
sequence points, while the sequence is strictly monotone). -/
lemma not_mem_of_openInterval {α : Type*} [LinearOrder α] {xs : List α}
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length),
      i < j → xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (i : ℕ) (z : α)
    (h_in : ∃ (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < z ∧ ∀ (hi_succ_lt : i + 1 < xs.length),
      z < xs.get ⟨i + 1, hi_succ_lt⟩) : z ∉ xs := by
  intro hz_mem
  obtain ⟨j, hz_eq⟩ := List.mem_iff_get.mp hz_mem
  grind

/-- Two open intervals defined by the same strictly increasing sequence are
disjoint: if an element `x` lies in both interval `i` and interval `k`,
then `i = k`. -/
lemma openInterval_unique {α : Type*} [LinearOrder α] (xs : List α)
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
      (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (x : α) (i k : ℕ) (hi : i < xs.length) (hk : k < xs.length)
    (hlt_i : xs.get ⟨i, hi⟩ < x)
    (hgt_i : ∀ h_next_lt : i + 1 < xs.length,
      x < xs.get ⟨i + 1, h_next_lt⟩)
    (hlt_k : xs.get ⟨k, hk⟩ < x)
    (hgt_k : ∀ h_next_lt : k + 1 < xs.length,
      x < xs.get ⟨k + 1, h_next_lt⟩) :
    i = k := by
  rcases lt_trichotomy i k with h | rfl | h <;>
    first | exfalso; grind | rfl

end GeneralUtility

end FactorizationForest
