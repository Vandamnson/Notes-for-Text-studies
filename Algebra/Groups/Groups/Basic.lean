/-
Groups/Basic.lean
-/

namespace Groups

/-- A binary operation on `G`. -/
def BinOp (G :Type) : Type := G → G → G
/- Shared `G` and `op` for the declarations below. -/
variable (G : Type) (op: BinOp G)
/-- `op` is associative, written right-nested = left-nested. -/
def Assoc(G:Type) (op: BinOp G) : Prop :=
∀ a b c : G, op a (op b c) = op (op a b) c
/-- `op` is commutative. -/
def Comm (G :Type) (op: BinOp G):Prop :=
∀ a b : G, op a b = op b a
/-- `e` fixes every element from the right. -/
def Id_right (G: Type) (op: BinOp G) (e : G): Prop:=
 ∀ a : G, op a e =a
/-- `e'` fixes every element from the left. -/
def Id_left (G: Type) (op: BinOp G) (e' : G): Prop:=
 ∀ a : G, op e' a = a
/-- A left identity and a right identity have to be the same element.
    Needs no associativity and no inverses. -/
theorem Unique_id (G: Type) (op : BinOp G) (e e' : G): (Id_left G op e' → Id_right G op e → (e' = e)) := by
    intro h_1 h_2
    calc e'= op e' e := by rw[h_2]
    _= e := by rw[h_1]
/-- `b` is a left inverse of `a` relative to `e`: `op b a = e`.
    `e` is just whatever you pass in; the identity laws come from the caller. -/
def left_inv_of (G:Type) (op : BinOp G)(a:G)(b e:G) : Prop :=
    op b a =e
/-- `b'` is a right inverse of `a` relative to `e`: `op a b' = e`.
    Note `op a b = e` reads both ways: `b` is a right inverse of `a`, and
    `a` is a left inverse of `b`. -/
def right_inv_of (G:Type) (op : BinOp G)(a:G) (b' e:G) : Prop :=
    op a b' =e
/-- A left inverse and a right inverse of the same `a` are equal.
    Expand `b'` to `op b' e`, swap `e` for `op a b`, reassociate, collapse. -/
theorem Unique_inv (G : Type) (op : BinOp G) (a b b' e : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e)
    (h1 : left_inv_of G op a b' e) (h2 : right_inv_of G op a b e) : b' = b := by
    calc b'= op b' e := by rw[hr]
    _= op b' (op a b) := by rw[h2]
    _= op (op b' a) b := by rw[hA]
    _=op e b := by rw[h1]
    _=b := by rw[hl]
/-- Inverse of an inverse: if `op a b = e` and `op b c = e` then `c = a`. -/
theorem Inv_Inv (G:Type)(op: BinOp G) (a b c e :G) (hl: left_inv_of G op c b e) (hr : right_inv_of G op a b e) (gl : Id_left G op e) (gr: Id_right G op e)(hA: Assoc G op): c = a := by
    calc c = op e c := by rw[gl]
    _= op (op a b) c := by rw[hr]
    _= op a (op b c) := by rw[hA]
    _= op a e := by rw[hl]
    _= a := by rw[gr]

/-- `(a·b)⁻¹ = b⁻¹·a⁻¹`, where `f` is `(a·b)⁻¹`, `c` is `a⁻¹`, `d` is `b⁻¹`.
    Insert `d·b` and `c·a` as copies of `e`, reassociate until `(a·b)·f`
    appears, then collapse it.  The deep `rw [hA ..]` steps name their
    arguments so they hit the intended subterm. -/
theorem op_inv (G : Type) (op : BinOp G) (a b c d e f : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e)
    (hf : right_inv_of G op (op a b) f e)
    (hc : left_inv_of G op a c e)
    (hd : left_inv_of G op b d e) : f = op d c := by
  calc f = op e f := by rw [hl]
    _ = op (op d b) f := by rw [hd]
    _ = op d (op b f) := by rw [hA d b f]
    _ = op d (op e (op b f)) := by rw [hl]
    _ = op d (op (op c a) (op b f)) := by rw [hc]
    _ = op d (op c (op a (op b f))) := by rw [hA c a (op b f)]
    _ = op d (op c (op (op a b) f)) := by rw [hA a b f]
    _ = op (op d c) (op (op a b) f) := by rw [hA d c (op (op a b) f)]
    _ = op (op d c) e := by rw [hf]
    _ = op d c := by rw [hr]

/-! ### Generalized associativity

The product `a₁ · a₂ · … · aₙ` does not depend on how it is bracketed.
Only `Assoc` is needed.  A bracketing is a binary tree, so the plan is:
show every tree equals one canonical product of its leaves, then two trees
with the same leaves must agree.  Sequences stay non-empty, which is why no
identity element shows up anywhere here. -/

/-- A bracketing: a binary tree with elements at the leaves. -/
inductive BTree (G : Type) : Type
  | leaf : G → BTree G
  | node : BTree G → BTree G → BTree G

/-- The element a bracketing computes. -/
def BTree.eval (G : Type) (op : BinOp G) : BTree G → G
  | .leaf a => a
  | .node l r => op (BTree.eval G op l) (BTree.eval G op r)

/-- Canonical right-nested product of a non-empty sequence, given as head plus
    tail: `prod a [x, y] = op a (op x y)`. -/
def prod (G : Type) (op : BinOp G) : G → List G → G
  | a, [] => a
  | a, x :: xs => op a (prod G op x xs)

/-- First leaf of a bracketing. -/
def BTree.head (G : Type) : BTree G → G
  | .leaf a => a
  | .node l _ => BTree.head G l

/-- The remaining leaves, left to right. -/
def BTree.tail (G : Type) : BTree G → List G
  | .leaf _ => []
  | .node l r => BTree.tail G l ++ BTree.head G r :: BTree.tail G r

/-- Splitting a sequence splits the product.  Induction on `xs`; `a` stays under
    the `∀` because the inductive hypothesis is needed at `x`, not at `a`. -/
theorem prod_append (G : Type) (op : BinOp G) (hA : Assoc G op) (b : G) (ys : List G) :
    ∀ (xs : List G) (a : G),
      prod G op a (xs ++ b :: ys) = op (prod G op a xs) (prod G op b ys) := by
  intro xs
  induction xs with
  | nil => intro a; rfl
  | cons x xs ih =>
      intro a
      show op a (prod G op x (xs ++ b :: ys)) = op (op a (prod G op x xs)) (prod G op b ys)
      rw [ih x, hA]

/-- Every bracketing equals the canonical product of its leaves. -/
theorem eval_eq_prod (G : Type) (op : BinOp G) (hA : Assoc G op) :
    ∀ t : BTree G, BTree.eval G op t = prod G op (BTree.head G t) (BTree.tail G t) := by
  intro t
  induction t with
  | leaf a => rfl
  | node l r ihl ihr =>
      show op (BTree.eval G op l) (BTree.eval G op r)
            = prod G op (BTree.head G l) (BTree.tail G l ++ BTree.head G r :: BTree.tail G r)
      rw [prod_append G op hA (BTree.head G r) (BTree.tail G r) (BTree.tail G l) (BTree.head G l),
          ihl, ihr]

/-- Same leaves, same value.  In use both hypotheses hold by `rfl`, since head
    and tail of a concrete tree just compute. -/
theorem assoc_general (G : Type) (op : BinOp G) (hA : Assoc G op) (s t : BTree G)
    (hh : BTree.head G s = BTree.head G t) (ht : BTree.tail G s = BTree.tail G t) :
    BTree.eval G op s = BTree.eval G op t := by
  rw [eval_eq_prod G op hA s, eval_eq_prod G op hA t, hh, ht]



/-- Left cancellation.  Only `Id_left` and a left inverse of `a` are needed. -/
theorem left_cancellation (G : Type) (op : BinOp G) (a x y b e : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hb : left_inv_of G op a b e) :
    (op a x = op a y) → x = y := by
    intro g
    rw [← hl x, ← hl y, ← hb, ← hA b a x, ← hA b a y, g]
/-- Right cancellation: the mirror image of `left_cancellation`. -/
theorem right_cancellation (G : Type) (op : BinOp G) (a x y b e : G)
    (hA : Assoc G op) (hl : Id_right G op e) (hb : right_inv_of G op a b e): (op x a = op y a ) → x = y := by
    intro g
    rw[← hl x, ← hl y, ← hb, hA, hA, g]

/-- `x` to the power `n`: `pow x 0 = e`, `pow x (n+1) = op x (pow x n)`.
    The identity is what the `0` case needs, so `e` has to be a parameter. -/
def pow (G : Type) (op : BinOp G) (e : G) (x : G) : Nat → G
  | 0 => e
  | n + 1 => op x (pow G op e x n)

/-- `n` is the order of `x`: the least positive power of `x` landing on `e`.

    A predicate, not a function.  An element need not have finite order (in `Int`
    under `+` no positive multiple of `1` is `0`), and a computable search would
    also need decidable equality on `G`, which an abstract `G` has not got. -/
def IsOrder (G : Type) (op : BinOp G) (e x : G) (n : Nat) : Prop :=
  0 < n ∧ pow G op e x n = e ∧ ∀ m : Nat, 0 < m → m < n → pow G op e x m ≠ e

/-- An element has at most one order, which is what justifies saying *the* order.
    Each minimality clause rules out the other number being smaller. -/
theorem IsOrder_unique (G : Type) (op : BinOp G) (e x : G) (m n : Nat)
    (hm : IsOrder G op e x m) (hn : IsOrder G op e x n) : m = n := by
  obtain ⟨hm0, hme, hmin⟩ := hm
  obtain ⟨hn0, hne, hnin⟩ := hn
  have h1 : ¬ n < m := fun h => hmin n hn0 h hne
  have h2 : ¬ m < n := fun h => hnin m hm0 h hme
  omega

/-- An element has order 1 exactly when it is the identity.
    Only `Id_right` is needed: forward it turns `op x e = e` into `x = e`,
    backward it supplies `op e e = e`.  The minimality clause is vacuous. -/
theorem order1iffidentity (G : Type) (op : BinOp G) (e x : G) (hr : Id_right G op e) :
    IsOrder G op e x 1 ↔ x = e := by
  constructor
  · intro h
    obtain ⟨_, h1, _⟩ := h
    rw [← hr x]
    exact h1
  · intro h
    refine ⟨Nat.zero_lt_one, ?_, ?_⟩
    · rw [h]
      exact hr e
    · intro m hm0 hm1
      omega

/-- Every element has a two-sided inverse.  Packaged as one hypothesis so the
    declarations below can take it as a single argument. -/
def HasInverses (G : Type) (op : BinOp G) (e : G) : Prop :=
  ∀ a : G, ∃ b : G, right_inv_of G op a b e ∧ left_inv_of G op a b e

/-- The inverse *function* `a ↦ inv a`.

    `Exists.choose` pulls a witness out of `hinv a`.  That needs
    `Classical.choice`, hence `noncomputable`; and the proof `hinv` is an
    argument, so the function is written `inv G op e hinv a`. -/
noncomputable def inv (G : Type) (op : BinOp G) (e : G)
    (hinv : HasInverses G op e) (a : G) : G :=
  (hinv a).choose

/-- `inv a` really is a right inverse of `a`. -/
theorem inv_right (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e) (a : G) :
    right_inv_of G op a (inv G op e hinv a) e := (hinv a).choose_spec.1

/-- `inv a` really is a left inverse of `a`. -/
theorem inv_left (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e) (a : G) :
    left_inv_of G op a (inv G op e hinv a) e := (hinv a).choose_spec.2

/-- Choice picks *some* inverse; uniqueness makes it *the* inverse.  Any right
    inverse of `a` is equal to `inv a`, so this converts inverse-shaped
    hypotheses into the function. -/
theorem eq_inv (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (a b : G)
    (h : right_inv_of G op a b e) : b = inv G op e hinv a :=
  (Unique_inv G op a b (inv G op e hinv a) e hA hl hr (inv_left G op e hinv a) h).symm

/-- `inv (inv a) = a`, now a one-liner: `a` is an inverse of `inv a`. -/
theorem inv_inv (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (a : G) :
    inv G op e hinv (inv G op e hinv a) = a :=
  (eq_inv G op e hinv hA hl hr (inv G op e hinv a) a (inv_left G op e hinv a)).symm


/-- The inverse of the identity is the identity. -/
theorem inv_e (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) :
    inv G op e hinv e = e :=
  Unique_inv G op e e (inv G op e hinv e) e hA hl hr (inv_left G op e hinv e) (hr e)

/-- `inv (a·b) = inv b · inv a` -- inverting a product reverses the order.

    A direct instance of `op_inv`.  Note it is *not* `inv (op a b) = inv (op b a)`:
    `inv` is injective, so that would force `op a b = op b a`. -/
theorem inv_op (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (a b : G) :
    inv G op e hinv (op a b) = op (inv G op e hinv b) (inv G op e hinv a) :=
  op_inv G op a b (inv G op e hinv a) (inv G op e hinv b) e (inv G op e hinv (op a b))
    hA hl hr (inv_right G op e hinv (op a b))
    (inv_left G op e hinv a) (inv_left G op e hinv b)

/-- Product of a list, with `e` for the empty list: `prodL [x, y] = op x (op y e)`.

    A second product alongside `prod`.  `prod` is head-plus-tail so that
    generalized associativity needs no identity; here reversal moves the head to
    the end, so a plain `List` with `e` as base is what works. -/
def prodL (G : Type) (op : BinOp G) (e : G) : List G → G
  | [] => e
  | x :: xs => op x (prodL G op e xs)

/-- Peeling the last factor off a `prodL`.  The `nil` case is where both identity
    laws are used; the `cons` case is one associativity step. -/
theorem prodL_snoc (G : Type) (op : BinOp G) (e : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (z : G) :
    ∀ ys : List G, prodL G op e (ys ++ [z]) = op (prodL G op e ys) z := by
  intro ys
  induction ys with
  | nil =>
      show op z e = op e z
      rw [hr z, hl z]
  | cons y ys ih =>
      show op y (prodL G op e (ys ++ [z])) = op (op y (prodL G op e ys)) z
      rw [ih, hA y (prodL G op e ys) z]

/-- `inv (a₁ · a₂ · … · aₙ) = inv aₙ · … · inv a₁`.

    Induction on the list: `inv_op` turns `inv (x · rest)` into
    `inv rest · inv x`, the hypothesis rewrites `inv rest`, and `prodL_snoc`
    reassembles the result with `inv x` moved to the end. -/
theorem inv_prodL (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) :
    ∀ l : List G, inv G op e hinv (prodL G op e l)
      = prodL G op e (List.reverse (List.map (inv G op e hinv) l)) := by
  intro l
  induction l with
  | nil => exact inv_e G op e hinv hA hl hr
  | cons x xs ih =>
      show inv G op e hinv (op x (prodL G op e xs))
            = prodL G op e (List.reverse (inv G op e hinv x :: List.map (inv G op e hinv) xs))
      rw [List.reverse_cons, inv_op G op e hinv hA hl hr x (prodL G op e xs), ih,
          prodL_snoc G op e hA hl hr (inv G op e hinv x)
            (List.reverse (List.map (inv G op e hinv) xs))]



/-- `x² = e` exactly when `x` has order 1 or order 2.

    Needs no group axioms at all -- only a case split on whether `pow x 1 = e`.
    Forward: if it is, order 1; if not, order 2, since `m = 1` is the only `m`
    the minimality clause has to rule out.  Backward: order 2 gives it directly,
    and order 1 gives it because `pow x 2 = op x (pow x 1)`. -/
theorem pow_two_eq_id_iff (G : Type) (op : BinOp G) (e x : G) :
    pow G op e x 2 = e ↔ (IsOrder G op e x 1 ∨ IsOrder G op e x 2) := by
  constructor
  · intro h
    rcases Classical.em (pow G op e x 1 = e) with h1 | h1
    · refine Or.inl ⟨by omega, h1, ?_⟩
      intro m hm0 hm1
      omega
    · refine Or.inr ⟨by omega, h, ?_⟩
      intro m hm0 hm2
      have hm : m = 1 := by omega
      rw [hm]
      exact h1
  · intro h
    rcases h with h | h
    · obtain ⟨_, h1, _⟩ := h
      show op x (pow G op e x 1) = e
      rw [h1]
      exact h1
    · exact h.2.1


/-- If `x` has order `n = k+1` then `x^k` is the inverse of `x`.

    Order written as `k+1` rather than `n-1`: `Nat` subtraction truncates, and
    `IsOrder` already forces the order positive, so nothing is lost.

    Only `pow x (k+1) = e` is used -- the minimality half of `IsOrder` is not
    needed, nor is `Id_right`.  `op x (pow x k) = e = op x (inv x)`, then cancel
    `x` on the left. -/
example (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (k : Nat)
    (h : IsOrder G op e x (k + 1)) :
    pow G op e x k = inv G op e hinv x := by
  have key : op x (pow G op e x k) = op x (inv G op e hinv x) :=
    h.2.1.trans (inv_right G op e hinv x).symm
  exact left_cancellation G op x (pow G op e x k) (inv G op e hinv x)
    (inv G op e hinv x) e hA hl (inv_left G op e hinv x) key



/-- The commutator `[x, y] = x⁻¹y⁻¹xy`.  `noncomputable` because `inv` is. -/
noncomputable def commutator (G : Type) (op : BinOp G) (e : G)
    (hinv : HasInverses G op e) (x y : G) : G :=
  op (inv G op e hinv x) (op (inv G op e hinv y) (op x y))

/-- `x = y⁻¹xy` exactly when `x` and `y` commute. -/
theorem conj_eq_iff_commutes (G : Type) (op : BinOp G) (e x y : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e) :
    x = op (inv G op e hinv y) (op x y) ↔ op x y = op y x := by
  constructor
  · intro h
    have hyx : op y x = op x y :=
      calc op y x = op y (op (inv G op e hinv y) (op x y)) := by rw [← h]
        _ = op (op y (inv G op e hinv y)) (op x y) := hA y (inv G op e hinv y) (op x y)
        _ = op e (op x y) := by rw [inv_right G op e hinv y]
        _ = op x y := hl (op x y)
    exact hyx.symm
  · intro h
    calc x = op e x := (hl x).symm
      _ = op (op (inv G op e hinv y) y) x := by rw [inv_left G op e hinv y]
      _ = op (inv G op e hinv y) (op y x) := (hA (inv G op e hinv y) y x).symm
      _ = op (inv G op e hinv y) (op x y) := by rw [h]

/-- `[x, y] = e` exactly when `x = y⁻¹xy`.  Forward is left cancellation of
    `x⁻¹`; backward folds the tail back into `x` and leaves `inv_left`. -/
theorem commutator_eq_id_iff_conj (G : Type) (op : BinOp G) (e x y : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e) :
    commutator G op e hinv x y = e ↔ x = op (inv G op e hinv y) (op x y) := by
  constructor
  · intro h
    exact (left_cancellation G op (inv G op e hinv x)
      (op (inv G op e hinv y) (op x y)) x x e hA hl
      (inv_right G op e hinv x) (h.trans (inv_left G op e hinv x).symm)).symm
  · intro h
    show op (inv G op e hinv x) (op (inv G op e hinv y) (op x y)) = e
    rw [← h]
    exact inv_left G op e hinv x

/-- The commutator is trivial exactly when the two elements commute.
    `Id_right` is needed nowhere in this group of results. -/
theorem commutator_eq_id_iff_commutes (G : Type) (op : BinOp G) (e x y : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e) :
    commutator G op e hinv x y = e ↔ op x y = op y x :=
  (commutator_eq_id_iff_conj G op e x y hinv hA hl).trans
    (conj_eq_iff_commutes G op e x y hinv hA hl)



/-- 19(a), first half: `x^(a+b) = x^a · x^b`.

    Induction on `a`, not `b`: `pow` multiplies on the left, so the recursion has
    to peel from the same side the induction does.  `Assoc` and `Id_left` only. -/
theorem pow_add (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) (b : Nat) :
    ∀ a : Nat, pow G op e x (a + b)
      = op (pow G op e x a) (pow G op e x b) := by
  intro a
  induction a with
  | zero =>
      rw [Nat.zero_add]
      exact (hl (pow G op e x b)).symm
  | succ k ih =>
      rw [Nat.succ_add]
      show op x (pow G op e x (k + b))
            = op (op x (pow G op e x k)) (pow G op e x b)
      rw [ih, hA]

/-- 19(a), second half: `(x^a)^b = x^(a·b)`.  Induction on `b`, using `pow_add`
    to merge `x^a · x^(a·k)` into `x^(a + a·k)`. -/
theorem pow_mul (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) :
    ∀ b a : Nat, pow G op e (pow G op e x a) b = pow G op e x (a * b) := by
  intro b
  induction b with
  | zero =>
      intro a
      rw [Nat.mul_zero]
      rfl
  | succ k ih =>
      intro a
      show op (pow G op e x a) (pow G op e (pow G op e x a) k) = pow G op e x (a * (k+1))
      rw [ih a, Nat.mul_succ, Nat.add_comm (a*k) a, pow_add G op e x hA hl (a*k) a]


/-- `x^n` is the product of `n` copies of `x`.  Bridges `pow` to `prodL` so the
    list-level theorems apply to powers. -/
theorem prodL_replicate (G : Type) (op : BinOp G) (e x : G) :
    ∀ n : Nat, prodL G op e (List.replicate n x) = pow G op e x n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show op x (prodL G op e (List.replicate k x)) = op x (pow G op e x k)
      rw [ih]

/-- 19(b): `(x^n)⁻¹ = (x⁻¹)^n`.

    Exactly your route -- rewrite `x^n` as a product of `n` copies, apply
    `inv_prodL`, and the reversal is invisible because all the factors are the
    same: `reverse (map inv (replicate n x)) = replicate n (inv x)`. -/
theorem inv_pow (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Nat) :
    inv G op e hinv (pow G op e x n) = pow G op e (inv G op e hinv x) n := by
  rw [← prodL_replicate G op e x n,
      inv_prodL G op e hinv hA hl hr (List.replicate n x),
      List.map_replicate, List.reverse_replicate,
      prodL_replicate G op e (inv G op e hinv x) n]




/-- `x` to an *integer* power.  Core's `Int` is literally these two
    constructors, so the definition splits cleanly: non-negative exponents reuse
    `pow`, negative ones invert. -/
noncomputable def zpow (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (x : G) : Int → G
  | Int.ofNat n => pow G op e x n
  | Int.negSucc n => inv G op e hinv (pow G op e x (n + 1))

/-- `x^(-n) = (x^n)⁻¹` for every integer `n` -- the two branches of `zpow` agree
    at the sign boundary.  Only the `0` case needs work (`inv e = e`); the
    positive case is `rfl` and the negative one is `inv_inv`. -/
theorem zpow_neg (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Int) :
    zpow G op e hinv x (-n) = inv G op e hinv (zpow G op e hinv x n) := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (inv_e G op e hinv hA hl hr).symm
      | succ j => rfl
  | negSucc k =>
      show pow G op e x (k + 1)
            = inv G op e hinv (inv G op e hinv (pow G op e x (k + 1)))
      rw [inv_inv G op e hinv hA hl hr (pow G op e x (k + 1))]

/-- 19(b) in the book's notation: `(x⁻¹)^n = x^(-n)` for every integer `n`.
    The positive case is `inv_pow`; the negative case is `inv_pow` then
    `inv_inv`. -/
theorem zpow_inv (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Int) :
    zpow G op e hinv (inv G op e hinv x) n = zpow G op e hinv x (-n) := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => rfl
      | succ j =>
          show pow G op e (inv G op e hinv x) (j + 1)
                = inv G op e hinv (pow G op e x (j + 1))
          rw [inv_pow G op e x hinv hA hl hr (j + 1)]
  | negSucc k =>
      show inv G op e hinv (pow G op e (inv G op e hinv x) (k + 1))
            = pow G op e x (k + 1)
      rw [inv_pow G op e (inv G op e hinv x) hinv hA hl hr (k + 1),
          inv_inv G op e hinv hA hl hr x]


/-- `x^1 = x`. -/
theorem pow_one (G : Type) (op : BinOp G) (e x : G) (hr : Id_right G op e) :
    pow G op e x 1 = x := hr x

/-- An element commutes with its own powers.  Needed because `pow` multiplies on
    the left while the `zpow` step lemmas peel from the right. -/
theorem pow_comm_self (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (k : Nat) :
    op x (pow G op e x k) = op (pow G op e x k) x := by
  have h := pow_add G op e x hA hl 1 k
  rw [pow_one G op e x hr] at h
  show pow G op e x (k + 1) = op (pow G op e x k) x
  exact h

/-- Step up: `x^(n+1) = x^n · x`, for every *integer* `n`.

    Three cases.  Non-negative is `pow_comm_self`; `n = -1` collapses to
    `inv_left`; `n ≤ -2` goes through `inv_pow` and then cancels `x⁻¹ · x`. -/
theorem zpow_succ (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Int) :
    zpow G op e hinv x (n + 1) = op (zpow G op e hinv x n) x := by
  cases n with
  | ofNat k =>
      have harith : (Int.ofNat k) + 1 = Int.ofNat (k + 1) := rfl
      rw [harith]
      show pow G op e x (k + 1) = op (pow G op e x k) x
      exact pow_comm_self G op e x hA hl hr k
  | negSucc k =>
      cases k with
      | zero =>
          have harith : (Int.negSucc 0) + 1 = (0 : Int) := by omega
          rw [harith]
          show e = op (inv G op e hinv (pow G op e x 1)) x
          rw [pow_one G op e x hr]
          exact (inv_left G op e hinv x).symm
      | succ j =>
          have harith : (Int.negSucc (j + 1)) + 1 = Int.negSucc j := by omega
          rw [harith]
          show inv G op e hinv (pow G op e x (j + 1))
                = op (inv G op e hinv (pow G op e x (j + 1 + 1))) x
          rw [inv_pow G op e x hinv hA hl hr (j + 1),
              inv_pow G op e x hinv hA hl hr (j + 1 + 1)]
          calc pow G op e (inv G op e hinv x) (j + 1)
              = op (pow G op e (inv G op e hinv x) (j + 1)) e := (hr _).symm
            _ = op (pow G op e (inv G op e hinv x) (j + 1))
                  (op (inv G op e hinv x) x) := by rw [inv_left G op e hinv x]
            _ = op (op (pow G op e (inv G op e hinv x) (j + 1))
                  (inv G op e hinv x)) x := hA _ _ _
            _ = op (op (inv G op e hinv x)
                  (pow G op e (inv G op e hinv x) (j + 1))) x := by
                  rw [pow_comm_self G op e (inv G op e hinv x) hA hl hr (j + 1)]
            _ = op (pow G op e (inv G op e hinv x) (j + 1 + 1)) x := rfl



/-- Step down: `x^(n-1) = x^n · x⁻¹`.  Derived from `zpow_succ` at `n-1` by
    multiplying through by `x⁻¹`. -/
theorem zpow_pred (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Int) :
    zpow G op e hinv x (n - 1) = op (zpow G op e hinv x n) (inv G op e hinv x) := by
  have h := zpow_succ G op e x hinv hA hl hr (n - 1)
  have hn : (n - 1) + 1 = n := by omega
  rw [hn] at h
  calc zpow G op e hinv x (n - 1)
      = op (zpow G op e hinv x (n - 1)) e := (hr _).symm
    _ = op (zpow G op e hinv x (n - 1)) (op x (inv G op e hinv x)) := by
          rw [inv_right G op e hinv x]
    _ = op (op (zpow G op e hinv x (n - 1)) x) (inv G op e hinv x) := hA _ _ _
    _ = op (zpow G op e hinv x n) (inv G op e hinv x) := by rw [← h]

/-- 19(c): `x^(a+b) = x^a · x^b` for arbitrary integers `a` and `b`.

    Induction on `b` in its two constructor families -- up from `0` with
    `zpow_succ`, down from `-1` with `zpow_pred`.  `a` stays an arbitrary integer
    throughout, so no sign cases on `a` are ever needed: the step lemmas already
    handle every sign uniformly.  That is what makes this shorter than the naive
    four-case split, where the mixed cases need explicit cancellation. -/
theorem zpow_add (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) :
    ∀ b a : Int, zpow G op e hinv x (a + b)
      = op (zpow G op e hinv x a) (zpow G op e hinv x b) := by
  have hpos : ∀ k : Nat, ∀ a : Int, zpow G op e hinv x (a + Int.ofNat k)
      = op (zpow G op e hinv x a) (zpow G op e hinv x (Int.ofNat k)) := by
    intro k
    induction k with
    | zero =>
        intro a
        have h0 : a + Int.ofNat 0 = a := Int.add_zero a
        rw [h0]
        exact (hr _).symm
    | succ j ih =>
        intro a
        have h1 : a + Int.ofNat (j + 1) = (a + Int.ofNat j) + 1 := by
          rw [show Int.ofNat (j + 1) = Int.ofNat j + 1 from rfl, ← Int.add_assoc]
        have h2 : Int.ofNat (j + 1) = Int.ofNat j + 1 := rfl
        rw [h1, zpow_succ G op e x hinv hA hl hr, ih a, h2,
            zpow_succ G op e x hinv hA hl hr, hA]
  have hneg : ∀ k : Nat, ∀ a : Int, zpow G op e hinv x (a + Int.negSucc k)
      = op (zpow G op e hinv x a) (zpow G op e hinv x (Int.negSucc k)) := by
    intro k
    induction k with
    | zero =>
        intro a
        have h0 : a + Int.negSucc 0 = a - 1 := by omega
        rw [h0, zpow_pred G op e x hinv hA hl hr]
        show op (zpow G op e hinv x a) (inv G op e hinv x)
              = op (zpow G op e hinv x a) (inv G op e hinv (pow G op e x 1))
        rw [pow_one G op e x hr]
    | succ j ih =>
        intro a
        have h1 : a + Int.negSucc (j + 1) = (a + Int.negSucc j) - 1 := by omega
        have h2 : Int.negSucc (j + 1) = Int.negSucc j - 1 := by omega
        rw [h1, zpow_pred G op e x hinv hA hl hr, ih a, h2,
            zpow_pred G op e x hinv hA hl hr, hA]
  intro b
  cases b with
  | ofNat k => exact hpos k
  | negSucc k => exact hneg k



/-- If `x` has order `n`, so does `x⁻¹`.

    `(x⁻¹)^n = (x^n)⁻¹ = e⁻¹ = e` gives the power; minimality transfers because
    `(x⁻¹)^k = e` forces `x^k = e` (invert both sides and use `inv_inv`), which
    would contradict minimality for `x`. -/
theorem IsOrder_inv (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Nat)
    (h : IsOrder G op e x n) : IsOrder G op e (inv G op e hinv x) n := by
  obtain ⟨hn0, hne, hmin⟩ := h
  refine ⟨hn0, ?_, ?_⟩
  · rw [← inv_pow G op e x hinv hA hl hr n, hne]
    exact inv_e G op e hinv hA hl hr
  · intro m hm0 hmn hc
    apply hmin m hm0 hmn
    have hc' : inv G op e hinv (pow G op e x m) = e := by
      rw [inv_pow G op e x hinv hA hl hr m]
      exact hc
    calc pow G op e x m
        = inv G op e hinv (inv G op e hinv (pow G op e x m)) :=
            (inv_inv G op e hinv hA hl hr (pow G op e x m)).symm
      _ = inv G op e hinv e := by rw [hc']
      _ = e := inv_e G op e hinv hA hl hr

/-- `ord x⁻¹ = ord x`.  The converse direction is `IsOrder_inv` applied to `x⁻¹`,
    then `inv_inv` to turn `(x⁻¹)⁻¹` back into `x`. -/
theorem IsOrder_inv_iff (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Nat) :
    IsOrder G op e x n ↔ IsOrder G op e (inv G op e hinv x) n := by
  constructor
  · exact IsOrder_inv G op e x hinv hA hl hr n
  · intro h
    have h2 := IsOrder_inv G op e (inv G op e hinv x) hinv hA hl hr n h
    rwa [inv_inv G op e hinv hA hl hr x] at h2


/-- If `x^(2j+1) = e` then `x = (x²)^(j+1)` -- an element of odd order is a square.

    Shorter than going through `x⁻¹`: `(x²)^(j+1) = x^(2j+2) = x^(2j+1) · x`, and
    the first factor is `e`.  So this needs neither inverses nor finiteness, and
    not even the minimality half of `IsOrder` -- just `x^(2j+1) = e`. -/
theorem eq_sq_pow_of_odd (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (j : Nat)
    (h : pow G op e x (2 * j + 1) = e) :
    pow G op e (pow G op e x 2) (j + 1) = x := by
  rw [pow_mul G op e x hA hl (j + 1) 2]
  have harith : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
  rw [harith]
  show op x (pow G op e x (2 * j + 1)) = x
  rw [h]
  exact hr x

/-- The same statement for an element of odd *order*. -/
theorem eq_sq_pow_of_odd_order (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (j : Nat)
    (h : IsOrder G op e x (2 * j + 1)) :
    pow G op e (pow G op e x 2) (j + 1) = x :=
  eq_sq_pow_of_odd G op e x hA hl hr j h.2.1


/-- Conjugation: `conj g x = g⁻¹ x g`. -/
noncomputable def conj (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (g x : G) : G :=
  op (inv G op e hinv g) (op x g)

/-- Conjugation telescopes through powers: `(g⁻¹xg)^k = g⁻¹ x^k g`.

    Induction on `k`; the step works because the `g · g⁻¹` in the middle
    collapses, which is what makes the whole chain of `n` copies reduce.
    `Id_right` is unused. -/
theorem conj_pow (G : Type) (op : BinOp G) (e g x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) :
    ∀ k : Nat, pow G op e (conj G op e hinv g x) k
      = op (inv G op e hinv g) (op (pow G op e x k) g) := by
  intro k
  induction k with
  | zero =>
      show e = op (inv G op e hinv g) (op e g)
      rw [hl g]
      exact (inv_left G op e hinv g).symm
  | succ k ih =>
      show op (op (inv G op e hinv g) (op x g))
             (pow G op e (conj G op e hinv g x) k)
            = op (inv G op e hinv g) (op (op x (pow G op e x k)) g)
      rw [ih,
          ← hA (inv G op e hinv g) (op x g)
              (op (inv G op e hinv g) (op (pow G op e x k) g)),
          ← hA x g (op (inv G op e hinv g) (op (pow G op e x k) g)),
          hA g (inv G op e hinv g) (op (pow G op e x k) g),
          inv_right G op e hinv g,
          hl (op (pow G op e x k) g),
          hA x (pow G op e x k) g]



/-- `(g⁻¹xg)^m = e` forces `x^m = e`: cancel `g⁻¹` on the left, then `g` on the
    right.  This is what carries minimality across. -/
theorem pow_eq_id_of_conj (G : Type) (op : BinOp G) (e g x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (m : Nat)
    (h : pow G op e (conj G op e hinv g x) m = e) : pow G op e x m = e := by
  rw [conj_pow G op e g x hinv hA hl m] at h
  have h1 : op (pow G op e x m) g = g :=
    left_cancellation G op (inv G op e hinv g) (op (pow G op e x m) g) g g e
      hA hl (inv_right G op e hinv g) (h.trans (inv_left G op e hinv g).symm)
  exact right_cancellation G op g (pow G op e x m) e (inv G op e hinv g) e
    hA hr (inv_right G op e hinv g) (h1.trans (hl g).symm)

/-- Conjugation preserves order: `ord (g⁻¹xg) = ord x`.

    The power is `conj_pow` plus `g⁻¹ e g = e`; minimality is
    `pow_eq_id_of_conj` handing the contradiction back to `x`. -/
theorem IsOrder_conj (G : Type) (op : BinOp G) (e g x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Nat)
    (h : IsOrder G op e x n) : IsOrder G op e (conj G op e hinv g x) n := by
  obtain ⟨hn0, hne, hmin⟩ := h
  refine ⟨hn0, ?_, ?_⟩
  · rw [conj_pow G op e g x hinv hA hl n, hne, hl g]
    exact inv_left G op e hinv g
  · intro m hm0 hmn hc
    exact hmin m hm0 hmn
      (pow_eq_id_of_conj G op e g x hinv hA hl hr m hc)



/-- `ab` is the conjugate of `ba` by `b`: `b⁻¹(ba)b = ab`.
    The `b⁻¹b` at the front collapses, leaving `ab`. -/
theorem conj_swap (G : Type) (op : BinOp G) (e a b : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) :
    conj G op e hinv b (op b a) = op a b := by
  show op (inv G op e hinv b) (op (op b a) b) = op a b
  rw [hA (inv G op e hinv b) (op b a) b, hA (inv G op e hinv b) b a,
      inv_left G op e hinv b, hl a]

/-- `ord (ab) = ord (ba)`, even when `ab ≠ ba`.  Immediate from `conj_swap` and
    `IsOrder_conj` -- no new induction. -/
theorem IsOrder_comm (G : Type) (op : BinOp G) (e a b : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (n : Nat)
    (h : IsOrder G op e (op b a) n) : IsOrder G op e (op a b) n := by
  have h2 := IsOrder_conj G op e b (op b a) hinv hA hl hr n h
  rwa [conj_swap G op e a b hinv hA hl] at h2


/-- If `ord x = s·t` then `ord (x^s) = t`.

    `(x^s)^t = x^(st) = e` gives the power.  Minimality transfers because
    `(x^s)^m = x^(sm)`, and `0 < m < t` with `s > 0` puts `sm` strictly between
    `0` and `st`, contradicting minimality for `x`.

    No inverses needed -- only `Assoc` and `Id_left`, via `pow_mul`. -/
theorem IsOrder_pow (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) (s t : Nat)
    (h : IsOrder G op e x (s * t)) : IsOrder G op e (pow G op e x s) t := by
  obtain ⟨hn0, hne, hmin⟩ := h
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · subst hs0; simp at hn0
    · exact hs0
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · subst ht0; simp at hn0
    · exact ht0
  refine ⟨ht, ?_, ?_⟩
  · rw [pow_mul G op e x hA hl t s]
    exact hne
  · intro m hm0 hmt hc
    rw [pow_mul G op e x hA hl m s] at hc
    exact hmin (s * m) (Nat.mul_pos hs hm0) ((Nat.mul_lt_mul_left hs).mpr hmt) hc


/-- `x = x⁻¹` exactly when `x² = e`. -/
theorem self_inv_iff_pow_two (G : Type) (op : BinOp G) (e x : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e)
    (hr : Id_right G op e) :
    x = inv G op e hinv x ↔ pow G op e x 2 = e := by
  constructor
  · intro h
    show op x (pow G op e x 1) = e
    rw [pow_one G op e x hr]
    calc op x x = op x (inv G op e hinv x) := by rw [← h]
      _ = e := inv_right G op e hinv x
  · intro h
    have hsq : pow G op e x 2 = op x x := by
      show op x (pow G op e x 1) = op x x
      rw [pow_one G op e x hr]
    have hx : op x x = e := by rw [← hsq]; exact h
    exact eq_inv G op e hinv hA hl hr x x hx

/-- An element that is its own inverse and is not the identity has order 2.
    This is the conclusion the counting argument aims at. -/
theorem IsOrder_two_of_self_inv (G : Type) (op : BinOp G) (e x : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e)
    (hr : Id_right G op e) (hne : x ≠ e) (h : x = inv G op e hinv x) :
    IsOrder G op e x 2 := by
  rcases (pow_two_eq_id_iff G op e x).mp
      ((self_inv_iff_pow_two G op e x hinv hA hl hr).mp h) with h1 | h2
  · exact absurd ((order1iffidentity G op e x hr).mp h1) hne
  · exact h2




/-- If every element squares to the identity then the group is abelian.

    `x² = e` means every element is its own inverse, so
    `ab = (ab)⁻¹ = b⁻¹a⁻¹ = ba`.  No finiteness needed. -/
theorem comm_of_self_inv (G : Type) (op : BinOp G) (e : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e)
    (h : ∀ x : G, op x x = e) : Comm G op := by
  have hsi : ∀ x : G, x = inv G op e hinv x :=
    fun x => eq_inv G op e hinv hA hl hr x x (h x)
  intro a b
  calc op a b = inv G op e hinv (op a b) := hsi (op a b)
    _ = op (inv G op e hinv b) (inv G op e hinv a) :=
        inv_op G op e hinv hA hl hr a b
    _ = op b a := by rw [← hsi b, ← hsi a]




/-- If `ord x = n` then `x⁰, x¹, …, x^(n-1)` are pairwise distinct.

    If `x^j = x^k` with `j < k < n`, split `x^k = x^j · x^(k-j)` and cancel `x^j`
    to get `x^(k-j) = e` with `0 < k-j < n`, contradicting minimality.
    No finiteness needed -- this is about `IsOrder` alone. -/
theorem pow_inj_of_IsOrder (G : Type) (op : BinOp G) (e x : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e)
    (hr : Id_right G op e) (n : Nat) (h : IsOrder G op e x n) :
    ∀ j k : Nat, j < n → k < n → pow G op e x j = pow G op e x k → j = k := by
  obtain ⟨hn0, hne, hmin⟩ := h
  have key : ∀ j k : Nat, j < k → k < n →
      pow G op e x j = pow G op e x k → False := by
    intro j k hjk hkn heq
    have hsplit : pow G op e x k
        = op (pow G op e x j) (pow G op e x (k - j)) := by
      have hpa := pow_add G op e x hA hl (k - j) j
      have hjk' : j + (k - j) = k := by omega
      rw [hjk'] at hpa
      exact hpa
    have h2 : op (pow G op e x j) (pow G op e x (k - j))
        = op (pow G op e x j) e := by
      rw [← hsplit, ← heq]
      exact (hr _).symm
    have h3 : pow G op e x (k - j) = e :=
      left_cancellation G op (pow G op e x j) (pow G op e x (k - j)) e
        (inv G op e hinv (pow G op e x j)) e hA hl
        (inv_left G op e hinv (pow G op e x j)) h2
    exact hmin (k - j) (by omega) (by omega) h3
  intro j k hjn hkn heq
  rcases Nat.lt_trichotomy j k with hlt | hjk | hgt
  · exact (key j k hlt hkn heq).elim
  · exact hjk
  · exact (key k j hgt hjn heq.symm).elim




/-- Every power of the identity is the identity. -/
theorem pow_id (G : Type) (op : BinOp G) (e : G) (hl : Id_left G op e) :
    ∀ q : Nat, pow G op e e q = e := by
  intro q
  induction q with
  | zero => rfl
  | succ k ih =>
      show op e (pow G op e e k) = e
      rw [ih]
      exact hl e

/-- Division algorithm for exponents: `x^m = x^(m mod n)` when `ord x = n`.

    `m = n·(m/n) + m%n`, and the `x^(n·(m/n))` factor is `(x^n)^(m/n) = e^(m/n) = e`.
    Together with `pow_inj_of_IsOrder` this says the powers of `x` are exactly
    the `n` distinct elements `x⁰, …, x^(n-1)`.  Needs no inverses. -/
theorem pow_mod (G : Type) (op : BinOp G) (e x : G)
    (hA : Assoc G op) (hl : Id_left G op e) (n : Nat)
    (h : IsOrder G op e x n) (m : Nat) :
    pow G op e x m = pow G op e x (m % n) := by
  have hpa := pow_add G op e x hA hl (m % n) (n * (m / n))
  rw [Nat.div_add_mod m n] at hpa
  rw [hpa, ← pow_mul G op e x hA hl (m / n) n, h.2.1,
      pow_id G op e hl (m / n), hl]




/- ### Generic helpers (no group theory) -/

/-- Mapping an injective-on-`l` function over a `Nodup` list keeps it `Nodup`.
    Core has no `List.nodup_map`, so it is proved here by induction. -/
theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ l : List α, l.Nodup → (∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) →
      (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
      intro hnd hinj
      rw [List.nodup_cons] at hnd
      obtain ⟨hat, hndt⟩ := hnd
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨b, hbt, hfb⟩ := hmem
        have hab : a = b :=
          hinj a b List.mem_cons_self (List.mem_cons_of_mem a hbt) hfb.symm
        exact hat (hab ▸ hbt)
      · exact ih hndt (fun a' b' ha' hb' =>
          hinj a' b' (List.mem_cons_of_mem a ha') (List.mem_cons_of_mem a hb'))

/-- Well-ordering for `Nat`: a satisfiable predicate has a least witness.
    Core has no `Nat.find`, so this stands in for it.  Strong induction plus a
    classical case split on whether a smaller witness exists. -/
theorem exists_least (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  obtain ⟨N, hN⟩ := h
  induction N using Nat.strongRecOn with
  | _ N ih =>
      rcases Classical.em (∃ m, m < N ∧ P m) with hlt | hlt
      · obtain ⟨m, hmN, hm⟩ := hlt
        exact ih m hmN hm
      · exact ⟨N, hN, fun m hm hPm => hlt ⟨m, hm, hPm⟩⟩



/- ### Finiteness -/

/-- `l` enumerates `G`: no repeats, and every element occurs.  `l.length` is `|G|`. -/
structure IsEnum (G : Type) (l : List G) : Prop where
  nodup : l.Nodup
  complete : ∀ g : G, g ∈ l

theorem pow_sub_eq_id (G : Type) (op : BinOp G) (e x : G) (hinv : HasInverses G op e)
    (hA : Assoc G op) (hl : Id_left G op e) (hr : Id_right G op e) (j k : Nat)
    (hjk : j ≤ k) (heq : pow G op e x j = pow G op e x k) :
    pow G op e x (k - j) = e := by
  have hpa := pow_add G op e x hA hl (k - j) j
  have hjk' : j + (k - j) = k := by omega
  rw [hjk'] at hpa
  have h2 : op (pow G op e x j) (pow G op e x (k - j))
      = op (pow G op e x j) e := by
    rw [← hpa, ← heq]
    exact (hr _).symm
  exact left_cancellation G op (pow G op e x j) (pow G op e x (k - j)) e
    (inv G op e hinv (pow G op e x j)) e hA hl
    (inv_left G op e hinv (pow G op e x j)) h2

/-- Pigeonhole: in a finite group some positive power of `x`, of exponent at most
    `|G|`, is the identity. -/
theorem exists_pow_eq_id (G : Type) (op : BinOp G) (e x : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e)
    (hr : Id_right G op e) (l : List G) (henum : IsEnum G l) :
    ∃ m, 0 < m ∧ m ≤ l.length ∧ pow G op e x m = e := by
  rcases Classical.em (∃ j k, j < l.length + 1 ∧ k < l.length + 1 ∧ j < k ∧
      pow G op e x j = pow G op e x k) with hdup | hnodup
  · obtain ⟨j, k, hjN, hkN, hjk, heq⟩ := hdup
    exact ⟨k - j, by omega, by omega,
      pow_sub_eq_id G op e x hinv hA hl hr j k (by omega) heq⟩
  · exfalso
    have hinj : ∀ a b, a ∈ List.range (l.length + 1) →
        b ∈ List.range (l.length + 1) →
        pow G op e x a = pow G op e x b → a = b := by
      intro a b ha hb hab
      rw [List.mem_range] at ha hb
      rcases Nat.lt_trichotomy a b with hlt | he | hgt
      · exact absurd ⟨a, b, ha, hb, hlt, hab⟩ hnodup
      · exact he
      · exact absurd ⟨b, a, hb, ha, hgt, hab.symm⟩ hnodup
    have hnd := nodup_map_of_inj (pow G op e x) (List.range (l.length + 1))
      List.nodup_range hinj
    have hsub : (List.range (l.length + 1)).map (pow G op e x) ⊆ l :=
      fun y _ => henum.complete y
    have hle := List.Nodup.length_le_of_subset hnd hsub
    rw [List.length_map, List.length_range] at hle
    omega

/-- Every element of a finite group has an order, and it is at most `|G|`. -/
theorem exists_IsOrder (G : Type) (op : BinOp G) (e x : G)
    (hinv : HasInverses G op e) (hA : Assoc G op) (hl : Id_left G op e)
    (hr : Id_right G op e) (l : List G) (henum : IsEnum G l) :
    ∃ n, IsOrder G op e x n ∧ n ≤ l.length := by
  obtain ⟨m, hm0, hmN, hm⟩ := exists_pow_eq_id G op e x hinv hA hl hr l henum
  obtain ⟨n, ⟨hn0, hne⟩, hmin⟩ :=
    exists_least (fun k => 0 < k ∧ pow G op e x k = e) ⟨m, hm0, hm⟩
  refine ⟨n, ⟨hn0, hne, ?_⟩, ?_⟩
  · intro k hk0 hkn hc
    exact hmin k hkn ⟨hk0, hc⟩
  · have hnm : ¬ (m < n) := fun hmn => hmin m hmn ⟨hm0, hm⟩
    omega



/- ### The cyclic group `Z/n`, as `Fin n` under addition -/

/-- Core has no `Fin.add_assoc` or `Fin.add_comm`, so they are proved here. -/
theorem fin_add_assoc (n : Nat) (a b c : Fin n) : a + b + c = a + (b + c) := by
  apply Fin.ext
  simp only [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem fin_add_comm (n : Nat) (a b : Fin n) : a + b = b + a := by
  apply Fin.ext
  simp only [Fin.val_add, Nat.add_comm]

theorem fin_add_neg (n : Nat) [NeZero n] (a : Fin n) : a + -a = 0 := by
  apply Fin.ext
  simp [Fin.add_def, Fin.neg_def]

theorem fin_neg_add (n : Nat) [NeZero n] (a : Fin n) : -a + a = 0 := by
  apply Fin.ext
  simp [Fin.add_def, Fin.neg_def]

def ZMod (n : Nat) : BinOp (Fin n) := fun a b => a + b

theorem ZMod_assoc (n : Nat) : Assoc (Fin n) (ZMod n) :=
  fun a b c => (fin_add_assoc n a b c).symm

theorem ZMod_id_left (n : Nat) [NeZero n] : Id_left (Fin n) (ZMod n) 0 := Fin.zero_add

theorem ZMod_id_right (n : Nat) [NeZero n] : Id_right (Fin n) (ZMod n) 0 := Fin.add_zero

theorem ZMod_comm (n : Nat) : Comm (Fin n) (ZMod n) := fin_add_comm n

theorem ZMod_hasInverses (n : Nat) [NeZero n] : HasInverses (Fin n) (ZMod n) 0 :=
  fun a => ⟨-a, fin_add_neg n a, fin_neg_add n a⟩



/- ### Dihedral groups -/

/-- `Dih n` is the dihedral group of order `2n`.  `(a, false)` is the rotation
    `r^a`; `(a, true)` is `r^a s`, the reflection composed with a rotation. -/
structure Dih (n : Nat) : Type where
  rot : Fin n
  flip : Bool
  deriving DecidableEq

/-- `(r^a s^i)(r^b s^j) = r^(a ± b) s^(i xor j)`, the sign depending on `i`. -/
def Dih.mul (n : Nat) : BinOp (Dih n) :=
  fun x y => ⟨x.rot + (if x.flip then -y.rot else y.rot), xor x.flip y.flip⟩

def Dih.one (n : Nat) [NeZero n] : Dih n := ⟨0, false⟩




theorem fin_neg_neg (n : Nat) [NeZero n] (a : Fin n) : - -a = a :=
  (Unique_inv (Fin n) (ZMod n) (-a) (- -a) a 0 (ZMod_assoc n)
    (ZMod_id_left n) (ZMod_id_right n) (fin_add_neg n a) (fin_add_neg n (-a))).symm

theorem fin_neg_add_distrib (n : Nat) [NeZero n] (a b : Fin n) :
    -(a + b) = -b + -a := by
  have hr : ZMod n (a + b) (-b + -a) = 0 := by
    show (a + b) + (-b + -a) = 0
    rw [fin_add_assoc, ← fin_add_assoc n b (-b) (-a), fin_add_neg,
        Fin.zero_add, fin_add_neg]
  exact (Unique_inv (Fin n) (ZMod n) (a + b) (-b + -a) (-(a + b)) 0
    (ZMod_assoc n) (ZMod_id_left n) (ZMod_id_right n)
    (fin_neg_add n (a + b)) hr)

theorem fin_add_left_comm (n : Nat) (a b c : Fin n) : a + (b + c) = b + (a + c) := by
  rw [← fin_add_assoc, ← fin_add_assoc, fin_add_comm n a b]

/-- Associativity of the dihedral product.  Eight cases on the three flips; the
    ones with a leading reflection need `fin_neg_add_distrib` and commutativity
    to push the negation through. -/
theorem Dih_assoc (n : Nat) [NeZero n] : Assoc (Dih n) (Dih.mul n) := by
  intro a b c
  obtain ⟨ar, af⟩ := a
  obtain ⟨br, bf⟩ := b
  obtain ⟨cr, cf⟩ := c
  cases af <;> cases bf <;> cases cf <;>
    simp [Dih.mul, fin_add_assoc, fin_neg_neg, fin_neg_add_distrib,
          fin_add_comm, fin_add_left_comm]



theorem fin_neg_zero (n : Nat) [NeZero n] : -(0 : Fin n) = 0 := by
  apply Fin.ext
  simp [Fin.neg_def]

theorem Dih_id_left (n : Nat) [NeZero n] :
    Id_left (Dih n) (Dih.mul n) (Dih.one n) := by
  intro a
  obtain ⟨ar, af⟩ := a
  simp [Dih.mul, Dih.one]

theorem Dih_id_right (n : Nat) [NeZero n] :
    Id_right (Dih n) (Dih.mul n) (Dih.one n) := by
  intro a
  obtain ⟨ar, af⟩ := a
  cases af <;> simp [Dih.mul, Dih.one, fin_neg_zero]

def Dih.inv (n : Nat) [NeZero n] (x : Dih n) : Dih n :=
  ⟨if x.flip then x.rot else -x.rot, x.flip⟩

/-- `(r^a)⁻¹ = r^(-a)`, and every reflection is its own inverse. -/
theorem Dih_hasInverses (n : Nat) [NeZero n] :
    HasInverses (Dih n) (Dih.mul n) (Dih.one n) := by
  intro a
  obtain ⟨ar, af⟩ := a
  refine ⟨Dih.inv n ⟨ar, af⟩, ?_, ?_⟩ <;>
    cases af <;>
    simp [right_inv_of, left_inv_of, Dih.mul, Dih.one, Dih.inv,
          fin_add_neg, fin_neg_add]


end Groups
