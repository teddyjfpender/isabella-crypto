# Isabelle/HOL Datatypes Reference

## Algebraic Datatypes

### Basic Datatype Definition

```isabelle
datatype color = Red | Green | Blue

datatype nat' = Zero | Suc nat'

datatype 'a option' = None' | Some' 'a
```

### Datatype with Multiple Constructors

```isabelle
datatype expr =
    Const int
  | Var string
  | Add expr expr
  | Mul expr expr
  | Neg expr

(* Using the datatype *)
definition example_expr :: expr where
  "example_expr = Add (Const 1) (Mul (Var ''x'') (Const 2))"
```

### Parameterized Datatypes

```isabelle
(* Single type parameter *)
datatype 'a list' = Nil' | Cons' 'a "'a list'"

(* Multiple type parameters *)
datatype ('a, 'b) either = Left 'a | Right 'b

(* Nested parameterized types *)
datatype 'a tree =
    Leaf
  | Node "'a tree" 'a "'a tree"
```

### Mutual Recursion

```isabelle
datatype 'a forest = Empty | Trees "'a tree_list"
     and 'a tree_list = Nil_trees | Cons_trees "'a tree" "'a tree_list"
     and 'a tree = Leaf' 'a | Node' "'a forest"
```

### Generated Theorems

When you define a datatype, Isabelle automatically generates:

```isabelle
datatype nat' = Zero | Suc nat'

(* Distinctness: constructors produce different values *)
thm nat'.distinct  (* Zero \<noteq> Suc n *)

(* Injectivity: equal results mean equal arguments *)
thm nat'.inject    (* Suc n = Suc m \<longleftrightarrow> n = m *)

(* Exhaustiveness: every value matches some constructor *)
thm nat'.exhaust   (* y = Zero \<or> (\<exists>n. y = Suc n) *)

(* Induction principle *)
thm nat'.induct    (* P Zero \<Longrightarrow> (\<forall>n. P n \<longrightarrow> P (Suc n)) \<Longrightarrow> P x *)

(* Case analysis *)
thm nat'.case      (* case rules *)

(* Size function *)
thm nat'.size      (* size_nat' definitions *)
```

## Primitive Recursion (primrec)

### Basic primrec

`primrec` defines functions by primitive recursion over a datatype:

```isabelle
primrec add' :: "nat' \<Rightarrow> nat' \<Rightarrow> nat'" where
  "add' Zero n = n"
| "add' (Suc m) n = Suc (add' m n)"

primrec length' :: "'a list' \<Rightarrow> nat" where
  "length' Nil' = 0"
| "length' (Cons' _ xs) = 1 + length' xs"
```

### primrec over Multiple Arguments

```isabelle
primrec zip' :: "'a list' \<Rightarrow> 'b list' \<Rightarrow> ('a \<times> 'b) list'" where
  "zip' Nil' _ = Nil'"
| "zip' (Cons' x xs) ys = (case ys of
      Nil' \<Rightarrow> Nil'
    | Cons' y ys' \<Rightarrow> Cons' (x, y) (zip' xs ys'))"
```

### primrec Restrictions

- Must have exactly one equation per constructor
- Recursive calls must be on constructor arguments
- Cannot do nested recursion directly

```isabelle
(* This WORKS - direct structural recursion *)
primrec sum_list' :: "nat list' \<Rightarrow> nat" where
  "sum_list' Nil' = 0"
| "sum_list' (Cons' x xs) = x + sum_list' xs"

(* This FAILS - non-structural recursion *)
(* primrec bad :: "nat \<Rightarrow> nat" where
     "bad 0 = 0"
   | "bad n = bad (n - 1)"  -- n-1 is not a constructor argument *)
```

## General Recursion (fun)

### Basic fun Definition

`fun` allows more flexible pattern matching:

```isabelle
fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

fun ackermann :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ackermann 0 n = Suc n"
| "ackermann (Suc m) 0 = ackermann m 1"
| "ackermann (Suc m) (Suc n) = ackermann m (ackermann (Suc m) n)"
```

### Pattern Matching with fun

```isabelle
fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "interleave [] ys = ys"
| "interleave xs [] = xs"
| "interleave (x # xs) (y # ys) = x # y # interleave xs ys"

fun flatten :: "'a tree \<Rightarrow> 'a list" where
  "flatten Leaf = []"
| "flatten (Node l x r) = flatten l @ [x] @ flatten r"
```

### Overlapping Patterns

```isabelle
(* fun handles overlapping patterns - first match wins *)
fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup _ [] = None"
| "lookup k ((k', v) # rest) = (if k = k' then Some v else lookup k rest)"
```

### Sequential vs Simultaneous

```isabelle
(* Sequential: patterns tried in order *)
fun take' :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take' _ [] = []"
| "take' 0 _ = []"
| "take' (Suc n) (x # xs) = x # take' n xs"

(* The second clause overlaps with the third, but order resolves it *)
```

## Complex Recursion (function)

### Manual Termination Proofs

When `fun` cannot prove termination automatically:

```isabelle
function gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd a 0 = a"
| "gcd a b = gcd b (a mod b)"
by pat_completeness auto

termination gcd
  apply (relation "measure (\<lambda>(a, b). b)")
  apply auto
  done
```

### Partial Functions

```isabelle
partial_function (option) collatz :: "nat \<Rightarrow> nat option" where
  "collatz n = (if n \<le> 1 then Some n
                else if even n then collatz (n div 2)
                else collatz (3 * n + 1))"
```

### Nested Recursion

```isabelle
function nested :: "nat \<Rightarrow> nat" where
  "nested 0 = 0"
| "nested (Suc n) = nested (nested n)"
by pat_completeness auto

termination
  sorry  (* Requires careful termination argument *)
```

## Records

### Basic Record Definition

```isabelle
record point =
  x_coord :: int
  y_coord :: int

(* Creating records *)
definition origin :: point where
  "origin = \<lparr> x_coord = 0, y_coord = 0 \<rparr>"

definition p1 :: point where
  "p1 = \<lparr> x_coord = 3, y_coord = 4 \<rparr>"
```

### Record Access and Update

```isabelle
(* Field access *)
definition get_x :: "point \<Rightarrow> int" where
  "get_x p = x_coord p"

(* Field update *)
definition move_right :: "point \<Rightarrow> point" where
  "move_right p = p \<lparr> x_coord := x_coord p + 1 \<rparr>"

(* Multiple field update *)
definition set_coords :: "point \<Rightarrow> int \<Rightarrow> int \<Rightarrow> point" where
  "set_coords p a b = p \<lparr> x_coord := a, y_coord := b \<rparr>"
```

### Record Extension

```isabelle
record colored_point = point +
  color :: color

definition red_origin :: colored_point where
  "red_origin = \<lparr> x_coord = 0, y_coord = 0, color = Red \<rparr>"

(* Inherited field access works *)
lemma "x_coord red_origin = 0"
  unfolding red_origin_def by simp
```

### Record Patterns in Functions

```isabelle
fun distance_from_origin :: "point \<Rightarrow> real" where
  "distance_from_origin \<lparr> x_coord = x, y_coord = y \<rparr> =
     sqrt (real_of_int (x^2 + y^2))"

(* With record extension (using more syntax) *)
fun point_to_string :: "point \<Rightarrow> string" where
  "point_to_string p = ''('' @ show (x_coord p) @ '', '' @ show (y_coord p) @ '')''"
```

### Record Theorems

```isabelle
record vec2 =
  vx :: int
  vy :: int

(* Isabelle generates: *)
thm vec2.simps        (* Constructor/selector equations *)
thm vec2.iffs         (* Equality in terms of fields *)
thm vec2.update_convs (* Update equations *)

(* Example lemmas *)
lemma "vx \<lparr> vx = a, vy = b \<rparr> = a" by simp
lemma "\<lparr> vx = a, vy = b \<rparr> \<lparr> vx := c \<rparr> = \<lparr> vx = c, vy = b \<rparr>" by simp
```

## Advanced Datatype Features

### Nested Datatypes

```isabelle
datatype 'a nested = Base 'a | Nest "'a list nested"

(* Functions over nested types require care *)
fun depth :: "'a nested \<Rightarrow> nat" where
  "depth (Base _) = 0"
| "depth (Nest n) = Suc (depth n)"
```

### Quotient Types

```isabelle
(* Define equivalence relation *)
definition int_rel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "int_rel p q = (fst p + snd q = snd p + fst q)"

(* Quotient type *)
quotient_type int' = "nat \<times> nat" / int_rel
  by (auto simp: int_rel_def intro!: equivpI reflpI sympI transpI)
```

### Codatatypes (Coinductive)

```isabelle
codatatype 'a stream = SCons 'a "'a stream"

(* Corecursive function *)
primcorec nats_from :: "nat \<Rightarrow> nat stream" where
  "nats_from n = SCons n (nats_from (Suc n))"

primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a stream \<Rightarrow> 'b stream" where
  "smap f s = SCons (f (shd s)) (smap f (stl s))"
```

## Function Packages Comparison

| Feature | `primrec` | `fun` | `function` |
|---------|-----------|-------|------------|
| Pattern matching | One per constructor | Arbitrary | Arbitrary |
| Overlapping | No | Yes (sequential) | Yes (sequential) |
| Termination | Automatic | Auto-proved | Manual |
| Complexity | Simple | Medium | Full control |
| Generated theorems | `.simps` | `.simps` | `.simps`, `.cases` |

## Code Generation for Datatypes

```isabelle
datatype 'a mylist = MNil | MCons 'a "'a mylist"

fun mlength :: "'a mylist \<Rightarrow> nat" where
  "mlength MNil = 0"
| "mlength (MCons _ xs) = Suc (mlength xs)"

(* Export to Haskell *)
export_code mlength in Haskell
```

## Common Patterns

### Accumulator Pattern

```isabelle
fun rev_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_acc [] acc = acc"
| "rev_acc (x # xs) acc = rev_acc xs (x # acc)"

definition fast_rev :: "'a list \<Rightarrow> 'a list" where
  "fast_rev xs = rev_acc xs []"
```

### Mutual Recursion with fun

```isabelle
fun even' :: "nat \<Rightarrow> bool"
  and odd' :: "nat \<Rightarrow> bool" where
  "even' 0 = True"
| "even' (Suc n) = odd' n"
| "odd' 0 = False"
| "odd' (Suc n) = even' n"
```

### Well-Founded Recursion

```isabelle
function quicksort :: "('a::linorder) list \<Rightarrow> 'a list" where
  "quicksort [] = []"
| "quicksort (x # xs) =
     quicksort [y \<leftarrow> xs. y < x] @ [x] @ quicksort [y \<leftarrow> xs. y \<ge> x]"
by pat_completeness auto

termination quicksort
  apply (relation "measure length")
  apply auto
  done
```

## Lemmas about Datatypes

### Induction over Datatypes

```isabelle
datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun size_tree :: "'a tree \<Rightarrow> nat" where
  "size_tree Leaf = 0"
| "size_tree (Node l _ r) = 1 + size_tree l + size_tree r"

lemma size_tree_nonneg: "size_tree t \<ge> 0"
  by (induction t) auto
```

### Case Analysis

```isabelle
lemma tree_cases:
  "(t = Leaf \<longrightarrow> P) \<longrightarrow> (\<forall>l x r. t = Node l x r \<longrightarrow> P) \<longrightarrow> P"
  by (cases t) auto
```

## Complete Example

```isabelle
theory Datatypes_Example
  imports Main
begin

(* Binary search tree *)
datatype 'a bst = Empty | BSTNode "'a bst" 'a "'a bst"

fun bst_insert :: "'a::linorder \<Rightarrow> 'a bst \<Rightarrow> 'a bst" where
  "bst_insert x Empty = BSTNode Empty x Empty"
| "bst_insert x (BSTNode l y r) =
     (if x < y then BSTNode (bst_insert x l) y r
      else if x > y then BSTNode l y (bst_insert x r)
      else BSTNode l y r)"

fun bst_member :: "'a::linorder \<Rightarrow> 'a bst \<Rightarrow> bool" where
  "bst_member _ Empty = False"
| "bst_member x (BSTNode l y r) =
     (if x < y then bst_member x l
      else if x > y then bst_member x r
      else True)"

fun inorder :: "'a bst \<Rightarrow> 'a list" where
  "inorder Empty = []"
| "inorder (BSTNode l x r) = inorder l @ [x] @ inorder r"

(* Key lemma: insert preserves membership *)
lemma bst_insert_member:
  "bst_member x (bst_insert y t) = (x = y \<or> bst_member x t)"
  by (induction t) auto

end
```
