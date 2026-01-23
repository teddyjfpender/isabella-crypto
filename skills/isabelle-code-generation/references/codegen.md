# Isabelle/HOL Code Generation Reference

## Overview

Isabelle's code generator translates HOL specifications into executable code. The key principle is that definitions in HOL are translated to function definitions in the target language.

## Basic Code Export

### export_code Command

```isabelle
theory CodeGen_Example
  imports Main
begin

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1"
| "factorial (Suc n) = Suc n * factorial n"

(* Export to Haskell *)
export_code factorial in Haskell

(* Export to file *)
export_code factorial in Haskell module_name Factorial file_prefix factorial

(* Multiple functions *)
export_code factorial fib gcd in Haskell module_name MyFunctions

end
```

### Target Languages

```isabelle
export_code f in Haskell   (* Haskell *)
export_code f in Scala     (* Scala *)
export_code f in SML       (* Standard ML *)
export_code f in OCaml     (* OCaml *)
```

## Module Organization

### module_name

```isabelle
(* Single module *)
export_code factorial
  in Haskell module_name Factorial

(* Qualified module name *)
export_code factorial
  in Haskell module_name "Math.Factorial"
```

### file_prefix

```isabelle
(* Output to factorial.hs *)
export_code factorial
  in Haskell module_name Factorial
  file_prefix factorial

(* Full path *)
export_code factorial
  in Haskell module_name Factorial
  file_prefix "generated/factorial"
```

### Multiple Modules

```isabelle
(* Separate modules for organization *)
export_code type1_funs
  in Haskell module_name "MyLib.Type1"

export_code type2_funs
  in Haskell module_name "MyLib.Type2"
```

## Code_Target_Numeral

### Why Use It

By default, Isabelle generates Peano numerals (inefficient). `Code_Target_Numeral` uses native integers:

```isabelle
theory Efficient_Numbers
  imports Main "HOL-Library.Code_Target_Numeral"
begin

(* Now uses Integer instead of Nat *)
fun sum_to :: "nat \<Rightarrow> nat" where
  "sum_to 0 = 0"
| "sum_to (Suc n) = Suc n + sum_to n"

export_code sum_to in Haskell

end
```

### Generated Code Comparison

Without Code_Target_Numeral:
```haskell
data Nat = Zero | Suc Nat
sum_to Zero = Zero
sum_to (Suc n) = plus (Suc n) (sum_to n)
```

With Code_Target_Numeral:
```haskell
sum_to :: Integer -> Integer
sum_to n = if n == 0 then 0 else n + sum_to (n - 1)
```

### Integer vs Natural

```isabelle
imports "HOL-Library.Code_Target_Numeral"

(* nat becomes Integer (non-negative) *)
definition nat_fun :: "nat \<Rightarrow> nat" where
  "nat_fun n = n + 1"

(* int becomes Integer *)
definition int_fun :: "int \<Rightarrow> int" where
  "int_fun i = i * 2"
```

## Code Equations

### Default Equations

Function definitions automatically become code equations:

```isabelle
fun length' :: "'a list \<Rightarrow> nat" where
  "length' [] = 0"
| "length' (_ # xs) = Suc (length' xs)"

(* These equations are used for code generation *)
```

### Custom Code Equations

```isabelle
definition slow_rev :: "'a list \<Rightarrow> 'a list" where
  "slow_rev xs = foldr (\<lambda>x acc. acc @ [x]) xs []"

(* More efficient implementation *)
fun fast_rev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "fast_rev_aux [] acc = acc"
| "fast_rev_aux (x # xs) acc = fast_rev_aux xs (x # acc)"

(* Replace code equation *)
lemma slow_rev_code [code]:
  "slow_rev xs = fast_rev_aux xs []"
  unfolding slow_rev_def
  by (induction xs) auto
```

### Code Attribute

```isabelle
(* Mark lemma as code equation *)
lemma my_code_eq [code]:
  "f x = efficient_impl x"
  by proof

(* Delete existing code equation *)
declare old_equation [code del]
```

### Abstract Functions

```isabelle
(* When you can't/won't implement directly *)
definition abstract_op :: "complex_type \<Rightarrow> complex_type" where
  "abstract_op x = ..."

(* Provide code equation *)
lemma abstract_op_code [code]:
  "abstract_op (Constructor args) = Constructor (transformed args)"
  by (simp add: abstract_op_def)
```

## Datatypes and Code Generation

### Standard Datatypes

```isabelle
datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun tree_size :: "'a tree \<Rightarrow> nat" where
  "tree_size Leaf = 0"
| "tree_size (Node l _ r) = 1 + tree_size l + tree_size r"

export_code tree_size in Haskell
```

### Generated Haskell

```haskell
data Tree a = Leaf | Node (Tree a) a (Tree a)

tree_size :: Tree a -> Integer
tree_size Leaf = 0
tree_size (Node l _ r) = 1 + tree_size l + tree_size r
```

### Records

```isabelle
record point =
  x_coord :: int
  y_coord :: int

definition move :: "point \<Rightarrow> int \<Rightarrow> point" where
  "move p dx = p \<lparr> x_coord := x_coord p + dx \<rparr>"

export_code move in Haskell
```

## Code Printing and Serialization

### code_printing

Map Isabelle types/constants to target language constructs:

```isabelle
(* Use Haskell's built-in Bool *)
code_printing
  type_constructor bool \<rightharpoonup> (Haskell) "Bool"
| constant True \<rightharpoonup> (Haskell) "True"
| constant False \<rightharpoonup> (Haskell) "False"

(* Use Haskell library function *)
code_printing
  constant "List.length" \<rightharpoonup> (Haskell) "length"
```

### code_identifier

Control generated identifiers:

```isabelle
code_identifier
  constant my_long_function_name \<rightharpoonup> (Haskell) "myFun"
| type_constructor my_type \<rightharpoonup> (Haskell) "MyT"
```

### code_reserved

Reserve identifiers (prevent name clashes):

```isabelle
code_reserved Haskell data type class where
```

## Abstract Types

### Hiding Implementation

```isabelle
(* Implementation type *)
typedef pos_int = "{n::int. n > 0}"
  by (rule exI[of _ 1]) simp

(* Setup code type *)
setup_lifting type_definition_pos_int

(* Lift operations *)
lift_definition mk_pos :: "int \<Rightarrow> pos_int option" is
  "\<lambda>n. if n > 0 then Some n else None"
  by auto

lift_definition pos_val :: "pos_int \<Rightarrow> int" is "\<lambda>x. x" .

(* Code setup for abstract type *)
code_datatype mk_pos

lemma pos_val_code [code]:
  "pos_val (mk_pos n) = (if n > 0 then n else undefined)"
  by transfer auto
```

### Using setup_lifting

```isabelle
typedef my_abs = "{x::int. P x}"
  by proof

setup_lifting type_definition_my_abs

(* Now can use lift_definition *)
lift_definition my_op :: "my_abs \<Rightarrow> my_abs \<Rightarrow> my_abs" is
  "\<lambda>x y. x + y"
  by proof
```

## Partial Functions

### Handling Undefined

```isabelle
(* This won't generate code (partial) *)
definition partial_hd :: "'a list \<Rightarrow> 'a" where
  "partial_hd (x # _) = x"

(* Total version with option *)
definition total_hd :: "'a list \<Rightarrow> 'a option" where
  "total_hd [] = None"
| "total_hd (x # _) = Some x"

export_code total_hd in Haskell  (* Works *)
```

### code_abort

```isabelle
(* Mark as aborting (generates error) *)
definition must_be_nonempty :: "'a list \<Rightarrow> 'a" where
  "must_be_nonempty xs = hd xs"

code_abort must_be_nonempty

(* Generated code will throw error if called *)
```

## Testing Generated Code

### Checking Code

```isabelle
(* Just check it compiles *)
export_code my_fun checking Haskell

(* Export and compile *)
export_code my_fun in Haskell file "test.hs"
```

### value Command

```isabelle
(* Evaluate using code generator *)
value "factorial 10"
(* Result: 3628800 *)

value "map (\<lambda>x. x * 2) [1,2,3,4,5]"
(* Result: [2, 4, 6, 8, 10] *)
```

## Common Issues

### Non-Executable Definitions

```isabelle
(* FAILS: uses non-computable SOME *)
definition bad :: "nat set \<Rightarrow> nat" where
  "bad S = (SOME x. x \<in> S)"

(* WORKS: explicit implementation *)
definition good :: "nat list \<Rightarrow> nat option" where
  "good [] = None"
| "good (x # _) = Some x"
```

### Type Class Issues

```isabelle
(* Need instance for code generation *)
instantiation mytype :: equal
begin
  definition "equal_mytype x y = ..."
  instance by standard auto
end
```

### Missing Code Equations

```isabelle
(* Check code equations *)
code_thms my_function

(* If missing, provide one *)
lemma my_function_code [code]:
  "my_function args = implementation"
  by proof
```

## Advanced Topics

### Refinement

```isabelle
(* Abstract specification *)
definition spec :: "nat \<Rightarrow> nat" where
  "spec n = (SOME m. m * m \<le> n \<and> n < (m+1)*(m+1))"

(* Concrete implementation *)
fun impl :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "impl n m = (if (m+1)*(m+1) \<le> n then impl n (m+1) else m)"

(* Prove refinement *)
lemma spec_impl [code]: "spec n = impl n 0"
  sorry

(* Now spec generates efficient code *)
```

### Monad Code Generation

```isabelle
(* State monad example *)
type_synonym 'a state = "int \<Rightarrow> 'a \<times> int"

definition return_state :: "'a \<Rightarrow> 'a state" where
  "return_state x = (\<lambda>s. (x, s))"

definition bind_state :: "'a state \<Rightarrow> ('a \<Rightarrow> 'b state) \<Rightarrow> 'b state" where
  "bind_state m f = (\<lambda>s. let (x, s') = m s in f x s')"

export_code return_state bind_state in Haskell
```

## Complete Example

```isabelle
theory Complete_CodeGen
  imports Main "HOL-Library.Code_Target_Numeral"
begin

section \<open>Data Types\<close>

datatype 'a vec = Vec "'a list"

section \<open>Operations\<close>

fun vec_length :: "'a vec \<Rightarrow> nat" where
  "vec_length (Vec xs) = length xs"

fun vec_add :: "int vec \<Rightarrow> int vec \<Rightarrow> int vec option" where
  "vec_add (Vec xs) (Vec ys) =
     (if length xs = length ys
      then Some (Vec (map2 (+) xs ys))
      else None)"

fun vec_dot :: "int vec \<Rightarrow> int vec \<Rightarrow> int option" where
  "vec_dot (Vec xs) (Vec ys) =
     (if length xs = length ys
      then Some (sum_list (map2 (*) xs ys))
      else None)"

fun vec_scale :: "int \<Rightarrow> int vec \<Rightarrow> int vec" where
  "vec_scale c (Vec xs) = Vec (map ((*) c) xs)"

section \<open>Lemmas\<close>

lemma vec_add_length:
  assumes "vec_add v1 v2 = Some v3"
  shows "vec_length v3 = vec_length v1"
  using assms by (cases v1; cases v2) auto

section \<open>Code Export\<close>

export_code
  vec_length vec_add vec_dot vec_scale
  in Haskell
  module_name "Lattice.Vector"
  file_prefix "generated/Vector"

end
```

### Generated Haskell Code

```haskell
module Lattice.Vector where

import qualified Data.Integer

data Vec a = Vec [a]

vec_length :: Vec a -> Integer
vec_length (Vec xs) = genericLength xs

vec_add :: Vec Integer -> Vec Integer -> Maybe (Vec Integer)
vec_add (Vec xs) (Vec ys) =
  if length xs == length ys
  then Just (Vec (zipWith (+) xs ys))
  else Nothing

vec_dot :: Vec Integer -> Vec Integer -> Maybe Integer
vec_dot (Vec xs) (Vec ys) =
  if length xs == length ys
  then Just (sum (zipWith (*) xs ys))
  else Nothing

vec_scale :: Integer -> Vec Integer -> Vec Integer
vec_scale c (Vec xs) = Vec (map (* c) xs)
```
