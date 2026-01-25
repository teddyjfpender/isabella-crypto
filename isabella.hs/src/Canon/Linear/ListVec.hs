{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | List-based vectors and matrices
--
-- This module provides vector and matrix operations using Haskell lists.
-- While not optimal for performance, this representation directly corresponds
-- to the Isabelle formalization and preserves all proven properties.
--
-- Generated from @Canon/Linear/ListVec.thy@
module Canon.Linear.ListVec (
    -- * Types
    Int_vec,
    Int_matrix,

    -- * Dimension validation
    valid_vec,
    valid_matrix,

    -- * Vector arithmetic
    vec_add,
    vec_sub,
    scalar_mult,
    vec_neg,

    -- * Products
    inner_prod,

    -- * Matrix operations
    mat_vec_mult,
    transpose,
    mat_transpose_vec_mult,

    -- * Vector manipulation
    vec_concat,
    split_vec
) where

import Prelude ((+), (-), (*), (==), (&&), Bool(..), Int, map, all, length,
                take, drop, (++), zipWith, sum, null, head, tail)
import qualified Prelude

-- | Integer vector (represented as a list)
type Int_vec = [Int]

-- | Integer matrix (list of row vectors)
type Int_matrix = [[Int]]

-- | Check if a vector has the specified dimension
--
-- >>> valid_vec 3 [1, 2, 3]
-- True
-- >>> valid_vec 3 [1, 2]
-- False
valid_vec :: Int -> Int_vec -> Bool
valid_vec n v = length v == n

-- | Check if a matrix has dimensions m × n
--
-- >>> valid_matrix 2 3 [[1,2,3], [4,5,6]]
-- True
-- >>> valid_matrix 2 3 [[1,2], [3,4]]
-- False
valid_matrix :: Int -> Int -> Int_matrix -> Bool
valid_matrix m n mat =
    length mat == m && all (\row -> length row == n) mat

-- | Element-wise vector addition
--
-- >>> vec_add [1, 2, 3] [4, 5, 6]
-- [5, 7, 9]
vec_add :: Int_vec -> Int_vec -> Int_vec
vec_add = zipWith (+)

-- | Element-wise vector subtraction
--
-- >>> vec_sub [4, 5, 6] [1, 2, 3]
-- [3, 3, 3]
vec_sub :: Int_vec -> Int_vec -> Int_vec
vec_sub = zipWith (-)

-- | Scalar multiplication
--
-- >>> scalar_mult 3 [1, 2, 3]
-- [3, 6, 9]
scalar_mult :: Int -> Int_vec -> Int_vec
scalar_mult c = map (* c)

-- | Vector negation
--
-- >>> vec_neg [1, -2, 3]
-- [-1, 2, -3]
vec_neg :: Int_vec -> Int_vec
vec_neg = map Prelude.negate

-- | Inner product (dot product) of two vectors
--
-- Computes the sum of element-wise products.
--
-- >>> inner_prod [1, 2, 3] [4, 5, 6]
-- 32
inner_prod :: Int_vec -> Int_vec -> Int
inner_prod xs ys = sum (zipWith (*) xs ys)

-- | Matrix-vector multiplication
--
-- Computes A * v where A is an m × n matrix and v is an n-vector,
-- producing an m-vector.
--
-- >>> mat_vec_mult [[1, 2], [3, 4]] [5, 6]
-- [17, 39]
mat_vec_mult :: Int_matrix -> Int_vec -> Int_vec
mat_vec_mult a v = map (inner_prod v) a

-- | Matrix transpose
--
-- Swaps rows and columns.
--
-- >>> transpose [[1, 2, 3], [4, 5, 6]]
-- [[1, 4], [2, 5], [3, 6]]
transpose :: Int_matrix -> Int_matrix
transpose [] = []
transpose ([]:_) = []
transpose rows = map head rows : transpose (map tail rows)

-- | Transposed matrix times vector
--
-- Computes A^T * v efficiently without explicitly constructing A^T.
--
-- >>> mat_transpose_vec_mult [[1, 2], [3, 4]] [5, 6]
-- [23, 34]
mat_transpose_vec_mult :: Int_matrix -> Int_vec -> Int_vec
mat_transpose_vec_mult a v = mat_vec_mult (transpose a) v

-- | Concatenate two vectors
--
-- >>> vec_concat [1, 2] [3, 4, 5]
-- [1, 2, 3, 4, 5]
vec_concat :: Int_vec -> Int_vec -> Int_vec
vec_concat = (++)

-- | Split a vector at position n
--
-- Returns (first n elements, remaining elements).
--
-- >>> split_vec 2 [1, 2, 3, 4, 5]
-- ([1, 2], [3, 4, 5])
split_vec :: Int -> Int_vec -> (Int_vec, Int_vec)
split_vec n v = (take n v, drop n v)
