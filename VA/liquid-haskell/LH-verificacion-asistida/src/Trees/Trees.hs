-----------------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) Ricardo Peña, March 2019               
-- License     :  LGPL
--
-- Maintainer  :  ricardo@sip.ucm.es
--
-- Liquid Haskell Binary Search Trees
-----------------------------------------------------------------------------

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}


module Trees.Trees where
import Prelude hiding (head, max)


--
-- Some liquid functions and types
--
{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

{-@ type Nat     = {v:Int | 0 <= v} @-}
{-@ type Pos     = {v:Int | 0 <  v} @-}
{-@ type NonZero = {v:Int | 0 /= v} @-}

-- This is the Haskell definition

data IncList a = Emp | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

-- This is the Liquid Haskell definition. Both are needed

{-@ data IncList a = Emp | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}} @-}


-- This is the Haskell definition

data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }

-- This is the Liquid Haskell definition. Both are needed
-- Note the order of the arguments in constructor Node

{-@ data BST a    = Leaf 
                  | Node { root  :: a
                         , left  :: BSTL a root
                         , right :: BSTR a root } @-}

{-@ type BSTL a X = BST {v:a | v < X}  @-}
{-@ type BSTR a X = BST {v:a | X < v}  @-}


-- This says that the first element is smaller than all those in the second one

{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}
data MinPair a = MP { mElt :: a, rest :: BST a }

{-
              Exercise 1: avoid the above LH error
-}

{-@ measure nonEmpty @-}
nonEmpty :: BST a -> Bool
nonEmpty Leaf           = False
nonEmpty t@(Node _ _ _) = True

{-@ delMin :: (Ord a) => {t : BST a | nonEmpty t} -> MinPair a @-}
delMin (Node k Leaf r) = MP k r
delMin (Node k l r)    = MP k' (Node k l' r)
  where
    MP k' l'           = delMin l
delMin Leaf            = die "Don't say I didn't warn ya!"




-- Exercise 2: avoid the above LH error

{-@ join :: x : a -> IncList {v : a | v <= x} -> IncList {v : a | v >= x} -> IncList a @-}
join :: a -> IncList a -> IncList a -> IncList a
join z Emp       ys = z :< ys
join z (x :< xs) ys = x :< join z xs ys


-- Exercise 3:  Define a Skew heap in Liquid Haskell and implement
-- and verify its operation join, joining two skew heaps 
-- into one (see the dafny file to inspire you)

{-@ data SkewH t = Empty
                 | Skew {
                    sk :: t,
                    sLeft :: SkewH { v : t | sk <= v },
                    sRight :: SkewH { v : t | sk <= v }
                    } 
@-}

data SkewH t = Empty
             | Skew t (SkewH t) (SkewH t)

-- El predicado SkewH{v: t | Trees.Trees.sk s <= v}
-- lo puedo hacer porque sk es una funcion definida en el scope de liquid haskell
-- el parametro del constructor del tipo refinado puede usarse como funcion en el propio tipo refinado
-- El modulo Trees esta alojado en la carpeta src/Trees/Trees.hs, por lo que tengo que hacer
-- un import de la funcion de la forma Trees.Trees.sk

{-@ refineSkew :: s: SkewH t -> SkewH{v: t | Trees.Trees.sk s <= v} @-}
refineSkew :: Ord t => SkewH t -> SkewH t
refineSkew (Skew a b c) = (Skew a b c)
refineSkew Empty = Empty


joinSk :: Ord t => SkewH t -> SkewH t -> SkewH t
joinSk Empty Empty = Empty
joinSk Empty sr = sr
joinSk sl@Skew{} Empty = sl
joinSk sl@(Skew k1 sll slr) sr@(Skew k2 _ _)
  | k1 <= k2 = Skew k1 (joinSk slr (refineSkew sr)) sll
  | otherwise = joinSk sr sl