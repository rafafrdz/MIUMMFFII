-----------------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) Ricardo Peña, December 2016               
-- License     :  LGPL
--
-- Maintainer  :  ricardo@sip.ucm.es
-- Stability   :  provisional
-- Portability :  portable
--
-- Liquid Haskell examples in the paper "An Introduction to Liquid Haskell"
-- PROLE 2016, selected papers published in EPTCS

-----------------------------------------------------------------------------

-- Rafael Fernandez Ortiz
--

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

 
module Basic.Lists where
import Prelude hiding (head, max)


--
-- Some liquid types
--

{-@ type Nat     = {v:Int | 0 <= v} @-}
{-@ type Pos     = {v:Int | 0 <  v} @-}
{-@ type NonZero = {v:Int | 0 /= v} @-}

--
-- Sorted lists
--

data IncList a = Emp | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

{-@ data IncList a = Emp | (:<) { hd::a, tl::IncList {v:a | hd <= v}} @-}

okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

{- badList = 2 :< 1 :< 3 :< Emp       -- rejected by LH -}


-- Exercise: The signature is wrong. Refine it

{-@ join :: x:a -> IncList {v:a | v <= x} -> IncList {v:a | v > x} -> IncList a @-}
join :: a -> IncList a -> IncList a -> IncList a
join z Emp       ys = z :< ys 
join z (x :< xs) ys = x :< join z xs ys 






