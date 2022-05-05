{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module NumericMeasures.NumericMeasures where
import Prelude  hiding  (map, zipWith, zip, take, drop, reverse)

{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size []     = 0
size (_:rs) = 1 + size rs


{-------------------------------------------------------------------------------
  Exercise 1: fix 'reverse'
-------------------------------------------------------------------------------}


