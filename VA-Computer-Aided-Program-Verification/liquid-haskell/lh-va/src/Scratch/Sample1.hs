{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}


module Scratch.Sample1 where
import Prelude hiding (head, max)

{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ type BList a Lw Up = {v:[a] | Lw <= size v  && size v < Up} @-}
{-@ type NList a = {v:[a] | 0 < size v} @-}



{-@ algo :: NList Int @-}
algo :: [Int]
algo = [1,2,3, 4, 5]


{-@ data SkewH t = Empty
                 | Skew {
                    sk :: t,
                    sLeft :: SkewH { v : t | sk <= v },
                    sRight :: SkewH { v : t | sk <= v }
                    } 
@-}

data SkewH t = Empty | Skew t (SkewH t) (SkewH t)


{-@ measure isNonSkewEmpty @-}
isNonSkewEmpty :: Ord a => SkewH a -> Bool
isNonSkewEmpty Empty = False
isNonSkewEmpty Skew{} = True


{-@ type NESkewH a = {s: SkewH a | isNonSkewEmpty s } @-}

{-@ measure getKey @-}
{-@ getKey :: NESkewH a -> a @-}
getKey :: Ord a => SkewH a -> a
getKey (Skew k a b) = k

{-@ type SubrSkewH a Sk = SkewH{v: a | (getKey Sk) <= v } @-}

{-@ refineSkew :: s: SkewH t -> SubrSkewH t s @-}
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