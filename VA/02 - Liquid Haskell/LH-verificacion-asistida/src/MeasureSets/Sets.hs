{-@ LIQUID "--no-termination" @-}

{-
  Author: Rafael Fernandez Ortiz
  Language: Haskell with Liquid Haskell
-}

module MeasureSets.Sets where
import Data.Set hiding (insert, partition, filter, split, elems)
import Prelude  hiding (elem, reverse, filter)

main :: IO ()
main = return ()

{-@ die :: {v:_ | false} -> a @-}
die = error

type List a = [a]

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ measure elts @-}
elts        :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

{-@ type ListS a S = {v:[a] | elts v = S} @-}

{-@ type ListEmp a = ListS a {Set_empty 0} @-}

{-@ type ListEq a X = ListS a {elts X}    @-}

{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}

{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}

{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{-@ append'       :: xs:_ -> ys:_ -> ListUn a xs ys @-}
append' []     ys = ys
append' (x:xs) ys = x : append' xs ys

{- ################################################### 
### Exercise 1: Type to revHelper
#######################################################-}

{-@ reverse' :: xs:[a] -> ListEq a xs @-}
reverse' xs = revHelper [] xs

{-@ revHelper :: xs: List a -> ys: List a -> ListUn a xs ys @-}
revHelper acc []     = acc
revHelper acc (x:xs) = revHelper (x:acc) xs


{- ################################################### 
### Exercise 2: Type to halve
#######################################################-}
{-@ type ListPairFrom a Ls = {p: (List a, List a) | elts Ls == Set_cup (elts (fst p)) (elts (snd p))} @-}

{-@ halve :: n: Int -> xs: List a -> ListPairFrom a xs @-}
halve            :: Int -> [a] -> ([a], [a])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

{-@ prop_halve_append  :: _ -> _ -> True @-}
prop_halve_append n xs = elts xs == elts xs'
  where
    xs'      =  append' ys zs
    (ys, zs) =  halve n xs


{- ################################################### 
### Exercise 3: Type to elem
#######################################################-}

{-@ elem      :: (Eq a) => x: a -> xs: List a -> {b: Bool | b <=> member x (elts xs) } @-}
elem _ []     = False
elem x (y:ys) = x == y || elem x ys

{-@ test1 :: True @-}
test1      = elem 2 [1, 2, 3]

{-@ test2 :: False @-}
test2      = elem 2 [1, 3]

{- ################################################### 
### Exercise 4: Fix quicksort
#######################################################-}

infixr 5 >+<

{-@ (>+<) :: xs :List a -> ys: List a -> { zs: List a | elts zs == union (elts xs) (elts ys) } @-}
(>+<) :: List a -> List a -> List a
(x:xs) >+< ys = x : (xs >+< ys)
[] >+< ys = ys

-- It's a kind of halve with a predicate a -> Bool
{-@ halveP :: (a -> Bool) -> xs: List a -> ListPairFrom a xs @-}
halveP          :: (a -> Bool) -> [a] -> ([a], [a])
halveP _ []     = ([], [])
halveP f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = halveP f xs


{-@ quickSort :: (Ord a) => xs:[a] -> ListEq a xs @-}
quickSort :: Ord a => [a] -> [a]
quickSort []     = []
quickSort (x:xs) = quickSort ls >+<  x:same >+<  quickSort gt
    where (ls, xs')     = halveP (< x) xs
          (gt, same) = halveP (> x) xs'

{-@ measure unique @-}
unique        :: (Ord a) => [a] -> Bool
unique []     = True
unique (x:xs) = unique xs && not (member x (elts xs))

{-@ type UList a = {v:[a] | unique v }@-}

-- isUnique = [1, 2, 3]           -- accepted by LH

{- ################################################### 
### Exercise 5: Type to filter'
####################################################### -}

{-@ filter' :: (a -> Bool) -> xs: List a -> {v: ListSub a xs | unique xs => unique v } @-}
filter' _ []   = []
filter' f (x:xs)
  | f x = x : xs'
  | otherwise = xs'
  where
    xs' = filter' f xs

{-@ test3 :: UList _ @-}
test3     = filter' (> 2) [1,2,3,4]

{-@ test4 :: [_] @-}
test4     = filter' (> 3) [3,1,2,3]

{- ################################################### 
### Exercise 6: Type go function
####################################################### -}

{-@ reverse :: UList a -> UList a @-}
reverse         = go []
  where
    {-@ go     :: acc: UList a -> {ys: UList a | intersection (elts ys) (elts acc) == empty } -> { zs: UList a | union (elts acc) (elts ys) == elts zs && len zs == len acc + len ys } @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs


{- ################################################### 
### Exercise 7: Fix append
####################################################### -}
{-@ append       :: xs: UList a -> {ys: UList a | intersection (elts xs) (elts ys) == empty } -> { zs: UList a | elts zs == union (elts xs) (elts ys) } @-}
append []     ys = ys
append (x:xs) ys = x : append xs ys
