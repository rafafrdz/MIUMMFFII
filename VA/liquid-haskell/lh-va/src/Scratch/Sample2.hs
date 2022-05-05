{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}


module Scratch.Sample2 where
import Prelude hiding (head, max)

{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

{-@ 
data IncList a = Emp | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}
@-}

data IncList a = Emp | (:<) { hd :: a, tl :: IncList a }
infixr 9 :<

okList = 1 :< 2 :< 3 :< Emp

insertSort :: (Ord a) => [a] -> IncList a
insertSort [] = Emp
insertSort (x:xs) = insert x (insertSort xs)

insert :: (Ord a) => a -> IncList a -> IncList a
insert y Emp = y :< Emp
insert y (x :< xs)
    | y <= x = y :< x :< xs
    | otherwise = x :< insert y xs

-- se usa el foldr en vez del foldl porque si se usara foldl despues
-- habria que aplicarle un reverse, y serian dos recorridos
insertSort' :: (Ord a) => [a] -> IncList a
insertSort' xs = foldr f b xs
    where
        f = insert
        b = Emp
