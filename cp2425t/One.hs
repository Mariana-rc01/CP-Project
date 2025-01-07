module One where

import Cp

import BTree
import List

hindex :: [Int] -> (Int, [Int])
hindex = hyloBTree (either f1 f2) qsep

f1 = const (0, [])

f2 :: (Int, ((Int, [Int]), (Int, [Int]))) -> (Int, [Int])
f2 (n, ((_, ll), (_, lr))) = (hIndex, contributors)
    where
        list = lr ++ [n] ++ ll
        hIndex = myfoldr (curry process) 0 (zip [1..] list)
        process :: (Ord a) => ((a, a), a) -> a
        process = cond (uncurry (>=).swap.p1) (uncurry max . swap . (p1 >< id)) p2
        contributors = filter (>= hIndex) list

