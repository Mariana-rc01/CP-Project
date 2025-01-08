{-# LANGUAGE NPlusKPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Two where
import List
import Data.List
import Cp
import Exp
import LTree

-- 2.1

smallestPrimeFactor :: (Integer, Integer) -> Integer
smallestPrimeFactor = cond (uncurry (>) . ((^2) >< id)) p2
      (cond ((== 0) . uncurry mod . swap) p1 (smallestPrimeFactor . (succ >< id)))

g 1 = i1 ()
g n = i2 (smallestPrimeFactor (2,n), div n (smallestPrimeFactor (2,n)))

primes = anaList g

-- 2.2

-- 1ª resolução
-- mergeTrees
mergeTrees :: (Exp Integer Integer, Exp Integer Integer) -> Exp Integer Integer
mergeTrees (Var v1, Var v2) = Term 1 [Var v1, Var v2]
mergeTrees (Var v, Term o sub) = Term o (Var v : sub)
mergeTrees (Term o sub, Var v) = Term o (sub ++ [Var v])
mergeTrees (Term o1 sub1, Term o2 sub2)
  | o1 == o2 = Term o1 (mergeSubtrees sub1 sub2)
  | otherwise = Term 1 [Term o1 sub1, Term o2 sub2]

mergeSubtrees :: [Exp Integer Integer] -> [Exp Integer Integer] -> [Exp Integer Integer]
mergeSubtrees [] t2 = t2
mergeSubtrees t1 [] = t1
mergeSubtrees (x:xs) ys =
  case find (sameRoot x) ys of
    Just y -> mergeTrees (x, y) : mergeSubtrees xs (filter (/= y) ys)
    Nothing -> x : mergeSubtrees xs ys

-- Checks if two trees have the same root
sameRoot :: Exp Integer Integer -> Exp Integer Integer -> Bool
sameRoot (Term o1 _) (Term o2 _) = o1 == o2
sameRoot _ _ = False

-- Generate a tree with a prime number as root and its prime factors as children
primeTree :: Integer -> Exp Integer Integer
primeTree n = Term 1 (myfoldr buildTree [Var n] (primes n))
  where
    buildTree prime acc = [Term prime acc]

geneCata :: Either () (Exp Integer Integer, Exp Integer Integer) -> Exp Integer Integer
geneCata = either (const (Term 1 [])) mergeTrees

geneAna :: [Integer] -> Either () (Exp Integer Integer, [Integer])
geneAna [] = i1 ()
geneAna (x:xs) = i2 (primeTree x, xs)

prime_tree' :: [Integer] -> Exp Integer Integer
prime_tree' = hyloList geneCata geneAna

-- l = prime_tree [455, 669, 6645, 34, 12, 2]
-- pict l
-- Term 1 [Term 5 [Term 7 [Term 13 [Var 455]]],Term 3 [Term 223 [Var 669],Term 5 [Term 443 [Var 6645]]],Term 2 [Term 17 [Var 34],Term 2 [Term 3 [Var 12]],Var 2]]

-- 2ª resolução
prime_tree :: [Integer] -> Exp Integer Integer
prime_tree = Term 1 . untar . map (\n -> (primes n, n))
