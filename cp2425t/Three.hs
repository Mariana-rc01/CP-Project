{-# LANGUAGE NPlusKPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Three where

import List (anaList)
import Cp
import Data.List (tails)

-- Resolução sem CP
-- convolve1 :: (Num a) => [a] -> [a] -> [a]
-- convolve1 hs xs =
    -- let pad = replicate (length hs - 1) 0
        -- ts  = pad ++ xs
    -- in map (sum . zipWith (*) (reverse hs)) (init $ tails ts)

-- Resolução com CP 2
-- convolve2 :: Num a => [a] -> [a] -> [a]
-- convolve2 l1 l2 = anaList (anaGene2 l1) (addzeros l2)
    -- where
      -- addzeros l = replicate (length l1 - 1) 0 ++ l2

-- anaGene2 :: Num a => [a] -> [a] -> Either () (a, [a])
-- anaGene2 l1 l2
    --  | null l2 = i1 ()
    --  | otherwise = i2 (sum (zipWith (*) (reverse l1) (take (length l1) l2)), tail l2)

-- Resolução com CP (Final)
convolve :: Num a => [a] -> [a] -> [a]
convolve l1 l2 = anaList (anaGene l1 l2) 0

anaGene :: Num a => [a] -> [a] -> Int -> Either () (a, Int)
anaGene l1 l2 = cond (>= m + n - 1) (const $ i1 ())
                    (\i -> i2 (sum  $ zipWith (*) l1 (map (\j -> access (l2, (i, j))) [0..(m - 1)]), i + 1))
    where
        m = length l1; n = length l2
        access = cond ((||) <$> cond1 <*> cond2) (const 0) (uncurry (!!) . (id >< uncurry (-)))
        cond1 = uncurry (>).(const 0 >< uncurry (-))
        cond2 = uncurry (<=).(length >< uncurry (-))
