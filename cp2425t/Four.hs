{-# LANGUAGE NPlusKPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Four where
import Cp
import Expr

-- 4.1 em Expr.hs

-- 4.2 em Expr.hs

-- 4.3
mcataExpr :: Monad m => (Either a (Either b (Op, m [c])) -> m c) -> Expr b a -> m c
mcataExpr = undefined

-- 4.4
let_exp :: (Num c) => (a -> Expr c b) -> Expr c a -> Expr c b
let_exp = undefined

-- 4.5
evaluate :: (Num a, Ord a) =>  Expr a b -> Maybe a
evaluate = undefined

