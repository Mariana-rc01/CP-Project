{-# LANGUAGE NPlusKPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Expr where
import Cp
import Data.Ratio

-- (1) Datatype definition -----------------------------------------------------

data Expr b a =   V a | N b | T Op [ Expr b a ]  deriving (Show,Eq)
data Op = ITE | Add | Mul | Suc deriving (Show,Eq)

soma  x y = T Add [x,y]
multi x y = T Mul [x,y]
ite x y z = T ITE [x,y,z]

inExpr = either V (either N (uncurry T))
outExpr = undefined

baseExpr g h f = g -|- (h -|- id >< map f)

-- (2) Ana + cata + hylo -------------------------------------------------------

recExpr = undefined

cataExpr g = undefined

anaExpr g = undefined
                
hyloExpr h g = undefined

-- (3) Monad -------------------------------------------------------------------

{-instance Monad LTree where
     return  = Leaf
     t >>= g = (mu . fmap g) t

mu  :: LTree (LTree a) -> LTree a
mu  =  cataLTree (either id Fork)-}

-- Exemplos
e = ite (V "x") (N 0) (multi (V "y") (soma (N 3) (V "y")))
i = ite (V "x") (N 1) (multi (V "y") (soma (N (3 % 5)) (V "y")))

