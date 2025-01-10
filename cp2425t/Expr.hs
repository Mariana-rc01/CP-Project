{-# LANGUAGE NPlusKPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# HLINT ignore "Use camelCase" #-}

module Expr where
import Cp
import Data.Ratio
import Data.Maybe (catMaybes)

-- (1) Datatype definition -----------------------------------------------------

data Expr b a =   V a | N b | T Op [ Expr b a ]  deriving (Show,Eq)
data Op = ITE | Add | Mul | Suc deriving (Show,Eq)

soma  x y = T Add [x,y]
multi x y = T Mul [x,y]
ite x y z = T ITE [x,y,z]

inExpr :: Either a (Either b (Op, [Expr b a])) -> Expr b a
inExpr = either V (either N (uncurry T))

outExpr :: Expr b a -> Either a (Either b (Op, [Expr b a]))
outExpr (V n) = i1 n
outExpr (N n) = (i2.i1) n
outExpr (T op exprs) = (i2.i2) (op,exprs)

baseExpr g h f = g -|- (h -|- id >< map f)

-- (2) Ana + cata + hylo -------------------------------------------------------

recExpr = baseExpr id id

cataExpr g = g . recExpr (cataExpr g) . outExpr

anaExpr g = inExpr . recExpr (anaExpr g) . g

hyloExpr :: (Either b1 (Either b2 (Op, [c])) -> c) -> (a -> Either b1 (Either b2 (Op, [a]))) -> a -> c
hyloExpr h g = cataExpr h . anaExpr g

-- (3) Monad -------------------------------------------------------------------

instance Functor (Expr b)
     where fmap f = cataExpr (inExpr . baseExpr f id id)

instance Applicative (Expr b) where
    pure :: a -> Expr b a
    pure = V
    (V f) <*> x = fmap f x
    (N b) <*> _ = N b
    (T op fs) <*> x = T op (map (<*> x) fs)

instance Monad (Expr b) where
    return :: a -> Expr b a
    return = pure

    (>>=) :: Expr b a -> (a -> Expr b b1) -> Expr b b1
    t >>= g = mu (fmap g t)

mu :: Expr b (Expr b a) -> Expr b a
mu  =  cataExpr (either id (inExpr . i2))

u :: a -> Expr b a
u = V

-- Monadic cata

mcataExpr :: Monad m => (Either a (Either b (Op, m [c])) -> m c) -> Expr b a -> m c
mcataExpr g = g .! (dl . recExpr (mcataExpr g) . outExpr)

dl :: Monad m => Either a (Either b (Op, [m c])) -> m (Either a (Either b (Op, m [c])))
dl = either (return . i1) (either (return . i2 . i1) aux)
    where aux (op, ms) = do m <- lamb ms; (return . i2 . i2) (op, return m)

-- Exemplos
e = ite (V "x") (N 0) (multi (V "y") (soma (N 3) (V "y")))
i = ite (V "x") (N 1) (multi (V "y") (soma (N (3 % 5)) (V "y")))

let_exp :: (Num c) => (a -> Expr c b) -> Expr c a -> Expr c b
let_exp f = cataExpr (either f (either N (uncurry T)))

f "x" = N 0
f "y" = N 5
f _ = N 99

-- 1ª resolução

evaluate :: (Num a, Ord a) => Expr a b -> Maybe a
evaluate = cataExpr gene

gene :: (Num a, Ord a) => Either b (Either a (Op, [Maybe a])) -> Maybe a
gene = either (const Nothing) (either Just evalOp)

evalOp :: (Num a, Ord a) => (Op, [Maybe a]) -> Maybe a
evalOp (op, xs)
  | Nothing `elem` xs = Nothing
  | otherwise = result op (catMaybes xs)

-- 2ª resolução

evaluateM :: (Num a, Ord a) => Expr a b -> Maybe a
evaluateM = mcataExpr geneM

geneM :: (Num a, Ord a) => Either b (Either a (Op, Maybe [a])) -> Maybe a
geneM = either (const Nothing) (either Just aux)
    where aux (op, args) = do argsR <- args; result op argsR

-- Função em comum para as duas resoluções
result :: (Num a, Ord a) => Op -> [a] -> Maybe a
result Add = Just . sum
result Mul = Just . product
result Suc = Just . (+1) . head
result ITE = Just . cond (uncurry (>) . split head (const 0)) (uncurry (!!) . split id (const 1)) (uncurry (!!) . split id (const 2))
result _ = const Nothing

g "x" = N 0
g "y" = N (1%7)

-- let_exp f e = T ITE [N 0, N 0, T Mul [N 5, T Add [N 3, N 5]]]