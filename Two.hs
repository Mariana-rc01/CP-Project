module Two where
import List (anaList)
import Cp

smallestPrimeFactor :: (Integer, Integer) -> Integer
smallestPrimeFactor = cond (uncurry (>) . ((^2) >< id)) p2
      (cond ((== 0) . uncurry mod . swap) p1 (smallestPrimeFactor . (succ >< id)))

g 1 = i1 ()
g n = i2 (smallestPrimeFactor (2,n), div n (smallestPrimeFactor (2,n)))

primes = anaList g
