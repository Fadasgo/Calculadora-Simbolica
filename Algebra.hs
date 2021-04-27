module Algebra where
import Term
import Data.List

--Integrantes: Moises Gonzalez 11-10406 
--             Fabio Suarez    12-10578

-- Funcion que calcula el numerador de la suma de dos fracciones
nume :: Int -> Int -> Int -> Int -> Int
nume w x y z = ((div (lcm x z) x) * w) + ((div (lcm x z) z) * y)

-- Permite simplificar una parte de la fraccion  
-- Recibe parametros numFraccion1 denomFraccion1 numFraccion2 denomFraccion2
simpFrac:: Int -> Int -> Int
simpFrac x y
  |((gcd x y) == 1) = x
  |((gcd x y) /= 1) = (div x (gcd x y)) 

-- Funcion factorial
factorial :: Int -> Int 
factorial 0 = 1
factorial 1 = 1
factorial n = n * factorial (n-1)

--Funcion Binomio de Newton
binomio :: Term -> Term -> Int -> Int -> Term
binomio x y n k
  |(k == 0) = (Sum (Exp x n) (binomio x y n (k+1)))
  |(k == 1) = (Sum (Mult (Mult (Const (div (factorial n) (factorial (n-k))) 1) (Exp x (n-k))) y) (binomio x y n (k+1)))
  |(k /= n) = (Sum (Mult (Mult (Const (div (factorial n) (factorial (n-k) * (factorial k))) 1) (Exp x (n-k))) (Exp y k)) (binomio x y n (k+1)))
  |(k == n) = (Exp y k)

-- Funcion que realiza simplificaciones a una expresion de Terms
simplify :: Term -> Term
simplify (Sum a b) = case (simplify a, simplify b) of ((Const 0 _), x) -> simplify x
                                                      (x, (Const 0 _)) -> simplify x
                                                      ((Const w x), (Const y z)) -> (Const (nume w x y z) (lcm x z))
                                                      (x, y) -> (Sum (simplify x) (simplify y))

simplify (Mult a b) = case (simplify a, simplify b) of ((Const 0 1), x) -> (Const 0 1)
                                                       (x, (Const 0 1)) -> (Const 0 1)
                                                       ((Const 1 1), x) -> simplify x
                                                       (x, (Const 1 1)) -> simplify x
                                                       (x, y) -> (Mult (simplify x) (simplify y))

simplify (Exp a b) = case (simplify a, b) of (x, 0) -> (Const 1 1)
                                             ((Const x y), z) -> (Const ((^) x z) ((^) y z))
                                             (x, y) -> (Exp (simplify x) y)

simplify (Const a b) = case (a, b) of (a,b) -> (Const (simpFrac a b) (simpFrac b a))

simplify (Integ a b) = case (simplify a, simplify b) of (a,b) -> (Integ (simplify a) (simplify b))

simplify (Fun a b) = case (a, simplify b) of (a, b) -> (Fun a (simplify b))

simplify t = t

-- Funcion que desarrolla la distributividad en una expresion Term
distrib :: Term -> Term
distrib (Sum a b) = (Sum (distrib a) (distrib b))
distrib (Exp a b) = (Exp (distrib a) b)
distrib (Fun a b) = (Fun a (distrib b))
distrib (Integ a b) = (Integ (distrib a) (distrib b))
distrib (Mult (Sum b c) a) = groupDistrib (Sum (distrib (Mult b a)) (distrib (Mult c a)))
distrib (Mult a (Sum b c)) = groupDistrib (Sum (distrib (Mult a b)) (distrib (Mult a c)))
distrib (Mult a b) = (Mult (distrib a) (distrib b))
distrib t = t

groupDistrib :: Term -> Term 
groupDistrib (Fun a b) = (Fun a (groupDistrib b))
groupDistrib (Integ a b) = (Integ (groupDistrib a) b)
groupDistrib (Sum a b) = (Sum (groupDistrib a) (groupDistrib b))
groupDistrib (Mult a b) = extractDistrib (sort (listAtoms (Mult a b)))
groupDistrib (Exp t i) = (Exp (groupDistrib t) i)
groupDistrib t = t

extractDistrib :: [Term] -> Term
extractDistrib [] = error "La lista no puede ser vacia"
extractDistrib [x] = x
extractDistrib ((Const x y):(Const s z):xs) = extractDistrib ((Const (x*s) (y*z)):xs)
extractDistrib (a:b:xs) = Mult a (extractDistrib (b:xs))

-- Funcion que desarrolla las potencias de una expresion Term
pow :: Term -> Term
pow (Sum a b) = (Sum (pow a) (pow b)) 
pow (Mult a b) = (Mult (pow a) (pow b))
pow (Fun a b) = (Fun a (pow b))
pow (Integ a b) = (Integ (pow a) (pow b)) 
pow (Exp t 0) = (Const 1 1)
pow (Exp t 1) = pow t
pow (Exp (Const a b) i) = (Const ((^) a i) ((^) b i))
pow (Exp (Mult t1 t2) i) = (Mult (Exp (pow t1) i) (Exp (pow t2) i))
pow (Exp (Exp t n) m) = (Exp (pow t) (n*m))
pow (Exp (Sum t1 t2) n) = (binomio (pow t1) (pow t2) n 0)
pow t = t

-- isAtom
isAtom :: Term -> Bool
isAtom (Const a b) = True
isAtom (Var x) = True
isAtom (Fun a b) = True
isAtom (Integ a b) = True
isAtom (Exp a b) = True
isAtom _ = False

-- Funcion que agrupa los atomos en una expresion
groupAtoms :: Term -> Term 
groupAtoms (Fun a b) = (Fun a (groupAtoms b))
groupAtoms (Integ a b) = (Integ (groupAtoms a) b)
groupAtoms (Sum a b) = (Sum (groupAtoms a) (groupAtoms b))
groupAtoms (Mult a b) = extractAtoms (sort (listAtoms (Mult a b)))
groupAtoms (Exp t i) = (Exp (groupAtoms t) i)
groupAtoms t = t

listAtoms :: Term -> [Term]
listAtoms (Mult a b) = (listAtoms a) ++ (listAtoms b)
listAtoms t = [groupAtoms t]

extractAtoms :: [Term] -> Term
extractAtoms [] = error "La lista no puede ser vacia"
extractAtoms [x] = x
extractAtoms ((Const x y):(Const s z):xs) = extractAtoms ((Const (x*s) (y*z)):xs)
extractAtoms ((Exp x a):(Exp y b):xs) -- (Exp x a) == (Exp y b)
  | ((x == y) && (0 <= a) && (0 <= b)) = extractAtoms ((Exp (x) (a+b)):xs)
  | otherwise = Mult (Exp x a) (extractAtoms ((Exp y b):xs))
extractAtoms (y:(Exp x a):xs)
  | (y == x) = extractAtoms ((Exp (x) (a+1)):xs)
  | otherwise = Mult y (extractAtoms ((Exp x a):xs))
extractAtoms ((Exp x a):y:xs)
  | (x == y) = extractAtoms ((Exp (x) (a+1)):xs)
  | otherwise = Mult (Exp x a) (extractAtoms (y:xs))
extractAtoms (a:b:xs)
  | (a == b) = extractAtoms ((Exp (a) (2)):xs)
  | otherwise = Mult a (extractAtoms (b:xs))

