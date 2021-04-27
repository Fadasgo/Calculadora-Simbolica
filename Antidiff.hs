module Antidiff where
import Term
import Algebra

--Integrantes: Moises Gonzalez 11-10406 
--             Fabio Suarez    12-10578

-- Antidiff.hs 

simbInt :: Term -> Term
simbInt (Sum a b) = (Sum (simbInt a) (simbInt b))
simbInt (Mult a b) = (Mult (simbInt a) (simbInt b))
simbInt (Exp a b) = (Exp (simbInt a) b)
simbInt (Integ (Sum t1 t2) x) = (Sum (Integ t1 x) (Integ t2 x))
simbInt (Integ (Fun "sen" x) y)
  |(equal x y) = (Mult (Const (-1) 1) (Fun "cos" x))
simbInt (Integ (Fun "cos" x) y)
  | (equal x y) = (Fun "sen" x)
simbInt (Integ (Fun "sen" (Mult (Const k 1) x)) y)
  | (equal x y) = (Mult (Const (-1) k) (Fun "cos" (Mult (Const k 1) x)))
simbInt (Integ (Fun "cos" (Mult (Const k 1) x)) y)
  | (equal x y) = (Mult (Const 1 k) (Fun "sen" (Mult (Const k 1) x)))
simbInt (Integ (Mult (Fun "cos" x) (Fun "sen" y) ) z) 
  | (equal x y) && (equal x z) = (Mult (Const (-1) 2 ) (Exp (Fun "cos" x) (2)))
simbInt (Integ (Mult (Fun "cos" x) (Exp (Fun "sen" y) n)) z) 
  | (equal x y) && (equal x z) = (Mult (Const 1 (succ n)) (Exp (Fun "sen" x) (succ n)))
  | (equal x y) && (equal x z) && (n==1) = (Mult (Const (-1) 2 ) (Exp (Fun "cos" x) (2)))
simbInt (Integ (Mult (Exp (Fun "cos" x) n) (Fun "sen" y)) z) 
  | (equal x y) && (equal x z) = (Mult (Const (-1) (succ n)) (Exp (Fun "cos" x) (succ n)))
  | (equal x y) && (equal x z) && (n==1) = (Mult (Const (-1) 2 ) (Exp (Fun "cos" x) (2)))
simbInt (Integ (Mult (Fun "cos" (Mult (Const k 1) x)) (Exp (Fun "sen" (Mult (Const p 1) y)) n)) z) 
  | (k == p) && (equal x y) && (equal x z) = (Mult (Const 1 (k*(succ n))) (Exp (Fun "sen" (Mult (Const k 1) x)) (succ n)))
simbInt (Integ (Mult (Exp (Fun "cos" (Mult (Const k 1) x)) n) (Fun "sen" (Mult (Const p 1) y))) z)
  | (k == p) && (equal x y) && (equal x z)  = (Mult (Const (-1) (k*(succ n))) (Exp (Fun "cos" (Mult (Const k 1) x)) (succ n)))
simbInt (Integ (Exp (Fun "sen" x) n) y) 
  | (equal x y) && (even n) = (Integ (Exp (Mult (Const 1 2) (Sum (Const 1 1) (Mult (Const (-1) 1) (Fun "cos" (Mult (fromInteger 2) x))))) (div n 2)) x) 
  | (equal x y) && (odd n) =  (Integ (Mult (Exp (Sum (Const 1 1) (Mult (Const (-1) 1) (Exp (Fun "cos" (x)) 2))) (div (n - 1) 2)) (Fun "sen" (x))) (x))
simbInt (Integ (Exp (Fun "cos" x) n) y) 
  | (equal x y) && (even n) = (Integ (Exp (Mult (Const 1 2) (Sum (Const 1 1) (Fun "cos" (Mult (fromInteger 2) x)))) (div n 2)) x)
  | (equal x y) && (odd n) =  (Integ (Mult (Exp (Sum (Const 1 1) (Mult (Const (-1) 1) (Exp (Fun "sen" (x)) 2))) (div (n - 1) 2)) (Fun "cos" (x))) (x))
simbInt (Integ (Exp (Fun "sen" (Mult (Const s d) x)) n) y)
  | (equal x y) && (even n) = ( (Integ (Exp (Mult (Const 1 2) (Sum (fromInteger 1) (Mult (fromInteger (-1)) (Fun "cos" (Mult (Const (2 * s) d) x))))) (div n 2)) x))
  | (equal x y) && (odd n) = ( (Integ (Mult (Exp (Sum (fromInteger 1) (Mult (fromInteger (-1)) (Exp (Fun "cos" (Mult (Const s d) x)) 2))) (div (pred n) 2)) (Fun "sen" (Mult (Const s d) x))) x))
simbInt (Integ (Exp (Fun "cos" (Mult (Const s d) x)) n) y)
  | (equal x y) && (even n) = ( (Integ (Exp (Mult (Const 1 2) (Sum (fromInteger 1) (Fun "cos" (Mult (Const (2 * s) d) x)))) (div n 2)) x))
  | (equal x y) && (odd n) = ( (Integ (Mult (Exp (Sum (fromInteger 1) (Mult (fromInteger (-1)) (Exp (Fun "sen" (Mult (Const s d) x)) 2))) (div (pred n) 2)) (Fun "cos" (Mult (Const s d) x))) x))
simbInt (Integ (Const a b) x) = (Mult (Const a b) x)
simbInt (Integ (Mult (Const a b) t) x) = (Mult (Const a b) (Integ t x)) 
simbInt (Integ x y) 
    | (equal x y) = (Mult (Const 1 2) (Exp x 2))
simbInt (Integ (Exp q k) x)
  |(equal x q) && (k > 0) = (Mult (Const 1 (succ k)) (Exp x (succ k)))
simbInt (Integ t x)
  | not (t `contains` x) = t*x
simbInt t = t

contains :: Term-> Term -> Bool
contains (Var y) (Var x) = x == y
contains (Const a b) v@(Var x) = False
contains (Mult a b) v@(Var x) = (contains a v) || (contains b v)
contains (Sum a b) v@(Var x) = (contains a v) || (contains b v)
contains (Exp a n) v@(Var x) = contains a v
contains (Fun f x) v@(Var y) = contains x v

equal :: Term-> Term -> Bool
equal (Const x a) (Const y b) = (x == y) && (a == b)
equal (Var x) (Var y) = (x == y)
equal (Fun x a) (Fun y b) = (x == y) && (a == b)
equal (Integ x a) (Integ y b) = (x == y) && (a == b)
equal (Exp x a) (Exp y b) = (x == y) && (a == b) && (0 <= a) && (0 <= b) 
equal (Sum a b) (Sum x y) = (a == x || a == y) && (b == x ||  b == y)
equal (Mult a b) (Mult x y) = (a == x || a == y) && (b == x ||  b == y)
equal _ _ = False
