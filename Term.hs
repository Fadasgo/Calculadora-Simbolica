module Term where

--Integrantes: Moises Gonzalez 11-10406 
--             Fabio Suarez    12-10578

data Term =
    Const Int Int
    | Var String
    | Fun String Term
    | Integ Term Term
    | Sum Term Term
    | Mult Term Term
    | Exp Term Int

t :: Term
t = Var "t"

u :: Term
u = Var "u"

v :: Term
v = Var "v"

w :: Term
w = Var "w"

x :: Term
x = Var "x"

y :: Term
y = Var "y"

z :: Term
z = Var "z"

sen :: (Term) -> Term
sen (t1) = Fun "sen" t1

cosen :: (Term) -> Term
cosen (t1) = Fun "cos" t1

instance Show Term where
  show (Const p 0) =
     error "Expresión inválida, el cero no puede estár en el denominador"
  show (Const 0 _) = show 0
  show (Const p 1) = show p
  show (Const p q) = "\\frac{" ++show p ++ "}{" ++ show q ++ "}"
  show (Var x) = x
  show (Fun "sen" t) = "sen" ++ "(" ++ show t ++ ")"
  show (Fun "cos" t) = "cos" ++ "(" ++ show t ++ ")"
  show (Fun f t) =  f ++ "(" ++ show t ++ ")"
  show (Integ t x) = "\\int " ++ show t ++ " d" ++ show x
  show (Sum t1 t2) = show t1 ++ "+" ++ show t2
  show (Mult t1 t2) = show t1 ++ " " ++ show t2
  show (Exp (Fun "sen" t) n) =
    "sen" ++ "^{" ++ show n ++ "}" ++ "(" ++ show t ++ ")"

  show (Exp (Fun "cos" t) n) =
     "cos" ++ "^{" ++ show n  ++ "}" ++ "(" ++ show t ++ ")"

  show (Exp t n) = "" ++ show t ++ "^{" ++ show n ++ "}"

instance Num Term where
  t1 + t2 = Sum t1 t2
  t1 * t2 = Mult t1 t2
  fromInteger a = (Const (fromInteger a) 1)

-- equality
equality :: Term -> Term -> Bool
equality (Exp x a) y = (x == y)
equality y (Exp x a) = (x == y)
equality _ _ = False

equalityConst :: Term -> Term -> Bool
equalityConst (Const a b) (Const c d) = (a == c) && (b == d)
equalityConst _ _ = False

instance Eq Term where
  (Const x a) == (Const y b) = True
  (Var x) == (Var y) = (x == y)
  (Fun x a) == (Fun y b) = (x == y) && (a == b)
  (Integ x a) == (Integ y b) = (x == y) && (a == b)
  (Exp x a) == (Exp y b) = (x == y) && (0 <= a) && (0 <= b)
  (Sum a b) == (Sum x y) = (a == x || a == y) && (b == x ||  b == y)
  (Mult a b) == (Mult x y) = (a == x || a == y) && (b == x ||  b == y)
  _ == _ = False

instance Ord Term where
    
    -- Las fracciones son los MENORES elementos en el ordenamiento
    compare (Const a b) (Const c d) = EQ
    compare (Const a b) _ = LT
    compare _ (Const a b) = GT

    -- una integral es menor a otra si su integrando es menor
    compare (Integ t1 s1) (Integ t2 s2) = compare t1 t2

    -- Las integrales son los MAYORES elementos en el ordenamiento
    compare (Integ x y) _ = GT
    compare _ (Integ x y) = LT

    -- Un termino suma es es menor que un termino multiplicacion y exponenciacion
    compare (Sum a b) (Mult c d) = LT
    compare (Mult c d) (Sum a b) = GT

    -- El termino multiplicacion es menor que un termino exponenciacion
    compare (Mult a b) (Exp c n) = LT
    compare (Exp c n) (Mult a b) = GT
    
    -- El primer termino de la suma y las multiplicaciones
    compare (Sum a b) (Sum c d)
        | a /= b = compare a b
        | a == b = compare c d

    compare (Mult a b) (Mult c d)
        | a /= b = compare a b
        | a == b = compare c d

    -- Todo atomo distinto de integral es menor que un termino que no sea atomo
    compare (Sum a b) _ = LT
    compare _ (Sum a b) = GT
    compare (Mult a b) _ = LT
    compare _ (Mult a b) = GT
    -- compare (Sum a b) (Fun x t) = LT

    -- Una variable es menor a otra si su nombre es menor alfabeticamente
    compare (Var x) (Var y) = compare x y

    -- Una funcion es menor si sus nombres son menores, si son iguales se decide
    -- por los argumentos
    compare (Fun s1 t1) (Fun s2 t2)
        | s1 /= s2 = compare s1 s2
        | s1 == s2 = compare t1 t2

    -- Entre una variable y una funcion se decide alfabeticamente
    compare (Fun s t) (Var q) = compare s q
    compare (Var q) (Fun s t) = compare q s

    -- Orden de exponenciales
    compare (Exp a n) (Exp b m)
        | a /= b = compare a b
        | a == b = compare n m

    compare (Exp a n) t = compare a t
    compare t (Exp a n) = compare t a
