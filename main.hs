import Term
import Algebra
import Antidiff
import Data.List

--Integrantes: Moises Gonzalez 11-10406 
--             Fabio Suarez    12-10578

-- Funcion auxiliar para determinar si un subtermino tiene integrales.
containsInteg :: Term -> Bool
containsInteg (Var x) = False
containsInteg (Const x y) = False
containsInteg (Integ a b) = True
containsInteg (Sum a b) = containsInteg a || containsInteg b
containsInteg (Mult a b) = containsInteg a || containsInteg b
containsInteg (Exp a b) = containsInteg a 
containsInteg (Fun a b) = containsInteg b

-- Monads auxiliares
simbInt' :: Term -> IO Term
simbInt' t = do 
    let sol = simbInt t
    if (sol /= t) then do
                  appendFile "index.html" ("$$=" ++ show sol ++ "$$\n")
                  return sol
    else do return sol

pow' :: Term -> IO Term
pow' t = do 
    let sol = pow t
    if (sol /= t) then do
                  appendFile "index.html" ("$$=" ++ show sol ++ "$$\n")
                  return sol
    else do return sol

distrib' :: Term -> IO Term
distrib' t = do 
    let sol = distrib t
    if (sol /= t) then do
                  appendFile "index.html" ("$$=" ++ show sol ++ "$$\n")
                  return sol
    else do return sol

groupAtoms' :: Term -> IO Term
groupAtoms' t = do 
    let sol = groupAtoms t
    if (sol /= t) then do
                  appendFile "index.html" ("$$=" ++ show sol ++ "$$\n")
                  return sol
    else do return sol

simplify' :: Term -> IO Term
simplify' t = do 
    let sol = simplify t
    if (sol /= t) then do
                  appendFile "index.html" ("$$=" ++ show sol ++ "$$\n")
                  return sol
    else do return sol

-- Funcion principal de solve. hace la llamada a las 5 funciones para resolver la antiderivada
solve' :: Term -> IO Term
solve' t 
    | not (containsInteg t) = return t
    | otherwise =
    return t
    >>=simbInt'
    >>=pow'
    >>=distrib'
    >>=groupAtoms'
    >>=simplify'
    >>=solve'

-- Funcion `wrapper` de solve' que crea el archivo index.html y llama a solve'
solve :: Term -> IO Term
solve t = do
    let agrupados = groupAtoms t
    writeFile "index.html" ("<html><head><script src='https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.5/MathJax.js?config=TeX-MML-AM_CHTML' async></script></head><body>\n")
    appendFile "index.html" ("$$" ++ (show agrupados) ++ "$$\n")
    return agrupados
    >>=solve'
    >>=printC
    >>=printFooter

-- Print + c
printC :: Term -> IO Term
printC t = do
    appendFile "index.html" ("$$" ++ (show (t + (Var "C"))) ++ "$$\n")
    return t

-- Funcion auxiliar para imprimir el footer
printFooter :: Term -> IO Term
printFooter t = do
    appendFile "index.html" "</body>\n</html>\n"
    return t
