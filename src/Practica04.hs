module Practica04 where

--Sintaxis de la logica proposicional
data Prop = Var String | Cons Bool | Not Prop
            | And Prop Prop | Or Prop Prop
            | Impl Prop Prop | Syss Prop Prop
            deriving (Eq)

instance Show Prop where 
                    show (Cons True) = "⊤"
                    show (Cons False) = "⊥"
                    show (Var p) = p
                    show (Not p) = "¬" ++ show p
                    show (Or p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
                    show (And p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
                    show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
                    show (Syss p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

type Literal = Prop
type Clausula = [Literal]

p, q, r, s, t, u :: Prop
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"
t = Var "t"
u = Var "u"

--Definicion de los tipos para la practica
type Interpretacion = [( String , Bool ) ]
type Estado = ( Interpretacion , [Clausula])
data ArbolDPLL = Node Estado ArbolDPLL | Branch Estado ArbolDPLL ArbolDPLL | Void deriving Show

--IMPLEMENTACION PARTE 1
--Ejercicio 1
conflict :: Estado -> Bool
conflict (_, []) = False
conflict (_, []:_) = True
conflict (m, _:xs) = conflict (m, xs)

--Ejercicio 2
success :: Estado -> Bool
success (_, []) = True
success(_, _) = False

--Ejercicio 3
unit :: Estado -> Estado
unit (m, []) = (m, [])
unit (m, ([Var p1]:xs)) =
    ((p1, True) : m, simplificar (Var p1) xs)
unit (m, ([Not (Var p1)]:xs)) =
    ((p1, False) : m, simplificar (Not (Var p1)) xs)
unit (m, (x:xs)) =
    (m', x : f')
  where
    (m', f') = unit (m, xs)
simplificar :: Literal -> [Clausula] -> [Clausula]

-- En el primer caso si la lista de cláusulas es vacía,
-- se regresa la lista vacía, ya que no hay nada que simplificar
simplificar _ [] = []

-- En el segundo caso si la cabeza de la lista de cláusulas es igual a [l],
-- entonces quitamos esa cláusula porque ya es verdadera,
-- y seguimos simplificando la cola
simplificar l (x:xs)
    | x == [l]  = simplificar l xs

-- En el tercer caso, si la cabeza no es igual a [l] dejamos la cláusula y seguimos con la cola
    | otherwise = x : simplificar l xs

--Ejercicio 4
elim :: Estado -> Estado
elim (m, []) = (m, [])
elim (m, x:xs)
    | revisarClausula m x = elim (m, xs)
    | otherwise = (m', x : f')
  where
    (m', f') = elim (m, xs)
revisarClausula :: Interpretacion -> Clausula -> Bool

-- En el primer caso, si la cláusula es vacía, se regresa false porque no hay literales que revisar
revisarClausula _ [] = False

-- En el segundo caso si la cabeza es var p, verificamos si (p, True) está en la interpretación
-- si está, la cláusula es verdadera si no seguimos revisando la cola
revisarClausula m (Var p2 : ls)
    | (p2, True) `elem` m = True
    | otherwise = revisarClausula m ls

-- En el tercer caso, si la cabeza es not (var p),  verificamos si (p, False) está en la interpretación
-- si está, la cláusula es verdadera si no, seguimos revisando la cola
revisarClausula m (Not (Var p2) : ls)
    | (p2, False) `elem` m = True
    | otherwise = revisarClausula m ls

-- En el último caso, si la literal es de otra forma,  se ignora y seguimos con la cola
revisarClausula m (_ : ls) = revisarClausula m ls

--Ejercicio 5
-- La reduccion quita de cada clausula las literales cuyo complemento ya esta en el modelo
-- si (p, True) esta en M entonces Not p es falsa y se puede quitar de las clausulas
-- si (p, False) esta en M entonces Var p es falsa y se puede quitar
red :: Estado -> Estado
red (m, []) = (m, [])
red (m, c:cs) =
    let (m', cs') = red (m, cs)
    in (m', reducirClausula m c : cs')

reducirClausula :: Interpretacion -> Clausula -> Clausula
reducirClausula _ [] = []

-- si p es verdadera en M, entonces Not p es falsa: la quitamos de la clausula
reducirClausula m (Not (Var p2) : ls)
    | (p2, True) `elem` m = reducirClausula m ls
    | otherwise = Not (Var p2) : reducirClausula m ls

-- si p es falsa en M, entonces Var p es falsa: la quitamos de la clausula
reducirClausula m (Var p2 : ls)
    | (p2, False) `elem` m = reducirClausula m ls
    | otherwise = Var p2 : reducirClausula m ls
reducirClausula m (l : ls) = l : reducirClausula m ls

--Ejercicio 6
-- sep toma una literal l y genera dos ramas de busqueda:
-- una donde l es verdadera y otra donde l es falsa
sep :: Literal -> Estado -> (Estado, Estado)
sep (Var p1) (m, f)     = (((p1, True) : m, f), ((p1, False) : m, f))
sep (Not (Var p1)) (m, f) = (((p1, True) : m, f), ((p1, False) : m, f))
sep _ estado = (estado, estado)

--IMPLEMENTACION PARTE 2
-- auxiliar: cuenta cuantas veces aparece una literal en toda la formula
contarLiteral :: Literal -> [Clausula] -> Int
contarLiteral _ [] = 0
contarLiteral lit (c:cs) = contarEnClausula lit c + contarLiteral lit cs

contarEnClausula :: Literal -> Clausula -> Int
contarEnClausula _ [] = 0
contarEnClausula lit (l:ls)
    | lit == l  = 1 + contarEnClausula lit ls
    | otherwise = contarEnClausula lit ls

-- junta todas las literales de la formula en una lista (con repeticion)
todasLiterales :: [Clausula] -> [Literal]
todasLiterales [] = []
todasLiterales (c:cs) = c ++ todasLiterales cs

-- busca la literal con mayor frecuencia recorriendo la lista de candidatos
buscarMejor :: Literal -> Int -> [Literal] -> [Clausula] -> Literal
buscarMejor mejor _ [] _ = mejor
buscarMejor mejor n (l:ls) clausulas
    | contarLiteral l clausulas > n = buscarMejor l (contarLiteral l clausulas) ls clausulas
    | otherwise = buscarMejor mejor n ls clausulas

--Ejercicio 1
heuristicsLiteral :: [Clausula] -> Literal
heuristicsLiteral clausulas =
    let lits = todasLiterales clausulas
        primera = cabeza lits
    in buscarMejor primera (contarLiteral primera clausulas) (cola lits) clausulas
  where
    cabeza (x:_) = x
    cabeza []    = Cons False 
    cola (_:xs)  = xs
    cola []      = []

hayUnitaria :: [Clausula] -> Bool
hayUnitaria [] = False
hayUnitaria ([_]:_) = True
hayUnitaria (_:cs) = hayUnitaria cs

-- construye el arbol de busqueda del algoritmo DPLL
-- primero aplica elim y red, luego decide que regla usar
construirArbol :: Estado -> ArbolDPLL
construirArbol estado
    | success e = Node e Void
    | conflict e = Void
    | hayUnitaria (snd e) =
        let eu = red (elim (unit e))
        in Node e (construirArbol eu)
    | otherwise =
        let lit = heuristicsLiteral (snd e)
            (e1, e2) = sep lit e
        in Branch e (construirArbol (red (elim e1))) (construirArbol (red (elim e2)))
  where
    e = red (elim estado)

-- recorre el arbol buscando una hoja exitosa (clausulas vacias)
-- si encuentra una regresa el modelo, si no regresa Nothing
buscarModelo :: ArbolDPLL -> Maybe Interpretacion
buscarModelo Void = Nothing
buscarModelo (Node (m, []) _) = Just m
buscarModelo (Node _ sub) = buscarModelo sub
buscarModelo (Branch _ izq der) =
    case buscarModelo izq of
        Just m  -> Just m
        Nothing -> buscarModelo der

--Ejercicio 2
dpll :: [Clausula] -> Interpretacion
dpll formula =
    case buscarModelo (construirArbol ([], formula)) of
        Just m  -> m
        Nothing -> []

--EXTRA
-- para dpll2 necesitamos convertir cualquier Prop a forma clausular
-- primero eliminamos implicaciones y bicondicionales
elimImpl :: Prop -> Prop
elimImpl (Var p1)      = Var p1
elimImpl (Cons b)      = Cons b
elimImpl (Not phi)     = Not (elimImpl phi)
elimImpl (And phi psi) = And (elimImpl phi) (elimImpl psi)
elimImpl (Or phi psi)  = Or  (elimImpl phi) (elimImpl psi)
elimImpl (Impl phi psi) = Or (Not (elimImpl phi)) (elimImpl psi)
elimImpl (Syss phi psi) = And (Or (Not ep) eq) (Or (Not eq) ep)
  where
    ep = elimImpl phi
    eq = elimImpl psi

-- luego convertimos a forma normal negativa (NNF)
-- empujando los Not hacia las variables
nnf :: Prop -> Prop
nnf (Not (Not phi))     = nnf phi
nnf (Not (And phi psi)) = Or  (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Or  phi psi)) = And (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Cons True))   = Cons False
nnf (Not (Cons False))  = Cons True
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or  phi psi) = Or  (nnf phi) (nnf psi)
nnf phi = phi

-- distribuye la disyuncion sobre la conjuncion para llegar a CNF
dist :: Prop -> Prop -> Prop
dist (And phi psi) rho = And (dist phi rho) (dist psi rho)
dist phi (And psi rho) = And (dist phi psi) (dist phi rho)
dist phi psi = Or phi psi

-- convierte NNF a CNF aplicando distribucion recursivamente
toCNF :: Prop -> Prop
toCNF (And phi psi) = And (toCNF phi) (toCNF psi)
toCNF (Or  phi psi) = dist (toCNF phi) (toCNF psi)
toCNF phi = phi

-- convierte una formula ya en CNF a lista de clausulas
cnfAClausulas :: Prop -> [Clausula]
cnfAClausulas (And phi psi) = cnfAClausulas phi ++ cnfAClausulas psi
cnfAClausulas (Cons True)   = []    -- tautologia, no aporta clausulas
cnfAClausulas (Cons False)  = [[]]  -- contradiccion directa
cnfAClausulas phi = [orAClausula phi]

-- convierte una disyuncion a una sola clausula
orAClausula :: Prop -> Clausula
orAClausula (Or phi psi) = orAClausula phi ++ orAClausula psi
orAClausula phi = [phi]

dpll2 :: Prop -> Interpretacion
dpll2 phi = dpll (cnfAClausulas (toCNF (nnf (elimImpl phi))))