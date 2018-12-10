module TyCalcLamb where

import ParserLambda
-- import Text.Show.Functions

-- types: conjunto de tipos: Booleanos e tipo funcional
-- data Ty = TyUnit | TyBool | TyFun Ty Ty | TyErr String deriving (Show,Eq,Ord)

--Definição de um tipo para o contexto usado no type checker
type TypeContext = [(Char,Ty)]

--Definição de um tipo para o contexto usado na representacao de CalcLambos sem nome
type Contexto = [(Char,Int)]

-- variavel: x
-- Abstração: lam x . expressao lambda
-- Aplicação: t t

--Nameless Representation of CalcLambs
data LamNL = TrueNL
         | FalseNL
         | IfNL LamNL LamNL LamNL 
         | VarNL Int
         | LamAbsNL LamNL
         | LamAppNL LamNL LamNL
         | UnitNL
         | SeqNL LamNL LamNL
         | LamAsNL LamNL Ty
         | LamLetNL Int LamNL LamNL
           deriving(Show, Eq)

-- ******************************************************************
-- ************************TypeChecker*******************************
-- ******************************************************************
--Testa se nao eh erro
isnterr :: Ty -> Bool
isnterr (TyErr str) = False
isnterr _ = True

typeof :: TypeContext -> CalcLamb -> Ty
typeof ctx LamTrue = TyBool
typeof ctx LamFalse = TyBool
typeof ctx (LamIf t1 t2 t3) = if ((typeof ctx t1) == TyBool) 
                             then let tyT2 = typeof ctx t2
                                      tyT3 = typeof ctx t3
                                  in if (isnterr tyT2) && (isnterr tyT3) && (tyT2 == tyT3) then tyT2
                                     else TyErr "arms of conditional have diff types"
                             else TyErr "guard of conditional not boolean"
typeof ctx (Var char) = findfirst char ctx
typeof ctx (LamAbs x tyT1 t2) = let ctx' = addbind ctx x tyT1 
                                    tyT2 = typeof ctx' t2 
                                in 
                                 if (isnterr tyT2) 
                                   then TyFun tyT1 tyT2
                                   else tyT2
typeof ctx (LamApp t1 t2) = let tyT1 = typeof ctx t1 -- T1 -> T2
                                tyT2 = typeof ctx t2 -- T1
                            in 
                             if (isnterr tyT1)
                               then 
                                 if (isfun tyT1)
                                   then                                       
                                     if (isnterr tyT2)
                                       then get_argument tyT1 tyT2                               
                                       else tyT2
                                   else TyErr "first CalcLamb is not a function"          
                               else tyT1

typeof ctx LamUnit = TyUnit
typeof ctx (LamSeq t1 t2) = let tyT1 = typeof ctx t1
                                tyT2 = typeof ctx t2
                            in
                             if ( tyT1 == TyUnit)
                               then
                                 tyT2
                               else
                                 TyErr "first argument is not unit type"
                                 
typeof ctx (LamAs t ty) = let ty'= typeof ctx t
                         in if (ty==ty') then ty else TyErr "Type is not the same as ascription"
typeof ctx (LamLet x t1 t2) = let ty1 = typeof ctx t1
                                  ctx' = addbind ctx x ty1
                                  ty2 = typeof ctx' t2
                             in ty2 
                                  
                            
--Adiciona CHAR no CONTEXTO
addbind :: TypeContext -> Char -> Ty -> TypeContext
addbind ctx char ty =  ctx++[(char,ty)]

findfirst :: Char -> TypeContext -> Ty
findfirst x [] = TyErr "no char in context"
findfirst x (head:tail) = if x == fst (head)
                   then snd (head)
                   else findfirst x tail 

isfun :: Ty -> Bool
isfun (TyFun a b) = True
isfun _ = False

get_argument :: Ty -> Ty -> Ty
get_argument (TyFun tyT1 tyT1') tyT2 = if ( tyT1 == tyT2) then tyT1' else TyErr "argument invalid"

-- ******************************************************************
-- *************************FREE VARS********************************
-- ******************************************************************

-- Função que retorna as variáveis livres de uma função
freevars :: CalcLamb -> [Char]
freevars (LamIf t1 t2 t3) = let t1' = freevars t1
                                t2' = freevars t2
                                t3' = freevars t3
                           in t1'++t2'++t3'
freevars (Var char) = [char]
freevars (LamAbs char ty t) = let l = freevars t
                             in remove l char
freevars (LamApp t1 t2) = (freevars t1)++(freevars t2)
freevars (LamSeq t1 t2) = (freevars t1)++(freevars t2)
freevars _ = []

--Função que remove um caracter de uma lista
remove :: [Char] -> Char -> [Char]
remove [] v = []
remove (a:x) v = if (a == v) then x else a:(remove x v)

-- Função que cria um contexto para um expressão
-- levando em conta as suas variáveis livres
gamma :: CalcLamb -> Contexto
gamma (t) = zip (freevars (t)) (reverse [0..(length (freevars (t)) - 1)])

-- ******************************************************************
-- *****************Nameless Representation of CalcLambs*****************
-- ******************************************************************

-- Função que substitui o nome das variáveis para números
-- LamAbs 'x' (Var 'x') = LamAbsNL (VarNL 0)
removenames :: CalcLamb -> Contexto -> (LamNL, Contexto)
removenames LamTrue c = (TrueNL, c)
removenames LamFalse c = (FalseNL, c)
removenames (LamIf t1 t2 t3) c = let t1' = fst (removenames t1 c)
                                     t2' = fst (removenames t2 c)
                                     t3' = fst (removenames t3 c)
                                in (IfNL t1' t2' t3', c)
removenames (Var x) c = (VarNL (findfirstNL x c), c)
removenames (LamAbs x ty t) c = let tmp = (removenames t (insertC x c) )                                 
                               in (LamAbsNL (fst tmp), c)
removenames (LamApp t1 t2) c = let t1' = fst (removenames t1 c)
                                   t2' = fst (removenames t2 c)
                               in
                                 (LamAppNL t1' t2' , c) 
removenames LamUnit c = (UnitNL, c)
removenames (LamSeq t1 t2) c = let t1' = fst (removenames t1 c)
                                   t2' = fst (removenames t2 c)
                              in (SeqNL t1' t2', c) 

-- Função que retorna a primeira ocorrência de x em c (buscando da direita para a esquerda)
findfirstNL :: Char -> Contexto -> Int
findfirstNL x c = if x == fst (last c)
                   then snd (last c)
                   else findfirstNL x (init c) 

-- Função que insere x na direita do contexto
-- somando o indice das outras posições
insertC :: Char -> Contexto -> Contexto 
insertC (x) c =  [ (fst a, (snd a) + 1) | a <- c]++[(x,0)]

-- Função que retorna uma expressão sem nomes
-- para original, dado seu contexto
-- LamAbsNL (VarNL 0) = LamAbs 'x' (Var 'x')
restorenames :: LamNL -> Contexto -> (CalcLamb, Contexto)
restorenames TrueNL c = (LamTrue, c)
restorenames FalseNL c = (LamFalse, c)
restorenames (IfNL t1 t2 t3) c = let t1' = fst (restorenames t1 c)
                                     t2' = fst (restorenames t2 c)
                                     t3' = fst (restorenames t3 c)
                                 in (LamIf t1' t2' t3', c)
restorenames (VarNL x) c = (Var (findfirstNL' x c), c)
restorenames (LamAbsNL t) c = let charc = geraChar c ['a'..'z']
                                  c' = insertC charc c
                              in (LamAbs charc TyBool (fst(restorenames t c')),c')
restorenames (LamAppNL t1 t2) c = let t1' = fst (restorenames t1 c)
                                      t2' = fst (restorenames t2 c)
                                  in ((LamApp t1' t2'), c) 
restorenames (UnitNL) c = (LamUnit, c)
restorenames (SeqNL t1 t2) c = let t1' = fst (restorenames t1 c)
                                   t2' = fst (restorenames t2 c)
                               in (LamSeq t1' t2', c) 


geraChar :: Contexto -> [Char] -> Char
geraChar c [] = error "todas as letras usadas"
geraChar c (a:b) = if (verificaCC c a) then (geraChar c b) else a

verificaCC :: Contexto -> Char -> Bool
verificaCC [] c = False
verificaCC ((a,_):b) c = if (a==c) then True else verificaCC b c
                                 
-- Função que substitui o valor inteiro passado
-- pelo respectivo caracter no contexto                                 
findfirstNL' :: Int -> Contexto -> Char
findfirstNL' x c = if x == (snd (last c)) then fst(last c) else findfirstNL' x (init c)

-- ******************************************************************
-- *****************Shifting em CalcLambos sem nome**********************
-- ******************************************************************

----shifting recebe tres parametros: o valor de incremento "d",
----o valor do cutoff "c" (a partir de qual numero deve ser incrementado)
----e o CalcLambo
shifting :: Int -> Int -> LamNL -> LamNL
shifting d c (VarNL k) = if (k < c) then (VarNL k) else (VarNL (k+d)) 
shifting d c (LamAbsNL t) = LamAbsNL (shifting d (c+1) t)
shifting d c (LamAppNL t1 t2) = LamAppNL (shifting d c t1) (shifting d c t2)

----- Substitution
subs ::  (Int, LamNL) -> LamNL -> LamNL
subs (x, s) (VarNL y) = if (x==y) then s else (VarNL y) 
subs (x, z) (LamAbsNL t1) = LamAbsNL (subs(x+1, shifting 1 0 z) t1)
subs (x,l3) (LamAppNL l1 l2) = LamAppNL (subs  (x,l3) l1)  (subs (x,l3) l2)

-- ******************************************************************
-- **************************EVAL************************************
-- ******************************************************************

-- eval usando a beta redução em CalcLambos lambda sem nome
isval :: LamNL -> Bool
isval (VarNL a) = True
isval (LamAbsNL t) = True
isval (LamAppNL t1 t2) = False 

internalEval :: LamNL -> LamNL
internalEval (TrueNL) = TrueNL
internalEval (FalseNL) = TrueNL
internalEval (IfNL t1 t2 t3) = IfNL (internalEval t1) (internalEval t2) (internalEval t3)
internalEval (VarNL y) = VarNL y
internalEval (LamAbsNL t1) = LamAbsNL t1
internalEval (LamAppNL (LamAbsNL t1) t2) = if (isval t2) 
                                            then (shifting (-1) 0 (subs (0, shifting 1 0 t2)   t1 ))
                                            else LamAppNL (LamAbsNL t1) (internalEval t2)
internalEval (LamAppNL t1 t2) = let t1' = internalEval t1 
                                in LamAppNL t1' t2
internalEval (SeqNL t1 t2) = let t1' = internalEval t1
                             in 
                               if t1' == UnitNL
                                 then t2
                                 else SeqNL t1' t2
--internalEval (SeqNL UnitNL t2) = t2
internalEval UnitNL = UnitNL
internalEval (LamAsNL t ty) = if (isval t) then t
                             else let t'= internalEval t
                                  in LamAsNL t' ty
internalEval (LamLetNL n t1 t2) = if (isval t1) then subs (n,t1) t2 
                                 else let t1'= internalEval t1 
                                      in LamLetNL n t1' t2



internalEval1 :: LamNL -> LamNL
internalEval1 t = let t' = internalEval t
              in if (t' == t) then t else (internalEval1 t')

eval :: CalcLamb -> Contexto -> CalcLamb
eval l c = let x = removenames l c 
               y = internalEval1 (fst x)
           in fst (restorenames y c)

iswelltyped :: Ty -> Bool
iswelltyped _ = True

tc =[('y',TyBool), ('z', TyBool), ('x', TyBool), ('y', TyFun TyBool TyBool),('z', TyFun TyBool TyBool)]
tv = []

interpret :: CalcLamb -> CalcLamb
interpret t  = if (iswelltyped (typeof tc t)) 
                  then eval t (gamma t)
               else error "Interpreter error"

                 
-- ******************************************************************
-- *****************Exemplos de Type Checker*********************
-- ******************************************************************

main = getContents >>= print . interpret . parserlamb .lexer