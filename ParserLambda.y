{
module ParserLambda where
import Data.Char
}

%name parserlamb
%tokentype { Token }
%error { parseError }

%token
	lam { TokenLam } 
	var { TokenVar $$ }
	'.' { TokenPoint }
	'(' { TokenOB }
	')' { TokenCB }
	bool { TokenBool }
	'>' { TokenFun }
	':'  { TokenDPoint }
	
%%

-- regras de producao da gramatica
CalcLamb : var                                        { (Var $1) }
	     |'(' lam '(' var ':' Ty ')' '.' CalcLamb ')' { ( LamAbs $4 $6 $9 )}
	     |'(' CalcLamb CalcLamb ')'                   { ( LamApp $2 $3 ) }
	   
Ty : bool       { ( TyBool ) }
   | Ty '>' Ty { ( TyFun $1 $3 ) } 

{

parseError :: [Token] -> a
parseError b = error "Parse Error"

data Ty 
		= TyBool
		| TyUnit 
		| TyFun Ty Ty 
		| TyErr String 
	deriving (Show,Eq,Ord)

data CalcLamb =  LamTrue
           | LamFalse
           | LamIf CalcLamb CalcLamb CalcLamb
           | Var Char 
           | LamAbs Char Ty CalcLamb
           | LamApp CalcLamb CalcLamb
           | LamUnit
           | LamSeq CalcLamb CalcLamb 
           | LamAs CalcLamb Ty
           | LamLet Char CalcLamb CalcLamb
             deriving (Show,Eq)


data Token 
		= TokenVar Char
		| TokenPoint
		| TokenOB
		| TokenCB
		| TokenLam 
		| TokenBool
		| TokenFun
		| TokenDPoint
	deriving Show


lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
	| areEqual (c:(take 2 cs)) "lam" = TokenLam : lexer (tail(tail(tail(cs))))
	| areEqual (c:(take 3 cs)) "bool" = TokenBool : lexer (tail(tail(tail(cs))))
	| isAlpha c = TokenVar c : lexer cs
	| isSpace c = lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer ('.':cs) = TokenPoint : lexer cs
lexer ('>':cs) = TokenFun : lexer cs
lexer (':':cs) = TokenDPoint : lexer cs

areEqual :: String -> String -> Bool
areEqual a b = a == b

main = getContents >>= print . parserlamb .lexer

}
