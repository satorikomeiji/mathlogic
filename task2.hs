{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

import System.IO
import Control.Monad
import Text.Parsec 
import Text.Parsec.ByteString --hiding ((<|>))
import Data.Char (isAlpha)
import Data.Hashable
import GHC.Generics (Generic)
import System.Exit (exitSuccess)
import System.Environment
import qualified Data.Set as S
import qualified Data.Map as M
--import Data.String.UTF8 (encode)
import qualified Data.ByteString.Char8 as BS
import qualified Data.HashTable.IO as H

import Control.Applicative ((<$>), (<*),  (*>){-,(<|>)-}, (<*>))

data Expr' = Impl Expr' Expr' | Disj Expr' Expr' | Conj Expr' Expr' | Var String | Not Expr'
          deriving (Show, Generic)


instance Eq Expr' where
  (Impl e1 e2) == (Impl e3 e4) = e1 == e3 && e2 == e4
  (Conj e1 e2) == (Conj e3 e4) = e1 == e3 && e2 == e4
  (Disj e1 e2) == (Disj e3 e4) = e1 == e3 && e2 == e4
  (Not e1) == (Not e2) = e1 == e2
  (Var x1) == (Var x2) = x1 == x2
  _ == _ = False
fromRight           :: Either a b -> b
fromRight (Left _)  = error "Either.Unwrap.fromRight: Argument takes form 'Left _'" -- yuck
fromRight (Right x) = x  
term::Parser Expr'
term = ( ((:) <$> satisfy isAlpha <*> many digit) >>= (return . Var) ) <|> do { string "("; x <- expr; string ")"; return x } <|> Not <$> (string "!" >> term)
impl = do
  e1 <- try disj' <|> term
  string "->"
  e2 <- expr
  return $ Impl e1 e2
--impl = Impl <$> term <* string "->" *> expr
disj = chainl1 term parseOperation 
expr = try impl <|> try disj' <|> term
disj' = chainl1 conj' $ parseOperation' "|"
conj' = chainl1 term  $ parseOperation' "&"
parseOperation' :: BS.ByteString -> Parser (Expr' -> Expr' -> Expr')
parseOperation' op =
  do spaces
     operator <- string $ BS.unpack op
     spaces
     case op of
       "&" -> return Conj
       "|" -> return Disj
parseOperation :: Parser (Expr' -> Expr' -> Expr')
parseOperation =
  do spaces
     operator <-  string "&"  <|> string "|"
     spaces
     case operator of
       "&" -> return Conj
       "|" -> return Disj

variables :: Expr' -> [Char]
variables expr = let vars_ (Var      v)     vs = v ++ vs
                     vars_ (Not      e)     vs = vars_ e vs
                     vars_ (Conj   e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
                     vars_ (Disj   e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
                     vars_ (Impl   e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
--                     vars_ (Biconditional e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
                 in  {-map head . group . sort $-} vars_ expr []

header::Parser ([Expr'], Expr')
header = (,) <$>  expr `sepBy1` char ','  <* string "|-" *> expr
getExpr = fromRight . parse expr ""
axiomExprs = map getExpr axioms                                                       
axioms = ["A->(B->A)",
          "((A->(B->C))->((A->B)->(A->C)))",
          "A&B->A",
          "A&B->B",
          "A->(B->(A&B))",
          "A->(A|B)",
          "B->(A|B)",
          "(A->C)->((B->C)->((A|B)->C))",
          "!A->(A->B)",
          "(A->B)->((A->!B)->!A)",
          "A|!A"
         ]
isAxiom::Expr' -> Bool
isAxiom expr = isAxiom' expr axiomExprs
  where
    isAxiom' expr [x] = appliable (expr, x)
    isAxiom' expr (x:xs) = appliable (expr, x) || isAxiom' expr xs
--appliable exp1@(Disj e1 e2) axiom@(Disj e3 e4) =
--  checkUnique $ appliable' exp1 axiom ++ appliable' exp
--appliable exp1@(Conj e1 e2) axiom@(Conj e3 e4) =
--  checkUnique $ appliable' exp1 axiom ++ appliable' exp
--nappliable exp1@(Impl e1 e2) axiom@(Impl e3 e4) =
--  checkUnique $ appliable' exp1 axiom ++ appliable' exp
appliable (ex, axiom) =
  case applicable' ex axiom of
    Just xs -> checkUnique xs []
    Nothing -> False
  where
    applicable' (Disj e1 e2) (Disj e3 e4) = (++) <$> applicable' e1 e3 <*> applicable' e2 e4
    applicable' (Conj e1 e2) (Conj e3 e4) = (++) <$> applicable' e1 e3 <*> applicable' e2 e4
    applicable' (Impl e1 e2) (Impl e3 e4) = (++) <$> applicable' e1 e3 <*> applicable' e2 e4
    applicable' (Not e1) (Not e2) = applicable' e1 e2
    applicable' ex (Var x) = Just $ [(x, ex)]
    applicable' _ _ = Nothing
    checkUnique [] _ = True
    checkUnique (x:xs) [] = checkUnique xs [x]
    checkUnique (x:xs) tx@(t:ts) = check' x t
      where check' (v1, ex1) (v2, ex2) = if v1 == v2 then
                                           if ex1 == ex2 then
                                             checkUnique xs ts
                                           else
                                             False
                                         else
                                           checkUnique xs (x:tx)


--  where vars = case s of
--          (ex@(Disj e1 e2),ey@(Disj e3 e4)) -> applicable' ex ey
--          (ex@(Conj e1 e2),ey@(Conj e3 e4)) -> applicable' ex ey
--          (ex@(Impl e1 e2),ey@(Conj e3 e4)) -> applicable' ex ey
--          ex@(Not e1) -> applicable'' ex
--        applicable
instance  Hashable  Expr'
--instance  Hashable  [Expr']
type HashTable = H.BasicHashTable Expr' Int
type HashTable' = H.BasicHashTable Expr' [Expr']
usage = "Usage: task1 INPUT_FILE OUTPUT_FILE"
construct_proof h mlines = 
  construct' [] _ = []
  construct' p@(s'@(Impl a delta):proof_sketch) hash1 hash2
  | isAxiom delta || find' delta = delta : ((Impl delta $ Impl a delta) : (s' : construct' proof_sketch (updated_hash1 delta) (updated_hash2 delta)))
  | delta == a = reflProof ++ (s':construct' proof_sketch)
  | 

  where
    updated_hash2 stmnt = S.insert stmnt hash2
    updated_hash1 s''@(Impl prem res) = case M.lookup res hash of
      Just prems -> M.update (add_prem prems) res hash
      Nothing -> M.insert res prem hash
    find' s = member s hypotheses
    proof_sketch = map (Impl last_premise) original_proof
    original_proof = map getExpr mlines
    hypotheses = fromList $ fst $ fromRight $ parse header "" h
    theorem = snd $ fromRight $ parse header "" h
    last_premise = hypotheses !! (length hypotheses)

main = do
  hashes <- H.new::IO HashTable
  impls <- H.new::IO HashTable'
--  forM_ [1..10] (\_ ->
  args <- getArgs
  when ( length args /= 2) $ putStrLn usage >> exitSuccess
                    
  ohandle <- openFile (args !! 1) WriteMode
  ihandle <- openFile (args !! 0) ReadMode
  (h:mlines) <- BS.lines $ BS.hGetContents ihandle
  printProof ohandle $ construct_proof h mlines ohandle
    
      


    
