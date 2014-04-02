{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

import System.IO
import Control.Monad
import Text.Parsec 
import Text.Parsec.ByteString --hiding ((<|>))
--import Data.Attoparsec
--import Data.Attoparsec.ByteString
--import Data.Attoparsec.Char8
--import Data.Attoparsec.Combinator --hiding ((<|>))
import Data.Char (isAlpha, isLower)
--import Data.Hashable
import GHC.Generics (Generic)
import System.Exit (exitSuccess)
import System.Environment
import qualified Data.Set as S
import qualified Data.Map as M
--import Data.String.UTF8 (encode)
import qualified Data.ByteString.Char8 as BS
--import qualified Data.HashTable.IO as H
--import qualified Data.HashMap as HM
import Control.Applicative ((<$>), (<*),  (*>){-,(<|>)-}, (<*>))
import Data.Maybe (fromJust)
import Data.List  (find, intercalate)

data Expr' = Impl Expr' Expr' | Disj Expr' Expr' | Conj Expr' Expr' | Var String [ObjTerm] | Not Expr' | Forall ObjTerm Expr' | Exists ObjTerm Expr'
          deriving (Generic, Ord)
data ObjTerm = ObjTerm String [ObjTerm] | ObjVar String  
            deriving (Generic, Ord)
instance Show ObjTerm where
    show (ObjTerm f objs) = f ++ "(" ++ intercalate "," (map show objs) ++ ")"
    show (ObjVar v)       = v
instance Show Expr' where
    show (Impl e1 e2) = "(" ++ show e1 ++ "->" ++ show e2 ++ ")"
    show (Conj e1 e2) = "(" ++ show e1 ++ "&"  ++ show e2 ++ ")"
    show (Disj e1 e2) = "(" ++ show e1 ++ "|"  ++ show e2 ++ ")"
    show (Not e1)     = "!" ++ show e1
    show (Var "=" (x:x1:[])) = show x ++ "=" ++ show x1
    show (Var x1 tms)     = x1  ++ "(" ++ intercalate "," (map show tms) ++ ")" 
    show (Forall t e) = "@" ++ show t ++ show e
    show (Exists t e) = "?" ++ show t ++ show e
instance Eq ObjTerm where
    ObjTerm s xs == ObjTerm s1 xs1 = s == s1 && xs == xs1
    ObjVar s ==ObjVar s1           = s == s1
    _  == _ = False
instance Eq Expr' where
  (Impl e1 e2) == (Impl e3 e4) = e1 == e3 && e2 == e4
  (Conj e1 e2) == (Conj e3 e4) = e1 == e3 && e2 == e4
  (Disj e1 e2) == (Disj e3 e4) = e1 == e3 && e2 == e4
  (Not e1) == (Not e2) = e1 == e2
  (Var x1 tms) == (Var x2 tms1) = x1 == x2 && tms == tms1
  (Forall t1 e1) == (Forall t2 e2)  = t1 == t2 && e1 == e2
  (Exists t1 e1) == (Exists t2 e2)  = t1 == t2 && e1 == e2
  _ == _ = False
fromRight           :: (Show a)=>Either a b -> b
fromRight (Left e)  = error $ (show e) ++ "Either.Unwrap.fromRight: Argument takes form 'Left _'" -- yuck
fromRight (Right x) = x  
equalsP::Parser Expr'
equalsP = Var "=" <$> ((:) <$> objterm' <* (string "=") <*> ((:) <$> objterm' <*> return [])) 
term::Parser Expr'
term = try equalsP <|> try parseforall <|> try parseexists <|> try (Var <$> ((:) <$> satisfy isAlpha <*> many digit <* string "(") <*> (objterm' `sepBy` string ",") <* string ")") <|> (Var <$> ((:) <$> satisfy isAlpha <*> many digit) <*> return []) <|> do { string "("; x <- expr; string ")"; return x } <|> Not <$> (string "!" >> term)
impl = do
  e1 <- try disj' <|> term
  string "->"
  e2 <- expr
  return $ Impl e1 e2
--impl = Impl <$> term <* string "->" *> expr
getTermWith::ObjTerm -> String -> ObjTerm
getTermWith t []    = t
getTermWith t (x:xs)  = getTermWith (ObjTerm "'" [t]) xs 
parseArOp op = do
    operator <- string op
    case op of
        "+" -> return (\x y -> ObjTerm "+" [x, y])
        "*" -> return (\x y -> ObjTerm "*" [x, y])
objterm'   =   chainl1 objterm''  (parseArOp "+")
objterm''  =  chainl1 objterm''' (parseArOp "*")
objterm''' =  getTermWith <$> objterm <*> many (char '\'') 
--objval  = (ObjVar <$> ((++) <$> ((try (char '0')) <|> ((:) <$> satisfy isLower <*> many digit))  <*> many (char '\'')))   
objterm = try (ObjTerm <$> ((:) <$> satisfy isLower <*> many digit <* string "(") <*> (objterm' `sepBy` string ",") <* string ")") <|> try (between (char '(') (char ')') objterm') <|> (ObjVar <$> ((try (string "0")) <|> ((:) <$> satisfy isLower <*> many digit))) 
--ObjVar <$> ((:) <$> satisfy isLower <*> many digit) 
disj = chainl1 term parseOperation 
expr = try impl <|> try disj' <|> term

parseforall = Forall <$> (string "@" >> (ObjVar <$> ((:) <$> satisfy isLower <*> many digit))) <*> term 
parseexists = Exists <$> (string "?" >> (ObjVar <$> ((:) <$> satisfy isLower <*> many digit))) <*> term 
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
variables expr = let vars_ (Var      v _)     vs = v ++ vs
                     vars_ (Not      e)     vs = vars_ e vs
                     vars_ (Conj   e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
                     vars_ (Disj   e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
                     vars_ (Impl   e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
--                     vars_ (Biconditional e1 e2) vs = vars_ e1 vs ++ vars_ e2 vs
                 in  {-map head . group . sort $-} vars_ expr []

header::Parser ([Expr'], Expr')
header = (,) <$>  (expr `sepBy1` (char ','))  <* (string "|-") <*> expr
getExpr = fromRight . parse expr ""

axiom1 a b = Impl a $ Impl b a
axiom2 a b c = Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c))
axiom3 a b = Impl a (Impl b (Conj a b))
axiom4 a b = Impl (Conj a b) a
axiom5 a b = Impl (Conj a b) b
axiom6 a b = Impl a $ Disj a b
axiom7 a b = Impl b $ Disj a b
axiom8 a b c =Impl (Impl a c) $ Impl (Impl b c) $ Impl (Disj a b) c
axiom9 a b = Impl (Impl a b) (Impl (Impl a (Not b)) (Not a))
axiom10 a = Impl (Not $ Not a) a



isAxiom :: Expr' -> Bool
isAxiom e = isAxiom1 e || isAxiom2 e || isAxiom3 e || isAxiom45 e || isAxiom67 e || isAxiom8 e || isAxiom9 e || isAxiom10 e  || isAxiom12 e || isAxiom13 e || isAriphmetic e
--ax2
isAxiom2 (Impl (Impl a1 b1) (Impl (Impl a2 (Impl b2 c1)) (Impl a3 c2))) = (a1 == a2) && (a2 == a3) && (b1 == b2) && (c1 == c2)
isAxiom2 _ = False

--ax3
isAxiom3 (Impl a1 (Impl b1 (Conj a2 b2))) = (a1 == a2) && (b1 == b2)
isAxiom3 _ = False

--ax4,5
isAxiom45 (Impl (Conj a1 b1) ab) = (a1 == ab) || (b1 == ab)
isAxiom45 _ = False

--ax6,7
isAxiom67 (Impl ab (Disj a1 b1)) = (a1 == ab) || (b1 == ab)
isAxiom67 _ = False

--ax8
isAxiom8 (Impl (Impl a1 c1) (Impl (Impl b1 c2) (Impl (Disj a2 b2) c3))) = (a1 == a2) && (b1 == b2) && (c1 == c2) && (c2 == c3)
isAxiom8 _ = False

--ax9
isAxiom9 (Impl (Impl a1 b1) (Impl (Impl a2 (Not b2)) (Not a3))) = (a1 == a2) && (a2 == a3) && (b1 == b2)
isAxiom9 _ = False

--ax10
isAxiom10 (Impl (Not (Not a1)) a2) = (a1 == a2)
isAxiom10 _ = False

--ax1
isAxiom1 (Impl a1 (Impl b1 a2)) = (a1 == a2)
isAxiom1 _ = False

--axexmiddle
isAxiom11 (Disj a1 (Not a2)) = (a1 == a2)
isAxiom11 _ = False


isAx1 (Impl (Var "=" ([a,b])) (Var "=" ([(ObjTerm "'" ([a1])),(ObjTerm "'" ([b1]))]))) = a == a1 && b == b1
isAx1 _ = False

isAx2 (Impl (Var "=" ([a,b])) (Impl (Var "=" ([a1,c])) (Var "=" ([b1,c1])))) = a == a1 && b == b1 && c == c1
isAx2 _ = False

isAx3 (Impl (Var "=" [(ObjTerm "'" [a]), (ObjTerm "'" [b])]) (Var "=" [a1, b1])) = a == a1 && b == b1
isAx3 _ = False

isAx4 (Not (Var "=" [(ObjTerm "'" [a]), (ObjVar "0")])) = True
isAx4 _ = False

isAx5 (Var "=" [(ObjTerm "+" [a, ObjTerm "'" [b]]), (ObjTerm "'" [ObjTerm "+" [a1, b1]])]) = a == a1 && b == b1
isAx5 _ = False

isAx6 (Var "=" [(ObjTerm "+" [a, ObjVar "0"]), a1]) = a == a1
isAx6 _ = False

isAx7 (Var "=" [(ObjTerm "*" [a, ObjVar "0"]), ObjVar "0"]) = True
isAx7 _ = False

isAx8 (Var "=" [(ObjTerm "*" [a, ObjTerm "'" [b]]), (ObjTerm "+" [(ObjTerm "*" [a1, b1]), a2])]) = a==a1 && a1 == a2 && b == b1
isAx8 _ = False

isAx9 (Impl (Conj psi (Forall x (Impl psi1 psi2))) psi3) = psi1 == psi3 && isFree psi1 x  && (subst psi1 x (ObjVar "0") == psi) && (subst psi1 x (ObjTerm "'" [x]) == psi2)
isAx9 _ = False

isAriphmetic e = isAx1 e || isAx2 e || isAx3 e || isAx4 e || isAx5 e || isAx6 e || isAx7 e || isAx8 e || isAx9 e
--isAx5 (
--free::ObjTerm->Expr'->ObjTerm->Bool
--free x (Forall x1 e1) y = if x1 == y then False else free x e1 y
--free x (Exists x1 e1) y = if x1 == y then False else free x e1 y
--free x (Disj e1 e2) y = free x e1 y && free x e2 y
--free x (Conj e1 e2) y = free x e1 y && free x e2 y
--free x (Impl e1 e2) y = free x e1 y && free x e2 y
--free x (Not e) y = free x e y
--free x (Var _ objs) y = True
boundNumber::Expr'->ObjTerm->Int
boundNumber (Forall x1 e1) x    | x1 == x = varterms e1 x 
                                | otherwise =  boundNumber e1 x 
boundNumber (Exists x1 e1) x    | x1 == x = varterms e1 x 
                                | otherwise = boundNumber e1 x
boundNumber (Disj e1 e2) x  = boundNumber e1 x  + boundNumber e2 x 
boundNumber (Conj e1 e2) x  = boundNumber e1 x  + boundNumber e2 x 
boundNumber (Impl e1 e2) x  = boundNumber e1 x  + boundNumber e2 x 
boundNumber (Not e)      x  = boundNumber e x
boundNumber (Var s xs)   x  = 0 
varterms (Disj e1 e2) x     = varterms e1 x + varterms e2 x
varterms (Conj e1 e2) x     = varterms e1 x + varterms e2 x
varterms (Impl e1 e2) x     = varterms e1 x + varterms e2 x
varterms (Forall x1 e1) x   = varterms e1 x
varterms (Exists x1 e1) x   = varterms e1 x
varterms (Var s xs) x       = foldr (\a b -> b + objvarNumber a x) 0 xs

objvarNumber (ObjVar s) (ObjVar s1) = if s == s1 then 1 else 0
objvarNumber (ObjTerm s ts) x = foldl (\a b -> a + objvarNumber b x) 0 ts 
free::Expr'->ObjTerm->ObjTerm->Bool
free exp x y = all (\t -> (boundNumber exp t) == (boundNumber (subst exp x y) t)) (objvars'' y)

objvars''::ObjTerm->[ObjTerm]
objvars'' x@(ObjVar s) = [x]
objvars'' x@(ObjTerm s xs) = concatMap objvars'' xs

subst::Expr'->ObjTerm->ObjTerm->Expr'
subst expr@(Forall x1 e1) x y = if x1 /= x then Forall x1 (subst e1 x y) else expr --Forall x1 (subst e1 x y)
subst expr@(Exists x1 e1) x y = if x1 /= x then Exists x1 (subst e1 x y) else expr --Exists x1  (subst e1 x y)
subst (Disj e1 e2) x y = Disj (subst  e1 x y)  (subst e2 x y)
subst (Conj e1 e2) x y = Conj (subst  e1 x y)  (subst e2 x y)
subst (Impl e1 e2) x y = Impl (subst  e1 x y)  (subst e2 x y)
subst (Not e) x y = Not $ subst e x y
subst (Var s xs) x y = Var s (replace xs x y)

isFree::Expr'->ObjTerm->Bool
isFree (Forall x1 e1) x = x1 /= x && isFree e1 x
isFree (Exists x1 e1) x = x1 /= x && isFree e1 x 
isFree (Disj e1 e2) x = (isFree  e1 x ) ||  (isFree e2 x)
isFree (Conj e1 e2) x = (isFree  e1 x ) || (isFree e2 x )
isFree (Impl e1 e2) x = (isFree  e1 x ) || (isFree e2 x )
isFree (Not e) x =  isFree e x 
isFree (Var s xs) x = elem x $ concatMap objvars'' xs



replace [] _ _ = []
replace (x:xs) x1 y1 = replaceObj x x1 y1 : replace xs x1 y1
replaceObj x@(ObjVar s) x1 y1   | x == x1 = y1
                                | otherwise = x 
replaceObj (ObjTerm s xs) x1 y1 = ObjTerm s $ map (\x -> replaceObj x x1 y1) xs

freeAndSubst e1 e2 x y = free e1 x y && subst e1 x y == e2
isAxiom12 e@(Impl (Forall x psi) psi1) =  any (freeAndSubst psi psi1 x) (objvars psi1) 
isAxiom12 _ = False
objvars::Expr'->[ObjTerm]
objvars (Disj a b) = objvars a ++ objvars b
objvars (Conj a b) = objvars a ++ objvars b
objvars (Impl a b) = objvars a ++ objvars b
objvars (Not a)    = objvars a
objvars (Exists s e) = s : objvars e
objvars (Forall s e) = s : objvars e
objvars (Var s xs)   = concatMap objvars' xs
objvars' x@(ObjVar s) = [x]
objvars' x@(ObjTerm s xs) = x:(concatMap objvars' xs)
isAxiom13 e@(Impl psi (Exists x psi1)) = any (freeAndSubst psi1 psi x) (objvars psi) 
isAxiom13 _ = False
usage = "Usage: task1 INPUT_FILE OUTPUT_FILE"
checkProof::[Expr']->Either String String
checkProof xs = checkProof' (zip [1..] xs) (S.empty::(S.Set Expr'), M.empty::(M.Map Expr' [Expr']))
checkProof'::[(Int,Expr')]->(S.Set Expr', M.Map Expr' [Expr'])->Either String String
checkProof' [] _ = Right "Доказательство верно"
checkProof' ((current_line,x):xs) hashes@(hash1, hash2) |   isAxiom x   = checkProof' xs (updated_hashes x hashes)
                                                        |   otherwise   = mMP' x hashes  
            where 
                mMP' delta (hash1, hash2) = case M.lookup delta hash2 of
                                                Just rxs -> case find (flip S.member $ hash1) rxs of
                                                            Just deltaj -> checkProof' xs (updated_hashes delta (hash1, hash2))
                                                            Nothing     -> quant' delta (hash1, hash2) 
                                                Nothing -> quant' delta (hash1, hash2) 

                quant' delta@(Impl phi (Forall x psi))  (hash1, hash2) = if isFree phi x  then Left (show current_line ++ "Переменная " ++ show x ++ " входит свободно в формулу " ++ show phi)
                                                                    else
                                                                    if S.member (Impl phi psi) hash1 then
                                                                        checkProof' xs (updated_hashes delta (hash1, hash2)) 
                                                                    else  quant'' delta (hash1, hash2) 
                quant' delta (hash1, hash2) = quant'' delta (hash1, hash2) 
                quant'' delta@(Impl (Exists x psi)  phi)  (hash1, hash2) = if isFree phi x  then Left (show current_line ++ "Переменная " ++ show x ++ " входит свободно в формулу " ++ show phi)
                                                                    else 
                                                                    if S.member (Impl psi phi) hash1 then
                                                                        checkProof' xs (updated_hashes delta (hash1, hash2))
                                                                    else Left (show current_line ++  " Ошибка")
                quant'' delta _ = Left (show current_line ++  " Ошибка")

                updated_hashes::Expr'->(S.Set Expr', M.Map Expr' [Expr'])->(S.Set Expr', M.Map Expr' [Expr'])
                updated_hashes del@(Impl x y) (hash1, hash2) = (S.insert del hash1, insert_impl x y hash2)
                updated_hashes del (hash1, hash2) = (S.insert del hash1, hash2)
                insert_impl::Expr'->Expr'->M.Map Expr' [Expr']->M.Map Expr' [Expr']
                insert_impl x y = M.insertWith (++) y [x] 

main = do
--      forM_ [1..10] (\_ ->
    args <- getArgs
    when ( length args /= 2) $ putStrLn usage >> exitSuccess
                        
    ohandle <- if ((args !! 1) /= "-" ) then openFile (args !! 1) WriteMode else return stdout
    ihandle <- if ((args !! 0) /= "-" ) then openFile (args !! 0) ReadMode  else return stdin
    --mlines <-(map (fromRight . (parse expr "") . BS.pack) . lines) <$> hGetContents ihandle
    --forM mlines (\x -> do putStrLn $ show x)
    mlines <- (map getExpr . BS.lines) <$> BS.hGetContents ihandle
    case checkProof mlines of 
        Right str -> hPutStrLn ohandle str
        Left  err -> hPutStrLn ohandle err
    when (ihandle /= stdin)  $ hClose ihandle
    when (ohandle /= stdout) $ hClose ohandle
      


    
