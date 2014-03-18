{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

import System.IO
import Control.Monad
import Text.Parsec 
import Text.Parsec.ByteString --hiding ((<|>))
import Data.Char (isAlpha, isLower)
import Data.Hashable
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
term::Parser Expr'
term = try parseforall <|> try parseexists <|> try (Var <$> ((:) <$> satisfy isAlpha <*> many digit <* string "(") <*> (objterm `sepBy` string ",") <* string ")") <|> (Var <$> ((:) <$> satisfy isAlpha <*> many digit) <*> return []) <|> do { string "("; x <- expr; string ")"; return x } <|> Not <$> (string "!" >> term)
impl = do
  e1 <- try disj' <|> term
  string "->"
  e2 <- expr
  return $ Impl e1 e2
--impl = Impl <$> term <* string "->" *> expr
objterm = try (ObjTerm <$> ((:) <$> satisfy isLower <*> many digit <* string "(") <*> (objterm `sepBy` string ",") <* string ")") <|> ObjVar <$> ((:) <$> satisfy isLower <*> many digit) 
disj = chainl1 term parseOperation 
expr = try impl <|> try disj' <|> term
parseforall = Forall <$> (string "@" >> objterm) <*> term 
parseexists = Exists <$> (string "?" >> objterm) <*> term 
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
isAxiom e = isAxiom1 e || isAxiom2 e || isAxiom3 e || isAxiom45 e || isAxiom67 e || isAxiom8 e || isAxiom9 e || isAxiom10 e  || isAxiom12 e || isAxiom13 e
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
free exp x y = (boundNumber exp x) == (boundNumber (subst exp x y) y)

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
isFree (Var s xs) x = elem x $ concatMap objvars' xs



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
objvars' (ObjTerm s xs) = concatMap objvars' xs
isAxiom13 e@(Impl psi (Exists x psi1)) = any (freeAndSubst psi1 psi x) (objvars psi) 
isAxiom13 _ = False
--instance  Hashable  Expr'
--instance  Hashable  ObjTerm
----instance  Hashable  [Expr']
--type HashTable = H.BasicHashTable Expr' Int
--type HashTable' = H.BasicHashTable Expr' [Expr']
usage = "Usage: task1 INPUT_FILE OUTPUT_FILE"
--construct_proof h mlines = 
--  construct' [] _ = []
--  construct' p@(s'@(Impl a delta):proof_sketch) hash1 hash2
--  | isAxiom delta || find' delta = delta : ((Impl delta $ Impl a delta) : (s' : construct' proof_sketch (updated_hash1 delta) (updated_hash2 delta)))
--  | delta == a = reflProof ++ (s':construct' proof_sketch)
--  | isMP delta = k
--
--  where
--    updated_hash2 stmnt = S.insert stmnt hash2
--    updated_hash1 s''@(Impl prem res) = case M.lookup res hash of
--      Just prems -> M.update (add_prem prems) res hash
--      Nothing -> M.insert res prem hash
--    find' s = member s hypotheses
--    proof_sketch = map (Impl last_premise) original_proof
--    original_proof = map getExpr mlines
--    hypotheses = fromList $ fst $ fromRight $ parse header "" h
--    theorem = snd $ fromRight $ parse header "" h
--    last_premise = hypotheses !! (length hypotheses)

--- ((a -&- b) ->- c) |- (a ->- (b ->- c))
addProof1Internal::Expr'->Expr'->Expr'->[Expr']
addProof1Internal a b c =
        [axiom3 a b
        ,Impl (Conj a b)  c --hypotheses
        ,axiom1 (Impl (Conj a b) c) a
        ,Impl (Impl (Conj a b) c) a
        ,axiom1 (Impl (Conj a b) c) b
        ,(Impl (Impl (Impl (Conj a b) c) (Impl b (Impl (Conj a b) c))) (Impl a (Impl (Impl (Conj a b) c) (Impl b (Impl (Conj a b) c)))))
        ,(Impl a (Impl (Impl (Conj a b) c) (Impl b (Impl (Conj a b) c))))
        ,(Impl (Impl a (Impl (Conj a b) c)) (Impl (Impl a (Impl (Impl (Conj a b) c) (Impl b (Impl (Conj a b) c)))) (Impl a (Impl b (Impl (Conj a b) c)))))
        ,(Impl (Impl a (Impl (Impl (Conj a b) c) (Impl b (Impl (Conj a b) c)))) (Impl a (Impl b  (Impl (Conj a b) c))))
        ,(Impl a (Impl b (Impl (Conj a b) c)))
        ,(Impl (Impl b (Conj a b)) (Impl (Impl b (Impl (Conj a b) c)) (Impl b c)))
        ,(Impl (Impl (Impl b (Conj a b)) (Impl (Impl b (Impl (Conj a b) c)) (Impl b c))) (Impl a (Impl (Impl b (Conj a b)) (Impl (Impl b (Impl (Conj a b) c)) (Impl b c)))))
        ,(Impl a (Impl (Impl b (Conj a b)) (Impl (Impl b (Impl (Conj a b) c)) (Impl b c))))
        ,(Impl (Impl a (Impl b (Conj a b))) (Impl (Impl a (Impl (Impl b (Conj a b)) (Impl (Impl b (Impl (Conj a b) c)) (Impl b c)))) (Impl a (Impl (Impl b (Impl (Conj a b) c)) (Impl b c)))))
        ,(Impl (Impl a (Impl (Impl b (Conj a b)) (Impl (Impl b (Impl (Conj a b) c)) (Impl b c)))) (Impl a (Impl (Impl b (Impl (Conj a b) c)) (Impl b c))))
        ,(Impl a (Impl (Impl b (Impl (Conj a b) c)) (Impl b c)))
        ,(Impl (Impl a (Impl b (Impl (Conj a b) c))) (Impl (Impl a (Impl (Impl b (Impl (Conj a b) c)) (Impl b c))) (Impl a (Impl b c))))
        ,(Impl (Impl a (Impl (Impl b (Impl (Conj a b) c)) (Impl b c))) (Impl a (Impl b c)))
        ,(Impl a (Impl b c))]

--- (a ->- (b ->- c)) |- ((a -&- b) ->- c)
addProof2Internal::Expr'->Expr'->Expr'->[Expr']
addProof2Internal a b c = 
         [(Impl (Conj a b) b)
         ,(Impl (Conj a b) a)
         ,(Impl a (Impl b c))
         ,(Impl (Impl a (Impl b c)) (Impl (Conj a b) (Impl a (Impl b c))))
         ,(Impl (Conj a b) (Impl a (Impl b c)))
         ,(Impl (Impl (Conj a b) a) (Impl (Impl (Conj a b) (Impl a (Impl b c))) (Impl (Conj a b) (Impl b c))))
         ,(Impl (Impl (Conj a b) (Impl a (Impl b c))) (Impl (Conj a b) (Impl b c)))
         ,(Impl (Conj a b) (Impl b c))
         ,(Impl (Impl (Conj a b) b) (Impl (Impl (Conj a b) (Impl b c)) (Impl (Conj a b) c)))
         ,(Impl (Impl (Conj a b) (Impl b c)) (Impl (Conj a b) c))
         ,(Impl (Conj a b) c)]
addProof3Internal::Expr'->Expr'->Expr'->[Expr']
addProof3Internal a b c = 
         [(Impl b (Impl a b))
         ,(Impl a (Impl b c))
         ,(Impl (Impl a (Impl b c)) (Impl b (Impl a (Impl b c))))
         ,(Impl b (Impl a (Impl b c)))
         ,(Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c)))
         ,(Impl (Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c))) (Impl b (Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c)))))
         ,(Impl b (Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c))))
         ,(Impl (Impl b (Impl a b)) (Impl (Impl b (Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c)))) (Impl b (Impl (Impl a (Impl b c)) (Impl a c)))))
         ,(Impl (Impl b (Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c)))) (Impl b (Impl (Impl a (Impl b c)) (Impl a c))))
         ,(Impl b (Impl (Impl a (Impl b c)) (Impl a c)))
         ,(Impl (Impl b (Impl a (Impl b c))) (Impl (Impl b (Impl (Impl a (Impl b c)) (Impl a c))) (Impl b (Impl a c))))
         ,(Impl (Impl b (Impl (Impl a (Impl b c)) (Impl a c))) (Impl b (Impl a c)))
         ,(Impl b (Impl a c))]

construct_proof::[Expr']->Expr'->[Expr']->[Expr']
construct_proof g a p= construct' p  (S.empty, M.empty)
    where
        construct'::[Expr']->(S.Set Expr', M.Map Expr' [Expr'])->[Expr']
        construct' [] _ = []
        construct' (delta:rest) hashes@(hash1, hash2)
            | isAxiom' delta || find' delta = delta : (Impl delta $ Impl a delta) : Impl a delta : construct' rest (updated_hashes delta hashes) 
            | delta == a = reflProof delta ++ construct' rest (updated_hashes delta hashes)
            | otherwise = mMP' delta hashes ++ construct' rest (updated_hashes delta hashes)
        find' d = S.member d  hypotheses
        hypotheses = S.fromList g
        isAxiom' delta@(Impl (Forall x psi) psi1) = let res = isAxiom delta in if res && S.member x freeVars then error ("Используется схема аксиом с квантором по переменной " ++ show x ++ " входящей свободно в допущение " ++ show a) else res
        isAxiom' delta@(Impl psi (Exists x psi1)) = let res = isAxiom delta in if res &&  S.member x freeVars then error ("Используется схема аксиом с квантором по переменной " ++ show x ++ " входящей свободно в допущение " ++ show a) else res                                               
        isAxiom' delta = isAxiom delta
        mMP::Expr'->(S.Set Expr', M.Map Expr' [Expr'])->[Expr']
        mMP delta (hash1, hash2) = let deltaj = fromJust $ find (flip S.member $ hash1 ) $ fromJust $ M.lookup delta hash2
                                       deltak = Impl deltaj delta
                                   in
                                    [Impl (Impl a deltaj) (Impl (Impl a (Impl deltaj delta)) (Impl a delta)),
                                     (Impl (Impl a (Impl deltaj delta)) (Impl a delta)),
                                     Impl a delta]
        mMP' delta (hash1, hash2) = case M.lookup delta hash2 of
                                        Just xs -> case find (flip S.member $ hash1) xs of
                                                    Just deltaj -> mMP delta (hash1, hash2)
                                                    Nothing     -> quant' delta (hash1, hash2)
                                        Nothing -> quant' delta (hash1, hash2)

        quant' delta@(Impl phi (Forall x psi))  (hash1, hash2) = if isFree phi x  then error ("Переменная " ++ show x ++ " входит свободно в формулу " ++ show phi)
                                                            else
                                                            if S.member x freeVars then error ("Используется правило вывода с квантором по переменной " ++ show x  ++ " входящей в допущение " ++ show a)
                                                            else 
                                                            if S.member (Impl phi psi) hash1 then
                                                                            addProof2Internal a phi psi ++
                                                                            [Impl (Conj a phi) (Forall x psi)] ++
                                                                            addProof1Internal a phi (Forall x psi)
                                                            else  quant'' delta (hash1, hash2)
        quant' delta (hash1, hash2) = quant'' delta (hash1, hash2)
        quant'' delta@(Impl (Exists x psi)  phi)  (hash1, hash2) = if isFree phi x  then error ("Переменная " ++ show x ++ " входит свободно в формулу " ++ show phi)
                                                        else
                                                        if S.member x freeVars then error ("Используется правило вывода с квантором по переменной " ++ show x ++ " входящей в допущение " ++ show a)
                                                        else 
                                                        if S.member (Impl psi phi) hash1 then
                                                                        addProof3Internal a psi phi ++
                                                                        [Impl (Exists x psi) (Impl a phi)] ++
                                                                        addProof3Internal (Exists x psi) a phi
                                                        else error "MP error" 
        quant'' delta _ = error ("This statement is invalid " ++ show delta)
 
        freeVars = S.fromList $ filter (isFree a) $ objvars a  
                                                                            
        updated_hashes::Expr'->(S.Set Expr', M.Map Expr' [Expr'])->(S.Set Expr', M.Map Expr' [Expr'])
        updated_hashes del@(Impl x y) (hash1, hash2) = (S.insert del hash1, insert_impl x y hash2)
        updated_hashes del (hash1, hash2) = (S.insert del hash1, hash2)
        insert_impl::Expr'->Expr'->M.Map Expr' [Expr']->M.Map Expr' [Expr']
        insert_impl x y = M.insertWith (++) y [x] 
reflProof stmt = [  axiom1 stmt stmt,
                    axiom1 stmt (Impl stmt stmt),
                    aAX2,
                    aMP1,
                    Impl stmt stmt
                    ]
            where   aAX1 = axiom1 stmt stmt
                    aAX2 = Impl aAX1 $ Impl aAX1' (Impl stmt stmt)
                    aMP1 = Impl (Impl stmt (Impl (Impl stmt stmt) stmt)) (Impl stmt stmt)
                    aAX1'= axiom1 stmt (Impl stmt stmt)
                   
printProof h = mapM_ (hPutStrLn h . show) 
main = do
--  hashes <- H.new::IO HashTable
--  impls <- H.new::IO HashTable'
--  forM_ [1..10] (\_ ->
  args <- getArgs
  when ( length args /= 2) $ putStrLn usage >> exitSuccess
                    
  ohandle <- if ((args !! 1) /= "-" ) then openFile (args !! 1) WriteMode else return stdout
  ihandle <- if ((args !! 0) /= "-" ) then openFile (args !! 0) ReadMode  else return stdin
  (h:mlines) <- BS.lines <$> BS.hGetContents ihandle
  let   (g, end) = fromRight $ parse header "" h
        proof = map (fromRight . parse expr "") mlines
        a = g !! (length g - 1)
        g' = init g

    in
        printProof ohandle $ construct_proof g' a proof
  when (ihandle /= stdin)  $ hClose ihandle
  when (ohandle /= stdout) $ hClose ohandle
      


    
