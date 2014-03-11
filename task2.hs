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
--import qualified Data.HashMap as HM
import Control.Applicative ((<$>), (<*),  (*>){-,(<|>)-}, (<*>))
import Data.Maybe (fromJust)
import Data.List  (find, init)

data Expr' = Impl Expr' Expr' | Disj Expr' Expr' | Conj Expr' Expr' | Var String | Not Expr'
          deriving (Generic, Ord)
instance Show Expr' where
    show (Impl e1 e2) = "(" ++ show e1 ++ "->" ++ show e2 ++ ")"
    show (Conj e1 e2) = "(" ++ show e1 ++ "&"  ++ show e2 ++ ")"
    show (Disj e1 e2) = "(" ++ show e1 ++ "|"  ++ show e2 ++ ")"
    show (Not e1)     = "!" ++ show e1
    show (Var x1)     = x1

instance Eq Expr' where
  (Impl e1 e2) == (Impl e3 e4) = e1 == e3 && e2 == e4
  (Conj e1 e2) == (Conj e3 e4) = e1 == e3 && e2 == e4
  (Disj e1 e2) == (Disj e3 e4) = e1 == e3 && e2 == e4
  (Not e1) == (Not e2) = e1 == e2
  (Var x1) == (Var x2) = x1 == x2
  _ == _ = False
fromRight           :: (Show a)=>Either a b -> b
fromRight (Left e)  = error $ (show e) ++ "Either.Unwrap.fromRight: Argument takes form 'Left _'" -- yuck
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
header = (,) <$>  (expr `sepBy1` (char ','))  <* (string "|-") <*> expr
getExpr = fromRight . parse expr ""


axiom1 a b = Impl a $ Impl b a
axiom4 a b = Impl (Conj a b) a
axiom5 a b = Impl (Conj a b) b
axiom6 a b = Impl a $ Disj a b
axiom7 a b = Impl b $ Disj a b
axiom8 a b c =Impl (Impl a c) $ Impl (Impl b c) $ Impl (Disj a b) c
axiom9 a b = Impl (Impl a b) (Impl (Impl a (Not b)) (Not a))
axiom10 a = Impl (Not $ Not a) a
--axiom11 a = Disj a (Not a)


isAxiom :: Expr' -> Bool
isAxiom e = isAxiom1 e || isAxiom2 e || isAxiom3 e || isAxiom45 e || isAxiom67 e || isAxiom8 e || isAxiom9 e || isAxiom10 e -- || isAxiom11 e
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
--isAxiom11 (Disj a1 (Not a2)) = (a1 == a2)
--isAxiom11 _ = False



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
construct_proof::[Expr']->Expr'->[Expr']->[Expr']
construct_proof g a p= construct' p  (S.empty, M.empty)
    where
        construct'::[Expr']->(S.Set Expr', M.Map Expr' [Expr'])->[Expr']
        construct' [] _ = []
        construct' (delta:rest) hashes@(hash1, hash2)
            | isAxiom delta || find' delta = delta : (Impl delta $ Impl a delta) : Impl a delta : construct' rest (updated_hashes delta hashes) 
            | delta == a = reflProof delta ++ construct' rest (updated_hashes delta hashes)
            | otherwise = mMP delta hashes ++ construct' rest (updated_hashes delta hashes)
        find' d = S.member d  hypotheses
        hypotheses = S.fromList g
        mMP::Expr'->(S.Set Expr', M.Map Expr' [Expr'])->[Expr']
        mMP delta (hash1, hash2) = let deltaj = fromJust $ find (flip S.member $ hash1 ) $ fromJust $ M.lookup delta hash2
                                       deltak = Impl deltaj delta
                                   in
                                    [Impl (Impl a deltaj) (Impl (Impl a (Impl deltaj delta)) (Impl a delta)),
                                     (Impl (Impl a (Impl deltaj delta)) (Impl a delta)),
                                     Impl a delta]
                                     
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
  hashes <- H.new::IO HashTable
  impls <- H.new::IO HashTable'
--  forM_ [1..10] (\_ ->
  args <- getArgs
  when ( length args /= 2) $ putStrLn usage >> exitSuccess
                    
  ohandle <- if ((args !! 1) /= "-" ) then openFile (args !! 1) WriteMode else return stdout
  ihandle <- if ((args !! 0) /= "-" ) then openFile (args !! 0) ReadMode  else return stdin
  (h:mlines) <- BS.lines <$> BS.hGetContents ihandle
  let   (g, end) = fromRight $ parse header "" h
        proof = map (fromRight . parse expr "") mlines
        tl = length g - 1
        a = g !! tl 
        g' = init g
    in
        printProof ohandle $ construct_proof g' a proof
  when (ihandle /= stdin)  $ hClose ihandle
  when (ohandle /= stdout) $ hClose ohandle
      


    
