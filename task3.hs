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
--import qualified Data.HashTable.IO as H
--import qualified Data.HashMap as HM
import Control.Applicative ((<$>), (<*),  (*>){-,(<|>)-}, (<*>))
import Data.Maybe (fromJust)
import Data.List  (find, nub)

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
--type HashTable = H.BasicHashTable Expr' Int
--type HashTable' = H.BasicHashTable Expr' [Expr']
getVariables :: Expr' -> [String]
getVariables expr = nub (getVariables' expr)
    where getVariables' expr =
            case expr of
                Var name -> [name]
                Not a -> getVariables a
                Impl a b -> (getVariables a) ++ (getVariables b)
                Conj a b -> (getVariables a) ++ (getVariables b)
                Disj a b -> (getVariables a) ++ (getVariables b)
data VariableValue = VariableValue String Bool
    deriving(Show)
getVariableValue :: String -> [VariableValue] -> Bool
getVariableValue name [] = error "Empty variable list"
getVariableValue name (head : tail) =
   case head of
      VariableValue name' value -> if (name == name') then
         value
      else
         getVariableValue name tail

truthImplication a b = [b,  axiom1 b a, Impl a b]

calculate :: Expr' -> [VariableValue] -> Bool
calculate (Var name) varlist = getVariableValue name varlist
calculate (Not e) varlist = not $ calculate e varlist
calculate (Impl a b) varlist = (not $ calculate a varlist) || (calculate b varlist)
calculate (Conj a b) varlist = (calculate a varlist) && (calculate b varlist)
calculate (Disj a b) varlist = (calculate a varlist) || (calculate b varlist)

generateAllVariants :: [String] -> [[VariableValue]]
generateAllVariants [] = []
generateAllVariants [name] = [[VariableValue name True], [VariableValue name False]]
generateAllVariants (name:tail) =
    let tailVariants = generateAllVariants tail in
    (map (\ values -> (VariableValue name True):values) tailVariants) ++ (map (\ values -> (VariableValue name False):values) tailVariants)

premsFromVarListExcluding [] _ = []
premsFromVarListExcluding ((VariableValue name val):rest) x 
--    | name == name_ = premsFromVarListExcluding rest x
    | otherwise = if val then (Var name:getRest) else ((Not $ Var name):getRest)
        where getRest = premsFromVarListExcluding rest x  
proveVariantError = error "Unable to prove false statement"

proveVariant :: Expr' -> [VariableValue] -> [Expr']
proveVariant x@(Var name) varlist =
   if getVariableValue name varlist then
      [x]
   else
      proveVariantError
proveVariant x@(Not (Var name)) varlist =
   if not (getVariableValue name varlist) then
      [x]
   else
      proveVariantError
proveVariant x@(Not (Not y)) varlist = 
   if calculate y varlist then
     (proveVariant y varlist) ++
     (doubleNegationProof y) ++ [Not $ Not y]
     
   else
      proveVariantError

                                                                                                                      
proveVariant x@(Impl a b) varlist =
  if calculate b varlist then
    proveVariant b varlist ++ [axiom1 b a] ++ [x]
  else if not $ calculate a varlist then
          construct_proof (premsFromVarListExcluding varlist a) a proof1'
       else
         proveVariantError
  where proof1' = (proveVariant (Not a) varlist) ++
                  [(axiom1 (Not a) (Not b))]  ++
                  [(Impl (Not b) (Not a))] ++
                  (truthImplication (Not b) a) ++
                  [(axiom9 (Not b) a)] ++
                  [right1 (axiom9 (Not b) a), right1 $ right1 $ axiom9 (Not b) a] ++
                  [axiom10 b, b]
  



proveVariant (Not (Impl a b)) varlist =
   if (calculate a varlist) && (not (calculate b varlist)) then
      (proveVariant (Not b) varlist) ++
      [(axiom1 (Not b) (Impl a b)), right1 $ axiom1 (Not b) (Impl a b)] ++
      (proveVariant a varlist) ++
      (construct_proof (premsFromVarListExcluding varlist a) 
       a
       (construct_proof [a] (Impl a b) [a, Impl a b, b])) ++
      [Impl (Impl a b) b] ++
      [(axiom9 (Impl a b) b), right1 $ axiom9 (Impl a b) b] ++
      [Not (Impl a b)]
   else
      proveVariantError
proveVariant (Conj a b) varlist =
  if (calculate a varlist) && (calculate b varlist) then
    proveVariant a varlist ++
    proveVariant b varlist ++
    [Impl a $ Impl b $ Conj a b, Impl b $ Conj a b, Conj a b]
  else
    proveVariantError
proveVariant (Not ( Conj a b)) varlist =
    if (not $ calculate a varlist) then
        proveVariant (Not a) varlist++
        [axiom1 (Not a) (Conj a b), Impl  (Conj a b) (Not a)] ++
        [axiom4 a b] ++
        [axiom9 (Conj a b) a,right1 $ axiom9 (Conj a b) a, Not (Conj a b)]
    else 
    if (not $ calculate b varlist) then
        proveVariant (Not b) varlist++
        [axiom1 (Not b) (Conj a b), Impl (Conj a b) (Not b)] ++
        [axiom5 a b] ++
        [axiom9 (Conj a b) b, right1 $ axiom9 (Conj a b) b, Not (Conj a b)]
    else 
        proveVariantError

proveVariant (Disj a b) varlist =
  if (calculate a varlist) then
    proveVariant a varlist ++
    [axiom6 a b, Disj a b]
  else if (calculate b varlist) then
         proveVariant b varlist ++
         [axiom7 a b, Disj a b]
       else
         proveVariantError


proveVariant (Not ( Disj a b)) varlist = 
   if (not $ calculate a varlist) && (not $ calculate b varlist) then
        proveVariant (Not a) varlist ++
        proveVariant (Not b) varlist ++
        reflProof a ++ 
        [axiom1 (Not b) (Not a), Impl (Not a) (Not b)] ++
        reverseContraposition a b ++
        [axiom8 a b a, right1 $ axiom8 a b a, right1 $ right1 $ axiom8 a b a] ++
        mto (Disj a b) a
    else 
        proveVariantError


--deMorgan p q = construct_proof [] (Disj p q) deMorgWithPrems
--    where deMorgWithPrems = [Disj  p q] ++
--                            [axiom9 (Conj (Not p) (Not q)) 

--nsyl phi hi psi = [Impl phi (Not psi), Impl (Not hi) psi] ++
--                    truthImplication phi  (Impl (Not hi) psi)


reverseContraposition a b =
        construct_proof [Impl (Not a) (Not b)] b $ (
            [Impl (Not a) (Not b)] ++
            contraposition (Not a) (Not b) ++
            [Impl (Not $ Not b) (Not $ Not a)] ++
            [b] ++ doubleNegationProof b ++
            [Not $ Not b] ++
            [Not $ Not a] ++
            [axiom10 a, a])

mto phi psi =   [Impl phi psi, Not psi, axiom1 (Not psi) phi, right1 $ axiom1 (Not psi) phi] ++
                [axiom9 phi psi, right1 $ axiom9 phi psi, right1 $ right1 $ axiom9 phi psi]
            

--proveVariant y@(Not x) varlist =
--  proveVariant (Impl x x) varlist ++
--  proveVariant (Impl x $ Not x) varlist ++
--  [axiom9 x x, right1 $ axiom9 x x, right1 $ right1 $ axiom9 x x, Not x]
proof1' a b varlist = (proveVariant (Not a) varlist) ++
                    [(axiom1 (Not a) (Not b))]  ++
                    [(Impl (Not b) (Not a))] ++
                    (truthImplication (Not b) a) ++
                    [(axiom9 (Not b) a)] ++
                    [right1 (axiom9 (Not b) a), right1 $ right1 $ axiom9 (Not b) a] ++
                    [axiom10 b, b]
  
doubleNegationProof :: Expr' -> [Expr']
doubleNegationProof a = construct_proof [] a $ 
      (reflProof $ Not a) ++
      (truthImplication (Not a) a) ++
      [(axiom9 (Not a) a), right1 $ axiom9 (Not a) a, Not $ Not a]    

right1 (Impl a b) = b
left1  (Impl a b) = a
--proof of A->!!A
--axiom10reverse ex = construct_proof 
contraposition a b =
   construct_proof [] (Impl a b) $
   construct_proof [Impl a b] (Not b) $
    (truthImplication a (Not b)) ++
        [(Impl a b)] ++
        [(axiom9 a b), right1 (axiom9 a b)] ++
    [Not a]
                                                            
                                                  
  

--getProofWithAssumptions::Expr'->Vars
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

excludedMiddle a =
            [(axiom7 a (Not a))] ++
            (contraposition (Not a) (Disj a (Not a))) ++
            [Impl (Not $ Disj a (Not a)) (Not $ Not a)] ++
               [(axiom6 a (Not a))] ++
               (contraposition a (Disj a (Not a))) ++
               [Impl (Not $ Disj a (Not a)) (Not $ a)] ++
            [(axiom9 (Not (Disj a (Not a))) (Not a)), right1 $ (axiom9 (Not (Disj a (Not a))) (Not a))] ++
            [Not $ Not (Disj a (Not a))] ++ 
            [(axiom10 (Disj a (Not a))), Disj a (Not a)]

processVariable :: Expr' -> [VariableValue] -> [String] -> [Expr']
processVariable expr valueList [] = proveVariant expr valueList
processVariable expr valueList (var:varTail) =
   let proofOf b = processVariable expr (VariableValue var b : valueList) varTail in
   let proofTrue = proofOf True in
   let proofFalse = proofOf False in
   let v = Var var in
   let toVar (VariableValue s x) = if x then Var s else (Not $ Var s) in
   let prems = map toVar valueList in
    excludedMiddle v ++
   -- [axiom11 v] ++ --MP
        (construct_proof prems (Not v) proofFalse) ++ --MP
            (construct_proof prems v proofTrue) ++ --MP
            [(axiom8 v (Not v) expr)] ++
            [right1 $ axiom8 v (Not v) expr] ++
        [right1 $ right1 $ axiom8 v (Not v) expr] ++
    [expr]

        
do_main :: Handle -> BS.ByteString -> IO ()
do_main h str =
    let expression = getExpr str
        variables = getVariables expression in
    if foldl (&&) True $ map (calculate expression) (generateAllVariants variables) then
      --mapM_ (\variant -> do {hPutStrLn h ("Proof for variant" ++ show variant) ; printProof h $ proveVariant expression variant }) $ generateAllVariants variables
      printProof h $ processVariable expression [] variables
    else
      error "The formula is not logically valid!"

main = do
  --hashes <- H.new::IO HashTable
  --impls <- H.new::IO HashTable'
--  forM_ [1..10] (\_ ->
  args <- getArgs
  when ( length args /= 2) $ putStrLn usage >> exitSuccess
                    
  ohandle <- if ((args !! 1) /= "-" ) then openFile (args !! 1) WriteMode else return stdout
  ihandle <- if ((args !! 0) /= "-" ) then openFile (args !! 0) ReadMode  else return stdin
  (h:mlines) <- BS.lines <$> BS.hGetContents ihandle
  do_main ohandle h
  when (ihandle /= stdin)  $ hClose ihandle
  when (ohandle /= stdout) $ hClose ohandle
      


    
