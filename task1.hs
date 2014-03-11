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
--import Data.String.UTF8 (encode)
import qualified Data.ByteString.Char8 as BS
import qualified Data.HashTable.IO as H
import qualified Data.Set as S
import Control.Applicative ((<$>), (<*),  (*>){-,(<|>)-}, (<*>))

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
fromRight           :: (Show e)=>Either e b -> b
fromRight (Left e)  = error $ show e ++ "Either.Unwrap.fromRight: Argument takes form 'Left _'" -- yuck
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
getExpr = fromRight . parse expr ""
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
main = do
  hashes <- H.new::IO HashTable
  impls <- H.new::IO HashTable'
  putStrLn "Enter premises"
  premises <- (S.fromList . map getExpr . BS.words) <$> BS.getLine
--  forM_ [1..10] (\_ ->
  do
    
                    args <- getArgs
                    when ( length args /= 2) $ putStrLn usage >> exitSuccess
                    
                    --ohandle <- openFile (args !! 1) WriteMode
                    --ihandle <- openFile (args !! 0) ReadMode
                    ohandle <- if ((args !! 1) /= "-" ) then openFile (args !! 1) WriteMode else return stdout
                    ihandle <- if ((args !! 0) /= "-" ) then openFile (args !! 0) ReadMode  else return stdin
                    mlines <- BS.hGetContents ihandle
                    
                    forM_ ([1..] `zip` BS.lines mlines) (\x ->
                                       let
                                         debugHash e = putStrLn $ "inserting " ++ show e
                                         debugImpls t = putStrLn $ "impls " ++ show t
                                         close_handles = do when (ihandle /= stdin)  $ hClose ihandle
                                                            when (ohandle /= stdout) $ hClose ohandle 
                                         expr = getExpr $ snd x
                                         current_line = fst x
                                         error_message =  "Доказательство некорректно с " ++ show current_line ++ " высказывания"::String
                                         implUpdate e@(Impl a1 a2) = do
                                           H.insert hashes e 0
--                                           debugHash e
                                           implies <- H.lookup impls a2
                                           case implies of
                                             Just t -> H.insert impls a2 (a1:t) -- >> debugImpls t
                                             Nothing -> H.insert impls a2 [a1]
                                         implUpdate e = H.insert hashes e 0 -- >> debugHash e
                                         lookUpXs [] _ = hPutStrLn ohandle error_message >> close_handles >> exitSuccess
                                         lookUpXs (x:xs) e = do
                                           impli <- H.lookup hashes x
                                           case impli of
                                             Nothing -> lookUpXs xs e
                                             Just _  -> implUpdate e
                                       in
                                       if isAxiom expr || S.member expr premises then
                                              do
                                                putStrLn $ show current_line ++ "Axiom " ++ show expr
                                                H.insert hashes expr 0
                                                implUpdate expr
                                                --print expr
                                            else 
                                              do
                                                pl <- H.lookup impls expr
                                                case pl of
                                                  Nothing -> hPutStrLn ohandle error_message >> close_handles >> exitSuccess
                                                  Just xs -> lookUpXs xs expr >> (putStrLn $ show current_line ++ "MP " ++ show expr)
     
                                                        
                                                   

                                     )
                    hPutStrLn ohandle "Доказательство корректно"
                    when (ihandle /= stdin)  $ hClose ihandle
                    when (ohandle /= stdout) $ hClose ohandle
                    --hClose ihandle
                    --hClose ohandle


                            
  --              )

--  forM_ [1..100] $ \_ ->  do
--    s <- BS.getLine
--    case parse expr "" s of
--      Left err -> print err
--      Right ex -> print $ variables ex
--    parseTest expr s
--    print $ isAxiom $ getExpr s
    
