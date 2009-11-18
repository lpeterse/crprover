module Main where

import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Maybe
import Data.Function.Predicate

import System.Exit
import System.Console.Readline
import Codec.Binary.UTF8.String 

import Datatypes
import Parser
import Demo
import License
import Manual
import SequenceCalculus

--einige String-Formatierungsfunktionen
putUtf8Ln   = putStrLn . encodeString
underline x = x ++ '\n':( map (const '-') x)

-- Userinterface und Hauptschleife
main = (putUtf8Ln manual) >> readEvalPrintLoop []

readEvalPrintLoop :: [Proof] -> IO ()
readEvalPrintLoop ps = do
  maybeLine <- readline ">> "
  case maybeLine of 
       Nothing     -> exitWith (ExitSuccess) -- EOF / control-d
       Just "exit" -> exitWith (ExitSuccess) 
       Just "clear"-> (addHistory "clear")>> readEvalPrintLoop []
       Just "ls"   -> (addHistory "ls")   >> (putStr $ unlines $ map (encodeString.show) $ map fromProof ps) >> (readEvalPrintLoop ps)
       Just "demo" -> (addHistory "demo") >> (sequence $ map (uncurry prove'n'print) examples) >> (readEvalPrintLoop ps)
       Just "help" -> (addHistory "help") >> (putUtf8Ln manual) >> (readEvalPrintLoop ps)
       Just "license" -> (addHistory "license") >> (putUtf8Ln license) >> (readEvalPrintLoop ps)
       Just line -> do addHistory line
                       case line of
                        'A':' ':line' -> case parse (decodeString line') of
                                           Left err -> do{ putStr "parse error at "; print err}
                                           Right x  -> readEvalPrintLoop (ps `union` [A x])
                        _             -> case parse (decodeString line) of
                                           Left err -> do{ putStr "parse error at "; print err}
                                           Right x  -> catch (prove'n'print x ps) (const $ readEvalPrintLoop ps) 
                       readEvalPrintLoop ps


-- Beweisfunktionen: Iterative Vertiefung mit und ohne Begrenzung. Aktion innerhalb der IO-Monade
prove             :: Proposition -> Assumptions -> Maybe Proof
prove p as         = runProver (deduce p) as (LimitedDepth 4)

prove'n'print     :: Proposition -> Assumptions -> IO ()
prove'n'print p as = do putUtf8Ln $ underline ("Beweis von "++(init $ tail $ show (map fromProof as))++" ⊦ "++(show p)++":")
                        case prove p as of
                          Nothing -> putUtf8Ln "Nicht beweisbar."
                          Just q  -> putUtf8Ln $ unlines $ map show $ proofToSequence q

data Strategy         = LimitedDepth { depth :: Int }
type AssumptionsT m a = StateT Assumptions m a
type StrategyT    m   = StateT Strategy    m 
type SearchM        a = AssumptionsT (StrategyT Maybe) a 
type Prover           = SearchM Proof
type Deducer          = SearchM ()

getAssumptions    :: SearchM Assumptions 
getAssumptions     = get
putAssumptions    :: Assumptions -> SearchM () 
putAssumptions     = put
modAssumptions    :: (Assumptions -> Assumptions) -> SearchM ()
modAssumptions f   = do a <- getAssumptions
                        putAssumptions (f a)

getStrategy       :: SearchM Strategy
getStrategy        = lift get 
putStrategy       :: Strategy -> SearchM ()
putStrategy        = lift . put 

decDepth          :: SearchM ()
decDepth           = do s <- getStrategy  
                        let n = depth s
                        if n==0 
                          then fail "depth-limit reached" 
                          else putStrategy (LimitedDepth (n-1))
                        

liftMaybe         :: Maybe Proof -> Prover
liftMaybe          = lift . lift

runProver         :: Prover -> Assumptions -> Strategy -> Maybe Proof
runProver m as ps  = evalStateT (evalStateT m as) ps


-------------------------------------------------------------------------------
provers  = [assume, split]
deducers = [splitImplications]

deduce  :: Proposition -> Prover
deduce p = do decDepth 
              sequence deducers
              strat <- getStrategy
              as    <- getAssumptions
              let ls = map (\f->f p) provers
              liftMaybe $ listToMaybe $ mapMaybe (\m->runProver m as strat) ls

try     :: Prover -> Prover -> Prover 
try m n  = do as <- getAssumptions
              st <- getStrategy
              if isJust $ runProver m as st then m else n
           
-- Teste, ob zu beweisender Satz im Set of Assumptions steht.
-- Hier wird die Rekursion beendet und ein Teilzweig gilt eventuell als bewiesen.
splitImplications        :: Deducer
splitImplications         = do as <- getAssumptions
                               let as'=[IfElim y z|z<-as, let If p q = fromProof z, let Just y = find (fromProof `equals` p) as] 
                               modAssumptions (`union` as')

splitConjuncts           :: Deducer
splitConjuncts            = do as <- getAssumptions
                               let as'=concat[[AndElim1 z, AndElim2 z]|z<-as, let And p q = fromProof z]
                               modAssumptions (`union` as')

--splitDisjuncts           :: Deducer
--splitDisjuncts            = do as <- getAssumptions
--                               let as'=concat[   |z<-as, let Or p q = fromProof z, 

assume  :: Proposition -> Prover  
assume p = do as <- getAssumptions 
              liftMaybe $ find ((==p).fromProof) as
           
split          :: Proposition -> Prover

split (If p q)  = do modAssumptions (`union` [A p]) 
                     x <- deduce q
                     return (IfInt (A p) x)

split (Iff p q) = do x <- deduce (If p q)
                     y <- deduce (If q p)
                     return (IffInt x y)

split (And p q) = do x <- deduce p
                     y <- deduce q
                     return (AndInt x y)

split (Or p q)  = try (
                       do x <- deduce p
                          return (OrInt1 x (A q))
                      ) (
                       do x <- deduce q
                          return (OrInt2 x (A p))
                      )
{-
-- Versuche im SoA gespiegelte Konditionale zu finden 
tryIffInt                  :: Transformation
tryIffInt q       as pr     = pr q as'
                              where
                                ls  = filter (isIf.fromProof) as
                                mirrored a b = premise a == consequence b && consequence a == premise b 
                                as' = as `union` [IffInt a b | a <- ls, b <- ls, (fromProof a) `mirrored` (fromProof b)]

tryIffElim                 :: Transformation
tryIffElim q      as pr     = pr q as'
                              where
                                ls  = filter (isIff.fromProof) as
                                as' = as `union` (map IffElim1 ls) `union` (map IffElim2 ls)

tryFoobar (Iff p q) as pr   = pr (If p q) as ->> \x->
                              pr (If q p) as ->> \y-> IffInt x y
tryFoobar _         _  _    = Unprovable
                              
                                  
-- Teste, ob die Aussage durch OrIntroduction zustande gekommen sein kann.
tryOrInt                   :: Transformation
tryOrInt (Or p q)  as pr    | pr p as /= Unprovable = pr p as ->> \x-> OrInt1 x (A q)
                            | otherwise             = pr q as ->> \x-> OrInt2 x (A p)
tryOrInt  _        _  _     = Unprovable

-- Wende Or-Eliminatino auf alle möglichen Elemte im SoA an. Versuche jeweils,
-- das negierte Element zu beweisen. Wenn dies möglich ist, erweitere das SoA.
tryOrElim              :: (Proposition -> Proposition) -> Transformation
tryOrElim dj p as pr    = pr p as'
                          where
                            pas = map fromProof as
                            f x = isOr (fromProof x) && (k x) /= Unprovable 
                            k x = pr (Neg (dj (fromProof x))) as
                            ls  = filter f as
                            as' = as `union` (map (\x-> OrElim1 x (k x)) ls) 

tryOrElim1              = tryOrElim sndDisj
tryOrElim2              = tryOrElim fstDisj

-- Versuche, im SoA Ands zu elminieren. Die einzelnen Conjuncte werden dem SoA
-- hinzugefügt.
tryAndElim                 :: Transformation
tryAndElim  p       as pr   = pr p $ as `union` (map AndElim1 ls) `union` (map AndElim2 ls)
                              where
                                ls = filter (\x->isAnd (fromProof x)) as

-- Teste, ob Aussage durch ReductioAdAdsurdum zustande gekommen sein kann.
-- Hierbei wird zunächst das SoA um die Annahme der negierten Aussage erweitert.
-- Danach wird versucht, im SoA ein Element zu finden, von dem auch das Gegenteil
-- beweisbar ist.
tryRAA                     :: Transformation
tryRAA    p        as pr    | null ks   = Unprovable
                            | otherwise = RAA (head ks) (pr (Neg $ fromProof $ head $ ks) as') (A (Neg p))
                              where
                                as' = as `union` [A (Neg p)]
                                ks  = filter ((/=Unprovable).(\x-> pr (Neg x) as').fromProof) as'
-}
-------------------------------------------------------------------------------



