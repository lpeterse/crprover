module Prover (prove) where

import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Maybe
import Data.Function.Predicate

import Datatypes

data Strategy         = LimitedDepth { depth :: Int } deriving Show
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
addAssumption a    = modAssumptions (a:)
addAssumptions as  = mapM_ addAssumption as

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

evalProver         :: Prover -> Assumptions -> Strategy -> Maybe Proof
evalProver m as ps  = evalStateT (evalStateT m as) ps

runProver          :: Prover -> Assumptions -> Strategy -> Maybe ((Proof, Assumptions), Strategy)
runProver m as ps   = runStateT (runStateT m as) ps

-- Beweisfunktionen: Iterative Vertiefung mit und ohne Begrenzung. Aktion innerhalb der IO-Monade
prove             :: Proposition -> Assumptions -> Maybe Proof
prove p as         = prove' 1
                     where
                       prove' 6 = Nothing
                       prove' n = case evalProver (deduce p) as (LimitedDepth n) of
                                    Nothing -> prove' (n+1)
                                    Just p  -> Just p


-------------------------------------------------------------------------------

deduce  :: Proposition -> Prover
deduce p = do decDepth 
              sequence deducers
              strat <- getStrategy
              as    <- getAssumptions
              let ls = map (\f->f p) provers
              liftMaybe $ listToMaybe $ mapMaybe (\m->evalProver m as strat) ls

try     :: Prover -> Prover -> Prover 
try m n  = do as <- getAssumptions
              st <- getStrategy
              case runProver m as st of
                Just ((p, as), st) -> putAssumptions as >> putStrategy st >> return p
                _                  -> n

provers  = [assume, split, absurdum]
deducers = [splitImplications, splitConjuncts, splitDisjuncts, splitBiconditionals]

assume  :: Proposition -> Prover  
assume p = do as <- getAssumptions 
              liftMaybe $ find ((==p).fromProof) as

absurdum  :: Proposition -> Prover
absurdum p = do addAssumption (A $ negated p)
                as <- getAssumptions
                let ps  = map (deduce . negated . fromProof) as
                a <- foldl try (fail "") ps
                b <- liftMaybe $ find (opposite a) as
                return (RAA a b (A $ negated p))
              where
                opposite a b = fromProof a == negated (fromProof b)

split          :: Proposition -> Prover

split p@(Const _) = deduce p

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

split (Neg (Neg (p))) = deduce p
split (Neg p)         = deduce (Neg p)


splitImplications        :: Deducer
splitImplications         = do as <- getAssumptions
                               addAssumptions [IfElim y z|z<-as, isIf (fromProof z), let If p q = fromProof z, y<-as, p==(fromProof y)]

splitConjuncts           :: Deducer
splitConjuncts            = do as <- getAssumptions
                               addAssumptions $ concat [[AndElim1 z, AndElim2 z]|z<-as, isAnd(fromProof z)]

splitDisjuncts           :: Deducer
splitDisjuncts            = do as <- getAssumptions
                               let ors = filter (isOr.fromProof) as
                               mapM_ orElimination ors

try'                     :: Prover -> (Proof -> Deducer) -> Deducer
try' m d                  = do as <- getAssumptions
                               st <- getStrategy
                               case evalProver m as st of
                                 Just pr -> d pr
                                 Nothing -> return ()

orElimination            :: Proof -> Deducer
orElimination a           = do let Or p q = fromProof a
                               try' (deduce (negated p)) (\b-> addAssumption (OrElim2 a b))
                               try' (deduce (negated q)) (\b-> addAssumption (OrElim2 a b))

splitBiconditionals      :: Deducer
splitBiconditionals       = do as <- getAssumptions
                               addAssumptions $ concat [[IffElim1 z, IffElim2 z]|z<-as, isIff (fromProof z)]

deleteDN                 :: Deducer
deleteDN                  = modAssumptions $ map f
                            where
                              f x = case fromProof x of
                                      Neg (Neg _) -> DNElim x
                                      _           -> x
