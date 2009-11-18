module Prover (prove) where

import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Maybe
import Data.Function.Predicate

import Datatypes

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

-- Beweisfunktionen: Iterative Vertiefung mit und ohne Begrenzung. Aktion innerhalb der IO-Monade
prove             :: Proposition -> Assumptions -> Maybe Proof
prove p as         = runProver (deduce p) as (LimitedDepth 4)

-------------------------------------------------------------------------------

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
 
provers  = [assume, split]
deducers = [splitImplications]

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
