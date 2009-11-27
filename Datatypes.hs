module Datatypes where 

-- Aussage mit den Junktoren "und", "oder", "dann", "gdw", "nicht"
data Proposition = Const { constant:: String }                                  -- propositionale Konstante
                 | And   { fstConj :: Proposition, sndConj :: Proposition }
                 | Or    { fstDisj :: Proposition, sndDisj :: Proposition } 
                 | If    { premise :: Proposition, consequence :: Proposition } -- Implikation
                 | Iff   { first   :: Proposition, second :: Proposition }      -- logische Äquivalenz
                 | Neg   { neg     :: Proposition }                             -- Negation
                   deriving (Eq) -- Vergleich bezieht sich auf Syntax

-- Funktionen zum Testen auf die verschiedenen Konstruktoren
isConst (Const _) = True
isConst _         = False
isAnd   (And _ _) = True
isAnd   _         = False
isOr    (Or  _ _) = True
isOr    _         = False
isIf    (If  _ _) = True
isIf    _         = False
isIff   (Iff _ _) = True
isIff   _         = False
isNeg   (Neg _)   = True
isNeg   _         = False

-- Instanz der Show-Klasse. Verwendung von Unicode-Zeichen.
instance Show Proposition where
  show (Const x) = x
  show (And x y) = "(" ++ (show x) ++ " ∧ "   ++ (show y) ++ ")"
  show (Or  x y) = "(" ++ (show x) ++ " ∨ "   ++ (show y) ++ ")"
  show (If  x y) = "(" ++ (show x) ++ " ⊃ "  ++ (show y) ++ ")"
  show (Iff x y) = "(" ++ (show x) ++ " ≡ " ++ (show y) ++ ")"
  show (Neg x)   = "¬" ++ (show x)

-- Datentyp, mit dem ein Beweis dargestellt werden kann. Ein Beweis ist,
-- wie unschwer zu erkennen, ein Baum. Der Datentyp macht keine expliziten
-- Angaben über die Annahmen, von denen das Ergebnis abhängig ist. Dies
-- bedarf einer externen Interpretation.
data Proof        = --Unprovable
                    A        Proposition
                  | IfInt    Proof       Proof 
                  | IfElim   Proof       Proof
                  | IffInt   Proof       Proof
                  | IffElim1 Proof
                  | IffElim2 Proof
                  | OrInt1   Proof       Proof
                  | OrInt2   Proof       Proof
                  | OrElim1  Proof       Proof
                  | OrElim2  Proof       Proof
                  | AndInt   Proof       Proof
                  | AndElim1 Proof  
                  | AndElim2 Proof 
                  | RAA      Proof       Proof       Proof
                  deriving (Eq, Show)

type Assumptions = [Proof]

-- Wandelt einen Beweis wieder in eine Aussage um. Es geht hierbei natürlich
-- Information verloren darüber, wie diese Aussage entstanden ist.
fromProof                 :: Proof -> Proposition
fromProof (A        a)     = a
fromProof (IfInt    a b)   = If (fromProof a) (fromProof b)
fromProof (IfElim   _ b)   = consequence (fromProof b)
fromProof (IffInt   a b)   = Iff (premise (fromProof a)) (consequence (fromProof a))
fromProof (IffElim1 a)     = If (first $ fromProof a) (second $ fromProof a) 
fromProof (IffElim2 a)     = If (second $ fromProof a) (first $ fromProof a)
fromProof (OrInt1   a b)   = Or (fromProof a) (fromProof b)
fromProof (OrInt2   a b)   = Or (fromProof b) (fromProof a)
fromProof (OrElim1  a _)   = fstDisj (fromProof a)
fromProof (OrElim2  a _)   = sndDisj (fromProof a)
fromProof (AndInt   a b)   = And (fromProof a) (fromProof b)
fromProof (AndElim1 a)     = fstConj (fromProof a)
fromProof (AndElim2 a)     = sndConj (fromProof a)
fromProof (RAA      _ _ c) = neg (fromProof c)


