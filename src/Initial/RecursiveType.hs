{-
01. Requirements:
  * Sums and products
  * Functions
  * Monomorphic types
  * Currying
-}
module Initial.RecursiveType where

import           Data.Map                       ( Map )
import qualified Data.Map                      as M

-- Syntax definition
type Id    = String
type Error = String

data Type = TInt | TBool deriving (Show, Eq)

data Value = VNumber Integer
           | VBool Bool
           | VUndefined
           deriving (Show, Eq)

data Expression = Constant Value
                | Variable Id
                | Plus Expression Expression
                | Minus Expression Expression
                | Multiply Expression Expression
                | Divide Expression Expression
                | And Expression Expression
                | Or Expression Expression
                deriving (Show, Eq)

data Statement = Sequence Statement Statement
               | NewVariable Type Id
               | Assign Id Expression
               | Print Expression
               | If Expression Statement Statement
               | Nop
               deriving (Show, Eq)

-- Evaluation state
data EvaluationState =
  EvaluationState { executionStack :: [Statement]
                  , symbolTable    :: SymbolTable
                  , output         :: [Value]
                  } deriving (Show, Eq)

type SymbolTable = Map Id (Maybe Value)
type FinalState  = EvaluationState

-- Evaluation of programs produces traces
data Trace =
  Trace { trSteps :: [(Statement, EvaluationState, EvaluationState)]
        , trError :: Maybe Error
        } deriving (Show, Eq)

newEvaluationState :: [Statement] -> EvaluationState
newEvaluationState statements =
  EvaluationState { executionStack = [mkProgram statements]
                  , symbolTable    = M.empty
                  , output         = []
                  }

stepTrace :: Statement
          -> EvaluationState
          -> EvaluationState
          -> Trace
          -> Trace
stepTrace statement before after oldTrace =
  oldTrace { trSteps = trSteps oldTrace ++ [(statement, before, after)] }

errorTrace :: Error -> Trace -> Trace
errorTrace error oldTrace =
  oldTrace { trError = Just error }

emptyTrace :: Trace
emptyTrace =
  Trace { trSteps = [], trError = Nothing }

showTrace :: Trace -> String
showTrace t@(Trace ((_, s, _) : _) _) = go t $ "Running program:\n" ++ show (head $ executionStack s) ++ "\n\n"
  where
    go :: Trace -> String -> String
    go (Trace [] Nothing) acc = acc
    go (Trace [] (Just error)) acc = acc ++ "\nException: " ++ error ++ "\n"
    go (Trace ((statement, before, after) : tl) error) acc =
      let acc' = acc ++ "--------\nExecuting: " ++ onlyLhs statement ++ "\n" ++
                        "Next state is: \n"     ++ showState after   ++ "\n"
      in  go (Trace tl error) acc'
    showState :: EvaluationState -> String
    showState (EvaluationState executionStack symbolTable output) =
      "Execution stack: " ++ show executionStack ++ "\n" ++
      "Symbol table   : " ++ show symbolTable    ++ "\n" ++
      "Output         : " ++ show output         ++ "\n"
    onlyLhs :: Statement -> String
    onlyLhs (Sequence lhs _) = "Sequence " ++ show lhs ++ " ..."
    onlyLhs statement        = show statement

-- What is evaluation of expressions?
eval :: Expression -> SymbolTable -> Either Error Value
eval (Variable id)       symbolTable =
  case M.lookup id symbolTable of
    Just (Just value) -> Right value
    Just Nothing      -> Left  $ "Variable " ++ id ++ " has no associated value"
    Nothing           -> Left  $ "Variable " ++ id ++ " not defined"
eval (Constant value) _           = Right value
eval (Plus leftE rightE) symbolTable =
  withEvaluated (numericOp (+)) symbolTable leftE rightE
eval (Minus leftE rightE) symbolTable =
  withEvaluated (numericOp (-)) symbolTable leftE rightE
eval (Multiply leftE rightE) symbolTable =
  withEvaluated (numericOp (*)) symbolTable leftE rightE
eval (Divide leftE rightE) symbolTable =
  withEvaluated (numericOp div) symbolTable leftE rightE
eval (And leftE rightE) symbolTable =
  withEvaluated (booleanOp (&&)) symbolTable leftE rightE
eval (Or leftE rightE) symbolTable =
  withEvaluated (booleanOp (||)) symbolTable leftE rightE

withEvaluated :: (Value -> Value -> Either Error Value)
              -> SymbolTable
              -> Expression
              -> Expression
              -> Either Error Value
withEvaluated operator symbolTable leftE rightE =
  case eval leftE symbolTable of
    Left  error -> Left $ "Failed evaluating left operand with " ++ error
    Right leftV ->
      case eval rightE symbolTable of
        Left  error  ->
          Left  $ "Failed evaluating right operand with " ++ error
        Right rightV -> operator leftV rightV

numericOp :: (Integer -> Integer -> Integer)
          -> Value
          -> Value
          -> Either Error Value
numericOp op (VNumber left) (VNumber right) =
  Right $ VNumber (op left right)
numericOp _ _ _ = Left "Invalid operand types."

booleanOp :: (Bool -> Bool -> Bool)
          -> Value
          -> Value
          -> Either Error Value
booleanOp op (VBool left) (VBool right) = Right $ VBool (op True False)
booleanOp _ _ _ = Left "Invalid operand types."

-- What is evaluation of statements?
oneStep :: Statement -> EvaluationState -> Either Error EvaluationState
oneStep (Sequence left right) state@(EvaluationState executionStack _ _) =
  Right $ state { executionStack = left : right : executionStack }
oneStep (Assign id expression) state@(EvaluationState _ symbolTable _) =
  let newValue = eval expression symbolTable
  in  case newValue of
        Left      error -> Left  $ "Failed evaluating expression: " ++ error
        Right newValue' ->
          case M.lookup id symbolTable of
            Just _  -> Right $ state { symbolTable = M.insert id (Just newValue') symbolTable }
            Nothing -> Left  $ "Variable " ++ id ++ " is not declared."
oneStep (NewVariable _ id) state@(EvaluationState _ symbolTable _) =
  case M.lookup id symbolTable of
    Nothing -> Right state { symbolTable = M.insert id Nothing symbolTable }
    Just  _ -> Left  $ "Variable " ++ id ++ " is already declared"
oneStep (Print expression) state@(EvaluationState _ symbolTable output) =
  let newValue = eval expression symbolTable
  in  case newValue of
        Left error      -> Left $ "Failed evaluating expression: " ++ error
        Right newValue' -> Right $ state { output = newValue' : output }
oneStep (If condition leftS rightS) state@(EvaluationState _ symbolTable _) =
  let newValue = eval condition symbolTable
  in  case newValue of
        Left error      -> Left $ "Failed evaluating expression: " ++ error
        Right newValue' -> if newValue' == VBool True
                           then oneStep leftS state
                           else oneStep rightS state
oneStep Nop state = Right state

allSteps :: EvaluationState -> Trace -> Trace
allSteps _ trace@(Trace _ (Just _))                  = trace
allSteps state@(EvaluationState [] _ _) trace        = trace
allSteps state@(EvaluationState (hd : tl) _ _) trace =
  let newState = state { executionStack = tl }
  in  case oneStep hd newState of
        Left  error          -> errorTrace error trace
        Right evaluatedState ->
          allSteps evaluatedState (stepTrace hd state evaluatedState trace)

-- Syntax helpers
mkProgram :: [Statement] -> Statement
mkProgram = foldr Sequence Nop

mkNum :: Integer -> Expression
mkNum = Constant . VNumber

mkBool :: Bool -> Expression
mkBool = Constant . VBool

traceExample :: [Statement] -> Trace
traceExample example =
  allSteps (newEvaluationState example) emptyTrace

evaluateExample :: [Statement] -> Either Error EvaluationState
evaluateExample example =
  let (Trace ((_, _, lastState) : _) error) = traceExample example
  in  case error of
        Just e  -> Left e
        Nothing -> Right lastState

-- Examples
example01 :: [Statement]
example01 =
  [ NewVariable TInt "v"
  , Assign "v" (mkNum 2)
  , Print (Variable "v")
  ]

example02 :: [Statement]
example02 =
  [ NewVariable TInt "a"
  , NewVariable TInt "b"
  , Assign "a" (Plus (mkNum 2)
                     (Multiply (mkNum 3) (mkNum 5)))
  , Assign "b" (Plus (Variable "a") (mkNum 1))
  , Print  (Variable "b")
  ]

example03 :: [Statement]
example03 =
  [ NewVariable TBool "a"
  , NewVariable TInt  "v"
  , Assign "a" (mkBool True)
  , If (Variable "a")
       (Assign "v" (mkNum 2))
       (Assign "v" (mkNum 3))
  , Print (Variable "v")
  ]
