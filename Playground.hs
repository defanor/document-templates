-- http://defanor.uberspace.net/notes/document-templates.html

import Control.Monad.Except
import Data.List
import qualified Data.Foldable as DF
import Data.Maybe
import Control.Applicative
import Control.Monad

-- http://augustss.blogspot.ru/2007/10/simpler-easier-in-recent-paper-simply.html

type Sym = String
type Template = String
type IsImplicit = Bool


-- might be nice to move things like Implicit and additional Pi args
-- to a separate AST later; perhaps when will map it all to a
-- map/database
data Expr
    = Var Sym
    | App Expr Expr
    | Lam Sym Type Expr
    | Pi IsImplicit Template Sym Type Type
    | Kind Kinds
    | Prim Prims
    | Implicit
    deriving (Eq, Read, Show)
type Type = Expr

data Kinds = Star | Box deriving (Eq, Read, Show)
data Prims = PInt Int | PString String deriving (Eq, Read, Show)

primType :: Prims -> String
primType (PInt _) = "Int"
primType (PString _) = "String"

newtype Env = Env [(Sym, (Type, Template))] deriving (Show)
type Ctx = Env

type ErrorMsg = String

type TC a = Either ErrorMsg a

initialEnv :: Env
initialEnv = Env []

extend :: Sym -> Type -> Template -> Env -> Env
extend s t tmpl (Env r) = Env ((s, (t, tmpl)) : r)

freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])
freeVars (Pi _ _ i k t) = freeVars k `union` (freeVars t \\ [i])
freeVars (Kind _) = []
freeVars (Prim _) = []

subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
  where sub e@(Var i) = if i == v then x else e
        sub (App f a) = App (sub f) (sub a)
        sub (Lam i t e) = abstr Lam i t e
        sub (Pi ii tm i t e) = abstr (Pi ii tm) i t e
        sub (Kind k) = Kind k
        sub (Prim x) = Prim x
        fvx = freeVars x
        cloneSym e i = loop i
           where loop i' = if i' `elem` vars then loop (i ++ "'") else i'
                 vars = fvx ++ freeVars e
        abstr con i t e
          | v == i = con i (sub t) e
          | i `elem` fvx = let i' = cloneSym e i
                               e' = substVar i i' e
                           in  con i' (sub t) (sub e')
          | otherwise = con i (sub t) (sub e)

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' = subst s (Var s')

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
    case lookup s r of
    Just (t, _) -> return t
    Nothing -> throwError $ "Cannot find variable " ++ s

nf :: Expr -> Expr
nf ee = spine ee []
  where
    -- a hack, but only need this one function for now
    spine (App (Var "pred") n) _ = case n of
      (App (Var "LS") m) -> m
      _ -> Var "LZ"
    spine (App f a) as = spine f (a:as)
    spine (Lam s t e) [] = Lam s (nf t) (nf e)
    spine (Lam s _ e) (a:as) = spine (subst s a e) as
    spine (Pi ii tm s k t) as = app (Pi ii tm s (nf k) (nf t)) as
    spine f as = app f as
    app f as = foldl App f (map nf as)

whnf :: Expr -> Expr
whnf ee = spine ee []
  where spine (App f a) as = spine f (a:as)
        spine (Lam s t e) (a:as) = spine (subst s a e) as
        spine f as = foldl App f as

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v)   (Var v')    = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t1 e) (Lam s' t2 e') = t1 == t2 && alphaEq e (substVar s' s e')
alphaEq (Pi _ _ s t1 e) (Pi _ _ s' t2 e') = t1 == t2 && alphaEq e (substVar s' s e')
alphaEq (Kind x) (Kind y) = x == y
alphaEq _ _ = False

betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

tCheck :: Env -> Expr -> TC Type
tCheck r (Prim p) = return $ Var (primType p)
tCheck r (Var s) =
    findVar r s
tCheck r (App f a) = do
    tf <- tCheckRed r f
    case tf of
     Pi _ _ x at rt -> do
        ta <- tCheck r a
        unless (betaEq ta at) $ throwError $ "Bad function argument type: expected " ++
          printExpr at ++ ", got " ++ printExpr ta
        return $ subst x a rt
     other -> throwError $ "Non-function in application: " ++ show other ++ "(" ++ printExpr f ++ ")"
tCheck r (Lam s t e) = do
    tCheck r t
    let r' = extend s t "" r
    te <- tCheck r' e
    let lt = Pi False "" s t te
    tCheck r lt
    return lt
tCheck _ (Kind Star) = return $ Kind Box
tCheck _ (Kind Box) = throwError "Found a Box"
tCheck r (Pi ii tmpl x a b) = do
    s <- tCheckRed r a
    let r' = extend x a tmpl r
    t <- tCheckRed r' b
    when ((s, t) `notElem` allowedKinds) $ throwError "Bad abstraction"
    return t

tCheckRed :: Env -> Expr -> TC Expr
tCheckRed r e = liftM whnf (tCheck r e)

allowedKinds :: [(Type, Type)]
allowedKinds = [(Kind Star, Kind Star), (Kind Star, Kind Box), (Kind Box, Kind Star), (Kind Box, Kind Box)]

-- decls

target :: Type -> Type
target (Pi _ _ _ _ e) = target e
target (App e _) = target e
target e = e

ensureTarget :: Type -> Type -> TC ()
ensureTarget t ty = unless (target ty == t) $
                    throwError ("Wrong target: expected " ++ show t ++ ", got " ++ show (target ty))

-- type Program = (Env, Ctx)
type Decl = (Type, [(Sym, Type, Template)])


checkConstructors :: Env -> (Sym, Decl) -> TC ()
checkConstructors env (n, (t, cl)) = do
  -- stict positivity
  -- _ <- mapM (strictlyPositive n . snd) cl
  -- types
  _ <- tCheck env t
  _ <- mapM (tCheck (extend n t "" env) . snd . (\(x,y,z) -> (x, y))) cl
  -- targets
  _ <- ensureTarget (Kind Star) t
  _ <- mapM (ensureTarget (Var n) . snd . (\(x,y,z) -> (x, y))) cl
  return ()

addDecl :: Env -> (Sym, Decl) -> TC Env
addDecl env sd@(n, (t, cl)) = do
  _ <- checkConstructors env sd
  return $ foldr extend' (extend n t ("(" ++ n ++ ")") env) cl
  where
    extend' (n, t, tmpl) = extend n t tmpl

addDecls :: Env -> [(Sym, Decl)] -> TC Env
addDecls = DF.foldrM (flip addDecl)

primEnv :: Env
primEnv = Env [("String", (Kind Star, "(String)")),
               ("Int", (Kind Star, "(Int)")),
               ("pred", (Pi False "pred1" "n" (Var "LNat") (Var "LNat"), "<pred>"))]

basicEnv :: TC Env
basicEnv = addDecls primEnv [("LazyList", (Pi False "list1" "x" (Kind Star)
                                           (Pi False "list2" "n" (Var "LNat")
                                            (Kind Star)),
                                           [("LNil", Pi True "lnil1" "a" (Kind Star)
                                                    (Pi True "lnil2" "n" (Var "LNat")
                                                     (App (App (Var "LazyList") (Var "a")) (Var "n"))),
                                             "CLNil"),
                                            ("LCons", Pi True "lcons1" "a" (Kind Star)
                                                      (Pi True "lnil2" "n" (Var "LNat")
                                                       (Pi False "lcons2" "x" (Var "a")
                                                        (Pi False "lcons3" "xs"
                                                         (App (App (Var "LazyList") (Var "a"))
                                                          (App (Var "pred") (Var "n")))
                                                         (App (App (Var "LazyList") (Var "a")) (Var "n"))))),
                                             "CLCons")])),
                             ("LNat", (Kind Star,
                                      [("LZ", Var "LNat", "CLZ"),
                                       ("LS", Pi False "ls1" "x" (Var "LNat") (Var "LNat"), "CLS")])),
                             ("Nat", (Kind Star,
                                      [("Z", Var "Nat", "CZ"),
                                       ("S", Pi False "s1" "x" (Var "Nat") (Var "Nat"), "CS")]))]

check :: Env -> Expr -> TC Expr
check env expr = do
  tCheck env expr
  return expr

check' :: Expr -> TC Type
check' expr = do
  env <- basicEnv
  tCheck env expr

-- print and render

printExpr :: Expr -> String
printExpr (Var s) = s
printExpr (App e1 e2) = "(" ++ printExpr e1 ++ " " ++ printExpr e2 ++ ")"
printExpr (Lam s t e) = "(" ++ s ++ ":" ++ printExpr t ++ " => " ++ printExpr e ++ ")"
printExpr (Pi False _ s t e) = "(" ++ s ++ ":" ++ printExpr t ++ " -> " ++ printExpr e ++ ")"
printExpr (Pi True _ s t e) = "{" ++ s ++ ":" ++ printExpr t ++ " -> " ++ printExpr e ++ "}"
printExpr (Kind Star) = "*"
printExpr (Kind Box) = "[]"
printExpr (Prim (PInt x)) = show x
printExpr (Prim (PString x)) = show x
printExpr Implicit = "_"


isPi :: Type -> Bool
isPi Pi{} = True
isPi _ = False


render :: Env -> Expr -> TC String
render r@(Env env) (Var v) = return $ snd (fromJust $ lookup v env)
render r (App e1 e2) = do
  t1 <- tCheck r e1
  t2 <- tCheck r e2
  case t1 of
    Pi ii tm x at rt -> do
      re1 <- render r e1
      re2 <- case (ii, hasZero t2) of
        (_, True) -> return "[delayed]"
        (True, _) -> do
          v <- render r e2
          return $ "{" ++ v ++ "}"
        _ -> render r e2
      return $ "(" ++ re1 ++ " " ++ re2 ++ " " ++ tm ++ ")"
  where
    hasZero (Var "LZ") = True
    hasZero (App (Var "LS") e2) = False
    hasZero (App e1 e2) = hasZero e1 || hasZero e2
    hasZero _ = False
render r v = return $ printExpr v

data Direction = L | R

findSub :: Expr -> [Direction] -> Expr
findSub (App e1 e2) (L:xs) = findSub e1 xs
findSub (App e1 e2) (R:xs) = findSub e2 xs
findSub expr [] = expr


renderSub :: Env -> Expr -> [Direction] -> Int -> TC String
renderSub env expr d skip = do
  t <- tCheck env (findSub expr d)
  -- get type and value
  -- then skip value * skip of that type constructors
  -- then render

  -- find LNat and type, remember
  -- increase every LNat in that type
  -- skip
  -- render
  render env (findSub expr d)

-- implicits: not a nice approach here, but will work for now (for
-- those basic datatypes, that is)

hasImplicits :: Expr -> Bool
hasImplicits Implicit = True
hasImplicits (App e1 e2) = hasImplicits e1 || hasImplicits e2
hasImplicits (Lam s t e) = hasImplicits t || hasImplicits e
hasImplicits (Pi _ _ s t e) = hasImplicits t || hasImplicits e
hasImplicits _ = False

-- checks if sym is not shadowed in type, returns final type that
-- could contain that sym
notShadowed :: Sym -> Type -> Maybe Type
notShadowed s (Pi _ _ s' _ e)
  | s == s' = Nothing
  | otherwise = notShadowed s e
notShadowed s e = Just e

-- sym -> constructor after implicit -> expected -> maybe value of that sym
varInType :: Sym -> Type -> Type -> Maybe Expr
varInType s e expected = case notShadowed s e of
  (Just result) -> findVar expected result
  where
    findVar :: Type -> Type -> Maybe Type
    findVar exp (Var v)
      | v == s = Just exp
      | otherwise = Nothing
    findVar (App e1 e2) (App e1' e2') = findVar e1 e1' <|> findVar e2 e2'
    findVar _ _ = Nothing
    -- add other cases later

-- "type" here is a target type, e.g. there's no Pi's
solveImplicits :: Env -> Expr -> Type -> TC Expr
-- here's an implicit -- check the expected type, and that's it
solveImplicits env (App e1 e2) t
  | hasImplicits e1 = do
    -- implicits on the left: solve them, then try again, passing type
    woImpl <- solveImplicits env e1 t
    t1 <- tCheck env woImpl
    solveImplicits env (App woImpl e2) t
  | e2 == Implicit = do
    t1 <- tCheck env e1
    case t1 of
      (Pi _ _ ps pt pe) -> case varInType ps pe t of
        Nothing -> throwError $ "unable to solve implicit: " ++ ps ++ " in " ++ printExpr e1 ++ " of type " ++ printExpr t
        (Just val) -> return $ App e1 val
  | otherwise = do
    -- no implicits on the left: solve implicits on the right, passing type
    t1 <- tCheck env e1
    case t1 of
      (Pi _ _ _ l1 _) -> do
        woImpl2 <- solveImplicits env e2 l1
        return $ App e1 woImpl2
solveImplicits env other t
  | hasImplicits other = throwError $ "can't solve implicits in " ++ printExpr other ++ " of type " ++ printExpr t
  | otherwise = return other


implicitPositions :: Type -> Int -> [Int]
implicitPositions (Pi True _ _ _ next) n = n : implicitPositions next (n + 1)
implicitPositions (Pi False _ _ _ next) n = implicitPositions next (n + 1)
implicitPositions _ _ = []

appLevel :: Expr -> Int
appLevel (App e1 e2) = 1 + appLevel e1
appLevel _ = 0

requiresImplicit :: Env -> Expr -> TC Bool
requiresImplicit env e = do
  t <- tCheck env (target e)
  let ip = implicitPositions t 0
  let al = appLevel e
  return $ al `elem` ip

ensureImplicit :: Env -> Expr -> TC Expr
ensureImplicit env e = do
  er <- requiresImplicit env e
  if er
    then ensureImplicit env (App e Implicit)
    else return e

insertImplicits :: Env -> Expr -> TC Expr
insertImplicits env (App e1 e2) = do
  e1n <- insertImplicits env e1
  e2n <- insertImplicits env e2
  ensureImplicit env (App e1n e2n)
insertImplicits env e@(Var v) = ensureImplicit env e
insertImplicits env other = return other


insAndSolveImpl :: Env -> Expr -> Type -> TC Expr
insAndSolveImpl env e t = do
  wi <- insertImplicits env e
  solveImplicits env wi t


intLazyList :: Expr
intLazyList = (App (App (Var "LCons") (Prim (PInt 1)))
               (App (App (Var "LCons") (Prim (PInt 2)))
                (App (App (Var "LCons") (Prim (PInt 3)))
                 (App (App (Var "LCons") (Prim (PInt 4)))
                  (App (App (Var "LCons") (Prim (PInt 5)))
                   (App (App (Var "LCons") (Prim (PInt 6)))
                    (App (App (Var "LCons") (Prim (PInt 7)))
                     (App (App (Var "LCons") (Prim (PInt 8)))
                      (Var "LNil")))))))))

illTest :: TC String
illTest = do
   env <- basicEnv
   expr <- insAndSolveImpl env intLazyList (App (App (Var "List") (Var "Int"))
                                            (App (Var "LS") (App (Var "LS") (Var "LZ"))))
   render env (nf expr)

-- do; env <- basicEnv; expr <- insAndSolveImpl env intList' (App (Var "List") (Var "Int")); render env expr Nothing

-- do; env <- basicEnv; expr <- insAndSolveImpl env (Var "MkTest2") (App (Var "Test") (App (Var "LS") (App (Var "LS") (Var "LZ")))); t <- tCheck env expr; return $ printExpr (nf t)


