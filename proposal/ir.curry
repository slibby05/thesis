-- This is a basic A-Normal form for Curry
-- All expressions must be trivial

-- That means function calls must evaluate have fully evaluated arguments
-- Note: This isn't the same as eager evaluation.
-- If I have f (4 + 2)
-- then that will be converted to
-- let x = 4 + 2 in f x
-- x is still a thunk, so if f never uses it, then x is never evaluated

-- This is similar to the FlatCurry definition, but it might be better
-- to make Expr more structured
-- Force the free variables to be at the top, then the cases, then the lets ...
data Expr
  = Atom Atom
  | Apply Name Atom
  | Let [(Name, Expr)] Expr
  | Free [Name] Expr
  | Or Atom Atom
  | Case Atom [BranchExpr]
 deriving (Eq, Ord, Read, Show)

data Atom
  = Var Name
  | Lit Literal
  | Cons Name [Expr]
 deriving (Eq, Ord, Read, Show)


