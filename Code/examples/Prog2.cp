open Analysis;
open Merged;

prog2 = open merged in
  Seq (Ass "x" (IntLit 10))                         -- x = 10;
 (Seq (IfElse (Less (Var "x") (IntLit 0))           -- if (x < 0) {
              (Ass "y" (Add (Var "x") (IntLit 1)))  --   y = x + 1
                                                    -- } else {
              (Ass "y" (Sub (Var "x") (IntLit 1)))) --   y = x - 1
                                                    -- }
      (Ass "z" (Add (Var "x") (Var "y"))));         -- z = x + y
analyzeLiveVar prog2 >> traverseGraph prog2
