open Analysis;
open Merged;

prog1 = open merged in
  Seq (Ass "x" (BoolLit true))                 -- x = true;
 (Seq (Ass "y" (BoolLit false))                -- y = false;
 (Seq (WhileDo (Var "x") (Ass "x" (Var "y")))  -- while (x) do { x = y };
      (Ass "z" (Not (Var "x")))));             -- z = not x
analyzeLiveVar prog1 >> traverseGraph prog1
