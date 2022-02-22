{-  A general tree with different task-categorys, subtrees are categorys with Tasklist as leafs
     -The empty tree and or leaf is given by Void
     -A non-empty TaskTree with label taskCategory has subtrees with a different label taskCategory and is given by Node taskCategory
     INVARIANT: For the moment unknown, looking up definition and doing research
  -}
data TaskTree taskCategory = Void | TaskLeaf Tasklist | Node taskCategory [TaskTree taskCategory]
type Tasklist = [Task]
type Task = (String, Bool)

testTree = Node "All Tasks" [
  Node "Groceries" [
  TaskLeaf [("Apples", False), ("Apples", False)]], 
  Node "Important" [
  TaskLeaf [("Finish datatypes", False), ("Get to Diamond1",False)]]
  ]
{- main 
     RETURNS: ... 
     SIDE EFFECTS: 
     EXAMPLES: 
   -}
main :: IO ()
main = do
    putStrLn  "\nWelcome to your HaskMonitor\n\nMenu                           🚩 - important\n1: All tasks                   🟥 - todo     \n2: Important only              ✅ - done     \n3: List manager\n4: Task manager"
    action <- getLine
    putStrLn "You chose to go to" 

-- function :: ... -> ...
--   {- empty function x
--      RETURNS: ...
--    -}
-- function = undefined 
   
-- function :: ... -> ...
--   {- empty function x
--      RETURNS: ...
--    -}
-- function = undefined 
   
-- function :: ... -> ...
--   {- empty function x
--      RETURNS: ...
--    -}
-- function = undefined 

-- function :: ... -> ...
--   {- empty function x
--      RETURNS: ...
--    -}
-- function = undefined 

-- function :: ... -> ...
--   {- empty function x
--      RETURNS: ...
--    -}
-- function = undefined 