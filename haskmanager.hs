{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
import System.IO ()
import Test.HUnit


{-  A binary-tree with different task-categorys which are polymorphic labels
- The empty binary search tree is given by Void.
- A non-empty binary search tree with label x,
  left subtree l and right subtree r is given
  by Node l x r. 
  INVARIANT: In any node (Node l x r), x is larger than all
  the labels of the labels of
  nodes in l and smaller than all nodes in r.
-}

data TaskTree a = Void | Node (TaskTree a) a Tasklist (TaskTree a) deriving (Ord,Eq,Show)
type Tasklist = [Task]
type Task = (String, Bool)

-- Modified data-tree operations. Courtesy of Johannes Borgström and PKD-team

findAll :: TaskTree a -> Tasklist
findAll Void  = []
findAll (Node l _ list r) = findAll l ++ list ++ findAll r

{- exists t v
 ...
   RETURNS: True iff v is in t
-}

exists :: (Ord a) => TaskTree a -> a -> Bool
exists Void _ = False
exists (Node l y list r) x 
                    | y == x = True
                    | y < x  = exists r x
                    | y > x  = exists l x

delete :: Eq a => TaskTree a -> a -> TaskTree a 
delete Void _ = Void
delete t@(Node l x list r) y
  | x == y    = deleteRoot t
  | otherwise = (Node (delete l y) x list (delete r y))
  where
    deleteRoot :: TaskTree a -> TaskTree a
    deleteRoot (Node Void _ _ Void)               = Void
    deleteRoot (Node t x list Void)               = deleteRoot (Node Void x list t)
    deleteRoot (Node l _ _ r@(Node rl x list rr)) = Node l x list $ deleteRoot r

{- insert t v
 ...
   RETURNS: A new tree with v and all values in t
-}
insert :: (Ord a) => TaskTree a -> a -> Tasklist -> TaskTree a
insert Void x list = (Node Void x list Void)
insert (Node l y list r) x list'
                      | y == x = (Node l y list' r)
                      | y < x  = (Node l y list (insert r x list'))
                      | y > x  = (Node (insert l x list') y list r)

-- Modified data-tree operations. Courtesy of Johannes Borgström and PKD-team


main :: IO ()
main = do
    contents <- readFile "Test.txt" -- Läser in lagrad data från en textfil               ? hur kan man nå lagrad data ?
    
    putStrLn  "\nWelcome to your HaskMonitor\n\nMenu                           \n1: All tasks                   * - important     \n2: Important only              O - todo     \n3: List manager                X - done\n4: Task manager \nq: quit"
    action <- getLine
    if action == "q" then do
      putStrLn "Have a nice day!"
      return ()
    else if action == "1" then do
      putStrLn "You chose to go to All tasks."
      print ((lines contents)!!2)
       
      ---- always available press "..." to go to main menu
      --1 get list of tasks and print them with putStrLn...
      --2 prompt user to say which task is now finished with getLine
      --3 change the state of element(Task) to done (or remove) 
      --4 update list and memory text-file
      --6 (overwrite memory textfile with new updated version)  
      --5 call on page function recursively(without the crossed of task)


    else if action == "2" then do
      putStrLn "You chose to go to Important tasks only."
      --1 searches all tasks in textfile and isolates the tasks with a sertain co-value (tuple) that indicates importance and print with PutStrLn
      --2 prompt user to say which task is now finished with getLine
      --3 change the state of element(Task) to done (or remove) 
      --4 update list and memory text-file
      --5 (overwrite memory textfile with new updated version)  
      --6 call on page function recursively(without the crossed of task)

    else if action == "3" then do
      putStrLn "You chose to go to List manager."

    else if action == "3" then do
      putStrLn "You chose to go to Task manager."

    else do
      putStrLn "Sorry that doesn't seen to be an option!"

  

    writeFile "Test.txt" (contents ++ "1") -- Uppdaterar textfilen med nya tasks om sådana finns med en hjälpfunktion som lagrar nya tasks i en lista 

--getTasks :: Num a => a -> IO()
--getTasks x = x*x


-- allTasks :: IO ()
-- allTasks = 
--     if important do
--       putStrLn "w"
--     else do return ()

-- --(importance (1/0) , )
-- printTasks :: (a,b,c,Str) -> IO ()
-- printTasks (0,0,c,str) = putStrLn ("O " ++ Str) 
-- printTasks (1,0,c,str) = putStrLn ("O " ++ Str)

--------------------------------------------------------------------------------
-- Test Cases/Material
--------------------------------------------------------------------------------
testTree = undefined
runtests = runTestTT $ TestList []