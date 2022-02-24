import System.IO ()
import qualified Distribution.SPDX as PutStrLn

{-  A general tree with different task-categorys, subtrees are categorys with Tasklist as leafs
     -The empty tree and or leaf is given by Void
     -A non-empty TaskTree with label taskCategory has subtrees with a different label taskCategory and is given by Node taskCategory
     INVARIANT: For the moment unknown, looking up definition and doing research
  -}
data TaskTree taskCategory = Void | Node (TaskTree taskCategory Tasklist) taskCategory Tasklist (TaskTree taskCategory Tasklist)
type Tasklist = [Task]
type Task = (String, Bool)

main :: IO ()
main = do
    contents <- readFile "Test.txt" -- Läser in lagrad data från en textfil
    putStrLn  "\nWelcome to your HaskMonitor\n\nMenu                           \n1: All tasks                   * - important     \n2: Important only              O - todo     \n3: List manager                X - done\n4: Task manager \nq: quit"
    action <- getLine 
    if action == "q" then do 
      putStrLn "Have a nice day!"
      return ()
    else if action == "1" then do
      putStrLn "You chose to go to All tasks."
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
    
    print contents -- Printar den data vi vill visa a.k.a tasks med hjälp av en processing funktion senare
    
    writeFile "Test.txt" (contents ++ "1") -- Uppdaterar textfilen med nya tasks om sådana finns med en hjälpfunktion som lagrar nya tasks i en lista 

testTree = Node "All Tasks" [
  Node "Groceries" [
  TaskLeaf [("Apples", False), ("Oranges", False)]],
  Node "Important" [
  TaskLeaf [("Finish datatypes", False), ("Get to Diamond1",False)]]
  ]

{- find t v
 ...
   RETURNS: True iff v is in t
-}
find :: (Ord a) => BSTree a -> a -> Bool
find Void _ = False
find (Node l y r) x | y == x = True
                    | y < x  = find r x
                    | y > x  = find l x