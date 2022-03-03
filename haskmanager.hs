{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
import System.IO ()
import Test.HUnit
import Data.Char

-- Project group 30: Agron Metaj, Pouria Karami, Zakarie Warsame
-- The HaskMonitor


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

{-  findAll t
    DESCRIPTION: A function that returns a list containing all the tasks from the tasktree.
    RETURNS: A Tasklist.
    EXAMPLES: findAll (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) ==
              [("Clean",False),("Cook",True),("Deadline",False)]
    VARIANT: The amount of nodes in the tree respectively their tasklists.
-}
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

{-  delete t a
    DESCRIPTION: A function that deletes the node equivalent to the input 
    RETURNS: A new tree without the node
    EXAMPLES: delete (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"   ==
              Node Void "Home" [("Clean",False),("Cook",True)] Void
              delete (Node Void "Home" [("Clean",False),("Cook",True)] Void)  "Home" ==
              Void
    VARIANT: The amount of nodes in the tree.
-} 

delete :: Eq a => TaskTree a -> a -> TaskTree a 
delete Void _ = Void
delete t@(Node l x list r) y
  | x == y    = deleteRoot t
  | otherwise = Node (delete l y) x list (delete r y)
  where
    deleteRoot :: TaskTree a -> TaskTree a
    deleteRoot (Node Void _ _ Void)               = Void
    deleteRoot (Node t x list Void)               = deleteRoot (Node Void x list t)
    deleteRoot (Node l _ _ r@(Node rl x list rr)) = Node l x list $ deleteRoot r

{-  insert t a
    DESCRIPTION: A function that inserts the node equivalent to the first input and a accompanying list of tasks 
    RETURNS: A new tree with the updated node and its list
    EXAMPLES: insert Void "Home" [("Clean", False), ("Cook", True)] ==
              Node Void "Home" [("Clean",False),("Cook",True)] Void
    VARIANT: The amount of nodes in the tree.
-} 

insert :: (Ord a) => TaskTree a -> a -> Tasklist -> TaskTree a
insert Void x list = Node Void x list Void
insert (Node l y list r) x list'
                      | y == x = Node l y list' r
                      | y < x  = Node l y list (insert r x list')
                      | y > x  = Node (insert l x list') y list r

-- End of modified data-tree operations. Courtesy of Johannes Borgström and PKD-team


{- main
   DESCRIPTION: The function that initiates the program and prints the menu and offers the user options
   EXAMPLES: Får väl testa när det funkar och se
   SIDE-EFFECTS: Bara Gud vet hur många som finns.
-}
main :: IO ()
main = do
    contents <- (readFile) "Test.txt" -- Läser in lagrad data från en textfil               ? hur kan man nå lagrad data ?
    --let (undefined contents) = taskTree -- binder innehållet från textfilen till taskTree efter parsing funktionen
    putStrLn  "\nWelcome to your HaskMonitor\n\nMenu                           \n1: All tasks                   * - important     \n2: Important only              O - todo     \nQ: quit                        X - done\n4: Task manager "
    action <- getLine
    if map toUpper action == "Q" then do
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

    else if action == "4" then do
      putStrLn "You chose to go to Task manager."

        
      else do
        putStrLn "Sorry that doesn't seem to be an option!"
        main

  

--    writeFile "Test.txt" (contents ++ "1") -- Uppdaterar textfilen med nya tasks om sådana finns med en hjälpfunktion som lagrar nya tasks i en lista 

taskMenu :: IO ()
taskMenu = do 
              putStrLn " " 
              putStrLn  "\n1: Add task                        \n2: Remove task                 \n3: Edit task status                \nAdd category            \nQ: quit to main menu"
              action <- getLine
              if action == "1" then do
                addTask taskTree
              else if action == "2" then do 
                deleteTask taskTree
              else do 
                 putStrLn "Sorry that doesn't seem to be an option!"
                 taskMenu

                 
addTask :: TaskTree String -> IO ()
addTask taskTree = do
        putStrLn "What task would you like to add?"
        newTask  <- getLine
        putStrLn "What category do you want to add to?" 
        newCat <- getLine
        if map toUpper newCat == "YES" then do 
          putStrLn "What would you like to name the category?"
          categoryName <- getLine
          let newTaskTree = insert taskTree categoryName [(newTask, False)]
          mapM_ print(findAll newTaskTree)
        else if map toUpper newCat == "NO" then do 
          let newTaskTree = insert taskTree "" [(newTask, False)]
          mapM_ print(findAll newTaskTree)
        else do putStrLn "Sorry that doesn't seen to be an option! Try again!"

deleteTask :: TaskTree String -> IO ()
deleteTask taskTree = do
        mapM_ print (findAll taskTree) 
        putStrLn "What task would you like to delete?"
        newTask  <- getLine
        putStrLn "Would you like to add a category, yes or no?" 
        newCat <- getLine
        if map toUpper newCat == "YES" then do 
          putStrLn "What would you like to name the category?"
          categoryName <- getLine
          let newTaskTree = insert taskTree categoryName [(newTask, False)]
          mapM_ print(findAll newTaskTree)
        else if map toUpper newCat == "NO" then do 
          let newTaskTree = insert taskTree "" [(newTask, False)]
          mapM_ print(findAll newTaskTree)
        else do putStrLn "Sorry that doesn't seen to be an option! Try again!"


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

