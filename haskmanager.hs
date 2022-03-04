{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
import System.IO ()
import Test.HUnit
import Data.Char
import Data.List

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

{-  existCat t a
    DESCRIPTION: A function that checks if a category exists in a tree
    RETURNS: A boolean value representing if the category exists, true or false.
    EXAMPLES: exists (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ==
              True
              exists (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "School" ==
              False
    VARIANT: The amount of nodes in the tree respectively their tasklists.
-}
existCat :: (Ord a) => TaskTree a -> a -> Bool
existCat Void _ = False
existCat (Node l y list r) x
                    | y == x = True
                    | y < x  = existCat r x
                    | y > x  = existCat l x

existTask :: (Ord a) => TaskTree a -> a  -> Task -> Bool
existTask Void x y = False
existTask (Node l y list r) category task 
                    | y == category = task `elem` list
                    | y < category  = existTask r category task
                    | y > category  = existTask l category task


{-  deleteCat t a
    DESCRIPTION: A function that deletes the node and its list 
    RETURNS: A new tree without the node
    EXAMPLES: delete (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"   ==
              Node Void "Home" [("Clean",False),("Cook",True)] Void
              delete (Node Void "Home" [("Clean",False),("Cook",True)] Void)  "Home" ==
              Void
    VARIANT: The amount of nodes in the tree.
-}

deleteCat :: Eq a => TaskTree a -> a -> TaskTree a
deleteCat Void _ = Void
deleteCat t@(Node l x list r) category
  | x == category    = deleteRoot t
  | otherwise = Node (deleteCat l category) x list (deleteCat r category)
  where
    deleteRoot :: TaskTree a -> TaskTree a
    deleteRoot (Node Void _ _ Void)               = Void
    deleteRoot (Node t x list Void)               = deleteRoot (Node Void x list t)
    deleteRoot (Node l _ _ r@(Node rl x list rr)) = Node l x list $ deleteRoot r

{-  deleteTask t a b
    DESCRIPTION: A function that deletes an element from the list binded to its node.
    RETURNS: A new tree without the element in the list at that node
    EXAMPLES: 
    VARIANT: The amount of nodes in the tree.
-}

deleteTask :: (Eq a, Ord a) => TaskTree a -> a -> Task -> TaskTree a
deleteTask Void _ _ = Void
deleteTask (Node l y list r) category task
                        | y == category = Node l y (delete task list) r
                        | y < category  = Node l y list (deleteTask r category task)
                        | y > category  = Node (deleteTask l category task) y list r


{-  insertCat t a
    DESCRIPTION: A function that inserts a node with the label a and an empty list 
    RETURNS: A new tree with the updated node and its empty list
    EXAMPLES: 
    VARIANT: The amount of nodes in the tree.
-}

insertCat :: (Ord a) => TaskTree a -> a -> TaskTree a
insertCat Void y  = Node Void y [] Void
insertCat (Node l y list r) x 
                      | y == x = Node l y list r
                      | y < x  = Node l y list (insertCat r x)
                      | y > x  = Node (insertCat l x) y list r

{-  insertTask t a
    DESCRIPTION: A function that finds a category and inserts a task in the corresponding node's list 
    RETURNS: A new tree with the task inserted in to its tasklist
    EXAMPLES: 
    VARIANT: The amount of nodes in the tree.
-}
insertTask :: (Eq a, Ord a) => TaskTree a -> a -> Task -> TaskTree a
insertTask Void category task = Void
insertTask (Node l y list r) category task
                      | y == category = Node l y (task : list) r
                      | y < category  = Node l y list (insertTask r category task)
                      | y > category  = Node (insertTask l category task) y list r

-- End of modified data-tree operations. Courtesy of Johannes Borgström and PKD-team



{-  allCategories t
    DESCRIPTION: A function that returns a list containing all the categories from a tasktree
    RETURNS: A list of the nodes in t
    EXAMPLES: 
    VARIANT: The amount of nodes in the tree 
-}

allCategories :: TaskTree a -> [a]
allCategories Void = []
allCategories (Node l x list r) = allCategories l ++ [x] ++ allCategories r 

{-  allTasks t
    DESCRIPTION: A function that returns a list containing all the tasks from the tasktree.
    RETURNS: A Tasklist.
    EXAMPLES: allTasks (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) ==
              [("Clean",False),("Cook",True),("Deadline",False)]
    VARIANT: The amount of nodes in the tree 
-}
allTasks :: TaskTree a -> Tasklist
allTasks Void  = []
allTasks (Node l _ list r) = allTasks l ++ list ++ allTasks r

findList :: Ord a => TaskTree a -> a -> Tasklist
findList Void _ = []
findList (Node l y list r) category 
                      | y == category = list
                      | y < category  = findList r category
                      | y > category  = findList l category 

{-
main :: IO()
main = do 
        putStrLn "\nWelcome to your Haskmonitor"
        main'

{- main
   DESCRIPTION: The function that initiates the program and prints the menu and offers the user options
   EXAMPLES: Får väl testa när det funkar och se
   SIDE-EFFECTS: Bara Gud vet hur många som finns.
-}

main' :: IO ()
main' = do
    contents <- readFile "Test.txt"               
    let taskTree = Void -- parsing funktionen kommer in här
    putStrLn  "\nMenu                           \n1: All tasks                   * - important     \n2: Important only              O - todo     \n3: List manager                X - done\n4: Task manager \nQ: quit"
    action <- getLine
    putStrLn ""
    if action == "1" then do
      putStrLn "All tasks"
      mapM_ print (allTasks taskTree)

    else if action == "2" then do
      putStrLn "Important tasks"

    else if action == "3" then do
      putStrLn "List manager"
      listMenu taskTree

    else if action == "4" then do
      putStrLn "Task manager"
      taskMenu taskTree

    else if map toUpper action == "Q" then do 
      putStrLn "Have a nice day!"
      return ()
      else do
        putStrLn "Sorry that doesn't seem to be an option!"
        main'



listMenu :: TaskTree String -> IO ()
listMenu taskTree = do
              putStrLn  "\n1: Add category \n2: Remove category \n3: Edit category \nQ: Quit to main menu"
              action <- getLine
              if action == "1" then do
                addCategory taskTree
              else if action == "2" then do
                deleteCategory taskTree
              else if action == "3" then do
                editCategory taskTree
              else if map toUpper action == "Q" then do
                main'
              else do
                 putStrLn "Sorry that doesn't seem to be an option!"
                 listMenu taskTree

addCategory :: TaskTree String -> IO()
addCategory taskTree = do
                putStrLn "What would you like to name the category?"
                categoryName <- getLine
                if existCat taskTree categoryName then do 
                  putStrLn "That category already exists!"
                  listMenu taskTree 
                else do 
                  --insertCat taskTree categoryName
                  listMenu taskTree          

deleteCategory :: TaskTree String -> IO()
deleteCategory taskTree = do
                putStrLn "What category would you like to delete?"
                categoryName <- getLine
                --delete taskTree categoryName
                listMenu taskTree       

editCategory = undefined 


taskMenu :: TaskTree String -> IO ()
taskMenu taskTree = do
              putStrLn " "
              putStrLn  "\n1: Add task                        \n2: Remove task                 \n3: Edit task status                            \nQ: Quit to main menu"
              action <- getLine
              if action == "1" then do
                addTask taskTree
              else if action == "2" then do
                deleteTask taskTree
              else if action == "3" then do
                editTask taskTree
              else if map toUpper action == "Q" then do
                main'
              else do
                 putStrLn "Sorry that doesn't seem to be an option!"
                 taskMenu taskTree


addTask :: TaskTree String -> IO ()
addTask taskTree = do
        putStrLn "What task would you like to add?"
        newTask  <- getLine
        putStrLn "What category would you like to add the task to?"
        whatCat <- getLine
        if existCat taskTree whatCat then do 
          let category = find (== whatCat) (allCategories taskTree)
          let task = (newTask, False)
          insertTask taskTree category newTask
        else do putStrLn "Sorry that doesn't seen to be an option! Try again!"

deleteTask :: TaskTree String -> IO ()
deleteTask taskTree = do
        mapM_ print (allCategories taskTree)
        putStrLn "What category is the task in?"
        cat <- getLine
        mapM_ print (findList taskTree cat)
        putStrLn "What task would you like to delete?"
        task <- getLine
        let task = (task, False)
        if existTask taskTree -- ej klar

--editTask = undefined



{-
editTask :: TaskTree String -> IO ()
editTask taskTree = do
        putStrLn "What task would you like to edit?"
        task  <- getLine
        if exists taskTree task then do
          putStrLn "Would you like to change the task's name or status"
          choice <- getLine 
        ifmap toUpper choice == "NAME" then do
            putStrLn "What would you like to name the task?"
            else if map toUpper choice == "STATUS" then do
              deleteTask taskTree
            else do putStrLn "Sorry that doesn't seen to be an option! Try again!"
             putStrLn "Would you like to change the task's name or status"
             choice <- getLine
            putStrLn "What would you like to name the category?"
          categoryName <- getLine
          let newTaskTree = insert taskTree categoryName [(newTask, False)]
          mapM_ print(findAll newTaskTree)
        else if map toUpper newCat == "NO" then do
          let newTaskTree = insert taskTree "" [(newTask, False)]
          mapM_ print(findAll newTaskTree)
        else do putStrLn "Sorry that doesn't seen to be an option! Try again!"
-}
 
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
--testTree = undefined
--runtests = runTestTT $ TestList []-}