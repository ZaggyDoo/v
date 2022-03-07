{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE BlockArguments #-}
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
    EXAMPLES: existCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ==
              True
              existCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "School" ==
              False
    VARIANT: The amount of nodes in the tree respectively their tasklists.
-}
existCat :: (Ord a) => TaskTree a -> a -> Bool
existCat Void _ = False
existCat (Node l y list r) x
  | y == x = True
  | y < x  = existCat r x
  | y > x  = existCat l x

{-  existTask t a b
    DESCRIPTION: A function that checks if a task exists in a given category in the tree
    RETURNS: A boolean value representing if the task exists, true or false.
    EXAMPLES: 
    VARIANT: The amount of nodes in the tree respectively their tasklists.
-}
existTask :: (Ord a) => TaskTree a -> a  -> Task -> Bool
existTask Void x y = False
existTask (Node l y list r) category task 
  | y == category = task `elem` list
  | y < category  = existTask r category task
  | y > category  = existTask l category task


{-  deleteCat t a
    DESCRIPTION: A function that deletes the node and its list 
    RETURNS: A new tree without the node
    EXAMPLES: deleteCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"   ==
              Node Void "Home" [("Clean",False),("Cook",True)] Void
              deleteCat (Node Void "Home" [("Clean",False),("Cook",True)] Void)  "Home" ==
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

deleteTask' :: (Eq a, Ord a) => TaskTree a -> a -> Task -> TaskTree a
deleteTask' Void _ _ = Void
deleteTask' (Node l y list r) category task
  | y == category = Node l y (delete task list) r
  | y < category  = Node l y list (deleteTask' r category task)
  | y > category  = Node (deleteTask' l category task) y list r


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

{-  insertTask t a b
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

{-  findList t a
    DESCRIPTION: A function that returns the category's list
    RETURNS: A Tasklist.
    EXAMPLES: 
    VARIANT: The amount of nodes in the tree 
-}

findList :: Ord a => TaskTree a -> a -> Tasklist
findList Void _ = []
findList (Node l y list r) category 
  | y == category = list
  | y < category  = findList r category
  | y > category  = findList l category 

{- main
   DESCRIPTION: A function to greet the user and intitiate the real main function
   EXAMPLES: 
   SIDE-EFFECTS: the main function and a string
-}
main :: IO()
main = do 
  putStrLn "\nWelcome to your Haskmonitor"
  main'

{- main
   DESCRIPTION: The actual function that runs the program and prints a menu with options for the user
   EXAMPLES: 
   SIDE-EFFECTS: A lot
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


{- listMenu
   DESCRIPTION: The function that is the submenu where the user is given options of different actions on categories
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
listMenu :: TaskTree String -> IO ()
listMenu taskTree = do
  putStrLn  "\n1: Add category \n2: Remove category \n3: Edit category \nQ: Quit to main menu"
  action <- getLine
  if action == "1" then do
    addCategory taskTree
  else if action == "2" then do
    deleteCategory taskTree
  else if action == "3" then do
    --editCategory taskTree
    main
  else if map toUpper action == "Q" then do
    main'
  else do
      putStrLn "Sorry that doesn't seem to be an option!"
      listMenu taskTree

{- addCategory 
   DESCRIPTION: The function that aids the user in creating a new category, where the user chooses the name
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}

addCategory :: TaskTree String -> IO()
addCategory taskTree = do
  putStrLn "What would you like to name the category?"
  categoryName <- getLine
  if existCat taskTree categoryName then do 
    putStrLn "That category already exists!"
    listMenu taskTree 
  else do 
    return $ insertCat taskTree categoryName -- DATATYP FEL
    listMenu taskTree          

{- deleteCategory 
   DESCRIPTION: The function that aids the user in deleting a category, where the user chooses which one
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}

deleteCategory :: TaskTree String -> IO()
deleteCategory taskTree = do
  mapM_ print(allCategories taskTree)
  putStrLn "What category would you like to delete?"
  categoryName <- getLine
  return $ deleteCat taskTree categoryName -- DATATYP FEL
  listMenu taskTree       

{- editCategory 
   DESCRIPTION: The function that aids the user in renaming a category, where the user chooses which one
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
--EJ KLAR 
{-editCategory :: TaskTree String -> IO()
editCategory taskTree = do 
                mapM_ print(allCategories taskTree)
                putStrLn "What category would you like to edit"
                categoryName <- getLine
                putStrLn "What would you like to rename it"
                newName <- getLine
                let list = findList categoryName 
                deleteCat taskTree categoryName -- DATATYP FEL
                insertCat taskTree newName
                insertTask 
                listMenu taskTree
-}

{- taskMenu
   DESCRIPTION: The function that is the submenu where the user is given options of different actions on tasks
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
taskMenu :: TaskTree String -> IO ()
taskMenu taskTree = do
  putStrLn " "
  putStrLn  "\n1: Add task                        \n2: Remove task                 \n3: Edit task status                            \nQ: Quit to main menu"
  action <- getLine
  if action == "1" then do
    addTask taskTree
    putStrLn "Task has been added"
  else if action == "2" then do
    deleteTask taskTree
    putStrLn "Task has been deleted"
  else if action == "3" then do
    editTask taskTree
    putStrLn ""
  else if map toUpper action == "Q" then do
    main'
  else do
      putStrLn "Sorry that doesn't seem to be an option!"
      taskMenu taskTree

{- addTask 
   DESCRIPTION: The function that aids the user in creating a new task, where the user chooses the name and later adds it to a category of their choice
   EXAMPLES:
   SIDE-EFFECTS: A lot
   PRE: The category must exist
-}
addTask :: TaskTree String -> IO ()
addTask taskTree = do
  putStrLn "What task would you like to add?"
  newTask  <- getLine
  putStrLn "What category would you like to add the task to?"
  whatCat <- getLine
  if existCat taskTree whatCat then do 
    let category = find (== whatCat) (allCategories taskTree)
    let task = (newTask, False)
    return $ insertTask taskTree category task
    putStrLn "Task has been added"
  else do putStrLn "Sorry that doesn't seem to be an option! Try again!"


{- deleteTask
   DESCRIPTION: The function that enables the user in deleting a task.
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
deleteTask :: TaskTree String -> IO ()
deleteTask taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (findList taskTree category)
  putStrLn "What task would you like to delete?"
  task <- getLine
  putStrLn "Is the task finished? Yes or no?"
  status <- getLine
  if map toUpper status == "YES" then do
    let taskk = (task, True)
    return $ deleteTask' taskTree category taskk
    putStrLn "Well done! Task removed!"
  else if map toUpper status == "NO" then do
    let taskk = (task, False)
    return $ deleteTask' taskTree category taskk
    putStrLn "Okay, task will remain"
  else do  
    putStrLn "Sorry that doesn't seem to be an option!"

{- editTask
   DESCRIPTION: The function that enables the user in changing a task's name or status, where the user chooses which task to change.
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
editTask :: TaskTree String -> IO ()
editTask taskTree = do
  putStrLn "Is the task you want to change finished? Yes or no?"
  status <- getLine
  if map toUpper status == "YES" then do
      putStrLn "Would you like to edit the status or name"
      choice <- getLine 
      if map toUpper choice == "STATUS" then do 
        finished taskTree
      else if map toUpper choice == "NAME" then do 
        renameFinished taskTree
      else do 
        putStrLn "Sorry that doesn't seem to be an option!"
  else if map toUpper status == "NO" then do
      putStrLn "Would you like to edit the status or name"
      choice <- getLine 
      if map toUpper choice == "STATUS" then do 
        unFinished taskTree
      else if map toUpper choice == "NAME" then do 
        renameUnfinished taskTree 
      else do 
          putStrLn "Sorry that doesn't seem to be an option!" 
  else do 
      putStrLn "Sorry that doesn't seem to be an option!"
 
-- Helper function that makes a task finished
finished :: TaskTree String -> IO ()
finished taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (findList taskTree category)
  putStrLn "What task would you like to edit?"
  task <- getLine   
  let taskk = (task, False)
  return $ deleteTask' taskTree category taskk
  return $ insertTask taskTree category (task, False) 
  putStrLn "Well"

-- Helper function that undoes a task
unFinished :: TaskTree String -> IO ()
unFinished taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (findList taskTree category)
  putStrLn "What task would you like to edit?"
  task <- getLine
  let taskk = (task, True)
  return $ deleteTask' taskTree category taskk 
  return $ insertTask taskTree category (task, False) 
  taskMenu taskTree

-- Helper function that edits an unfinished task's name
renameUnfinished :: TaskTree String -> IO ()
renameUnfinished taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (findList taskTree category)
  putStrLn "What task would you like to edit?"
  task <- getLine 
  putStrLn "What would you like to name the task?"
  newName <- getLine
  let taskk = (task, False)
  let newNamee =(newName, False)
  return $ deleteTask' taskTree category taskk 
  return $ insertTask taskTree category newNamee 
  taskMenu taskTree


-- Helper function that edits a finished task's name if the user wishes to do so
renameFinished :: TaskTree String -> IO ()
renameFinished taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (findList taskTree category)
  putStrLn "What task would you like to edit?"
  task <- getLine        
  putStrLn "What would you like to name the task?"
  newName <- getLine
  let taskk = (task, True)
  let newNamee =(newName, True)
  return $ deleteTask' taskTree category taskk 
  return $ insertTask taskTree category newNamee
  putStrLn "Task has been renamed"
      
       
 
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
--runtests = runTestTT $ TestList []