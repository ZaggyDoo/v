import System.IO ()
import Test.HUnit
import Data.Char ( toUpper )
import Data.List ( delete ) 

-- The HaskMonitor

-- Project group 30: Agron Metaj, Pouria Karami, Zakarie Warsame

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

-- The majority of 

{-  existCat tree category
    DESCRIPTION: A function that checks if a category exists in a tree
    RETURNS: A boolean value representing if the category exists, true or false.
    EXAMPLES: existCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ==
              True
              existCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "School" ==
              False
-}
existCat :: (Ord a) => TaskTree a -> a -> Bool
-- VARIANT: height tree
existCat Void _ = False
existCat (Node l y list r) x
  | y == x = True
  | y < x  = existCat r x
  | y > x  = existCat l x

{-  existTask tree category task
    DESCRIPTION: A function that checks if a task exists in a given category in the tree
    RETURNS: A boolean value representing if the task exists, true or false.
    EXAMPLES: existTask (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ("Deadline", False) == True
              existTask (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "School" ("Dance with Apurva",False) == False
              existTask Void "School" ("Dance with Apurva",False)
-}
existTask :: (Ord a) => TaskTree a -> a  -> Task -> Bool
existTask Void x y = False
existTask (Node l y list r) category task
  | y == category = task `elem` list
  | y < category  = existTask r category task
  | y > category  = existTask l category task


{-  deleteCat tree category
    DESCRIPTION: A function that deletes the node and its list 
    RETURNS: A new tree without the node
    EXAMPLES: deleteCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"   ==
              Node Void "Home" [("Clean",False),("Cook",True)] Void
              deleteCat (Node Void "Home" [("Clean",False),("Cook",True)] Void)  "Home" ==
              Void
-}

deleteCat :: Eq a => TaskTree a -> a -> TaskTree a
-- VARIANT: height tree
deleteCat Void _ = Void
deleteCat t@(Node l x list r) category
  | x == category    = deleteRoot t
  | otherwise = Node (deleteCat l category) x list (deleteCat r category)
  where
    deleteRoot :: TaskTree a -> TaskTree a
    deleteRoot (Node Void _ _ Void)               = Void
    deleteRoot (Node t x list Void)               = deleteRoot (Node Void x list t)
    deleteRoot (Node l _ _ r@(Node rl x list rr)) = Node l x list $ deleteRoot r

{-  deleteTask t category task
    DESCRIPTION: A function that deletes an element from the list binded to its node.
    RETURNS: A new tree from t without task in category's accompanying list at that
    EXAMPLES: deleteTask' Void "" ("Yes", False) == Void
              deleteTask' (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ("Deadline",False) == Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [] Void)
-}

deleteTask' :: (Eq a, Ord a) => TaskTree a -> a -> Task -> TaskTree a
-- VARIANT: height tree
deleteTask' Void _ _ = Void
deleteTask' (Node l y list r) category task
  | y == category = Node l y (delete task list) r
  | y < category  = Node l y list (deleteTask' r category task)
  | y > category  = Node (deleteTask' l category task) y list r

{-  insertCat tree category
    DESCRIPTION: A function that inserts a node with the label a and an empty list 
    RETURNS: A new tree with the updated node and its empty list
    EXAMPLES: insertCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Groceries" == Node (Node Void "Groceries" [] Void) "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)
              insertCat Void "Groceries" == Node Void "Groceries" [] Void
-}

insertCat :: (Ord a) => TaskTree a -> a -> TaskTree a
-- VARIANT: height tree
insertCat Void y  = Node Void y [] Void
insertCat (Node l y list r) x
  | y == x = Node l y list r
  | y < x  = Node l y list (insertCat r x)
  | y > x  = Node (insertCat l x) y list r

{-  insertTask t category task
    DESCRIPTION: A function that finds a category and inserts a task in the corresponding node's list 
    RETURNS: A new tree with the task inserted in to its tasklist
    EXAMPLES: insertTask (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ("Send report",False) == Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Send report",False),("Deadline",False)] Void)
              insertTask Void "Work" ("Send report",False) == Void
-}
insertTask :: (Eq a, Ord a) => TaskTree a -> a -> Task -> TaskTree a
-- VARIANT: height t
insertTask Void category task = Void
insertTask (Node l y list r) category task
  | y == category = Node l y (task : list) r
  | y < category  = Node l y list (insertTask r category task)
  | y > category  = Node (insertTask l category task) y list r

{-  renameCat t a b
    DESCRIPTION: A function that renames a node with the label a to b 
    RETURNS: A new tree with the updated node and its empty list
    EXAMPLES: 
-}
-- VARIANT: height t
renameCat :: (Ord a) => TaskTree a -> a  -> a -> TaskTree a
renameCat Void y z = Void
renameCat (Node l y list r) x z
  | y == x = Node l z list r
  | y < x  = Node l y list (renameCat r x z)
  | y > x  = Node (renameCat l x z) y list r


{-  allCategories t
    DESCRIPTION: A function that returns a list containing all the categories from a tasktree
    RETURNS: A list of the nodes in tree
    EXAMPLES: allCategories (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) == ["Home","Work"]
              allCategories Void == []
-}

allCategories :: TaskTree a -> [a]
-- VARIANT: height tree
allCategories Void = []
allCategories (Node l x list r) = allCategories l ++ [x] ++ allCategories r

{-  allTasks tree
    DESCRIPTION: A function that returns a list containing all the tasks from the tasktree.
    RETURNS: A Tasklist.
    EXAMPLES: allTasks (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) ==
              [("Clean",False),("Cook",True),("Deadline",False)]
              allTasks Void == []
-}
allTasks :: TaskTree a -> Tasklist
-- VARIANT: height tree
allTasks Void  = []
allTasks (Node l _ list r) = allTasks l ++ list ++ allTasks r

{-  findList tree category
    DESCRIPTION: A function that returns the category's list
    RETURNS: The list accompanying category
    EXAMPLES: findList (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" == [("Deadline",False)]
              findList Void "Work" == []
-}

findList :: Ord a => TaskTree a -> a -> Tasklist
-- VARIANT: height t
findList Void _ = []
findList (Node l y list r) category
  | y == category = list
  | y < category  = findList r category
  | y > category  = findList l category

{-  taskStatus l
    DESCRIPTION: A function that returns the same tasklist but changes the second element in the tuple to a character to represent the status instead of using a bool
    RETURNS: A Tasklist.
    EXAMPLES: 
    VARIANT: The amount of tasks in the list 
-}

taskStatus :: Tasklist -> [(String, String)]
taskStatus [] = [("", "")]
taskStatus [x] = if not (snd x) then [(fst x, "O")] else [(fst x, "X")]
taskStatus (x:y:xs) = taskStatus [x] ++ taskStatus (y:xs)


-- END OF PURE FUNCTIONS

--------------------------------------------------------------------------------
-- Main menu
--------------------------------------------------------------------------------
{- main
   DESCRIPTION: A function to greet the user and intitiate the real main function
   EXAMPLES: 
   SIDE-EFFECTS: the main function and a string
-}
main :: IO()
main = do
  let taskTree = Void
  putStrLn "\nWelcome to your Haskmonitor"
  main' taskTree

{- main'
   DESCRIPTION: The actual function that runs the program and prints a menu with options for the user
   EXAMPLES: 
   SIDE-EFFECTS: A lot
-}
main' ::  TaskTree String -> IO ()
main' taskTree = do
  putStrLn  "\nMenu        \n1: All tasks                        O - To-do\n2: View category                    X - Done\n3: Category manager                \n4: Task manager \nQ: Quit"
  action <- getLine
  putStrLn ""
  if action == "1" then do
    putStrLn "All tasks:"
    if null (allTasks taskTree) then do 
      putStrLn "\nYou have no tasks"
      main' taskTree
    else do   
      mapM_ print (taskStatus (allTasks taskTree))
      main' taskTree

  else if action == "2" then do
    viewCategory taskTree

  else if action == "3" then do
    putStrLn "Category manager"
    categoryMenu taskTree

  else if action == "4" then do
    putStrLn "Task manager"
    taskMenu taskTree

  else if map toUpper action == "Q" then do
    putStrLn "If you quit the program, your tasks will go lost. Are you sure you want to quit? Yes or No?"
    action <- getLine 
    if map toUpper action == "YES" then do 
      return ()
    else if map toUpper action == "NO" then do 
      main' taskTree
    else do
      putStrLn "Sorry that doesn't seem to be an option!"
      main' taskTree
  else do
      putStrLn "Sorry that doesn't seem to be an option!"
      main' taskTree

--------------------------------------------------------------------------------
-- Main menu end
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Category menu and functions
--------------------------------------------------------------------------------

{- viewCategory
   DESCRIPTION: The function that asks the user for a category and then prints the list of tasks in that category
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
viewCategory :: TaskTree String -> IO()
viewCategory taskTree = do
  putStrLn "What category would you like to view?"
  mapM_ print(allCategories taskTree)
  categoryName <- getLine
  if existCat taskTree categoryName then do
    mapM_ print (taskStatus (findList taskTree categoryName))
    main' taskTree
  else do
    putStrLn "Sorry that category doesn't seem to exist! Try again!"
    main' taskTree


{- categoryMenu
   DESCRIPTION: The function that is the submenu where the user is given options of different actions on categories
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
categoryMenu :: TaskTree String -> IO ()
categoryMenu taskTree = do
  putStrLn  "\n1: Add category \n2: Remove category \n3: Edit category \nQ: Quit to main menu"
  action <- getLine
  if action == "1" then do
    addCategory taskTree
  else if action == "2" then do
    deleteCategory taskTree
  else if action == "3" then do
    editCategory taskTree
  else if map toUpper action == "Q" then do
    main' taskTree
  else do
      putStrLn "Sorry that doesn't seem to be an option!"
      categoryMenu taskTree

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
    categoryMenu taskTree
  else do
    putStrLn "Category added"
    categoryMenu $ insertCat taskTree categoryName

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
  if existCat taskTree categoryName then do
    putStrLn "Category deleted"
    categoryMenu $ deleteCat taskTree categoryName
  else do 
    putStrLn "That category doesn't exist"
    categoryMenu taskTree  

{- editCategory 
   DESCRIPTION: The function that aids the user in renaming a category, where the user chooses which category
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}

editCategory :: TaskTree String -> IO()
editCategory taskTree = do 
  mapM_ print(allCategories taskTree)
  putStrLn "What category would you like to edit"
  categoryName <- getLine
  putStrLn "What would you like to rename it"
  newName <- getLine
  categoryMenu $ renameCat taskTree categoryName newName


--------------------------------------------------------------------------------
-- Category menu and functions end
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Task menu and functions
--------------------------------------------------------------------------------
{- taskMenu
   DESCRIPTION: The function that is the submenu where the user is given options of different actions on tasks
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
taskMenu :: TaskTree String -> IO ()
taskMenu taskTree = do
  putStrLn " "
  putStrLn  "\n1: Add task \n2: Remove task \n3: Edit task \nQ: Quit to main menu"
  action <- getLine
  if action == "1" then do
    addTask taskTree
  else if action == "2" then do
    deleteTask taskTree
  else if action == "3" then do
    editTask taskTree
  else if map toUpper action == "Q" then do
    main' taskTree
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
  mapM_ print (allCategories taskTree)
  whatCat <- getLine
  if existCat taskTree whatCat then do
    let task = (newTask, False)
    putStrLn "Task has been added"
    taskMenu $ insertTask taskTree whatCat task
  else do
    putStrLn "Sorry that category doesn't seem to exist! Try again!"
    taskMenu taskTree


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
  if existCat taskTree category then do
    mapM_ print (findList taskTree category)
    putStrLn "What task would you like to delete?"
    task <- getLine
    putStrLn "Is the task finished? Yes or no?"
    status <- getLine
    if map toUpper status == "YES" then do
      let taskk = (task, True)
      putStrLn "Well done! Task removed!"
      taskMenu $ deleteTask' taskTree category taskk
    else if map toUpper status == "NO" then do
      let taskk = (task, False)
      putStrLn "Well done! Task removed!"
      taskMenu $ deleteTask' taskTree category taskk
    else do
      putStrLn "Sorry that doesn't seem to be an option!"
      taskMenu taskTree
  else do 
    putStrLn "That category doesn't seem to exist! Try again!"
    taskMenu taskTree
{- editTask
   DESCRIPTION: The function that enables the user in changing a task's name or status, where the user chooses which task to change.
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
editTask :: TaskTree String -> IO ()
editTask taskTree = do
  putStrLn "Is the task you want to change marked as finished? Answer with yes or no!"
  status <- getLine
  if map toUpper status == "YES" then do
      putStrLn "Would you like to edit the status or name? Answer with status or name!"
      choice <- getLine
      if map toUpper choice == "STATUS" then do
        unfinish taskTree
      else if map toUpper choice == "NAME" then do
        renameFinished taskTree
      else do
        putStrLn "Sorry that doesn't seem to be an option!"
        taskMenu taskTree
  else if map toUpper status == "NO" then do
      putStrLn "Would you like to edit the status or name"
      choice <- getLine
      if map toUpper choice == "STATUS" then do
        finish taskTree
      else if map toUpper choice == "NAME" then do
        renameUnfinished taskTree
      else do
          putStrLn "Sorry that doesn't seem to be an option!"
          taskMenu taskTree
  else do
      putStrLn "Sorry that doesn't seem to be an option!"
      taskMenu taskTree


{- finish
   DESCRIPTION: The function that changes the status of a task to finished (True == "X")
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
finish :: TaskTree String -> IO ()
finish taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (taskStatus (findList taskTree category))
  putStrLn "What task would you like to edit?"
  task <- getLine
  if existTask taskTree category (task, False) then do
    let taskk = (task, False)
    let tree = deleteTask' taskTree category taskk
    putStrLn "Well done! Task set to finished."
    taskMenu $ insertTask tree category (task, True)
  else do 
    putStrLn "Sorry that that task doesn't seem to exist! Try again!"
    taskMenu taskTree

{- unfinish
   DESCRIPTION: The function that changes the status of a task to unfinished (False == "O")
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
unfinish :: TaskTree String -> IO ()
unfinish taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (taskStatus(findList taskTree category))
  putStrLn "What task would you like to edit?"
  task <- getLine
  if existTask taskTree category (task, True) then do
    let taskk = (task, True)
    let tree = deleteTask' taskTree category taskk
    putStrLn "Task is now set to not finished."
    taskMenu $ insertTask tree category (task, False)
  else do
    putStrLn "Sorry that that task doesn't seem to exist! Try again!"
    taskMenu taskTree

{-renameFinished
   DESCRIPTION: The function that changes the name of a unfinished task
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}
renameUnfinished :: TaskTree String -> IO ()
renameUnfinished taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (taskStatus(findList taskTree category))
  putStrLn "What task would you like to edit?"
  task <- getLine
  if existTask taskTree category (task, False) then do
    putStrLn "What would you like to name the task?"
    newName <- getLine
    let taskk = (task, False)
    let newNamee = (newName, False)
    let tree = deleteTask' taskTree category taskk
    putStrLn "Task has been renamed."
    taskMenu $ insertTask tree category newNamee
  else do 
    putStrLn "Sorry that that task doesn't seem to exist! Try again!"
    taskMenu taskTree

{-renameFinished
   DESCRIPTION: The function that changes the name of a finished task
   EXAMPLES:
   SIDE-EFFECTS: A lot
-}

renameFinished :: TaskTree String -> IO ()
renameFinished taskTree = do
  mapM_ print (allCategories taskTree)
  putStrLn "What category is the task in?"
  category <- getLine
  mapM_ print (taskStatus(findList taskTree category))
  putStrLn "What task would you like to edit?"
  task <- getLine
  if existTask taskTree category (task, True) then do
    putStrLn "What would you like to name the task?"
    newName <- getLine
    let taskk = (task, True)
    let newNamee = (newName, True)
    let tree = deleteTask' taskTree category taskk
    putStrLn "Task has been renamed."
    taskMenu $ insertTask tree category newNamee
  else do 
    putStrLn "Sorry that that task doesn't seem to exist! Try again!"
    taskMenu taskTree


--------------------------------------------------------------------------------
-- Test Cases/Material
--------------------------------------------------------------------------------
-- existCat
test1 = TestCase $ assertEqual "Category does exist" True $ existCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"
test2 = TestCase $ assertEqual "Category doesn't exist" False $ existCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "School"
test3 = TestCase $ assertEqual "Empty tree" False $ existCat Void "School"
-- existTask
test4 = TestCase $ assertEqual "Empty tree" False $ existTask Void "School" ("Dance with Apurva",False)
test5 = TestCase $ assertEqual "Task doesn't exist" False $ existTask (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "School" ("Dance with Apurva",False)
test6 = TestCase $ assertEqual "Task does exist" True $ existTask (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ("Deadline", False)
-- deleteCat
test7 = TestCase $ assertEqual "Delete Root" Void $ deleteCat (Node Void "Home" [("Clean",False),("Cook",True)] Void)  "Home"
test8 = TestCase $ assertEqual "Empty tree" Void $ deleteCat Void  "Home"
test9 = TestCase $ assertEqual "Simple removal" (Node Void "Home" [("Clean",False),("Cook",True)] Void) $ deleteCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"
-- deleteTask'
test10 = TestCase $ assertEqual "Empty tree" Void $ deleteTask' Void "Groceries" ("Yes", False)
test11 = TestCase $ assertEqual "Remove a task" (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [] Void)) $ deleteTask' (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ("Deadline",False)
-- insertCat
test12 = TestCase $ assertEqual "Simple insert category" (Node (Node Void "Groceries" [] Void) "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) $ insertCat (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Groceries"
test13 = TestCase $ assertEqual "Insert to empty tree" (Node Void "Groceries" [] Void) $ insertCat Void "Groceries"
-- insertTask
test14 = TestCase $ assertEqual "Simple insert task" (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Send report",False),("Deadline",False)] Void)) $ insertTask (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work" ("Send report",False)
test15 = TestCase $ assertEqual "Empty tree" Void $ insertTask Void "Work" ("Send report",False)
--allCategories
test16 = TestCase $ assertEqual "Non-empty tree" ["Home","Work"] $ allCategories (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void))
test17 = TestCase $ assertEqual "Empty tree" "" $ allCategories Void 
--allTasks
test18 = TestCase $ assertEqual "Non-empty tree" [("Clean",False),("Cook",True),("Deadline",False)] $ allTasks (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void))
--findList
test19 = TestCase $ assertEqual "Finding a list" [("Deadline",False)] $ findList (Node Void "Home" [("Clean",False),("Cook",True)] (Node Void "Work" [("Deadline",False)] Void)) "Work"

runtests = runTestTT $ TestList [test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11, test12, test13, test14, test15, test16, test17, test18, test19]