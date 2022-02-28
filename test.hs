import System.IO ()



main :: IO ()
main = do
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

    {-
main :: IO ()
  {- main 
     RETURNS: ... 
     SIDE EFFECTS: 
     EXAMPLES: 
   -}
main = do
    putStrLn  "\nWelcome to your HaskMonitor\n\nMenu                           🚩 - important\n1: All tasks                   🟥 - todo     \n2: Important only              ✅ - done     \n3: List manager\n4: Task manager"
    action <- getLine
    putStrLn "You chose to go to" 

function :: ... -> ...
  {- empty function x
     RETURNS: ...
   -}
function = undefined 
   
function :: ... -> ...
  {- empty function x
     RETURNS: ...
   -}
function = undefined 
   
function :: ... -> ...
  {- empty function x
     RETURNS: ...
   -}
function = undefined 

function :: ... -> ...
  {- empty function x
     RETURNS: ...
   -}
function = undefined 

function :: ... -> ...
  {- empty function x
     RETURNS: ...
   -}
function = undefined 
-}