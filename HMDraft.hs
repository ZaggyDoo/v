 import System.IO
 main:: IO () 
 main = do    
    putStrLn  "\nWelcome to your HaskMonitor\n\nMenu                           \n1: All tasks                   * - important     \n2: Important only              O - todo     \n3: List manager                X - done\n4: Task manager \nq: quit"
    action <- getLine 
    case action of 
        "1" -> putStrLn "You chose to go to All tasks."
        "2" -> putStrLn "You chose to go to Important tasks only."
        "3" -> putStrLn "You chose to go to List manager."
        "4" -> putStrLn "You chose to go to Task manager."
        "q" -> putStrLn "Have a nice day!" 
        "a" -> putStrLn "Sorry that doesn't seen to be an option!"