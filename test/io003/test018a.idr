module Main

import System
import System.Concurrency.Process

ping : ProcID String -> ProcID String -> Process String ()
ping main proc
   = do Lift (usleep 1000)
        send proc "Hello!"
        Lift (putStrLn "Sent ping")
        msg <- recv
        Lift (putStrLn ("Reply: " ++ show msg))
        send main "Done"

pong : Process String ()
pong = do -- Lift (putStrLn "Waiting for message")
          (sender, m) <- recvWithSender
          Lift $ putStrLn ("Received " ++ m)
          send sender ("Hello back!")

mainProc : Process String ()
mainProc = do mainID <- myID
              pongth <- create pong
              pingth <- create (ping mainID pongth)
              recv -- block until everything done
              return ()

repeatIO : Int -> IO ()
repeatIO 0 = return ()
repeatIO n = do printLn n
                run mainProc
                repeatIO (n - 1)

main : IO ()
main = repeatIO 100

