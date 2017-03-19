module CommandLine.HelpMessage where

  helpMessage :: String
  helpMessage = ""
    ++ "gameinfo - displays information about the current state of the game\n"
    ++ "pause - display the message \"Press ENTER to continue . . .\" until the ENTER key is pressed\n\n"
    ++ "help - print this helpMessage\n\n"
    ++ "select [LOCATION] - selects a square on the board\n\n"
    ++ "moveto [LOCATION] - moves the piece at the selected square to the specified LOCATION\n\n"
    ++ "move [START] (\"to\") [DESTINATION] - moves the piece at the START to the DESTINATION\n\n"
    ++ "view [VIS_T] [N] [VIS_X] [VIS_Y] - sets the perspective of the board such that VIS_X is presented horizontally, VIS_Y is presented vertically, and the entire board being presented under VIS_T at level [N]\n\n"
    ++ "view [LEVEL] - sets the perspective of the board. Infers VIS_T VIS_X and VIS_Y by weather LEVEL is a letter, a digit, or a roman numeral\n\n"
    ++ "quit - quits the game\n\n"
