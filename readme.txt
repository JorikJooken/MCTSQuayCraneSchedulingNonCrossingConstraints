The source code can be found in the file "MCTS.cpp"

************************************************************************************************

An example of a toy problem instance can be found in the file "toyInstance.txt"

The first line of this file contains two integers: n and m, which denote the number of bays and quay cranes respectively.
The next line contains n space separated integers, which denote the processing times of the bays.

************************************************************************************************

The file "MCTSParameters.txt" contains the parameters that the algorithm will use.
The first line contains the number t, which denotes the amount of seconds for which the algorithm will run.
The second line contains the integer w, which denotes the beam width.


************************************************************************************************

To execute a problem instance, first compile the source code (we assume a linux environment):

g++ -g -std=c++11 -O2 MCTS.cpp -o MCTSExecutable

Now, run the executable on the toy problem instance and write the output to a file called "MCTSOutput.txt"

./MCTSExecutable < toyInstance.txt > MCTSOutput.txt

