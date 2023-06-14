CC_FLAGS = -std=c++2a
OPT_FLAGS = -O3
DBG_FLAGS = -g -fsanitize=address

satTest: clean File.o Proof.o Solver.o satTest.o
	g++ -o $@ $(CC_FLAGS) $(OPT_FLAGS) File.o Proof.o Solver.o satTest.o

File.o: File.cpp
	g++ -c $(CC_FLAGS) $(OPT_FLAGS) File.cpp

Proof.o: Proof.cpp
	g++ -c $(CC_FLAGS) $(OPT_FLAGS) Proof.cpp

Solve.o: Solver.cpp
	g++ -c $(CC_FLAGS) $(OPT_FLAGS) Solver.cpp

satTest.o: satTest.cpp
	g++ -c $(CC_FLAGS) $(OPT_FLAGS) satTest.cpp

satTest_dbg:
	g++ -o satTest $(CC_FLAGS) $(DBG_FLAGS) File_dbg.o Proof_dbg.o Solver_dbg.o satTest_dbg.o

File_dbg.o: File.cpp
	g++ -c $(CC_FLAGS) $(DBG_FLAGS) File.cpp

Proof_dbg.o: Proof.cpp
	g++ -c $(CC_FLAGS) $(DBG_FLAGS) Proof.cpp

Solver_dbg.o: Solver.cpp
	g++ -c $(CC_FLAGS) $(DBG_FLAGS) Solver.cpp

satTest_dbg.o: satTest.cpp
	g++ -c $(CC_FLAGS) $(DBG_FLAGS) satTest.cpp

test02: satTest
	./satTest ../CAD_testdata/case02/name ../CAD_testdata/case02/circuit_1.aag ../CAD_testdata/case02/circuit_2.aag ../CAD_testdata/case02/out

clean:
	rm -f *.o satTest tags
