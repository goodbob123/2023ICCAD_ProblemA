satTest: clean File.o Proof.o Solver.o satTest.o
	g++ -o $@ -std=c++20 -g -fsanitize=address File.o Proof.o Solver.o satTest.o

File.o: File.cpp
	g++ -c -std=c++20 -g -fsanitize=address File.cpp

Proof.o: Proof.cpp
	g++ -c -std=c++20 -g -fsanitize=address Proof.cpp

Solve.o: Solver.cpp
	g++ -c -std=c++20 -g -fsanitize=address Solver.cpp

satTest.o: satTest.cpp
	g++ -c -std=c++20 -g -fsanitize=address satTest.cpp

clean:
	rm -f *.o satTest tags
