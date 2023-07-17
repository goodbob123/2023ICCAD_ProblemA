PP := g++
CC := gcc
CFLAGS := -g -O3 -DNDEBUG
LDFLAGS := -lm -ldl -lreadline -lpthread

TARGET := bmatch
SRCS := ./src/bmatch.cpp ./src/aigtoaig.c ./src/aiger.c ./src/SAT/test/File.cpp ./src/SAT/test/Proof.cpp ./src/SAT/test/Solver.cpp ./src/bmatchSolver.cpp \
  ./src/cir/cirFraig.cpp ./src/cir/cirGate.cpp ./src/cir/cirMgr.cpp ./src/cir/cirSim.cpp
  
OBJS := $(SRCS:.cpp=.o)
OBJS := $(OBJS:.c=.o)

.PHONY: all clean

all: $(TARGET)

$(TARGET): $(OBJS) ./lib/libabc.a
	$(PP) $(CFLAGS) $(OBJS)  ./lib/libreadline.so.6 ./lib/libabc.a -o $(TARGET) -L. $(LDFLAGS)

./src/aiger.o: ./src/aiger.h ./src/aiger.c
	$(CC) $(CFLAGS) -c ./src/aiger.c -o ./src/aiger.o

./src/aigtoaig.o: ./src/aigtoaig.c ./src/aiger.h
	$(CC) $(CFLAGS) -c  ./src/aigtoaig.c -o ./src/aigtoaig.o

./src/SAT/test/File.o: ./src/SAT/test/File.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/SAT/test/File.cpp -o ./src/SAT/test/File.o

./src/SAT/test/Proof.o: ./src/SAT/test/Proof.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/SAT/test/Proof.cpp -o ./src/SAT/test/Proof.o

./src/SAT/test/Solve.o: ./src/SAT/test/Solver.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/SAT/test/Solver.cpp -o ./src/SAT/test/Solver.o

./src/bmatch.o: ./src/bmatch.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/bmatch.cpp -o ./src/bmatch.o

./src/bmatchSolver.o: ./src/bmatchSolver.cpp ./src/bmatchSolver.h 
	$(PP) $(CFLAGS) -std=c++11 -c ./src/bmatchSolver.cpp -o ./src/bmatchSolver.o

./src/cir/cirFraig.o: ./src/cir/cirFraig.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/cir/cirFraig.cpp -o ./src/cir/cirFraig.o

./src/cir/cirGate.o: ./src/cir/cirGate.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/cir/cirGate.cpp -o ./src/cir/cirGate.o

./src/cir/cirMgr.o: ./src/cir/cirMgr.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/cir/cirMgr.cpp -o  ./src/cir/cirMgr.o

./src/cir/cirSim.o: ./src/cir/cirSim.cpp
	$(PP) $(CFLAGS) -std=c++11 -c ./src/cir/cirSim.cpp -o ./src/cir/cirSim.o


clean:
	rm -rf $(OBJS) $(TARGET)
	rm -rf match support name *.aig *.aag ./src/SAT/test/*.o
	rm -rf CAD_testdata/case*/match CAD_testdata/case*/*.aag
